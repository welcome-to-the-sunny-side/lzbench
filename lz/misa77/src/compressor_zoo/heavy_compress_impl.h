// misa77 - A codec optimized for decompression throughput
// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Shreyas Ghildiyal <nonadhocproblems@gmail.com>

#pragma once

#include "format.h"
#include "misa77/misa77.h"
#include "util.h"

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <vector>

namespace misa77
{
    namespace heavy_detail
    {
        using namespace heavy;

        constexpr uint64_t max_chain = 2048; // hash-chain walk limit
        constexpr uint64_t nice_len = 192;   // stop the walk once a match this long is found
        constexpr uint64_t accept_len = 5;   // min match length to accept (>= min_match_len)
        constexpr uint64_t lazy_gain = 1; // defer only if (pos + 1)'s match beats pos's by >= this
        constexpr float cond_flag_thresh = 0.14f; // set the conditional-decode flag if fraction of
                                                  // long matches below this, empirically chosen

        constexpr uint32_t hash_bits = 21;
        constexpr uint32_t NIL = UINT32_MAX;

        // 5-byte hash
        [[gnu::always_inline]]
        inline uint32_t hash5(const uint8_t* p)
        {
            uint64_t x = loadu8(p) & 0xFFFFFFFFFFULL;
            return uint32_t((x * 0x9E3779B185EBCA87ULL) >> (64 - hash_bits));
        }

        // Assuming that rem contains 6 bits specifying match length in token, emits bytes
        // specifying `n`.
        [[gnu::always_inline]]
        inline void emit_length_extras(uint8_t* dst, uint64_t& dlpos, uint64_t n, uint8_t rem)
        {
            if (rem != uint8_t(63)) [[likely]]
                return;

            // Write this unconditionally first, if it's wrong we'll just overwrite
            dst[dlpos] = static_cast<uint8_t>(n);

            constexpr uint64_t block = 255;
            if (n >= block) [[unlikely]]
            {
                while (n >= block) [[unlikely]]
                    dst[dlpos] = block, ++dlpos, n -= block;
                dst[dlpos] = static_cast<uint8_t>(n);
            }

            ++dlpos;
        }
    } // namespace heavy_detail

    // Returns number of bytes written to `dst`, and 0 on failure.
    // `isa_lib` is ISA-dependent.
    template <class isa_lib>
    uint64_t heavy_compress_impl(const uint8_t* __restrict src,
                                 uint64_t src_size,
                                 uint8_t* __restrict dst,
                                 uint64_t dst_cap)
    {
        using namespace heavy;
        using namespace heavy_detail;

        if (compress_bound(src_size, config(config::heavy_lb)) > dst_cap)
            return 0;

        auto lcp_long = [&](const uint8_t* a, const uint8_t* b, uint32_t max_len) -> uint32_t
        {
            uint32_t i = 0;
            while (i + vector_width <= max_len)
            {
                uint32_t len = isa_lib::lcp(isa_lib::loadvec(a + i), isa_lib::loadvec(b + i));
                i += len;
                if (len < vector_width)
                    return i;
            }
            while (i < max_len and a[i] == b[i])
                ++i;
            return i;
        };

        // Left pointer in the destination buffer (metadata and control bytes)
        uint64_t dlpos = 0;

        // Right pointer in the destination buffer (literal bytes)
        // We've written to `[drpos, dst_cap)` at any given point of time
        uint64_t drpos = dst_cap;

        storeu8(dst, src_size | (uint64_t(1) << (format_bit + 56)));
        dlpos += 8;

        if (src_size <= small_lim)
        {
            if (src_size != 0)
                memcpy(dst + dlpos, src, src_size);
            dlpos += src_size;
            return dlpos;
        }

        uint64_t literal_suffix_pos = dlpos;
        dlpos += 8;

        // Ensure that the last `literal_suffix` bytes will be literals
        uint64_t match_end_limit = (src_size < literal_suffix ? 0 : src_size - literal_suffix);

        // Beginning of the pending literal window
        uint64_t lit = 0;

        // `[lit, pos]` corresponds to the new range from the src buffer we're going to be
        // turning into a lit + match pair
        uint64_t pos = 0;

        // `[0, hpos)` represents the range we've written into the hashtable
        uint64_t hpos = 0;

        uint64_t miss_run = 0;

        // Token stats for the conditional-decode bit
        uint64_t tokens = 0;
        uint64_t long_matches = 0;

        // chains
        const uint64_t ring_size = uint64_t(1) << (win_bits + 1);
        const uint64_t ring_mask = ring_size - 1;
        std::vector<uint32_t> head(uint64_t(1) << hash_bits, NIL);
        std::vector<uint32_t> prev(ring_size, NIL);

        // distance to previously accepted
        uint32_t seed = 0;

        auto insert = [&](uint64_t p) -> void
        {
            uint32_t h = hash5(src + p);
            prev[p & ring_mask] = head[h];
            head[h] = uint32_t(p);
        };

        // longest match at p, returns raw length
        auto find = [&](uint64_t p, uint32_t seed, uint32_t& out_dis) -> uint32_t
        {
            if (p + min_match_len > match_end_limit)
                return 0;

            const uint32_t limit = uint32_t(std::min<uint64_t>(max_match_len, match_end_limit - p));
            uint32_t best_len = min_match_len - 1;
            uint32_t best_dis = 0;

            if (seed >= min_dis and uint64_t(seed) <= std::min<uint64_t>(max_dis, p))
            {
                uint32_t l = lcp_long(src + p, src + p - seed, limit);
                if (l >= min_match_len)
                {
                    best_len = l;
                    best_dis = seed;
                }
            }

            if (best_len < nice_len)
            {
                uint32_t h = hash5(src + p);
                uint32_t c = head[h];
                uint32_t steps = 0;
                // very rare false triggers here when the stored head is NIL but valid.
                // but it only triggers on > 4 GB data and is vanishingly rare, so no visible ratio
                // loss.
                while (c != NIL and steps < max_chain)
                {
                    uint64_t dis = uint32_t(p) - c;
                    if (dis > max_dis)
                        break;
                    if (dis >= min_dis)
                    {
                        ++steps;
                        // skip unless we can beat best_len, so matches are closer
                        if (src[(p - dis) + best_len] == src[p + best_len])
                        {
                            uint32_t l = lcp_long(src + p, src + (p - dis), limit);
                            if (l > best_len)
                            {
                                best_len = l;
                                best_dis = uint32_t(dis);
                                if (l >= nice_len)
                                    break;
                            }
                        }
                    }
                    c = prev[c & ring_mask];
                }
            }

            if (best_len < min_match_len)
                return 0;
            out_dis = best_dis;
            return best_len;
        };

        while (pos + min_match_len <= match_end_limit)
        {
            // we'll just reject the too-close insertions while finding matches
            while (hpos <= pos)
                insert(hpos++);

            uint32_t d0 = 0;
            uint32_t m0 = find(pos, seed, d0);
            if (m0 < accept_len)
            {
                pos += 1 + (miss_run >> 6);
                ++miss_run;
                continue;
            }

            uint64_t match_start = pos;
            uint32_t match_len = m0;
            uint32_t match_dis = d0;

            // keep looking ahead while we keep getting improvements
            while (1)
            {
                uint64_t npos = match_start + 1;
                if (npos + min_match_len > match_end_limit)
                    break;

                while (hpos <= npos)
                    insert(hpos++);

                uint32_t nmatch_dis = 0;
                uint32_t nmatch_len = find(npos, seed, nmatch_dis);

                if (nmatch_len < accept_len)
                    break;

                uint32_t cur_use = LUT.len_floor[match_len <= 255 ? match_len : 255];
                uint32_t nxt_use = LUT.len_floor[nmatch_len <= 255 ? nmatch_len : 255];

                // need gains
                if (nxt_use < cur_use + lazy_gain)
                    break;

                match_start = npos;
                match_len = nmatch_len;
                match_dis = nmatch_dis;
            }

            // backward extension
            while (match_start > lit and match_start > match_dis and
                   src[match_start - 1] == src[match_start - match_dis - 1] and
                   match_len < max_match_len)
                --match_start, ++match_len;

            if (match_len > max_match_len)
                match_len = max_match_len;

            uint32_t use_len = LUT.len_floor[match_len <= 255 ? match_len : 255];
            uint32_t code = LUT.code_floor[match_len <= 255 ? match_len : 255];

            ++tokens;
            long_matches += uint64_t(use_len > vector_width);

            // emit

            // 4 byte token
            uint64_t lit_len = match_start - lit;
            uint32_t lrem = lit_len < lit_lim ? lit_len : lit_lim;
            uint32_t tok = uint32_t((match_dis - min_dis) & dis_mask) | (code << 20) | (lrem << 26);
            storeu4(dst + dlpos, tok);
            dlpos += 4;

            // Extra literal length bytes
            emit_length_extras(dst, dlpos, lit_len - lit_lim, lrem);
            if (lit_len)
            {
                drpos -= lit_len;
                memcpy(dst + drpos, src + lit, lit_len);
            }

            seed = match_dis;
            pos = match_start + use_len;
            lit = pos;
            miss_run = 0;
        }

        // Close the gap between the two streams by moving the literal stream to the left
        if (drpos < dst_cap)
        {
            memmove(dst + dlpos, dst + drpos, dst_cap - drpos);
            dlpos += dst_cap - drpos;
        }

        // Just deal with the last few literals (guaranteed to be `>= literal_suffix >=
        // vector_width` bytes)
        uint64_t literal_suffix_cnt = src_size - lit;
        storeu8(dst + literal_suffix_pos, literal_suffix_cnt);
        memcpy(dst + dlpos, src + lit, literal_suffix_cnt);
        dlpos += literal_suffix_cnt;

        bool cond = float(long_matches) < cond_flag_thresh * float(tokens);
        uint64_t flags = (uint64_t(1) << format_bit) | (uint64_t(cond) << cond_bit);
        storeu8(dst, src_size | (flags << 56));

        return dlpos;
    }
} // namespace misa77
