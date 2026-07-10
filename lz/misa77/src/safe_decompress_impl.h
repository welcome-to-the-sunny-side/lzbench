// safed: bounds-checked decoder experiment.
// src/decompress_impl.h + 7 guards. Structure/instructions otherwise untouched so the
// A/B against the unsafe decoder isolates the cost of the guards themselves.
//
// Safety argument (why these 7 are sufficient), relying on cyccpy/copy32 writing
// exactly 32 bytes at their stated offsets:
//   - src reads: every unconditional read is at most 32 bytes past a cursor that
//     GUARDs 3/5 keep <= src_size - literal_suffix_cnt, and GUARD 3 forces
//     literal_suffix_cnt >= 32. The extras walk (the one unbounded read) is
//     bounded by GUARD 4.
//   - dst writes: GUARD 6 keeps dpos <= loop_limit at all times, and
//     loop_limit + 32 <= original_size <= dst_cap (again via GUARD 3's >= 32).
//   - dst reads (match source): GUARD 7 keeps dpos - dis >= 0.
// Every guarded quantity is checked before the arithmetic that would wrap.

#pragma once

#include "format.h"
#include "misa77/misa77.h"
#include "util.h"

#include <cstdint>
#include <cstring>

namespace misa77
{
    // Returns number of bytes written to `dst`, and 0 on malformed input.
    template <class isa_lib>
    uint64_t safe_decompress_impl(const uint8_t* __restrict src,
                                  uint64_t src_size,
                                  uint8_t* __restrict dst,
                                  uint64_t dst_cap)
    {
        // GUARD 1: header fields must exist before we read them.
        if (src_size < 8) [[unlikely]]
            return 0;

        const uint64_t original_size = decompressed_size(src);

        if (dst_cap < original_size)
            return 0;

        // Small source
        if (original_size <= small_lim)
        {
            // GUARD 2: a truncated stream must not over-read the raw payload.
            if (src_size < 8 + original_size) [[unlikely]]
                return 0;
            if (original_size > 0)
                memcpy(dst, src + uint64_t(8), original_size);
            return original_size;
        }

        // GUARD 1 (cont.): non-small mode reads a second 8-byte field.
        if (src_size < 16) [[unlikely]]
            return 0;

        // Left and right pointers in the source buffer
        uint64_t lpos = 0, rpos = src_size;

        // Read the original size
        lpos += 8;

        // Size of literal suffix
        uint64_t literal_suffix_cnt = loadu8(src + lpos);
        lpos += 8;

        // GUARD 3: the suffix must fit in both buffers, and must be >= 32 — that
        // floor is what makes every unconditional 32-wide read/write below safe.
        if (literal_suffix_cnt < literal_suffix or literal_suffix_cnt > src_size - 16 or
            literal_suffix_cnt > original_size) [[unlikely]]
            return 0;

        rpos -= literal_suffix_cnt;

        // The loop may produce at most this much output; the suffix fills the rest.
        const uint64_t loop_limit = original_size - literal_suffix_cnt;

        // Position in the destination buffer
        uint64_t dpos = 0;

        // Guard notes (all measured):
        //  - GUARDs are SEPARATE branches; a fused OR-predicate branch measured ~2×
        //    the overhead (the setcc+or chain must resolve before the one branch,
        //    while several never-taken branches are nearly free once predicted).
        //  - GUARD 5 is the weak form `lit_len > rpos`: that is all MEMORY safety
        //    needs (reads stay inside src). A lit run that crosses the control
        //    cursor decodes garbage, but the loop condition / exit equality check
        //    reject the stream.
        //  - GUARD 6 deliberately omits match_len: this token's writes only need
        //    `dpos + lit_len <= loop_limit` (wide-copy overshoot rides on the
        //    >= 32-byte suffix, GUARD 3). If the final match overproduces, the
        //    next token's GUARD 6 or the exit equality check rejects — before any
        //    out-of-bounds write can happen.
        //  - GUARD 7 (`dis > dpos`) only exists in the prologue: dis <= dis_ceil
        //    by construction, so once dpos >= dis_ceil it can never fire and the
        //    main loop runs without it.
        constexpr uint64_t dis_ceil = dis_lim + hashtab_lag; // max representable dis

        // Prologue: first dis_ceil output bytes, GUARD 7 live.
        while (lpos < rpos and dpos < dis_ceil)
        {
            // Overread is safe here
            uint8_t token = src[lpos];
            uint64_t lit_len = token >> 5;
            uint64_t match_len = (token & uint8_t(0x1F)) + min_match_len - 1;

            uint16_t dis_small = loadu2(src + lpos + 1);
            uint32_t dis = dis_small + hashtab_lag + 1;

            lpos += 3;

            if (lit_len == 7) [[unlikely]]
            {
                uint64_t pot_add = src[lpos];
                lit_len += pot_add;
                lpos++;

                constexpr uint64_t block = 255;
                if (pot_add == block) [[unlikely]]
                {
                    // GUARD 4: bound the walk — the only unbounded read in the
                    // format. (Reads may trail up to 3 bytes past rpos before the
                    // bound trips; those stay inside the >= 32-byte suffix.)
                    while (src[lpos] == block) [[unlikely]]
                    {
                        lit_len += block, ++lpos;
                        if (lpos >= rpos) [[unlikely]]
                            return 0;
                    }
                    lit_len += src[lpos], ++lpos;
                }
            }

            // GUARD 5 (weak form): no src underflow.
            if (lit_len > rpos) [[unlikely]]
                return 0;

            // GUARD 6: bound this token's dst writes.
            if (dpos + lit_len > loop_limit) [[unlikely]]
                return 0;

            if (lit_len > dec_literal_copy) [[unlikely]]
            {
                rpos -= lit_len;

                isa_lib::copy32(dst + dpos, src + rpos);

                if (lit_len > vector_width) [[unlikely]]
                {
                    memcpy(dst + (dpos + vector_width),
                           src + (rpos + vector_width),
                           lit_len - vector_width);
                }
            }
            else
            {
                // Unconditional copy, safe because we have `dec_literal_copy` bytes of
                // breathing room at the end in src and dst due to `literal_suffix`
                rpos -= lit_len;
                memcpy(dst + dpos, src + rpos, dec_literal_copy);
            }
            dpos += lit_len;

            // GUARD 7: the match source must not start before dst[0].
            if (dis > dpos) [[unlikely]]
                return 0;

            isa_lib::cyccpy(dst + (dpos - dis), dis);
            dpos += match_len;
        }

        // Main loop: dpos >= dis_ceil >= dis, GUARD 7 compiled out.
        while (lpos < rpos)
        {
            // Overread is safe here
            uint8_t token = src[lpos];
            uint64_t lit_len = token >> 5;
            uint64_t match_len = (token & uint8_t(0x1F)) + min_match_len - 1;

            uint16_t dis_small = loadu2(src + lpos + 1);
            uint32_t dis = dis_small + hashtab_lag + 1;

            lpos += 3;

            if (lit_len == 7) [[unlikely]]
            {
                uint64_t pot_add = src[lpos];
                lit_len += pot_add;
                lpos++;

                constexpr uint64_t block = 255;
                if (pot_add == block) [[unlikely]]
                {
                    // GUARD 4 (as above).
                    while (src[lpos] == block) [[unlikely]]
                    {
                        lit_len += block, ++lpos;
                        if (lpos >= rpos) [[unlikely]]
                            return 0;
                    }
                    lit_len += src[lpos], ++lpos;
                }
            }

            // GUARD 5 (weak form): no src underflow.
            if (lit_len > rpos) [[unlikely]]
                return 0;

            // GUARD 6: bound this token's dst writes.
            if (dpos + lit_len > loop_limit) [[unlikely]]
                return 0;

            if (lit_len > dec_literal_copy) [[unlikely]]
            {
                rpos -= lit_len;

                isa_lib::copy32(dst + dpos, src + rpos);

                if (lit_len > vector_width) [[unlikely]]
                {
                    memcpy(dst + (dpos + vector_width),
                           src + (rpos + vector_width),
                           lit_len - vector_width);
                }
            }
            else
            {
                rpos -= lit_len;
                memcpy(dst + dpos, src + rpos, dec_literal_copy);
            }
            dpos += lit_len;

            isa_lib::cyccpy(dst + (dpos - dis), dis);
            dpos += match_len;
        }

        if (dpos != loop_limit)
            return 0;

        // Literal suffix at the end
        memcpy(dst + (original_size - literal_suffix_cnt),
               src + (src_size - literal_suffix_cnt),
               literal_suffix_cnt);
        dpos += literal_suffix_cnt;

        return dpos;
    }
} // namespace misa77
