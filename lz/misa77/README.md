# misa77

A fast-decode LZ compressor.

- Upstream: https://github.com/welcome-to-the-sunny-side/misa77
- License:  MIT

Registered lzbench codecs:

| name              | description                                              |
| ----------------- | -------------------------------------------------------- |
| `misa77`          | the library codec; levels 0 (fastest decompression) / 1 (best ratio, the library default) |
| `misa77_adaptive` | decoder-friendly adaptive parse for homogeneous data; levels 0 (loose) / 1 (tight) |
| `misa77_safe`     | (this branch only) same compressor as `misa77`, decoded with an experimental bounds-checked decoder that rejects malformed input instead of UB |

All emit bitstreams conforming to the same format; `misa77` and `misa77_adaptive` share the unguarded decompressor.
