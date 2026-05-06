# pdgzip

pdgzip - a public-domain, embeddable gzip decoder in c11.
report issues to kamila szewczyk <k@iczelia.net>.
project homepage: https://github.com/iczelia/pdgzip.

pdgzip is a reasonably fast gzip decoder. we have a couple of tricks up our sleeve:
- extra validation of huffman trees via the kraft-mcmillan condition
- multi-level huffman tables; standard technique in accelerated zlib
  decompressors, here implemented in a low code volume.
- semi-space based window design to decrease overall latency and move
  a hotspot to semi-space memcpy() back to history buffer.
- full support of the RFC quirks for deflate/gzip, including fixed
  huffman trees.
- fast crc32 implementation via runtime-computed tables and the
  slicing-by-8 algorithm.
- 64-bit bulk bit-refill fast path (little-endian): one unaligned
  load per ~7 decoded bits, vs. byte-at-a-time refills.
- the library is embeddable: it does not use any dynamic memory
  allocation (instead accepting a fixed-size arena from the caller)
  and only depends on `<string.h>`, the necessary functions of which
  are re-implemented upon absence of the header.

comparisons:
- size: tinf ~2.5kb x86 code, pdgzip ~15kb x86 code, zlib ~22kb of x86 code.
- code volume: tinf 639 sloc, pdgzip 596 sloc, zlib >=10k sloc, libdeflate >=7.7k sloc.
- performance (r7 pro 7840u; enwik8 100MB): tinf ~2.3s, this ~313.4 ms, zlib-gz ~417.7 ms.

extras:
- fuzzed with afl++ for ub and compliance with zlib, passes cppcheck.
- licensed under cc0, use anywhere for any purpose. attribution is
  appreciated but not required.
- the code is written in c11, but should be compatible with c99 with
  minor adjustments.

building:
- drop pdgzip.h and pdgzip.c into your project.

## api

you give the decoder one callback to pull compressed bytes and one
constant-size scratch buffer (see `pdgzip_state_size()` /
`pdgzip_state_align()`). Then you call `pdgzip_read(gz, buf, n)` in a
loop. positive return means bytes produced; zero means clean
end-of-stream with the CRC32 trailer already verified; negative means
one of `PDGZIP_E_FORMAT / PDGZIP_E_CHECKSUM / PDGZIP_E_IO`. Enable
`cfg.concat` to decode back-to-back gzip members as one logical
stream.

peak memory is a single caller-owned scratch buffer of
`pdgzip_state_size()` bytes; about 376 KiB with default tuning
(`HUFF_BITS` = 9). Raising `HUFF_BITS` shrinks it at a measurable
decode-speed cost: 9 -> 376 KiB, 10 -> 225 KiB, 11 -> 145 KiB.

threat model: input is treated as untrusted. we validate:
- gzip magic, method == deflate, header structure (FEXTRA / FNAME /
  FCOMMENT / FHCRC).
- FHCRC when the flag is set (low 16 bits of CRC-32 over every
  preceding header byte).
- huffman code-length tables (kraft's inequality, per-symbol length
  limits, sub-table capacity).
- deflate block types; stored-block `~LEN` field; distance/length
  code symbol ranges.
- trailer CRC-32 over the decompressed output.
- trailer ISIZE against `total_out mod 2^32` (matches zlib; for
  streams >= 4 GiB this wraps, which is an inherent gzip format
  limitation, not a bug).

there is no decompressed size cap (must be enforced by the caller)
and seeking/random access is not supported. because of a file format
limitation, the caller must manually reset the underlying stream that
they supplied and recreate a decoder instance. this is typically not
a problem for typical use cases.

concat=1 mode allows the decoder to seamlessly decode back-to-back gzip
members as one logical stream, which is a common use case.

# fuzzing

harnesses:
- fuzz_decode: feeds fuzzer bytes, asan/ubsan catches crashes, msan
  catches uninit. reads; runs both concat=0 and concat=1 paths.
- fuzz_diff: differential testing against zlib. 
- fuzz_huff: validates the huffman table fast path logic.

```
cd fuzz
make corpus         # generate seed corpus
make libfuzzer      # ASAN + UBSAN + libFuzzer
make libfuzzer-msan # MSAN (decode & huff only; diff needs an MSAN libz)
make afl            # AFL++ persistent mode
make repro          # Sanitizer replay binary for crash repros
make check          # cppcheck static sweep
make run-short      # 60-second smoke of each harness
```

the static sweep runs clean on cppcheck 2.20 with
`--enable=all --std=c11 --inconclusive`. The source builds with zero
warnings under gcc *and* clang at
`-std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow
-Wstrict-prototypes -Wcast-qual -Wvla -Wdouble-promotion -Wformat=2`.

# attic

reference gzip-compatible compressor, under 1000 lines.
also public domain.

- fixed (pre-defined) and uncompressed deflate blocks supported.
- shoddy code-length-limiting algorithm per RFC so edge cases 
  round-trip.
- lazy Rabin-Karp (hash-chain) matcher with nice/good length tuning.
- output is plausibly something gzip/zlib could have produced.
- previously AFL-fuzzed against gzip for segfaults and
  incompatibilities.
