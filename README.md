# pdgzip
gzip-compatible compressor in under 1000loc released to the public domain. correctly decompresses all files that were produced according to rfc1951.
- supports blocks that use fixed (pre-defined) or no huffman codes.
- implements a shoddy algorithm for huffman code length-limiting per the rfc to handle edge cases in compression.
- lazy rabin-karp (hash chain) matcher with nice/good lengths.
- produces files that could have plausibly been produced by gzip/zlib.
