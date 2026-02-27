#!/usr/bin/env bash
# Regenerate the seed corpus under fuzz/corpus/.  Deterministic: the
# output only depends on gzip + python3 + the byte sequences written
# below.  Safe to re-run.  Public domain.

set -euo pipefail

ROOT="$(cd -- "$(dirname -- "$0")" && pwd)"
CORPUS="$ROOT/corpus"
export CORPUS_DIR="$CORPUS"
rm -rf "$CORPUS"
mkdir -p "$CORPUS"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# ---------------------------------------------------------------------------
# Standard gzip outputs at several levels.
# ---------------------------------------------------------------------------
: > "$WORK/empty"
printf 'A' > "$WORK/one"
head -c 1024 /dev/urandom > "$WORK/rnd_1k"
# `head` closing the pipe early makes its producer SIGPIPE; in
# `set -o pipefail` that'd be fatal, so produce these in pure shell.
python3 -c 'import sys,os; sys.stdout.buffer.write(os.urandom(4096*3).hex().encode()[:4096])' > "$WORK/text_4k"
head -c 16384 /dev/urandom > "$WORK/rnd_16k"
python3 -c 'import sys; sys.stdout.buffer.write((b"abcdefghijklmnop"*512)[:8192])' > "$WORK/rep_8k"

gzip -1c < "$WORK/empty"   > "$CORPUS/empty_l1.gz"
gzip -9c < "$WORK/empty"   > "$CORPUS/empty_l9.gz"
gzip -1c < "$WORK/one"     > "$CORPUS/one_l1.gz"
gzip -1c < "$WORK/rnd_1k"  > "$CORPUS/rnd_1k_l1.gz"
gzip -6c < "$WORK/rnd_1k"  > "$CORPUS/rnd_1k_l6.gz"
gzip -9c < "$WORK/rnd_1k"  > "$CORPUS/rnd_1k_l9.gz"
gzip -1c < "$WORK/text_4k" > "$CORPUS/text_4k_l1.gz"
gzip -9c < "$WORK/text_4k" > "$CORPUS/text_4k_l9.gz"
gzip -9c < "$WORK/rnd_16k" > "$CORPUS/rnd_16k_l9.gz"
gzip -9c < "$WORK/rep_8k"  > "$CORPUS/rep_8k_l9.gz"   # exercises matches

# Multi-member: concatenation is valid gzip per RFC 1952 §2.2.
cat "$CORPUS/one_l1.gz" "$CORPUS/one_l1.gz"               > "$CORPUS/concat_2.gz"
cat "$CORPUS/rnd_1k_l1.gz" "$CORPUS/text_4k_l9.gz"        > "$CORPUS/concat_mixed.gz"
cat "$CORPUS/empty_l9.gz" "$CORPUS/empty_l9.gz"           > "$CORPUS/concat_empties.gz"

# ---------------------------------------------------------------------------
# Stored-only block stream.  gzip won't emit stored blocks at normal
# sizes, so synthesise via zlib(level=0, wbits=31).
# ---------------------------------------------------------------------------
python3 - <<'PY'
import os, zlib, pathlib
corpus = pathlib.Path(os.environ["CORPUS_DIR"])

def gz_level0(data):
    co = zlib.compressobj(level=0, wbits=31)
    return co.compress(data) + co.flush()

(corpus / "stored_empty.gz").write_bytes(gz_level0(b""))
(corpus / "stored_small.gz").write_bytes(gz_level0(b"A" * 17))
(corpus / "stored_large.gz").write_bytes(gz_level0(b"B" * 70000))  # > 65535 -> multi-block
PY

# ---------------------------------------------------------------------------
# Header-flag permutations.  Craft by hand so we don't depend on a
# tool that happens to emit them.  Each starts 1f 8b 08 <flags> then
# 6 bytes of MTIME/XFL/OS, then optional flag-driven segments, then
# the compressed payload + trailer from a known-good gzip file.
# ---------------------------------------------------------------------------
python3 - <<'PY'
import os, pathlib, zlib, struct
corpus = pathlib.Path(os.environ["CORPUS_DIR"])

payload = b"hello header flags\n"
# Produce a minimal raw-deflate + gzip-style trailer for `payload`.
co = zlib.compressobj(level=9, wbits=-15)
deflate = co.compress(payload) + co.flush()
crc = zlib.crc32(payload) & 0xFFFFFFFF
trailer = struct.pack("<II", crc, len(payload) & 0xFFFFFFFF)

def make(flags, extras_no_fhcrc):
    """Build a gzip stream.  If FHCRC is set in `flags`, a valid CRC
       over every header byte preceding the 2-byte CRC field is
       appended automatically."""
    hdr = bytes([0x1f, 0x8b, 0x08, flags,
                 0, 0, 0, 0,   # mtime
                 0,            # xfl
                 0xff])        # os
    header = hdr + extras_no_fhcrc
    if flags & 0x02:  # FHCRC
        crc16 = zlib.crc32(header) & 0xFFFF
        header += struct.pack("<H", crc16)
    return header + deflate + trailer

# FNAME (flag 0x08)
(corpus / "flag_fname.gz").write_bytes(make(0x08, b"foo.txt\x00"))
# FCOMMENT (flag 0x10)
(corpus / "flag_fcomment.gz").write_bytes(make(0x10, b"a comment\x00"))
# FEXTRA (flag 0x04): two-byte XLEN LE + XLEN bytes
extra = struct.pack("<H", 4) + b"ABCD"
(corpus / "flag_fextra.gz").write_bytes(make(0x04, extra))
# FHCRC alone (flag 0x02) -- CRC is appended by make()
(corpus / "flag_fhcrc.gz").write_bytes(make(0x02, b""))
# All flags combined.
combined = extra + b"bar\x00" + b"nice file\x00"
(corpus / "flag_all.gz").write_bytes(make(0x02 | 0x04 | 0x08 | 0x10, combined))
PY

# ---------------------------------------------------------------------------
# A couple of deliberately-malformed inputs to anchor the fuzzer around
# realistic failure modes (bad magic, truncated, bad CRC).  The
# fuzzer will mutate these further.
# ---------------------------------------------------------------------------
head -c 32 "$CORPUS/rnd_1k_l9.gz" > "$CORPUS/truncated.gz" || true
cp "$CORPUS/rnd_1k_l9.gz" "$CORPUS/bad_crc.gz"
python3 - <<'PY'
import os, pathlib
corpus = pathlib.Path(os.environ["CORPUS_DIR"])
p = corpus / "bad_crc.gz"
data = bytearray(p.read_bytes())
# Flip the low byte of the stored CRC (last 8 bytes are CRC||ISIZE).
data[-8] ^= 0x01
p.write_bytes(bytes(data))
PY

# Random bytes with a gzip-magic prefix -- easy entry for the fuzzer
# into the parse_gz_header path.
{ printf '\x1f\x8b\x08\x00'; head -c 60 /dev/urandom; } > "$CORPUS/magic_garbage.gz"

echo "corpus: $(ls "$CORPUS" | wc -l) files in $CORPUS"
