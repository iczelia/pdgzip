/* Differential harness: pdgzip vs zlib.  For any single-member gzip
   stream, the two decoders must either both accept (and agree byte-
   for-byte) or both reject.  Silent corruption shows up here.

   Invariants enforced:
     * pdgzip OK && zlib OK    => outputs byte-identical.
     * pdgzip OK && zlib fail  => divergence  (trap).
     * pdgzip fail && zlib OK  => divergence  (trap).
     * both fail               => OK.

   Note: we run concat=0 only; zlib's single inflate call does not
   transparently handle concatenated members, so comparing concat=1
   would require mirroring that logic here.  concat is covered by
   fuzz_decode under sanitizers, which is sufficient.

   Public domain.  */

#include <zlib.h>
#include "fuzz_common.h"

/*  Must match FZ_TOTAL_CAP so either side hitting the cap is treated
    equivalently.  Inputs whose expansion overruns this cap are
    ambiguous (a "bomb") and we skip the diff for them.  */
#define Z_CAP FZ_TOTAL_CAP

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size > (size_t)0x7FFFFFFFu) return 0;

    /* --- pdgzip side --- */
    uint8_t *p_out = NULL;
    size_t   p_len = 0;
    int p_rc = fz_decode(data, size, &p_out, &p_len, 0);

    /* --- zlib side --- */
    uint8_t *z_out = (uint8_t *)malloc(Z_CAP);
    if (!z_out) { free(p_out); return 0; }

    z_stream zs = {0};
    zs.next_in   = (Bytef *)(uintptr_t)data;   /* zlib Bytef*, not const */
    zs.avail_in  = (uInt)size;
    zs.next_out  = z_out;
    zs.avail_out = Z_CAP;

    int z_ok = 0, z_bomb = 0;
    size_t z_len = 0;

    if (inflateInit2(&zs, 15 + 16 /* gzip only */) == Z_OK) {
        int ir = inflate(&zs, Z_FINISH);
        z_len = (size_t)zs.total_out;
        if (ir == Z_STREAM_END) z_ok = 1;
        /*  Z_BUF_ERROR with avail_out == 0 means zlib filled the buffer
            but had more to emit: it's a bomb from zlib's point of view.
            We'll skip comparison below.  */
        else if (ir == Z_BUF_ERROR && zs.avail_out == 0) z_bomb = 1;
        inflateEnd(&zs);
    }

    /*  Either side hitting the cap leaves the other's verdict
        indeterminate -- skip this input.  */
    int p_bomb = (p_rc == -2);
    if (p_bomb || z_bomb) {
        free(p_out); free(z_out); return 0;
    }

    int p_ok = (p_rc == 0);

    if (p_ok && z_ok) {
        if (p_len != z_len) __builtin_trap();
        if (p_len && memcmp(p_out, z_out, p_len) != 0) __builtin_trap();
    } else if (p_ok && !z_ok) {
        /*  pdgzip accepted something zlib rejects.  This is a real
            divergence against a reference decoder.  */
        __builtin_trap();
    } else if (!p_ok && z_ok) {
        /*  zlib produced a clean stream pdgzip rejected.  Bug.  */
        __builtin_trap();
    }

    free(p_out);
    free(z_out);
    return 0;
}
