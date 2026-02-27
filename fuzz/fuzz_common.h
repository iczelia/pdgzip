/* Shared harness helpers.  Public domain.  */
#ifndef PDGZIP_FUZZ_COMMON_H
#define PDGZIP_FUZZ_COMMON_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "../pdgzip.h"

/*  Hard caps: catch gzip-bomb-style inputs as fuzzer-reported hangs
    rather than OOM kills.  A well-behaved decoder should never exceed
    these on fuzz-sized inputs.  */
#define FZ_OUT_CAP    (16u * 1024u * 1024u)   /* 16 MiB per call    */
#define FZ_TOTAL_CAP  (64u * 1024u * 1024u)   /* 64 MiB per input   */

typedef struct {
    const uint8_t *data;
    size_t         pos, len;
} fz_src_t;

static size_t fz_read(void *u, void *buf, size_t n) {
    fz_src_t *s = (fz_src_t *)u;
    size_t avail = s->len - s->pos;
    if (n > avail) n = avail;
    if (n) memcpy(buf, s->data + s->pos, n);
    s->pos += n;
    return n;
}

/*  Decode the whole input.  Returns:
     0  success (clean EOS), output in *out/ *out_len (caller frees)
    -1  pdgzip reported a decode error (normal for fuzzer input)
    -2  total-cap hit (treated as a hang -- caller may trap)  */
static int fz_decode(const uint8_t *data, size_t len,
                     uint8_t **out, size_t *out_len, int concat) {
    fz_src_t src = { data, 0, len };
    pdgzip_cfg_t cfg = { .read = fz_read, .user = &src, .concat = concat };

    void *scratch = aligned_alloc(pdgzip_state_align(),
                                  pdgzip_state_size());
    if (!scratch) return -1;
    pdgzip_t *gz = pdgzip_init(scratch, &cfg);
    if (!gz) { free(scratch); return -1; }

    size_t cap = 4096, used = 0;
    uint8_t *buf = malloc(cap);
    if (!buf) { free(scratch); return -1; }

    int rc = 0;
    for (;;) {
        if (cap - used < 4096) {
            size_t ncap = cap * 2;
            if (ncap > FZ_TOTAL_CAP) ncap = FZ_TOTAL_CAP;
            if (ncap <= cap) { rc = -2; break; }
            uint8_t *nb = realloc(buf, ncap);
            if (!nb) { rc = -1; break; }
            buf = nb; cap = ncap;
        }
        int64_t n = pdgzip_read(gz, buf + used, cap - used);
        if (n < 0) { rc = -1; break; }
        if (n == 0) break;
        used += (size_t)n;
        if (used >= FZ_TOTAL_CAP) { rc = -2; break; }
    }

    free(scratch);
    if (rc == 0) { *out = buf; *out_len = used; }
    else         { free(buf);  *out = NULL;  *out_len = 0; }
    return rc;
}

#endif
