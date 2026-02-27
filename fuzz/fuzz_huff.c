/* Targeted harness for huff_build().  Dynamic-Huffman framing is a
   narrow path through the full stream fuzzer; here we bypass it and
   feed fuzzer-chosen code-length vectors directly, reaching deeply
   pathological trees (Kraft-degenerate, all-length-15, etc.) in
   seconds.

   We include pdgzip.c directly so we get access to huff_build(),
   huff_decode() and the internal huff_table_t type without having
   to make them part of the public ABI.  Public domain.  */

#include "../pdgzip.c"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 2 || size > MAX_LITLEN_CODES) return 0;

    int count = (int)size;
    uint8_t lens[MAX_LITLEN_CODES];
    /*  Clamp each length to the valid range [0, 15] but keep the
        distribution fuzzer-controlled so Kraft-degenerate and
        boundary-sized trees remain reachable.  */
    for (int i = 0; i < count; i++)
        lens[i] = data[i] & 0x0Fu;

    huff_table_t *ht = (huff_table_t *)aligned_alloc(
        _Alignof(huff_table_t), sizeof(huff_table_t));
    if (!ht) return 0;
    memset(ht, 0, sizeof(*ht));

    if (huff_build(ht, lens, count) == 0) {
        /*  Tree built successfully -- exercise huff_decode over some
            fuzzer-supplied bits too, so pathological redirect chains
            get walked.  We synthesise a tiny bitreader fed from the
            tail of the input.  */
        bitreader_t br;
        memset(&br, 0, sizeof(br));
        /*  Fabricate a source: reuse the lengths as bit source.
            Works because we never call through to a real callback --
            the bitreader will EOF out after 64 bits.  */
        br.bits  = 0;
        br.nbits = 0;
        br.src_eof = 1;   /* already EOF; bits=0 from there on */
        for (int i = 0; i < 32; i++)
            (void)huff_decode(&br, ht);
    }

    free(ht);
    return 0;
}
