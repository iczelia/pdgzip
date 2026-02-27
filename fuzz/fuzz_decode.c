/* Smoke harness: feed fuzzer bytes through pdgzip.  Verifies no
   crash, no UB, no leak (under ASAN/UBSAN/MSAN).  Runs both
   concat=0 and concat=1 paths on every input so the multi-member
   codepath gets coverage too.  Public domain.  */
#include "fuzz_common.h"

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    /*  A gzip bomb is not a bug: valid gzip streams can expand
        arbitrarily.  We cap output just to keep fuzz iterations
        from OOMing, and quietly drop bombs (rc == -2) without
        flagging them as crashes.  */
    uint8_t *out = NULL;
    size_t   out_len = 0;

    (void)fz_decode(data, size, &out, &out_len, 0);
    free(out);  out = NULL;  out_len = 0;

    (void)fz_decode(data, size, &out, &out_len, 1);
    free(out);
    return 0;
}
