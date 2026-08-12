/* Feed fuzzer bytes through pdgzip.  Verifies no crash, no UB,
   no leak (under ASAN/UBSAN/MSAN) happens.  Runs both concat=0 and concat=1
   paths on every input so the multi-member codepath gets coverage too.  */
#include "fuzz_common.h"

int LLVMFuzzerTestOneInput(const uint8_t * data, size_t size) {
  uint8_t * out = NULL;  size_t out_len = 0;
  (void)fz_decode(data, size, &out, &out_len, 0);
  free(out);  out = NULL;  out_len = 0;
  (void)fz_decode(data, size, &out, &out_len, 1);
  free(out);  return 0;
}
