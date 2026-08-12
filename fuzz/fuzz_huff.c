/*  Targeted harness for huff_build().  */

#include "../pdgzip.c"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int LLVMFuzzerTestOneInput(const uint8_t * data, size_t size) {
  if (size < 2 || size > MAX_LITLEN_CODES) return 0;
  int count = (int)size;
  uint8_t lens[MAX_LITLEN_CODES];
  for (int i = 0; i < count; i++) lens[i] = data[i] & 0x0Fu;
  huff_table_t * ht = aligned_alloc(_Alignof(huff_table_t), sizeof(huff_table_t));
  if (!ht) return 0;
  memset(ht, 0, sizeof(*ht));
  if (huff_build(ht, lens, count) == 0) {
    bitreader_t br;  memset(&br, 0, sizeof(br));
    br.bits  = 0;  br.nbits = 0;  br.src_eof = 1;   /*  already EOF  */
    for (int i = 0; i < 32; i++) (void)huff_decode(&br, ht);
  }
  free(ht);  return 0;
}
