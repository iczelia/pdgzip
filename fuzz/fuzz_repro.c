/* Standalone reproducer: reads a file and runs it through one of the
   LLVMFuzzerTestOneInput harnesses, without a fuzzing engine.  Built
   with sanitizers enabled, this is how you reproduce a crash outside
   libFuzzer.  Public domain.  */

#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int LLVMFuzzerTestOneInput(const uint8_t *, size_t);

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s <file> [<file>...]\n", argv[0]);
        return 2;
    }
    for (int i = 1; i < argc; i++) {
        FILE *f = fopen(argv[i], "rb");
        if (!f) { fprintf(stderr, "%s: %s\n", argv[i], strerror(errno));
                  return 1; }
        fseek(f, 0, SEEK_END);
        long sz = ftell(f);
        if (sz < 0) { fclose(f); return 1; }
        fseek(f, 0, SEEK_SET);
        uint8_t *buf = (uint8_t *)malloc((size_t)sz);
        if (!buf) { fclose(f); return 1; }
        if (fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
            free(buf); fclose(f); return 1;
        }
        fclose(f);
        LLVMFuzzerTestOneInput(buf, (size_t)sz);
        free(buf);
    }
    return 0;
}
