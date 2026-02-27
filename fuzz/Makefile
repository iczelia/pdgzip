# Fuzzing + static-analysis driver.
# Targets:
#   libfuzzer        ASAN+UBSAN+libFuzzer builds of all three harnesses
#   libfuzzer-msan   MSAN+libFuzzer (decode & huff only; diff needs msan libz)
#   afl              AFL++ builds (requires afl-clang-fast)
#   repro            Sanitizer replay binary (ASAN+UBSAN, no fuzzer)
#   check            cppcheck sweep of pdgzip.c and harness sources
#   corpus           Regenerate fuzz/corpus via make_corpus.sh
#   run-short        60s smoke of each libfuzzer harness
#   clean            Remove build/
# Override tools/flags on the command line if needed:
#   make CC=clang-18 libfuzzer
#   make AFL_CC=afl-clang-fast afl

# libFuzzer/MSAN require clang.
FUZZ_CC       ?= clang
AFL_CC        ?= afl-clang-fast
CPPCHECK      ?= cppcheck
BUILD         := build
CORPUS        := corpus
DICT          := pdgzip.dict

SRC_LIB       := ../pdgzip.c
INC           := -I..
BASEFLAGS     := -std=c11 -g -O1 $(INC) \
                 -Wall -Wextra -Wpedantic
FUZZFLAGS     := -fsanitize=fuzzer,address,undefined \
                 -fno-sanitize-recover=all \
                 -fno-omit-frame-pointer
MSANFLAGS     := -fsanitize=fuzzer,memory \
                 -fno-sanitize-recover=all \
                 -fno-omit-frame-pointer -fPIE
SANFLAGS      := -fsanitize=address,undefined \
                 -fno-sanitize-recover=all \
                 -fno-omit-frame-pointer
AFLFLAGS      := -O2 $(INC) -Wall -Wextra

ZLIB_LDFLAGS  := -lz

HARNESSES     := fuzz_decode fuzz_diff fuzz_huff

.PHONY: all libfuzzer libfuzzer-msan afl repro check corpus run-short clean

all: libfuzzer

$(BUILD):
	@mkdir -p $(BUILD)

libfuzzer: $(BUILD) \
           $(BUILD)/fuzz_decode_fuzzer \
           $(BUILD)/fuzz_diff_fuzzer \
           $(BUILD)/fuzz_huff_fuzzer

$(BUILD)/fuzz_decode_fuzzer: fuzz_decode.c fuzz_common.h $(SRC_LIB) | $(BUILD)
	$(FUZZ_CC) $(BASEFLAGS) $(FUZZFLAGS) fuzz_decode.c $(SRC_LIB) -o $@

$(BUILD)/fuzz_diff_fuzzer: fuzz_diff.c fuzz_common.h $(SRC_LIB) | $(BUILD)
	$(FUZZ_CC) $(BASEFLAGS) $(FUZZFLAGS) fuzz_diff.c $(SRC_LIB) $(ZLIB_LDFLAGS) -o $@

$(BUILD)/fuzz_huff_fuzzer: fuzz_huff.c $(SRC_LIB) | $(BUILD)
	$(FUZZ_CC) $(BASEFLAGS) $(FUZZFLAGS) fuzz_huff.c -o $@

libfuzzer-msan: $(BUILD) \
                $(BUILD)/fuzz_decode_msan \
                $(BUILD)/fuzz_huff_msan

$(BUILD)/fuzz_decode_msan: fuzz_decode.c fuzz_common.h $(SRC_LIB) | $(BUILD)
	$(FUZZ_CC) $(BASEFLAGS) $(MSANFLAGS) fuzz_decode.c $(SRC_LIB) -o $@

$(BUILD)/fuzz_huff_msan: fuzz_huff.c $(SRC_LIB) | $(BUILD)
	$(FUZZ_CC) $(BASEFLAGS) $(MSANFLAGS) fuzz_huff.c -o $@

afl: $(BUILD) \
     $(BUILD)/fuzz_decode_afl \
     $(BUILD)/fuzz_diff_afl \
     $(BUILD)/fuzz_huff_afl

$(BUILD)/fuzz_decode_afl: fuzz_decode.c fuzz_common.h fuzz_repro.c $(SRC_LIB) | $(BUILD)
	$(AFL_CC) $(AFLFLAGS) fuzz_decode.c fuzz_repro.c $(SRC_LIB) -o $@

$(BUILD)/fuzz_diff_afl: fuzz_diff.c fuzz_common.h fuzz_repro.c $(SRC_LIB) | $(BUILD)
	$(AFL_CC) $(AFLFLAGS) fuzz_diff.c fuzz_repro.c $(SRC_LIB) $(ZLIB_LDFLAGS) -o $@

$(BUILD)/fuzz_huff_afl: fuzz_huff.c fuzz_repro.c $(SRC_LIB) | $(BUILD)
	$(AFL_CC) $(AFLFLAGS) fuzz_huff.c fuzz_repro.c -o $@

repro: $(BUILD) \
       $(BUILD)/fuzz_decode_repro \
       $(BUILD)/fuzz_diff_repro \
       $(BUILD)/fuzz_huff_repro

$(BUILD)/fuzz_decode_repro: fuzz_decode.c fuzz_common.h fuzz_repro.c $(SRC_LIB) | $(BUILD)
	$(FUZZ_CC) $(BASEFLAGS) $(SANFLAGS) fuzz_decode.c fuzz_repro.c $(SRC_LIB) -o $@

$(BUILD)/fuzz_diff_repro: fuzz_diff.c fuzz_common.h fuzz_repro.c $(SRC_LIB) | $(BUILD)
	$(FUZZ_CC) $(BASEFLAGS) $(SANFLAGS) fuzz_diff.c fuzz_repro.c $(SRC_LIB) $(ZLIB_LDFLAGS) -o $@

$(BUILD)/fuzz_huff_repro: fuzz_huff.c fuzz_repro.c $(SRC_LIB) | $(BUILD)
	$(FUZZ_CC) $(BASEFLAGS) $(SANFLAGS) fuzz_huff.c fuzz_repro.c -o $@

check:
	$(CPPCHECK) --enable=all --std=c11 --inconclusive \
	            --error-exitcode=1 --platform=unix64 \
	            --inline-suppr \
	            --suppress=missingIncludeSystem \
	            --suppress=unusedFunction \
	            --suppress=unmatchedSuppression \
	            --suppress=checkersReport \
	            --suppress=normalCheckLevelMaxBranches \
	            --suppress=uninitvar:../pdgzip.c \
	            $(INC) \
	            $(SRC_LIB) fuzz_decode.c fuzz_diff.c fuzz_huff.c \
	            fuzz_common.h fuzz_repro.c

corpus:
	./make_corpus.sh

TIME ?= 60
run-short: libfuzzer corpus
	$(BUILD)/fuzz_decode_fuzzer -max_total_time=$(TIME) \
	    -dict=$(DICT) -print_final_stats=1 $(CORPUS)
	$(BUILD)/fuzz_diff_fuzzer   -max_total_time=$(TIME) \
	    -dict=$(DICT) -print_final_stats=1 $(CORPUS)
	$(BUILD)/fuzz_huff_fuzzer   -max_total_time=$(TIME) \
	    -print_final_stats=1

clean:
	rm -rf $(BUILD)
