# Usage
# make            # build mode2 + mode3 + mode5
# make mode2      # build only HAETAE mode2
# make mode3      # build only HAETAE mode3
# make mode5      # build only HAETAE mode5
# make clean      # remove build/

CC           ?= /usr/bin/cc
CSTD         ?= c11
CPPFLAGS     ?=
CFLAGS       ?= -O2
LDFLAGS      ?=
LDLIBS       ?=
OPENSSL_LIBS ?= -lcrypto
WARNFLAGS    ?=

INCLUDES     := -I./include
BASE_CFLAGS  := $(INCLUDES) $(WARNFLAGS) -std=$(CSTD) -MMD -MP
PICFLAGS     := -fPIC
RPATH_FLAG   := -Wl,-rpath,'$$ORIGIN/../lib'

BUILD_DIR    := build
COMMON_DIR   := $(BUILD_DIR)/common
LIB_DIR      := $(BUILD_DIR)/lib
BIN_DIR      := $(BUILD_DIR)/bin

COMMON_SRCS := \
	src/randombytes.c \
	src/fips202.c \
	src/symmetric-shake.c

LIB_SRCS := \
	src/decompose.c \
	src/encoding.c \
	src/fft.c \
	src/fixpoint.c \
	src/ntt.c \
	src/packing.c \
	src/poly.c \
	src/polyvec.c \
	src/polymat.c \
	src/polyfix.c \
	src/reduce.c \
	src/sampler.c \
	src/sign.c

COMMON_OBJS := $(patsubst %.c,$(COMMON_DIR)/%.o,$(COMMON_SRCS))

MODE2_LIB_OBJS   := $(patsubst src/%.c,$(BUILD_DIR)/mode2/src/%.o,$(LIB_SRCS))
MODE3_LIB_OBJS   := $(patsubst src/%.c,$(BUILD_DIR)/mode3/src/%.o,$(LIB_SRCS))
MODE5_LIB_OBJS   := $(patsubst src/%.c,$(BUILD_DIR)/mode5/src/%.o,$(LIB_SRCS))

MODE2_MAIN_OBJ   := $(BUILD_DIR)/mode2/test/main.o
MODE3_MAIN_OBJ   := $(BUILD_DIR)/mode3/test/main.o
MODE5_MAIN_OBJ   := $(BUILD_DIR)/mode5/test/main.o

MODE2_KAT_OBJS   := $(BUILD_DIR)/mode2/kat/kat_sign.o $(BUILD_DIR)/mode2/kat/PQCgenKAT_sign.o $(BUILD_DIR)/mode2/kat/rng.o
MODE3_KAT_OBJS   := $(BUILD_DIR)/mode3/kat/kat_sign.o $(BUILD_DIR)/mode3/kat/PQCgenKAT_sign.o $(BUILD_DIR)/mode3/kat/rng.o
MODE5_KAT_OBJS   := $(BUILD_DIR)/mode5/kat/kat_sign.o $(BUILD_DIR)/mode5/kat/PQCgenKAT_sign.o $(BUILD_DIR)/mode5/kat/rng.o

MODE2_BENCH_OBJS := $(BUILD_DIR)/mode2/benchmark/speed.o $(BUILD_DIR)/mode2/benchmark/cpucycles.o $(BUILD_DIR)/mode2/benchmark/speed_print.o
MODE3_BENCH_OBJS := $(BUILD_DIR)/mode3/benchmark/speed.o $(BUILD_DIR)/mode3/benchmark/cpucycles.o $(BUILD_DIR)/mode3/benchmark/speed_print.o
MODE5_BENCH_OBJS := $(BUILD_DIR)/mode5/benchmark/speed.o $(BUILD_DIR)/mode5/benchmark/cpucycles.o $(BUILD_DIR)/mode5/benchmark/speed_print.o

MODE2_LIB   := $(LIB_DIR)/libhaetae-mode2.so
MODE3_LIB   := $(LIB_DIR)/libhaetae-mode3.so
MODE5_LIB   := $(LIB_DIR)/libhaetae-mode5.so

MODE2_MAIN  := $(BIN_DIR)/haetae-mode2-main
MODE3_MAIN  := $(BIN_DIR)/haetae-mode3-main
MODE5_MAIN  := $(BIN_DIR)/haetae-mode5-main

MODE2_KAT   := $(BIN_DIR)/haetae-mode2-kat
MODE3_KAT   := $(BIN_DIR)/haetae-mode3-kat
MODE5_KAT   := $(BIN_DIR)/haetae-mode5-kat

MODE2_BENCH := $(BIN_DIR)/haetae-mode2-benchmark
MODE3_BENCH := $(BIN_DIR)/haetae-mode3-benchmark
MODE5_BENCH := $(BIN_DIR)/haetae-mode5-benchmark

ALL_OBJS := \
	$(COMMON_OBJS) \
	$(MODE2_LIB_OBJS) $(MODE3_LIB_OBJS) $(MODE5_LIB_OBJS) \
	$(MODE2_MAIN_OBJ) $(MODE3_MAIN_OBJ) $(MODE5_MAIN_OBJ) \
	$(MODE2_KAT_OBJS) $(MODE3_KAT_OBJS) $(MODE5_KAT_OBJS) \
	$(MODE2_BENCH_OBJS) $(MODE3_BENCH_OBJS) $(MODE5_BENCH_OBJS)

DEPS := $(ALL_OBJS:.o=.d)

.PHONY: all clean mode2 mode3 mode5 libs mains kats benchmarks

all: mode2 mode3 mode5

mode2: $(MODE2_LIB) $(MODE2_MAIN) $(MODE2_KAT) $(MODE2_BENCH)
mode3: $(MODE3_LIB) $(MODE3_MAIN) $(MODE3_KAT) $(MODE3_BENCH)
mode5: $(MODE5_LIB) $(MODE5_MAIN) $(MODE5_KAT) $(MODE5_BENCH)

libs: $(MODE2_LIB) $(MODE3_LIB) $(MODE5_LIB)
mains: $(MODE2_MAIN) $(MODE3_MAIN) $(MODE5_MAIN)
kats: $(MODE2_KAT) $(MODE3_KAT) $(MODE5_KAT)
benchmarks: $(MODE2_BENCH) $(MODE3_BENCH) $(MODE5_BENCH)

$(COMMON_DIR)/src/%.o: src/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) $(PICFLAGS) -o $@ -c $<

$(BUILD_DIR)/mode2/src/%.o: src/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) $(PICFLAGS) \
		-DHAETAE_CONFIG_MODE=HAETAE_MODE2 -Dhaetae_mode2_EXPORTS \
		-o $@ -c $<

$(BUILD_DIR)/mode3/src/%.o: src/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) $(PICFLAGS) \
		-DHAETAE_CONFIG_MODE=HAETAE_MODE3 -Dhaetae_mode3_EXPORTS \
		-o $@ -c $<

$(BUILD_DIR)/mode5/src/%.o: src/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) $(PICFLAGS) \
		-DHAETAE_CONFIG_MODE=HAETAE_MODE5 -Dhaetae_mode5_EXPORTS \
		-o $@ -c $<

$(BUILD_DIR)/mode2/test/%.o: test/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE2 -o $@ -c $<

$(BUILD_DIR)/mode3/test/%.o: test/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE3 -o $@ -c $<

$(BUILD_DIR)/mode5/test/%.o: test/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE5 -o $@ -c $<

$(BUILD_DIR)/mode2/kat/%.o: kat/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE2 -o $@ -c $<

$(BUILD_DIR)/mode3/kat/%.o: kat/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE3 -o $@ -c $<

$(BUILD_DIR)/mode5/kat/%.o: kat/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE5 -o $@ -c $<

$(BUILD_DIR)/mode2/benchmark/%.o: benchmark/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE2 -o $@ -c $<

$(BUILD_DIR)/mode3/benchmark/%.o: benchmark/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE3 -o $@ -c $<

$(BUILD_DIR)/mode5/benchmark/%.o: benchmark/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(BASE_CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE5 -o $@ -c $<

$(MODE2_LIB): $(COMMON_OBJS) $(MODE2_LIB_OBJS)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) -shared -Wl,-soname,$(@F) -o $@ $^ $(LDLIBS)

$(MODE3_LIB): $(COMMON_OBJS) $(MODE3_LIB_OBJS)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) -shared -Wl,-soname,$(@F) -o $@ $^ $(LDLIBS)

$(MODE5_LIB): $(COMMON_OBJS) $(MODE5_LIB_OBJS)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) -shared -Wl,-soname,$(@F) -o $@ $^ $(LDLIBS)

$(MODE2_MAIN): $(COMMON_DIR)/src/randombytes.o $(MODE2_MAIN_OBJ) $(MODE2_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(COMMON_DIR)/src/randombytes.o $(MODE2_MAIN_OBJ) -o $@ $(RPATH_FLAG) $(MODE2_LIB) $(LDLIBS)

$(MODE3_MAIN): $(COMMON_DIR)/src/randombytes.o $(MODE3_MAIN_OBJ) $(MODE3_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(COMMON_DIR)/src/randombytes.o $(MODE3_MAIN_OBJ) -o $@ $(RPATH_FLAG) $(MODE3_LIB) $(LDLIBS)

$(MODE5_MAIN): $(COMMON_DIR)/src/randombytes.o $(MODE5_MAIN_OBJ) $(MODE5_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(COMMON_DIR)/src/randombytes.o $(MODE5_MAIN_OBJ) -o $@ $(RPATH_FLAG) $(MODE5_LIB) $(LDLIBS)

$(MODE2_KAT): $(MODE2_KAT_OBJS) $(MODE2_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(MODE2_KAT_OBJS) -o $@ $(RPATH_FLAG) $(MODE2_LIB) $(OPENSSL_LIBS) $(LDLIBS)

$(MODE3_KAT): $(MODE3_KAT_OBJS) $(MODE3_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(MODE3_KAT_OBJS) -o $@ $(RPATH_FLAG) $(MODE3_LIB) $(OPENSSL_LIBS) $(LDLIBS)

$(MODE5_KAT): $(MODE5_KAT_OBJS) $(MODE5_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(MODE5_KAT_OBJS) -o $@ $(RPATH_FLAG) $(MODE5_LIB) $(OPENSSL_LIBS) $(LDLIBS)

$(MODE2_BENCH): $(MODE2_BENCH_OBJS) $(COMMON_DIR)/src/randombytes.o $(MODE2_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(MODE2_BENCH_OBJS) $(COMMON_DIR)/src/randombytes.o -o $@ $(RPATH_FLAG) $(MODE2_LIB) $(LDLIBS)

$(MODE3_BENCH): $(MODE3_BENCH_OBJS) $(COMMON_DIR)/src/randombytes.o $(MODE3_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(MODE3_BENCH_OBJS) $(COMMON_DIR)/src/randombytes.o -o $@ $(RPATH_FLAG) $(MODE3_LIB) $(LDLIBS)

$(MODE5_BENCH): $(MODE5_BENCH_OBJS) $(COMMON_DIR)/src/randombytes.o $(MODE5_LIB)
	@mkdir -p $(dir $@)
	$(CC) $(LDFLAGS) $(MODE5_BENCH_OBJS) $(COMMON_DIR)/src/randombytes.o -o $@ $(RPATH_FLAG) $(MODE5_LIB) $(LDLIBS)

clean:
	rm -rf $(BUILD_DIR)

-include $(DEPS)
