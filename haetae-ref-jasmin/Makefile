.RECIPEPREFIX := >

CC ?= cc
JASMINC ?= jasminc

CPPFLAGS ?=
CPPFLAGS += -Iinclude
CFLAGS ?= -O3 -g -fPIC -std=c11 -MMD -MP
LDFLAGS ?=
LDLIBS ?=
OPENSSL_LDLIBS ?= -lcrypto

MODES := mode2 mode3 mode5

HPOLY_DEPS := jasmin/hpoly.jazz jasmin/params.jinc jasmin/poly.jinc \
  jasmin/pack.jinc jasmin/decompose.jinc jasmin/sampler.jinc \
  jasmin/polyfix.jinc jasmin/challenge.jinc jasmin/reduce.jinc \
  jasmin/fixpoint.jinc jasmin/hyperball_phase.jinc jasmin/sign.jinc \
  jasmin/encoding.jinc jasmin/keccak.jinc jasmin/fft.jinc jasmin/zetas.jinc
POLYNOMIAL_SAMPLER_DEPS := jasmin/polynomial_sampler.jazz jasmin/polynomial_sampler.jinc \
  jasmin/params.jinc jasmin/keccak.jinc
SHAKE256_MULTI_ABSORB_DEPS := jasmin/shake256_multi_absorb.jazz jasmin/shake256_multi_absorb.jinc \
  jasmin/keccak.jinc
CHALLENGE_SAMPLER_DEPS := jasmin/challenge_sampler.jazz \
  jasmin/challenge_sampler.jinc jasmin/params.jinc jasmin/keccak.jinc \
  jasmin/challenge.jinc
EXPAND_DEPS := jasmin/expand.jazz jasmin/expand.jinc \
  jasmin/polynomial_sampler.jinc jasmin/params.jinc jasmin/keccak.jinc
PUBLIC_KEY_UNPACK_DEPS := jasmin/public_key_unpack.jazz \
  jasmin/public_key_unpack.jinc jasmin/params.jinc jasmin/reduce.jinc \
  jasmin/zetas.jinc jasmin/keccak.jinc jasmin/pack.jinc \
  jasmin/poly.jinc jasmin/polynomial_sampler.jinc jasmin/expand.jinc
ENCODING_DEPS := jasmin/encoding.jazz jasmin/sparse_encoding.jinc \
  jasmin/encoding.jinc
FIPS202_DEPS := jasmin/fips202.jazz jasmin/keccak.jinc
GAUSSIAN_SAMPLER_DEPS := jasmin/gaussian_sampler.jazz jasmin/gaussian_sampler.jinc \
  jasmin/params.jinc jasmin/keccak.jinc jasmin/fixpoint.jinc \
  jasmin/sampler.jinc jasmin/polynomial_sampler.jinc
FFT_DEPS := jasmin/fft.jazz jasmin/fft_pipeline.jinc jasmin/fft.jinc
SIGNATURE_PACK_FINALIZE_DEPS := jasmin/signature_pack_finalize.jazz \
  jasmin/signature_pack_finalize.jinc jasmin/pack.jinc jasmin/params.jinc
SIGNATURE_PACK_DEPS := jasmin/signature_pack.jazz jasmin/signature_pack.jinc \
  jasmin/params.jinc jasmin/pack.jinc jasmin/encoding.jinc \
  jasmin/sparse_encoding.jinc jasmin/encoding_tables.jinc
SIGNATURE_UNPACK_DEPS := jasmin/signature_unpack.jazz \
  jasmin/signature_unpack.jinc jasmin/params.jinc jasmin/pack.jinc \
  jasmin/encoding.jinc jasmin/sparse_encoding.jinc \
  jasmin/encoding_tables.jinc
VERIFICATION_TRANSCRIPT_DEPS := jasmin/verification_transcript.jazz jasmin/verification_transcript.jinc \
  jasmin/params.jinc jasmin/keccak.jinc jasmin/challenge.jinc \
  jasmin/poly.jinc jasmin/pack.jinc jasmin/challenge_sampler.jinc
VERIFY_MATRIX_DEPS := jasmin/verification_matrix.jazz jasmin/params.jinc \
  jasmin/poly.jinc jasmin/reduce.jinc jasmin/zetas.jinc
VERIFY_DEPS := jasmin/verify.jazz jasmin/api.jinc \
  jasmin/params.jinc jasmin/reduce.jinc jasmin/zetas.jinc \
  jasmin/keccak.jinc jasmin/pack.jinc jasmin/encoding.jinc \
  jasmin/sparse_encoding.jinc jasmin/encoding_tables.jinc \
  jasmin/challenge.jinc jasmin/poly.jinc jasmin/polynomial_sampler.jinc \
  jasmin/expand.jinc jasmin/signature_unpack.jinc \
  jasmin/public_key_unpack.jinc jasmin/sign.jinc \
  jasmin/challenge_sampler.jinc jasmin/verification_transcript.jinc
SINGULAR_VALUES_DEPS := jasmin/singular_values.jazz jasmin/params.jinc \
  jasmin/fft.jinc jasmin/fft_pipeline.jinc jasmin/sign.jinc jasmin/poly.jinc \
  jasmin/reduce.jinc jasmin/zetas.jinc jasmin/keccak.jinc \
  jasmin/fft_tables.jinc jasmin/singular_values.jinc
SIGNING_CHALLENGE_DEPS := jasmin/signing_challenge.jazz jasmin/params.jinc \
  jasmin/keccak.jinc jasmin/challenge.jinc jasmin/decompose.jinc \
  jasmin/pack.jinc jasmin/challenge_sampler.jinc
SIGNING_ROUND_DEPS := jasmin/signing_round.jazz jasmin/params.jinc \
  jasmin/polyfix.jinc jasmin/keccak.jinc
SIGNING_CHALLENGE_PRODUCT_DEPS := jasmin/signing_challenge_product.jazz jasmin/params.jinc jasmin/poly.jinc \
  jasmin/reduce.jinc jasmin/zetas.jinc
KEYPAIR_MATRIX_DEPS := jasmin/keypair_matrix.jazz jasmin/params.jinc \
  jasmin/poly.jinc jasmin/reduce.jinc jasmin/zetas.jinc
KEYPAIR_DEPS := jasmin/keypair.jazz jasmin/api.jinc \
  jasmin/params.jinc jasmin/keccak.jinc jasmin/polynomial_sampler.jinc \
  jasmin/expand.jinc jasmin/poly.jinc jasmin/reduce.jinc \
  jasmin/zetas.jinc jasmin/pack.jinc jasmin/sign.jinc \
  jasmin/fft.jinc jasmin/fft_pipeline.jinc jasmin/fft_tables.jinc \
  jasmin/singular_values.jinc
HYPERBALL_DEPS := jasmin/hyperball.jazz jasmin/params.jinc \
  jasmin/keccak.jinc jasmin/fixpoint.jinc jasmin/sampler.jinc \
  jasmin/polynomial_sampler.jinc jasmin/gaussian_sampler.jinc jasmin/polyfix.jinc \
  jasmin/hyperball_phase.jinc
SIGN_DEPS := jasmin/sign.jazz jasmin/api.jinc \
  jasmin/params.jinc jasmin/keccak.jinc jasmin/polynomial_sampler.jinc \
  jasmin/fixpoint.jinc jasmin/sampler.jinc jasmin/gaussian_sampler.jinc \
  jasmin/polyfix.jinc jasmin/hyperball_phase.jinc jasmin/reduce.jinc \
  jasmin/zetas.jinc jasmin/poly.jinc jasmin/pack.jinc \
  jasmin/encoding.jinc jasmin/sparse_encoding.jinc \
  jasmin/encoding_tables.jinc jasmin/challenge.jinc \
  jasmin/challenge_sampler.jinc jasmin/expand.jinc \
  jasmin/decompose.jinc jasmin/sign.jinc jasmin/signature_pack.jinc \
  jasmin/public_key_unpack.jinc

JAZZ_ASM := \
  build/jasmin/hpoly.s \
  build/jasmin/polynomial_sampler.s \
  build/jasmin/shake256_multi_absorb.s \
  build/jasmin/challenge_sampler.s \
  build/jasmin/expand.s \
  build/jasmin/public_key_unpack.s \
  build/jasmin/encoding.s \
  build/jasmin/fips202.s \
  build/jasmin/gaussian_sampler.s \
  build/jasmin/fft.s \
  build/jasmin/signature_pack_finalize.s \
  build/jasmin/signature_pack.s \
  build/jasmin/signature_unpack.s \
  build/jasmin/verification_transcript.s \
  build/jasmin/verification_matrix.s \
  build/jasmin/verify.s \
  build/jasmin/singular_values.s \
  build/jasmin/signing_challenge.s \
  build/jasmin/signing_round.s \
  build/jasmin/signing_challenge_product.s \
  build/jasmin/keypair_matrix.s \
  build/jasmin/keypair.s \
  build/jasmin/hyperball.s \
  build/jasmin/sign.s

.PHONY: all libs bins kat-bins sign-test test kat clean

all: libs bins
libs: $(foreach mode,$(MODES),build/$(mode)/lib/libhaetae-$(mode)-jazz.so)
bins: $(foreach mode,$(MODES),build/bin/haetae-$(mode)-main-jazz)
kat-bins: $(foreach mode,$(MODES),build/bin/haetae-$(mode)-kat-jazz)
sign-test: $(foreach mode,$(MODES),sign-test-$(mode))
test: sign-test kat
kat: kat-bins $(foreach mode,$(MODES),kat-$(mode))

build/jasmin/hpoly.s: $(HPOLY_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/hpoly.jazz

build/jasmin/polynomial_sampler.s: $(POLYNOMIAL_SAMPLER_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/polynomial_sampler.jazz

build/jasmin/shake256_multi_absorb.s: $(SHAKE256_MULTI_ABSORB_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/shake256_multi_absorb.jazz

build/jasmin/challenge_sampler.s: $(CHALLENGE_SAMPLER_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/challenge_sampler.jazz

build/jasmin/expand.s: $(EXPAND_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/expand.jazz

build/jasmin/public_key_unpack.s: $(PUBLIC_KEY_UNPACK_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/public_key_unpack.jazz

build/jasmin/encoding.s: $(ENCODING_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/encoding.jazz

build/jasmin/fips202.s: $(FIPS202_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/fips202.jazz

build/jasmin/gaussian_sampler.s: $(GAUSSIAN_SAMPLER_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -auto-spill-all -o $@ jasmin/gaussian_sampler.jazz

build/jasmin/fft.s: $(FFT_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/fft.jazz

build/jasmin/signature_pack_finalize.s: $(SIGNATURE_PACK_FINALIZE_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/signature_pack_finalize.jazz

build/jasmin/signature_pack.s: $(SIGNATURE_PACK_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/signature_pack.jazz

build/jasmin/signature_unpack.s: $(SIGNATURE_UNPACK_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/signature_unpack.jazz

build/jasmin/verification_transcript.s: $(VERIFICATION_TRANSCRIPT_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/verification_transcript.jazz

build/jasmin/verification_matrix.s: $(VERIFY_MATRIX_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/verification_matrix.jazz

build/jasmin/verify.s: $(VERIFY_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -auto-spill-all -o $@ jasmin/verify.jazz

build/jasmin/singular_values.s: $(SINGULAR_VALUES_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -auto-spill-all -o $@ jasmin/singular_values.jazz

build/jasmin/signing_challenge.s: $(SIGNING_CHALLENGE_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/signing_challenge.jazz

build/jasmin/signing_round.s: $(SIGNING_ROUND_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/signing_round.jazz

build/jasmin/signing_challenge_product.s: $(SIGNING_CHALLENGE_PRODUCT_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/signing_challenge_product.jazz

build/jasmin/keypair_matrix.s: $(KEYPAIR_MATRIX_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -o $@ jasmin/keypair_matrix.jazz

build/jasmin/keypair.s: $(KEYPAIR_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -auto-spill-all -o $@ jasmin/keypair.jazz

build/jasmin/hyperball.s: $(HYPERBALL_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -auto-spill-all -o $@ jasmin/hyperball.jazz

build/jasmin/sign.s: $(SIGN_DEPS) Makefile
>mkdir -p $(@D)
>$(JASMINC) -auto-spill-all -o $@ jasmin/sign.jazz

define MODE_RULES
$(1)_OBJS := $$(patsubst build/jasmin/%.s,build/$(1)/jasmin/%.o,$$(JAZZ_ASM))
$(1)_MAIN_OBJS := build/$(1)/test/main.o build/$(1)/test/randombytes.o
$(1)_KAT_OBJS := build/$(1)/kat/PQCgenKAT_sign.o \
  build/$(1)/kat/kat_sign.o build/$(1)/kat/rng.o

build/$(1)/jasmin/%.o: build/jasmin/%.s Makefile
>mkdir -p $$(@D)
>$$(CC) $$(CFLAGS) -c -o $$@ $$<

build/$(1)/test/%.o: test/%.c Makefile
>mkdir -p $$(@D)
>$$(CC) $$(CPPFLAGS) $$(CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE$(2) -c -o $$@ $$<

build/$(1)/kat/%.o: kat/%.c Makefile
>mkdir -p $$(@D)
>$$(CC) $$(CPPFLAGS) -Ikat $$(CFLAGS) -DHAETAE_CONFIG_MODE=HAETAE_MODE$(2) -c -o $$@ $$<

build/$(1)/lib/libhaetae-$(1)-jazz.so: $$($(1)_OBJS)
>mkdir -p $$(@D)
>$$(CC) -shared $$(LDFLAGS) -Wl,-soname,libhaetae-$(1)-jazz.so -o $$@ $$^ $$(LDLIBS)

build/bin/haetae-$(1)-main-jazz: $$($(1)_MAIN_OBJS) build/$(1)/lib/libhaetae-$(1)-jazz.so
>mkdir -p $$(@D)
>$$(CC) $$(LDFLAGS) -o $$@ $$($(1)_MAIN_OBJS) -Lbuild/$(1)/lib -lhaetae-$(1)-jazz -Wl,-rpath,$$(abspath build/$(1)/lib) $$(LDLIBS)

build/bin/haetae-$(1)-kat-jazz: $$($(1)_KAT_OBJS) build/$(1)/lib/libhaetae-$(1)-jazz.so
>mkdir -p $$(@D)
>$$(CC) $$(LDFLAGS) -o $$@ $$($(1)_KAT_OBJS) -Lbuild/$(1)/lib -lhaetae-$(1)-jazz -Wl,-rpath,$$(abspath build/$(1)/lib) $$(LDLIBS) $$(OPENSSL_LDLIBS)

.PHONY: sign-test-$(1) kat-$(1)
sign-test-$(1): build/bin/haetae-$(1)-main-jazz
>$$<

kat-$(1): build/bin/haetae-$(1)-kat-jazz
>mkdir -p build/kat/$(1)
>cd build/kat/$(1) && ../../bin/haetae-$(1)-kat-jazz && \
  diff -u ../../../kat/PQCsignKAT_haetae_$(1).req PQCsignKAT_haetae_$(1).req && \
  diff -u ../../../kat/PQCsignKAT_haetae_$(1).fax PQCsignKAT_haetae_$(1).rsp
endef

$(eval $(call MODE_RULES,mode2,2))
$(eval $(call MODE_RULES,mode3,3))
$(eval $(call MODE_RULES,mode5,5))

clean:
>rm -rf build

DEPS := $(foreach mode,$(MODES),build/$(mode)/test/main.d) \
  $(foreach mode,$(MODES),build/$(mode)/test/randombytes.d) \
  $(foreach mode,$(MODES),build/$(mode)/kat/PQCgenKAT_sign.d) \
  $(foreach mode,$(MODES),build/$(mode)/kat/kat_sign.d) \
  $(foreach mode,$(MODES),build/$(mode)/kat/rng.d)
-include $(DEPS)
