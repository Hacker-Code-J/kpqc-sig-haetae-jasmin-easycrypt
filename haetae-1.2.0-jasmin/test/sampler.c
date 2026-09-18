// SPDX-License-Identifier: MIT
/* Differential oracle: the pinned release's production sampler, including its
 * static functions and CDT. Do not substitute upstream test/test_sampler.c:
 * that auxiliary file contains a different, obsolete exponential polynomial.
 * The C reference and its dependencies are linked into this test only. */
#include <inttypes.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../HAETAE-1.2.0/reference_implementation/include/symmetric.h"

static size_t squeeze_calls, refill_calls;

static void counted_squeeze(uint8_t *out, size_t nblocks, keccak_state *state) {
  if (squeeze_calls == 0 && nblocks != 49) {
    fputs("FAIL: production sampler must begin with 49 SHAKE256 blocks\n", stderr);
    exit(1);
  }
  if (squeeze_calls++ != 0) {
    if (nblocks != 1) {
      fputs("FAIL: production sampler refill must use one SHAKE256 block\n", stderr);
      exit(1);
    }
    ++refill_calls;
  }
  shake256_squeezeblocks(out, nblocks, state);
}

/* Count refills without changing the random stream or the sampler algorithm. */
#undef stream256_squeezeblocks
#define stream256_squeezeblocks counted_squeeze
#include "../../HAETAE-1.2.0/reference_implementation/src/sampler.c"
#undef stream256_squeezeblocks

uint64_t test_sample_gauss83_jazz(uint64_t lo, uint32_t hi);
int64_t test_smulh48_jazz(int64_t a, uint64_t b);
uint64_t test_approx_exp_jazz(uint64_t x);
void test_sample_gauss_sigma76_jazz(uint64_t r[1], uint64_t sqr[2],
                                   uint32_t accepted[1], const uint8_t in[26]);
void test_sample_gauss_jazz(uint64_t r[512], uint64_t sqsum[2], uint64_t count[1],
                           const uint8_t buf[8192], uint64_t counts,
                           uint64_t dont_write_last);
void sample_gauss_N_full_jazz(uint64_t r[4096], uint8_t signs[512],
                              uint64_t sqsum[2], const uint8_t seed[64],
                              uint64_t nonce, uint64_t len);

#define ARRAY_LEN(a) (sizeof(a) / sizeof((a)[0]))
#define MASK48 UINT64_C(0xffffffffffff)
#define CANARY UINT64_C(0x9bd327aee57460c1)

static uint64_t random_state = UINT64_C(0x1200a37ec9b4826d);

static uint64_t next_random(void) {
  uint64_t x = (random_state += UINT64_C(0x9e3779b97f4a7c15));
  x = (x ^ (x >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  x = (x ^ (x >> 27)) * UINT64_C(0x94d049bb133111eb);
  return x ^ (x >> 31);
}

static void random_bytes(uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; ++i)
    p[i] = (uint8_t)next_random();
}

static void expect_u64(const char *name, size_t i, uint64_t expected,
                       uint64_t actual) {
  if (expected != actual) {
    fprintf(stderr, "FAIL %s[%zu]: expected 0x%016" PRIx64
                    ", got 0x%016" PRIx64 "\n",
            name, i, expected, actual);
    exit(1);
  }
}

static void expect_bytes(const char *name, const void *expected,
                         const void *actual, size_t n) {
  const uint8_t *a = expected, *b = actual;
  for (size_t i = 0; i < n; ++i)
    expect_u64(name, i, a[i], b[i]);
}

static void store_le(uint8_t *p, uint64_t x, size_t n) {
  for (size_t i = 0; i < n; ++i) {
    p[i] = (uint8_t)x;
    x >>= 8;
  }
}

static uint128 cdt_threshold(size_t i) {
  uint64_t hi = i < CDTHILEN ? CDT83_HI[i] : UINT32_C(0x7ffff);
  return ((uint128)hi << 64) | CDT83_LO[i];
}

static void check_cdt(uint128 input, size_t i) {
  uint64_t lo = (uint64_t)input;
  uint32_t hi = (uint32_t)(input >> 64);
  expect_u64("83-bit CDT", i, sample_gauss83(lo, hi),
              test_sample_gauss83_jazz(lo, hi));
}

static void test_cdt_thresholds_and_borrows(void) {
  for (size_t i = 0; i < CDTLEN; ++i) {
    uint128 t = cdt_threshold(i);
    for (int delta = -1; delta <= 1; ++delta) {
      uint128 input = delta < 0 ? t - 1 : t + (unsigned)delta;
      uint64_t expected = i + (delta > 0);
      expect_u64("reference CDT threshold", i, expected,
                  sample_gauss83((uint64_t)input, (uint32_t)(input >> 64)));
      check_cdt(input, i);
    }
    uint32_t hi = (uint32_t)(t >> 64);
    check_cdt((uint128)hi << 64, i);
    check_cdt(((uint128)hi << 64) | UINT64_MAX, i);
    check_cdt(((uint128)(hi - 1) << 64) | UINT64_MAX, i);
    if (hi < UINT32_C(0x7ffff))
      check_cdt((uint128)(hi + 1) << 64, i);
  }
  expect_u64("CDT minimum", 0, 0, test_sample_gauss83_jazz(0, 0));
  expect_u64("CDT maximum", 0, 166,
              test_sample_gauss83_jazz(UINT64_MAX, UINT32_C(0x7ffff)));
  for (size_t i = 0; i < 4096; ++i) {
    uint128 input = ((uint128)(next_random() & UINT32_C(0x7ffff)) << 64) |
                   next_random();
    check_cdt(input, i);
  }
}

static void test_smulh48_signed_ceiling(void) {
  static const struct {
    int64_t a;
    uint64_t b;
    int64_t expected;
  } vectors[] = {
    {0, UINT64_MAX, 0}, {1, 1, 1}, {-1, 1, 0},
    {1, MASK48, 1}, {-1, MASK48, 0},
    {1, MASK48 + 1, 1}, {-1, MASK48 + 1, -1},
    {1, MASK48 + 2, 2}, {-1, MASK48 + 2, -1},
    {1, UINT64_MAX, 65536}, {-1, UINT64_MAX, -65535},
    {INT64_MAX, MASK48 + 1, INT64_MAX},
    {INT64_MIN, MASK48 + 1, INT64_MIN},
    {INT64_C(281474976710655), MASK48, INT64_C(281474976710655)},
    {-INT64_C(281474976710655), MASK48, -INT64_C(281474976710654)},
  };
  for (size_t i = 0; i < ARRAY_LEN(vectors); ++i) {
    expect_u64("reference ceiling", i, vectors[i].expected,
                smulh48(vectors[i].a, vectors[i].b));
    expect_u64("signed ceiling", i, vectors[i].expected,
                test_smulh48_jazz(vectors[i].a, vectors[i].b));
  }
  for (size_t i = 0; i < 8192; ++i) {
    /* Full-width unsigned b, with a restricted so the quotient fits int64_t. */
    int64_t a = (int64_t)(next_random() & ((UINT64_C(1) << 46) - 1));
    if (i & 1)
      a = -a;
    uint64_t b = next_random();
    expect_u64("random signed ceiling", i, smulh48(a, b),
                test_smulh48_jazz(a, b));
  }
}

static void test_exact_production_exponential(void) {
  /* Recorded from the pinned production source, not its auxiliary test. */
  static const uint64_t vectors[][2] = {
    {UINT64_C(0), UINT64_C(281474976710657)},
    {UINT64_C(1), UINT64_C(281474976710657)},
    {UINT64_C(2), UINT64_C(281474976710656)},
    {UINT64_C(17592186044416), UINT64_C(264421269977111)},
    {UINT64_C(70368744177664), UINT64_C(219212932277266)},
    {UINT64_C(140737488355327), UINT64_C(170723203316915)},
    {UINT64_C(140737488355328), UINT64_C(170723203316914)},
    {UINT64_C(140737488355329), UINT64_C(170723203316914)},
    {UINT64_C(281474976710655), UINT64_C(103548857163706)},
    {UINT64_C(281474976710656), UINT64_C(103548857163701)},
  };
  for (size_t i = 0; i < ARRAY_LEN(vectors); ++i) {
    expect_u64("reference exponential", i, vectors[i][1],
                approx_exp(vectors[i][0]));
    expect_u64("production exponential", i, vectors[i][1],
                test_approx_exp_jazz(vectors[i][0]));
  }
  for (size_t i = 0; i < 8192; ++i) {
    uint64_t x = next_random() & MASK48;
    expect_u64("random exponential", i, approx_exp(x), test_approx_exp_jazz(x));
  }
}

static void sigma_input(uint8_t in[26], unsigned x, uint64_t rej,
                         uint64_t noise_lo, uint32_t noise_hi) {
  uint128 input = x == 0 ? 0 : cdt_threshold(x - 1) + 1;
  memset(in, 0, 26);
  store_le(in, (uint64_t)input, 8);
  store_le(in + 8, (uint64_t)(input >> 64), 3);
  store_le(in + 11, rej, 6);
  store_le(in + 17, noise_lo, 6);
  store_le(in + 23, noise_hi, 3);
}

static uint64_t check_sigma(const uint8_t in[26], size_t i) {
  uint64_t expected_r, r[3] = {CANARY, CANARY, CANARY};
  uint64_t sqr[4] = {CANARY, CANARY, CANARY, CANARY};
  uint32_t accepted[3] = {UINT32_C(0xacf97351), 2, UINT32_C(0xacf97351)};
  uint8_t original[26];
  fp96_76 expected_sqr;
  memcpy(original, in, 26);
  int expected_accepted = sample_gauss_sigma76(&expected_r, &expected_sqr, in);
  test_sample_gauss_sigma76_jazz(r + 1, sqr + 1, accepted + 1, in);
  expect_u64("sigma76 rounded output", i, expected_r, r[1]);
  expect_u64("sigma76 square low", i, expected_sqr.limb48[0], sqr[1]);
  expect_u64("sigma76 square high", i, expected_sqr.limb48[1], sqr[2]);
  expect_u64("sigma76 accepted", i, expected_accepted, accepted[1]);
  expect_u64("sigma76 output prefix", i, CANARY, r[0]);
  expect_u64("sigma76 output suffix", i, CANARY, r[2]);
  expect_u64("sigma76 square prefix", i, CANARY, sqr[0]);
  expect_u64("sigma76 square suffix", i, CANARY, sqr[3]);
  expect_u64("sigma76 accepted prefix", i, UINT32_C(0xacf97351), accepted[0]);
  expect_u64("sigma76 accepted suffix", i, UINT32_C(0xacf97351), accepted[2]);
  expect_bytes("sigma76 immutable input", original, in, 26);
  return r[1];
}

static void test_sigma76_26_bytes_and_tail_rounding(void) {
  static const unsigned tails[] = {0, 1, 63, 64, 75, 76, 127, 128, 129, 165, 166};
  static const uint64_t noise[] = {0, 1, 32767, 32768, 65535, MASK48};
  uint8_t in[26];
  for (size_t i = 0; i < ARRAY_LEN(tails); ++i) {
    for (size_t j = 0; j < ARRAY_LEN(noise); ++j) {
      for (unsigned h = 0; h < 2; ++h) {
        uint32_t hi = h ? UINT32_C(0xffffff) : 0;
        for (unsigned b = 0; b < 3; ++b) {
          uint64_t rej = b == 2 ? MASK48 : b;
          sigma_input(in, tails[i], rej, noise[j], hi);
          uint64_t r = check_sigma(in, i * 36 + j * 6 + h * 3 + b);
          uint64_t rounded = (((noise[j] >> 15) + 1) >> 1) +
                             (((uint64_t)hi | ((uint64_t)tails[i] << 24)) << 32);
          expect_u64("tail rounding with x >= 128", i, rounded, r);
        }
      }
    }
  }
  sigma_input(in, 128, 1, MASK48, UINT32_C(0xffffff));
  uint64_t expected = check_sigma(in, 0);
  in[10] |= UINT8_C(0xf8);
  expect_u64("unused CDT high bits masked", 0, expected, check_sigma(in, 1));

  /* Input byte 25 carries high noise bits; the old 17-byte layout misses it. */
  sigma_input(in, 1, 1, 0, 0);
  uint64_t before = check_sigma(in, 0);
  in[25] = 1;
  expect_u64("26th input byte contributes to sample", 0,
              before + (UINT64_C(1) << 48), check_sigma(in, 1));
  for (size_t i = 0; i < 4096; ++i) {
    random_bytes(in, sizeof(in));
    check_sigma(in, i);
  }
}

static void test_sample_gauss_lengths_and_dummy(void) {
  static const size_t byte_lengths[] = {
    0, 1, 16, 17, 25, 26, 27, 51, 52, 53, 135, 136, 137, 6655, 6664, 8192
  };
  static const size_t lengths[] = {0, 1, 2, 8, 255, 256, 257, 512};
  uint8_t buf[8192], original[8192];
  uint64_t expected[514], actual[514];
  for (size_t i = 0; i < ARRAY_LEN(byte_lengths); ++i) {
    random_bytes(buf, sizeof(buf));
    memcpy(original, buf, sizeof(buf));
    for (size_t j = 0; j < ARRAY_LEN(lengths); ++j) {
      for (unsigned dont = 0; dont < 2; ++dont) {
        for (size_t k = 0; k < ARRAY_LEN(expected); ++k)
          expected[k] = actual[k] = CANARY;
        fp96_76 expected_sum = {{MASK48 - 13, UINT64_C(0x348120)}};
        uint64_t actual_sum[4] = {CANARY, MASK48 - 13, UINT64_C(0x348120), CANARY};
        uint64_t count[3] = {CANARY, CANARY, CANARY};
        int want = sample_gauss(expected + 1, &expected_sum, buf, byte_lengths[i],
                                 lengths[j], dont);
        uint64_t counts = ((uint64_t)byte_lengths[i] << 32) | lengths[j];
        test_sample_gauss_jazz(actual + 1, actual_sum + 1, count + 1, buf,
                               counts, dont);
        expect_u64("sample_gauss accepted count", i, want, count[1]);
        expect_bytes("sample_gauss samples and guards", expected, actual,
                      sizeof(expected));
        expect_bytes("sample_gauss accumulated square", expected_sum.limb48,
                      actual_sum + 1, sizeof(expected_sum));
        expect_u64("sample_gauss sum prefix", i, CANARY, actual_sum[0]);
        expect_u64("sample_gauss sum suffix", i, CANARY, actual_sum[3]);
        expect_u64("sample_gauss count prefix", i, CANARY, count[0]);
        expect_u64("sample_gauss count suffix", i, CANARY, count[2]);
        expect_bytes("sample_gauss immutable stream", original, buf, sizeof(buf));
      }
    }
  }
}

static void test_sample_N_deterministic_stream_and_refills(void) {
  static const size_t lengths[] = {0, 1, 7, 8, 9, 255, 256, 257, 258, 512, 513, 4096};
  static const uint16_t nonces[] = {0, 1, 256, UINT16_C(0xff00), UINT16_MAX};
  uint64_t expected[4098], actual[4098];
  uint8_t signs_expected[514], signs_actual[514], seed[HAETAE_CRHBYTES];
  size_t total_refills = 0, multi_refill_cases = 0;
  for (size_t i = 0; i < ARRAY_LEN(nonces); ++i) {
    for (size_t k = 0; k < sizeof(seed); ++k)
      seed[k] = i == 0 ? 0 : i == 1 ? UINT8_MAX : (uint8_t)(k + 17 * i);
    for (size_t j = 0; j < ARRAY_LEN(lengths); ++j) {
      for (size_t k = 0; k < ARRAY_LEN(expected); ++k)
        expected[k] = actual[k] = CANARY;
      memset(signs_expected, 0xa7, sizeof(signs_expected));
      memset(signs_actual, 0xa7, sizeof(signs_actual));
      fp96_76 expected_sum = {{MASK48 - 7, UINT64_C(0x120034)}};
      uint64_t actual_sum[4] = {CANARY, MASK48 - 7, UINT64_C(0x120034), CANARY};
      uint8_t original_seed[HAETAE_CRHBYTES];
      memcpy(original_seed, seed, sizeof(seed));
      squeeze_calls = refill_calls = 0;
      sample_gauss_N(expected + 1, signs_expected + 1, &expected_sum,
                      seed, nonces[i], lengths[j]);
      total_refills += refill_calls;
      multi_refill_cases += refill_calls >= 2;
      sample_gauss_N_full_jazz(actual + 1, signs_actual + 1, actual_sum + 1,
                               seed, nonces[i], lengths[j]);
      expect_bytes("sample_N samples and guards", expected, actual, sizeof(expected));
      expect_bytes("sample_N sign bytes and guards", signs_expected, signs_actual,
                    sizeof(signs_expected));
      expect_bytes("sample_N accumulated square", expected_sum.limb48,
                    actual_sum + 1, sizeof(expected_sum));
      expect_u64("sample_N sum prefix", j, CANARY, actual_sum[0]);
      expect_u64("sample_N sum suffix", j, CANARY, actual_sum[3]);
      expect_bytes("sample_N immutable seed", original_seed, seed, sizeof(seed));
    }
  }
  if (total_refills == 0 || multi_refill_cases == 0) {
    fputs("FAIL: deterministic sample_N vectors did not exercise repeated refills\n",
          stderr);
    exit(1);
  }
  printf("  sample_N: %zu refill blocks, %zu cases with repeated refills\n",
         total_refills, multi_refill_cases);
}

int main(void) {
  test_cdt_thresholds_and_borrows();
  puts("PASS 83-bit CDT thresholds, equality and high-word borrows");
  test_smulh48_signed_ceiling();
  puts("PASS smulh48 signed ceiling and full-width unsigned multipliers");
  test_exact_production_exponential();
  puts("PASS production degree-10 exponential fixed vectors and random inputs");
  test_sigma76_26_bytes_and_tail_rounding();
  puts("PASS 26-byte sigma76, rejection, masked bits and tails through x=166");
  test_sample_gauss_lengths_and_dummy();
  puts("PASS sample_gauss byte lengths, accumulated squares and dummy outputs");
  test_sample_N_deterministic_stream_and_refills();
  puts("PASS sample_N deterministic SHAKE streams, sign bytes and refill carry");
  return 0;
}
