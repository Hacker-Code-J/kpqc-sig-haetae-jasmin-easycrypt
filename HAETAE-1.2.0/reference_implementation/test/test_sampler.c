/*
 * test_sampler.c — Statistical + security-proof verification of HAETAE Gaussian
 * sampler.
 *
 * Tests 1-3: CDT83 table (standalone, no HAETAE library needed internally;
 *            uses a local copy of CDT83 and xoshiro256** PRNG).
 *   (1) CDT83 monotonicity
 *   (2) Per-k chi-squared goodness-of-fit (D_{Z+,16}, k=0..14 + tail)
 *   (3) E[X] and E[X²] vs discrete half-Gaussian theory
 *
 * Test 4: Full sampler via HAETAE library (sample_gauss).
 *   (4) Acceptance rate of sample_gauss_sigma76
 *       Expected: Z_accept ≈ 1 − P_CDT[0]/2 ≈ 0.9757
 *
 * Test 5: Security proof conditions for approx_exp (direct R_α bound).
 *   [C1] Ceiling property: P(xi) ≥ f(xi) for all xi ∈ [0, X_max]
 *        Phase 1: exhaustive xi ∈ [1, 2^28] (~268M values)
 *        Phase 2: dense octave scan xi ∈ [2^28, X_max] (2M pts/octave)
 *   [C2] K₁ = -log₂(max (P-f)/f) ≥ K_req = 44.022
 *   [C3] R_511 - 1 ≤ 1/(4Q),  Q ≤ 2^{78.05}
 *
 * Compile (mode5):
 *   gcc -O3 -DHAETAE_CONFIG_MODE=HAETAE_MODE5 -I include \
 *       -o /tmp/test_sampler test/test_sampler.c \
 *       -L build/lib -lhaetae-mode5 -Wl,-rpath,build/lib -lm
 */

#include "fixpoint.h"
#include "params.h"
#include "sampler.h"
#include "symmetric.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define GAUSS_RAND_BYTES_TEST 26

/* sample_gauss is non-static in sampler.c but not exposed in sampler.h */
extern int sample_gauss(uint64_t *r, fp96_76 *sqsum, const uint8_t *buf,
                        size_t buflen, size_t len, int dont_write_last);

/* ─── xoshiro256** PRNG (for CDT-direct tests) ──────────────────────────── */
static uint64_t xstate[4];

static void xseed(void) {
  FILE *f = fopen("/dev/urandom", "rb");
  if (!f) {
    fprintf(stderr, "cannot open /dev/urandom\n");
    exit(1);
  }
  fread(xstate, sizeof(xstate), 1, f);
  fclose(f);
  xstate[0] |= 1;
}

static inline uint64_t rotl64(uint64_t x, int k) {
  return (x << k) | (x >> (64 - k));
}

static uint64_t xrand(void) {
  uint64_t r = rotl64(xstate[1] * 5, 7) * 9;
  uint64_t t = xstate[1] << 17;
  xstate[2] ^= xstate[0];
  xstate[3] ^= xstate[1];
  xstate[1] ^= xstate[2];
  xstate[0] ^= xstate[3];
  xstate[2] ^= t;
  xstate[3] = rotl64(xstate[3], 45);
  return r;
}

/* ─── /dev/urandom helper ───────────────────────────────────────────────── */
static void fill_urandom(uint8_t *buf, size_t n) {
  FILE *f = fopen("/dev/urandom", "rb");
  if (!f) {
    fprintf(stderr, "cannot open /dev/urandom\n");
    exit(1);
  }
  if (fread(buf, 1, n, f) != n) {
    fprintf(stderr, "urandom short read\n");
    exit(1);
  }
  fclose(f);
}

/* ─── CDT83 table (local copy; CDT83_HI/LO in sampler.c are static) ────── */
#define CDTLEN 166

static const uint32_t CDT83_HI[CDTLEN] = {
    UINT32_C(0x063a5), UINT32_C(0x0c718), UINT32_C(0x129f6), UINT32_C(0x18bdf),
    UINT32_C(0x1ec73), UINT32_C(0x24b59), UINT32_C(0x2a83a), UINT32_C(0x302c6),
    UINT32_C(0x35ab6), UINT32_C(0x3afc7), UINT32_C(0x401be), UINT32_C(0x4506a),
    UINT32_C(0x49ba1), UINT32_C(0x4e343), UINT32_C(0x52736), UINT32_C(0x5676c),
    UINT32_C(0x5a3dc), UINT32_C(0x5dc86), UINT32_C(0x61172), UINT32_C(0x642ad),
    UINT32_C(0x6704c), UINT32_C(0x69a68), UINT32_C(0x6c120), UINT32_C(0x6e496),
    UINT32_C(0x704ef), UINT32_C(0x72255), UINT32_C(0x73cf1), UINT32_C(0x754f0),
    UINT32_C(0x76a7c), UINT32_C(0x77dc4), UINT32_C(0x78ef2), UINT32_C(0x79e32),
    UINT32_C(0x7abaf), UINT32_C(0x7b78f), UINT32_C(0x7c1fb), UINT32_C(0x7cb17),
    UINT32_C(0x7d304), UINT32_C(0x7d9e4), UINT32_C(0x7dfd4), UINT32_C(0x7e4f0),
    UINT32_C(0x7e950), UINT32_C(0x7ed0d), UINT32_C(0x7f03b), UINT32_C(0x7f2ec),
    UINT32_C(0x7f531), UINT32_C(0x7f71a), UINT32_C(0x7f8b3), UINT32_C(0x7fa08),
    UINT32_C(0x7fb24), UINT32_C(0x7fc0e), UINT32_C(0x7fccf), UINT32_C(0x7fd6e),
    UINT32_C(0x7fdf0), UINT32_C(0x7fe5a), UINT32_C(0x7feaf), UINT32_C(0x7fef5),
    UINT32_C(0x7ff2c), UINT32_C(0x7ff59), UINT32_C(0x7ff7d), UINT32_C(0x7ff99),
    UINT32_C(0x7ffb0), UINT32_C(0x7ffc2), UINT32_C(0x7ffd0), UINT32_C(0x7ffdb),
    UINT32_C(0x7ffe3), UINT32_C(0x7ffea), UINT32_C(0x7ffef), UINT32_C(0x7fff3),
    UINT32_C(0x7fff6), UINT32_C(0x7fff8), UINT32_C(0x7fffa), UINT32_C(0x7fffb),
    UINT32_C(0x7fffd), UINT32_C(0x7fffd), UINT32_C(0x7fffe), UINT32_C(0x7fffe),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff), UINT32_C(0x7ffff),
    UINT32_C(0x7ffff), UINT32_C(0x7ffff),
};

static const uint64_t CDT83_LO[CDTLEN] = {
    UINT64_C(0x0aa572bc88db1e27), UINT64_C(0x4f3820e69064b2ed),
    UINT64_C(0xd68dc44dd1418702), UINT64_C(0x6587a04d9b97b1db),
    UINT64_C(0x9b843ce0a65d004e), UINT64_C(0x02b62cb869003e7b),
    UINT64_C(0x0d44f194f8bf43c3), UINT64_C(0xfaa0c7acb211b4d8),
    UINT64_C(0xa11387f7f524be7c), UINT64_C(0x18526ca6f2ceb77b),
    UINT64_C(0x42a01a906b7dad13), UINT64_C(0x32e5337a1966b9a2),
    UINT64_C(0x6f00f7ac9735f585), UINT64_C(0x0e6c48f40642ba5a),
    UINT64_C(0xb6192fa1afb5e4e6), UINT64_C(0x7339dba8ffc2fcee),
    UINT64_C(0x7746cbe1ac90c9e4), UINT64_C(0xb83004341d784667),
    UINT64_C(0x781dcca572bb3d82), UINT64_C(0xb880376cc82a537b),
    UINT64_C(0x9c68a5c477dfecb0), UINT64_C(0xbe45ceb02a25feeb),
    UINT64_C(0x7d1a8ccd208dba98), UINT64_C(0x452c002b9085e7d2),
    UINT64_C(0xd7ef361c55513783), UINT64_C(0x96b4ff49d9e5a8b1),
    UINT64_C(0xd337c94ede732d79), UINT64_C(0x28c75b8d3fe83c2e),
    UINT64_C(0xe05d7bd130fe20d6), UINT64_C(0x6170e60b76d850fe),
    UINT64_C(0xb0e59892414901f4), UINT64_C(0xff05cf70b911f3d4),
    UINT64_C(0x4501460fdfd508bf), UINT64_C(0xf20b1303a2a548fc),
    UINT64_C(0xa7d3badbeb04b202), UINT64_C(0x05ce666b741b6663),
    UINT64_C(0x826e689fded20426), UINT64_C(0x5155d1354fcf6feb),
    UINT64_C(0x55469226a1d318eb), UINT64_C(0x1c8d3820cfa9cab1),
    UINT64_C(0xe68d83bbf700fc35), UINT64_C(0xb1152d89440427f8),
    UINT64_C(0x4c1e741aabe536f5), UINT64_C(0x72b94c56e0f9a95c),
    UINT64_C(0xe7e5a80a79e45391), UINT64_C(0x9641c5d11feb4d07),
    UINT64_C(0xb18b71598b73ddd5), UINT64_C(0xd9112fb5a7904d74),
    UINT64_C(0x3a4f57cbefabc816), UINT64_C(0xb314025fd502296c),
    UINT64_C(0xf2a2b228aab19811), UINT64_C(0x996ce1e60378cd8e),
    UINT64_C(0x570ec64b38e3ca86), UINT64_C(0x0657269615dcd7bc),
    UINT64_C(0xc7360038bdc85309), UINT64_C(0x167fa02a57a8ae11),
    UINT64_C(0xe380fab2ea9b2be6), UINT64_C(0xa36e6abd6509b59a),
    UINT64_C(0x62bfcf1d6ba81c2f), UINT64_C(0xd4946e8bf96caa8b),
    UINT64_C(0x603e6262ea8cda25), UINT64_C(0x2d18c8b333ae91fc),
    UINT64_C(0x2ccdedb5a7718d59), UINT64_C(0x24333ecab8497c03),
    UINT64_C(0xb2e06eb33bf2b7d2), UINT64_C(0x59a5f6c550dfe7db),
    UINT64_C(0x800548f3927f9067), UINT64_C(0x78cac146b573bc39),
    UINT64_C(0x85e6dadec4b6afea), UINT64_C(0xdba17dfa17def8e5),
    UINT64_C(0xa33f84d06ce20a8c), UINT64_C(0xfd2fe967c518673f),
    UINT64_C(0x02d37ecd7e9b1808), UINT64_C(0xc7efafa8bd33f0b4),
    UINT64_C(0x5bda826341e791c5), UINT64_C(0xca6c1c6ce0455998),
    UINT64_C(0x1cc02c0faa9a5267), UINT64_C(0x59d002901a4a4e4b),
    UINT64_C(0x86ecbd139ce07539), UINT64_C(0xa81f9f15ffb47f45),
    UINT64_C(0xc075b17481687aea), UINT64_C(0xd23ad13e68301c5f),
    UINT64_C(0xdf27955fae1c84c4), UINT64_C(0xe884cdb07368c260),
    UINT64_C(0xef46d4f897fc83f0), UINT64_C(0xf4227e46663ec043),
    UINT64_C(0xf79d091c1b5aff01), UINT64_C(0xfa183c533c3890a0),
    UINT64_C(0xfbdb8a602066b0ec), UINT64_C(0xfd1af06df3db86b1),
    UINT64_C(0xfdfc1a818587e2a3), UINT64_C(0xfe9a37a348ac2a8c),
    UINT64_C(0xff08d0797970dbf7), UINT64_C(0xff55df73fd7a00b6),
    UINT64_C(0xff8b5aa573bca5c7), UINT64_C(0xffb053c109f5167a),
    UINT64_C(0xffc9c9bd39a036e5), UINT64_C(0xffdb40bd4ee1f83f),
    UINT64_C(0xffe72fa859b20a43), UINT64_C(0xffef4edda93d2666),
    UINT64_C(0xfff4d07a9fb0d4d9), UINT64_C(0xfff88868ef31b1c5),
    UINT64_C(0xfffb08c16a3f5f05), UINT64_C(0xfffcb5d30be5cab8),
    UINT64_C(0xfffdd43465d95fdf), UINT64_C(0xfffe929a538ad2f3),
    UINT64_C(0xffff10b1c211972b), UINT64_C(0xffff63df8795a2c2),
    UINT64_C(0xffff9a87a0a9f2a8), UINT64_C(0xffffbe4df6f0f4a2),
    UINT64_C(0xffffd5a10f20490a), UINT64_C(0xffffe4c6f1668b2c),
    UINT64_C(0xffffee939680bfa8), UINT64_C(0xfffff4e4216290d4),
    UINT64_C(0xfffff8f1c0446137), UINT64_C(0xfffffb892dc2b16d),
    UINT64_C(0xfffffd2fb4188601), UINT64_C(0xfffffe3bc0a56eb3),
    UINT64_C(0xfffffee523b218bf), UINT64_C(0xffffff4fc31097dc),
    UINT64_C(0xffffff929d76dbe4), UINT64_C(0xffffffbc5e7c0349),
    UINT64_C(0xffffffd6586c667d), UINT64_C(0xffffffe6716865f0),
    UINT64_C(0xfffffff0613c76dc), UINT64_C(0xfffffff67d62ab5e),
    UINT64_C(0xfffffffa3b6664ba), UINT64_C(0xfffffffc83e13d61),
    UINT64_C(0xfffffffde713ef6c), UINT64_C(0xfffffffebe18936a),
    UINT64_C(0xffffffff3fbfc991), UINT64_C(0xffffffff8d9fa294),
    UINT64_C(0xffffffffbc37258a), UINT64_C(0xffffffffd7fb7df7),
    UINT64_C(0xffffffffe87747f3), UINT64_C(0xfffffffff2368b84),
    UINT64_C(0xfffffffff7f44d83), UINT64_C(0xfffffffffb52a496),
    UINT64_C(0xfffffffffd4a9ff6), UINT64_C(0xfffffffffe700574),
    UINT64_C(0xffffffffff1a287a), UINT64_C(0xffffffffff7c6f01),
    UINT64_C(0xffffffffffb4fa94), UINT64_C(0xffffffffffd562fb),
    UINT64_C(0xffffffffffe7e35f), UINT64_C(0xfffffffffff268d1),
    UINT64_C(0xfffffffffff85e88), UINT64_C(0xfffffffffffbbb69),
    UINT64_C(0xfffffffffffd9f43), UINT64_C(0xfffffffffffeae26),
    UINT64_C(0xffffffffffff4537), UINT64_C(0xffffffffffff9922),
    UINT64_C(0xffffffffffffc791), UINT64_C(0xffffffffffffe129),
    UINT64_C(0xffffffffffffef36), UINT64_C(0xfffffffffffff6e5),
    UINT64_C(0xfffffffffffffb15), UINT64_C(0xfffffffffffffd5a),
    UINT64_C(0xfffffffffffffe94), UINT64_C(0xffffffffffffff3e),
    UINT64_C(0xffffffffffffff98), UINT64_C(0xffffffffffffffc9),
    UINT64_C(0xffffffffffffffe3), UINT64_C(0xfffffffffffffff0),
    UINT64_C(0xfffffffffffffff8), UINT64_C(0xfffffffffffffffb),
};

static uint64_t cdt83_sample(uint64_t rand_lo, uint32_t rand_hi) {
  uint64_t r = 0;
  for (unsigned i = 0; i < CDTLEN; i++) {
    uint128 cdt = ((uint128)CDT83_HI[i] << 64) | CDT83_LO[i];
    uint128 rnd = ((uint128)rand_hi << 64) | rand_lo;
    r += (uint64_t)((cdt - rnd) >> 127);
  }
  return r;
}

/* ─── theoretical D_{Z+,16} probabilities ──────────────────────────────── */
static double theory_prob(int k) {
  static double Z_half = 0.0;
  if (Z_half == 0.0)
    for (int j = 0; j < 10000; j++)
      Z_half += exp(-(double)j * j / 512.0);
  return exp(-(double)k * k / 512.0) / Z_half;
}

/* ─── Test 1: CDT83 monotonicity ────────────────────────────────────────── */
static int test_cdt_monotonicity(void) {
  printf("=== Test 1: CDT83 Monotonicity ===\n");
  int ok = 1;
  for (int i = 1; i < CDTLEN; i++) {
    if (CDT83_HI[i] < CDT83_HI[i - 1] ||
        (CDT83_HI[i] == CDT83_HI[i - 1] && CDT83_LO[i] < CDT83_LO[i - 1])) {
      printf("  FAIL: CDT83[%d] < CDT83[%d]\n", i, i - 1);
      ok = 0;
    }
  }
  uint128 cdt_last =
      ((uint128)CDT83_HI[CDTLEN - 1] << 64) | CDT83_LO[CDTLEN - 1];
  uint128 two83 = (uint128)1 << 83;
  uint64_t tail_gap = (uint64_t)(two83 - cdt_last);
  printf("  2^83 - CDT83[%d] = %llu (should be ≤ 16)\n", CDTLEN - 1,
         (unsigned long long)tail_gap);
  printf("  Monotonicity: %s\n\n", ok ? "PASS" : "FAIL");
  return ok;
}

/* ─── Tests 2-3: CDT83 chi-squared, E[X], E[X²] ────────────────────────── */
static int test_cdt_stats(void) {
  const long N = 20000000L;
  printf("=== Tests 2-3: CDT83 statistics (N=%ld) ===\n\n", N);

  long cnt[200] = {0};
  long long sum_x = 0, sum_x2 = 0;

  for (long i = 0; i < N; i++) {
    uint64_t rlo = xrand();
    uint32_t rhi = (uint32_t)(xrand() & UINT32_C(0x7FFFF));
    uint64_t x = cdt83_sample(rlo, rhi);
    if (x < 200)
      cnt[x]++;
    sum_x += (long long)x;
    sum_x2 += (long long)(x * x);
  }

  printf("=== Test 2: Per-k chi-squared (k=0..14 + tail) ===\n");
  printf("  %-4s  %-12s  %-12s  %8s\n", "k", "empirical", "theory", "pull(σ)");

  double chi2 = 0.0;
  int dof = 0;
  for (int k = 0; k <= 14; k++) {
    double p_th = theory_prob(k);
    double p_obs = (double)cnt[k] / N;
    double pull = (p_obs - p_th) / sqrt(p_th * (1.0 - p_th) / N);
    chi2 += pull * pull;
    dof++;
    printf("  k=%-2d  %.8f    %.8f    %+7.2f\n", k, p_obs, p_th, pull);
  }
  long tail_cnt = 0;
  for (int k = 15; k < 200; k++)
    tail_cnt += cnt[k];
  double p_tail_th = 0.0;
  for (int k = 15; k < 10000; k++)
    p_tail_th += theory_prob(k);
  double p_tail_obs = (double)tail_cnt / N;
  double pull_tail =
      (p_tail_obs - p_tail_th) / sqrt(p_tail_th * (1.0 - p_tail_th) / N);
  chi2 += pull_tail * pull_tail;
  dof++;
  printf("  k≥15  %.8f    %.8f    %+7.2f\n", p_tail_obs, p_tail_th, pull_tail);

  double chi2_thresh = dof + 4.0 * sqrt(2.0 * dof);
  printf("\n  chi²(%d dof) = %.2f  (PASS if < %.1f)\n", dof, chi2, chi2_thresh);
  int chi2_ok = (chi2 < chi2_thresh);
  printf("  Chi-squared: %s\n\n", chi2_ok ? "PASS" : "FAIL");

  /* Discrete half-Gaussian theory moments */
  double Z_half = 0.0;
  for (int k = 0; k < 10000; k++)
    Z_half += exp(-(double)k * k / 512.0);
  double EX_th = 0.0, EX2_th = 0.0, EX4_th = 0.0;
  for (int k = 0; k < 10000; k++) {
    double pk = exp(-(double)k * k / 512.0) / Z_half;
    EX_th += k * pk;
    EX2_th += (double)k * k * pk;
    EX4_th += (double)k * k * k * k * pk;
  }

  double EX_obs = (double)sum_x / N;
  double EX2_obs = (double)sum_x2 / N;
  double pull_EX = (EX_obs - EX_th) / sqrt((EX2_th - EX_th * EX_th) / N);
  double pull_EX2 = (EX2_obs - EX2_th) / sqrt((EX4_th - EX2_th * EX2_th) / N);

  printf("=== Test 3: Moments (discrete half-Gaussian) ===\n");
  printf("  E[X]:  obs=%.6f  theory=%.6f  pull=%+.2fσ  %s\n", EX_obs, EX_th,
         pull_EX, fabs(pull_EX) < 4.0 ? "PASS" : "FAIL");
  printf("  E[X²]: obs=%.6f  theory=%.6f  pull=%+.2fσ  %s\n\n", EX2_obs, EX2_th,
         pull_EX2, fabs(pull_EX2) < 4.0 ? "PASS" : "FAIL");

  return chi2_ok && fabs(pull_EX) < 4.0 && fabs(pull_EX2) < 4.0;
}

/* ─── discrete half-Gaussian (for acceptance rate test) ─────────────────── */
static double Z_half_g = 0.0;
static double rho_k(int k) { return exp(-(double)k * k / 512.0); }
static double p_cdt(int k) {
  if (Z_half_g == 0.0)
    for (int j = 0; j < 10000; j++)
      Z_half_g += rho_k(j);
  return rho_k(k) / Z_half_g;
}

/* ─── Test 4: acceptance rate ───────────────────────────────────────────── */
static int test_acceptance_rate(void) {
  printf("=== Test 4: Acceptance rate of sample_gauss_sigma76 ===\n");

  const size_t N_TRIALS = 2000000;
  const size_t BUFSIZE = N_TRIALS * GAUSS_RAND_BYTES_TEST;
  uint8_t *buf = malloc(BUFSIZE);
  if (!buf) {
    fprintf(stderr, "OOM\n");
    exit(1);
  }
  fill_urandom(buf, BUFSIZE);

  uint64_t *out = calloc(N_TRIALS, sizeof(uint64_t));
  fp96_76 sqsum = {{0, 0}};

  long accepted = sample_gauss(out, &sqsum, buf, BUFSIZE, N_TRIALS + 1, 0);
  double rate = (double)accepted / N_TRIALS;
  double z_accept_th = 1.0 - 0.5 * p_cdt(0);
  double pull =
      (rate - z_accept_th) / sqrt(z_accept_th * (1.0 - z_accept_th) / N_TRIALS);

  printf("  Trials      = %zu\n", N_TRIALS);
  printf("  Accepted    = %ld\n", accepted);
  printf("  Accept rate = %.4f  (theory = %.4f)\n", rate, z_accept_th);
  printf("  Pull        = %+.2fσ  %s\n\n", pull,
         fabs(pull) < 5.0 ? "PASS" : "FAIL");

  free(buf);
  free(out);
  return fabs(pull) < 5.0;
}

/* ─── Test 5: R_α proof conditions ─────────────────────────────────────── */
#define T5_XMAX                                                                \
  UINT64_C(0xa68000000000) /* floor(333/512 * 2^48): max xi in domain          \
                            */
#define T5_ALPHA 511       /* Rényi order = 2λ-1, λ=256 */
#define T5_LOG2_Q 78.05    /* log₂(Q), Q = Q_sign × M × (nk+2) */
#define T5_OCTAVE_N UINT64_C(2000000) /* dense sampling: 2M pts per octave */
#define T5_SCALE ((double)(UINT64_C(1) << 48))

/* local copy of approx_exp — uses smulh48 from fixpoint.h (ceiling version) */
static uint64_t approx_exp_test(uint64_t xi) {
  int64_t r = -INT64_C(2712374);
  r = smulh48(r, xi) + INT64_C(37757730);
  r = smulh48(r, xi) - INT64_C(387131940);
  r = smulh48(r, xi) + INT64_C(3490247303);
  r = smulh48(r, xi) - INT64_C(27924059918);
  r = smulh48(r, xi) + INT64_C(195468737155);
  r = smulh48(r, xi) - INT64_C(1172812405893);
  r = smulh48(r, xi) + INT64_C(5864062015325);
  r = smulh48(r, xi) - INT64_C(23456248059260);
  r = smulh48(r, xi) + (INT64_C(1) << 46);
  r = smulh48(r, xi) - (INT64_C(1) << 47);
  return (uint64_t)((INT64_C(1) << 48) + 2 * smulh48(r, xi));
}

static int test_Ralpha_proof(void) {
  printf("=== Test 5: R_α proof conditions (approx_exp) ===\n\n");

  double alpha = (double)T5_ALPHA;
  double log2_Q = T5_LOG2_Q;
  double K_req = 0.5 * (1.0 + log2(alpha - 1.0) + log2_Q);
  double one_over_4Q = pow(2.0, -(2.0 + log2_Q));

  printf("  α=%d, log₂(Q)=%.2f, K_req=%.4f, 1/(4Q)=%.4e\n\n", T5_ALPHA, log2_Q,
         K_req, one_over_4Q);

  /* xi=0 boundary */
  if (approx_exp_test(0) != (UINT64_C(1) << 48)) {
    printf("  FAIL: approx_exp_test(0) != 2^48\n");
    return 0;
  }

  /* Phase 1: exhaustive xi ∈ [1, 2^28] */
  double max_c1_p1 = 0.0;
  uint64_t under_p1 = 0;
  printf("  [Phase 1] Exhaustive xi ∈ [1, 2^28]  (%u values) ...\n", UINT32_C(1)
                                                                         << 28);
  fflush(stdout);
  for (uint64_t xi = 1; xi <= (UINT64_C(1) << 28); xi++) {
    double fz = exp(-(double)xi / T5_SCALE);
    double pz = (double)approx_exp_test(xi) / T5_SCALE;
    if (pz < fz - 0.5 / T5_SCALE)
      under_p1++;
    double c1 = (pz - fz) / fz;
    if (c1 > max_c1_p1)
      max_c1_p1 = c1;
  }
  double K1_p1 = (max_c1_p1 > 0) ? -log2(max_c1_p1) : 300.0;
  printf("  Phase 1: K₁=%.4f, under-accepts=%llu\n\n", K1_p1,
         (unsigned long long)under_p1);

  /* Phase 2: dense octave scan xi ∈ [2^28, X_max] */
  double max_c1_p2 = 0.0;
  uint64_t under_p2 = 0;
  printf(
      "  [Phase 2] Dense octave scan xi ∈ [2^28, X_max]  (%llu pts/oct) ...\n",
      (unsigned long long)T5_OCTAVE_N);
  for (int oct = 28; oct <= 47; oct++) {
    uint64_t lo = (UINT64_C(1) << oct);
    uint64_t hi = (oct < 47) ? (UINT64_C(1) << (oct + 1)) - 1 : T5_XMAX;
    if (lo > T5_XMAX)
      break;
    if (hi > T5_XMAX)
      hi = T5_XMAX;
    uint64_t range = hi - lo + 1;
    uint64_t step = range / T5_OCTAVE_N;
    if (step == 0)
      step = 1;
    double max_c1_oct = 0.0;
    uint64_t under_oct = 0;
    for (uint64_t xi = lo; xi <= hi; xi += step) {
      double fz = exp(-(double)xi / T5_SCALE);
      double pz = (double)approx_exp_test(xi) / T5_SCALE;
      if (pz < fz - 0.5 / T5_SCALE)
        under_oct++;
      double c1 = (pz - fz) / fz;
      if (c1 > max_c1_oct)
        max_c1_oct = c1;
    }
    double K1o = (max_c1_oct > 0) ? -log2(max_c1_oct) : 300.0;
    printf("  oct=%2d: K₁=%.4f  under=%llu  %s\n", oct, K1o,
           (unsigned long long)under_oct,
           (K1o >= K_req && under_oct == 0) ? "OK" : "*** FAIL ***");
    if (max_c1_oct > max_c1_p2)
      max_c1_p2 = max_c1_oct;
    under_p2 += under_oct;
  }

  /* Final results */
  double max_c1 = (max_c1_p1 > max_c1_p2) ? max_c1_p1 : max_c1_p2;
  double K1 = (max_c1 > 0) ? -log2(max_c1) : 300.0;
  uint64_t total_under = under_p1 + under_p2;
  double Rminus1 = (alpha - 1.0) / 2.0 * pow(2.0, -2.0 * K1);

  int pass_C1 = (total_under == 0);
  int pass_C2 = (K1 >= K_req);
  int pass_C3 = (Rminus1 <= one_over_4Q);

  printf("\n  [C1] Ceiling  — under-accepts=%llu  →  %s\n",
         (unsigned long long)total_under, pass_C1 ? "PASS" : "FAIL");
  printf("  [C2] K₁=%.4f ≥ K_req=%.4f (margin %.4f bits)  →  %s\n", K1, K_req,
         K1 - K_req, pass_C2 ? "PASS" : "FAIL");
  printf("  [C3] R_α-1=%.4e ≤ 1/(4Q)=%.4e (margin %.4f bits)  →  %s\n\n",
         Rminus1, one_over_4Q, log2(one_over_4Q) - log2(Rminus1),
         pass_C3 ? "PASS" : "FAIL");

  return pass_C1 && pass_C2 && pass_C3;
}

/* ─── main ──────────────────────────────────────────────────────────────── */
int main(void) {
  xseed();
  (void)p_cdt(0); /* warm up Z_half_g */

  int ok = 1;
  ok &= test_cdt_monotonicity();
  ok &= test_cdt_stats();
  ok &= test_acceptance_rate();
  ok &= test_Ralpha_proof();

  printf("=== Overall: %s ===\n", ok ? "ALL PASS" : "SOME FAIL");
  return ok ? 0 : 1;
}
