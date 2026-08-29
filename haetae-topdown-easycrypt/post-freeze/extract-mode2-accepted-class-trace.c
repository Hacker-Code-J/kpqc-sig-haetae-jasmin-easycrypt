// SPDX-License-Identifier: MIT

/* Deterministic, non-production harness for the accepted mode-2 keygen
 * context.  It mirrors crypto_sign_keypair_internal up to acceptance and
 * snapshots A*s1 immediately after invNTT, before s2 and a are added. */

#include "params.h"
#include "poly.h"
#include "polymat.h"
#include "polyvec.h"
#include "symmetric.h"

#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#if HAETAE_MODE != HAETAE_MODE2
#error "This extractor must be compiled for HAETAE mode 2"
#endif

static int class_index(int32_t pre_bp, int32_t avec) {
  int64_t rho = ((int64_t)pre_bp + (int64_t)avec) % HAETAE_Q;
  if (rho < 0)
    rho += HAETAE_Q;
  if (rho == 0)
    return 0;
  if (rho == HAETAE_Q - 1)
    return 1;
  return 2 + (int)(rho % 4);
}

static void print_hex(const uint8_t *bytes, size_t length) {
  for (size_t i = 0; i < length; ++i)
    printf("%02x", bytes[i]);
}

static void print_polyveck(const polyveck *value) {
  putchar('[');
  for (size_t row = 0; row < HAETAE_K; ++row) {
    if (row != 0)
      putchar(',');
    putchar('[');
    for (size_t column = 0; column < HAETAE_N; ++column) {
      if (column != 0)
        putchar(',');
      printf("%" PRId32, value->vec[row].coeffs[column]);
    }
    putchar(']');
  }
  putchar(']');
}

static void print_class_trace(const polyveck *pre_bp, const polyveck *avec) {
  putchar('[');
  for (size_t row = 0; row < HAETAE_K; ++row) {
    if (row != 0)
      putchar(',');
    putchar('[');
    for (size_t column = 0; column < HAETAE_N; ++column) {
      if (column != 0)
        putchar(',');
      printf("%d", class_index(pre_bp->vec[row].coeffs[column],
                               avec->vec[row].coeffs[column]));
    }
    putchar(']');
  }
  putchar(']');
}

static int validate_context(const polyveck *pre_bp, const polyveck *avec) {
  for (size_t row = 0; row < HAETAE_K; ++row) {
    for (size_t column = 0; column < HAETAE_N; ++column) {
      int32_t b = pre_bp->vec[row].coeffs[column];
      int32_t a = avec->vec[row].coeffs[column];
      if (b < INT16_MIN || INT16_MAX < b)
        return 0;
      if (a < 0 || HAETAE_Q <= a)
        return 0;
      int cls = class_index(b, a);
      if (cls < 0 || 5 < cls)
        return 0;
    }
  }
  return 1;
}

int main(void) {
  uint8_t seed[HAETAE_SEEDBYTES] = {0};
  uint8_t seedbuf[2 * HAETAE_SEEDBYTES + HAETAE_CRHBYTES] = {0};
  uint16_t counter = 0;
  polyvecm matrix[HAETAE_K], s1, s1hat;
  polyveck avec, sampled_s2, work_b, pre_bp, b0, final_s2;
  xof256_state state;
  unsigned int attempt = 0;
  uint16_t accepted_counter_start = 0;
  int64_t squared_singular_value = 0;
  int64_t attempt_scores[10000] = {0};

  memcpy(seedbuf, seed, sizeof(seed));
  xof256_absorb_once(&state, seedbuf, sizeof(seed));
  xof256_squeeze(seedbuf, sizeof(seedbuf), &state);

  const uint8_t *rhoprime = seedbuf;
  const uint8_t *sigma = rhoprime + HAETAE_SEEDBYTES;

  polymatkm_expand_matA(matrix, rhoprime);
  polyveck_expand_vecA(&avec, rhoprime);

  for (;;) {
    if (attempt >= 10000) {
      fprintf(stderr, "accepted-attempt search exceeded 10000 iterations\n");
      return 2;
    }

    accepted_counter_start = counter;
    polyvecmk_expand_S(&s1, &sampled_s2, sigma, counter);
    counter += HAETAE_M + HAETAE_K;

    s1hat = s1;
    polyvecm_ntt(&s1hat);
    polymatkm_pointwise_montgomery(&work_b, matrix, &s1hat);
    polyveck_invntt_tomont(&work_b);
    pre_bp = work_b;

    polyveck_add(&work_b, &work_b, &sampled_s2);
    polyveck_add(&work_b, &work_b, &avec);
    polyveck_freeze(&work_b);
    polyveck_decompose_vk(&b0, &work_b);
    polyveck_sub(&final_s2, &sampled_s2, &b0);

    squared_singular_value = polyvecmk_sk_singular_value(&s1, &final_s2);
    attempt_scores[attempt] = squared_singular_value;
    if (squared_singular_value <=
        HAETAE_GAMMA * HAETAE_GAMMA * HAETAE_N)
      break;
    ++attempt;
  }

  if (!validate_context(&pre_bp, &avec)) {
    fprintf(stderr, "accepted context violates the EasyCrypt scalar domain\n");
    return 3;
  }

  printf("{\"schema\":\"haetae-mode2-accepted-class-trace-v1\",");
  printf("\"seed_hex\":\"");
  print_hex(seed, sizeof(seed));
  printf("\",\"rhoprime_hex\":\"");
  print_hex(rhoprime, HAETAE_SEEDBYTES);
  printf("\",\"sigma_hex\":\"");
  print_hex(sigma, HAETAE_CRHBYTES);
  printf("\",\"accepted_attempt\":%u,", attempt);
  printf("\"attempt_scores\":[");
  for (unsigned int i = 0; i <= attempt; ++i) {
    if (i != 0)
      putchar(',');
    printf("%" PRId64, attempt_scores[i]);
  }
  printf("],");
  printf("\"counter_start\":%u,", accepted_counter_start);
  printf("\"counter_end\":%u,", counter);
  printf("\"squared_singular_value\":%" PRId64 ",",
         squared_singular_value);
  printf("\"acceptance_bound_floor\":%" PRId64 ",",
         (int64_t)(HAETAE_GAMMA * HAETAE_GAMMA * HAETAE_N));
  printf("\"pre_bp\":");
  print_polyveck(&pre_bp);
  printf(",\"avec\":");
  print_polyveck(&avec);
  printf(",\"class_trace\":");
  print_class_trace(&pre_bp, &avec);
  puts("}");

  return 0;
}
