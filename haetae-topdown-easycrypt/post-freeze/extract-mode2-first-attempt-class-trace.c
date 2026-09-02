// SPDX-License-Identifier: MIT

/* Non-production harness for one deterministic mode-2 first attempt.
 * The 64-bit fixture index is encoded little-endian in the first eight bytes
 * of the 32-byte raw seed.  The harness exposes the exact context needed by
 * the class-sensitive accumulator feasibility checker; it does not loop to a
 * later accepted attempt. */

#include "params.h"
#include "poly.h"
#include "polymat.h"
#include "polyvec.h"
#include "symmetric.h"

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
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

static int parse_seed_index(const char *text, uint64_t *result) {
  char *end = NULL;
  if (text[0] == '-')
    return 0;
  errno = 0;
  unsigned long long value = strtoull(text, &end, 0);
  if (errno != 0 || end == text || *end != '\0')
    return 0;
  *result = (uint64_t)value;
  return 1;
}

static void set_seed_index(uint8_t seed[HAETAE_SEEDBYTES], uint64_t index) {
  memset(seed, 0, HAETAE_SEEDBYTES);
  for (size_t i = 0; i < sizeof(index); ++i)
    seed[i] = (uint8_t)(index >> (8 * i));
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

int main(int argc, char **argv) {
  uint64_t seed_index = 0;
  if (argc != 2 || !parse_seed_index(argv[1], &seed_index)) {
    fprintf(stderr, "usage: %s SEED_INDEX\n", argv[0]);
    return 2;
  }

  uint8_t seed[HAETAE_SEEDBYTES];
  uint8_t seedbuf[2 * HAETAE_SEEDBYTES + HAETAE_CRHBYTES] = {0};
  polyvecm matrix[HAETAE_K], s1, s1hat;
  polyveck avec, sampled_s2, work_b, pre_bp, b0, final_s2;
  xof256_state state;

  set_seed_index(seed, seed_index);
  memcpy(seedbuf, seed, sizeof(seed));
  xof256_absorb_once(&state, seedbuf, sizeof(seed));
  xof256_squeeze(seedbuf, sizeof(seedbuf), &state);

  const uint8_t *rhoprime = seedbuf;
  const uint8_t *sigma = rhoprime + HAETAE_SEEDBYTES;

  polymatkm_expand_matA(matrix, rhoprime);
  polyveck_expand_vecA(&avec, rhoprime);
  polyvecmk_expand_S(&s1, &sampled_s2, sigma, 0);

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

  int64_t score = polyvecmk_sk_singular_value(&s1, &final_s2);
  int64_t bound = (int64_t)(HAETAE_GAMMA * HAETAE_GAMMA * HAETAE_N);
  int accepted = score <= bound;

  if (!validate_context(&pre_bp, &avec)) {
    fprintf(stderr, "first-attempt context violates the scalar domain\n");
    return 3;
  }

  printf("{\"schema\":\"haetae-mode2-first-attempt-class-trace-v1\",");
  printf("\"seed_index\":%" PRIu64 ",", seed_index);
  printf("\"seed_hex\":\"");
  print_hex(seed, sizeof(seed));
  printf("\",\"rhoprime_hex\":\"");
  print_hex(rhoprime, HAETAE_SEEDBYTES);
  printf("\",\"sigma_hex\":\"");
  print_hex(sigma, HAETAE_CRHBYTES);
  printf("\",\"accepted\":%s,", accepted ? "true" : "false");
  printf("\"counter_start\":0,\"counter_end\":5,");
  printf("\"squared_singular_value\":%" PRId64 ",", score);
  printf("\"acceptance_bound_floor\":%" PRId64 ",", bound);
  printf("\"pre_bp\":");
  print_polyveck(&pre_bp);
  printf(",\"avec\":");
  print_polyveck(&avec);
  printf(",\"class_trace\":");
  print_class_trace(&pre_bp, &avec);
  puts("}");

  return 0;
}
