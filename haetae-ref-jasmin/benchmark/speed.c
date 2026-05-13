// SPDX-License-Identifier: MIT

#include "api.h"
#include "cpucycles.h"
#include "params.h"
#include "speed_print.h"

#include <stdint.h>
#include <stdio.h>

#define NTESTS 1000

static uint64_t t[NTESTS];

int main(void) {
  uint8_t vk[HAETAE_CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[HAETAE_CRYPTO_SECRETKEYBYTES];
  uint8_t sig[HAETAE_CRYPTO_BYTES];
  uint8_t msg[2 * HAETAE_SEEDBYTES];
  size_t siglen = 0;

  for (size_t i = 0; i < sizeof(msg); i++)
    msg[i] = (uint8_t)i;

  for (int i = 0; i < NTESTS; i++) {
    t[i] = cpucycles();
    crypto_sign_keypair(vk, sk);
  }
  print_results("crypto_sign_keypair:", t, NTESTS);

  if (crypto_sign_keypair(vk, sk) != 0) {
    fprintf(stderr, "crypto_sign_keypair failed\n");
    return 1;
  }

  for (int i = 0; i < NTESTS; i++) {
    t[i] = cpucycles();
    crypto_sign(sig, &siglen, msg, sizeof(msg), NULL, 0, sk);
  }
  print_results("crypto_sign:", t, NTESTS);

  for (int i = 0; i < NTESTS; i++) {
    t[i] = cpucycles();
    crypto_sign_verify(sig, siglen, msg, sizeof(msg), NULL, 0, vk);
  }
  print_results("crypto_sign_verify:", t, NTESTS);

  return 0;
}
