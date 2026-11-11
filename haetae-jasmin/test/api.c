// SPDX-License-Identifier: MIT

#include "api.h"

#include <stdio.h>
#include <string.h>

#define GUARD_BYTES 16
#define MESSAGE_BYTES (CRYPTO_BYTES + 173)

#define CHECK(condition)                                                       \
  do {                                                                         \
    if (!(condition)) {                                                        \
      fprintf(stderr, "%s:%d: %s failed\n", __FILE__, __LINE__, #condition);    \
      return 1;                                                                \
    }                                                                          \
  } while (0)

static int all_bytes(const uint8_t *buf, size_t len, uint8_t value) {
  for (size_t i = 0; i < len; ++i)
    if (buf[i] != value)
      return 0;
  return 1;
}

int main(void) {
  uint8_t pk[CRYPTO_PUBLICKEYBYTES + GUARD_BYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES + GUARD_BYTES];
  uint8_t pk2[CRYPTO_PUBLICKEYBYTES], sk2[CRYPTO_SECRETKEYBYTES];
  uint8_t seed[HAETAE_SEEDBYTES], rnd[HAETAE_SEEDBYTES];
  uint8_t sig[CRYPTO_BYTES + GUARD_BYTES], sig2[CRYPTO_BYTES];
  uint8_t msg[MESSAGE_BYTES], ctx[256], pre[301];
  uint8_t sm[CRYPTO_BYTES + MESSAGE_BYTES + GUARD_BYTES];
  uint8_t out[sizeof sm];
  size_t siglen, siglen2, smlen, mlen;

  for (size_t i = 0; i < sizeof seed; ++i) {
    seed[i] = (uint8_t)(3 * i + 7);
    rnd[i] = (uint8_t)(5 * i + 11);
  }
  for (size_t i = 0; i < sizeof msg; ++i)
    msg[i] = (uint8_t)(i * i + 17 * i + 23);
  for (size_t i = 0; i < sizeof ctx; ++i)
    ctx[i] = (uint8_t)(7 * i + 9);
  for (size_t i = 0; i < sizeof pre; ++i)
    pre[i] = (uint8_t)(11 * i + 13);

  memset(pk, 0xa5, sizeof pk);
  memset(sk, 0xa5, sizeof sk);
  CHECK(crypto_sign_keypair_internal(pk, sk, seed) == 0);
  CHECK(crypto_sign_keypair_internal(pk2, sk2, seed) == 0);
  CHECK(memcmp(pk, pk2, sizeof pk2) == 0);
  CHECK(memcmp(sk, sk2, sizeof sk2) == 0);
  CHECK(all_bytes(pk + CRYPTO_PUBLICKEYBYTES, GUARD_BYTES, 0xa5));
  CHECK(all_bytes(sk + CRYPTO_SECRETKEYBYTES, GUARD_BYTES, 0xa5));

  /* Internal prefixes are raw byte strings, without the public context limit. */
  memset(sig, 0xa5, sizeof sig);
  CHECK(crypto_sign_signature_internal(sig, &siglen, msg, sizeof msg, pre,
                                       sizeof pre, rnd, sk) == 0);
  CHECK(siglen == CRYPTO_BYTES);
  CHECK(all_bytes(sig + CRYPTO_BYTES, GUARD_BYTES, 0xa5));
  CHECK(crypto_sign_signature_internal(sig2, &siglen2, msg, sizeof msg, pre,
                                       sizeof pre, rnd, sk) == 0);
  CHECK(siglen2 == siglen && memcmp(sig, sig2, siglen) == 0);
  CHECK(crypto_sign_verify_internal(sig, siglen, msg, sizeof msg, pre,
                                    sizeof pre, pk) == 0);
  pre[0] ^= 1;
  CHECK(crypto_sign_verify_internal(sig, siglen, msg, sizeof msg, pre,
                                    sizeof pre, pk) == -1);
  pre[0] ^= 1;
  rnd[0] ^= 1;
  CHECK(crypto_sign_signature_internal(sig2, &siglen2, msg, sizeof msg, pre,
                                       sizeof pre, rnd, sk) == 0);
  CHECK(memcmp(sig, sig2, CRYPTO_BYTES) != 0);
  CHECK(crypto_sign_verify_internal(sig2, siglen2, msg, sizeof msg, pre,
                                    sizeof pre, pk) == 0);

  pre[0] = 255;
  memcpy(pre + 1, ctx, 255);
  CHECK(crypto_sign_signature_internal(sig, &siglen, msg, sizeof msg, pre, 256,
                                       rnd, sk) == 0);
  CHECK(crypto_sign_verify(sig, siglen, msg, sizeof msg, ctx, 255, pk) == 0);
  CHECK(crypto_sign_signature(sig, &siglen, msg, sizeof msg, ctx, 255, sk) == 0);
  CHECK(crypto_sign_verify_internal(sig, siglen, msg, sizeof msg, pre, 256,
                                    pk) == 0);
  CHECK(crypto_sign_verify(sig, siglen, msg, sizeof msg, ctx, 255, pk) == 0);
  CHECK(crypto_sign_verify(sig, siglen, msg, sizeof msg, ctx, 254, pk) == -1);
  ctx[0] ^= 1;
  CHECK(crypto_sign_verify(sig, siglen, msg, sizeof msg, ctx, 255, pk) == -1);
  ctx[0] ^= 1;
  msg[0] ^= 1;
  CHECK(crypto_sign_verify(sig, siglen, msg, sizeof msg, ctx, 255, pk) == -1);
  msg[0] ^= 1;
  sig[0] ^= 1;
  CHECK(crypto_sign_verify(sig, siglen, msg, sizeof msg, ctx, 255, pk) == -1);
  sig[0] ^= 1;
  CHECK(crypto_sign_verify(NULL, 0, NULL, 0, NULL, 0, NULL) == -1);
  CHECK(crypto_sign_verify(sig, CRYPTO_BYTES - 1, msg, sizeof msg, ctx, 255,
                           pk) == -1);
  CHECK(crypto_sign_verify(sig, CRYPTO_BYTES + 1, msg, sizeof msg, ctx, 255,
                           pk) == -1);
  CHECK(crypto_sign_verify(NULL, CRYPTO_BYTES, NULL, 0, NULL, 256, NULL) == -1);

  memset(sig, 0xa5, sizeof sig);
  siglen = 19;
  CHECK(crypto_sign_signature(sig, &siglen, NULL, 0, NULL, 256, NULL) == -1);
  CHECK(siglen == 19 && all_bytes(sig, sizeof sig, 0xa5));

  /* The message is deliberately longer than the signature: forward copying
   * would silently corrupt this in-place signing case. */
  memset(sm, 0xa5, sizeof sm);
  memcpy(sm, msg, sizeof msg);
  CHECK(crypto_sign(sm, &smlen, sm, sizeof msg, ctx, 255, sk) == 0);
  CHECK(smlen == CRYPTO_BYTES + sizeof msg);
  CHECK(memcmp(sm + CRYPTO_BYTES, msg, sizeof msg) == 0);
  CHECK(all_bytes(sm + smlen, GUARD_BYTES, 0xa5));
  CHECK(crypto_sign_verify(sm, CRYPTO_BYTES, msg, sizeof msg, ctx, 255, pk) == 0);

  memset(out, 0xa5, sizeof out);
  CHECK(crypto_sign_open(out, &mlen, sm, smlen, ctx, 255, pk) == 0);
  CHECK(mlen == sizeof msg && memcmp(out, msg, sizeof msg) == 0);
  CHECK(all_bytes(out + mlen, sizeof out - mlen, 0xa5));
  memcpy(out, sm, smlen);
  CHECK(crypto_sign_open(out, &mlen, out, smlen, ctx, 255, pk) == 0);
  CHECK(mlen == sizeof msg && memcmp(out, msg, sizeof msg) == 0);

  sm[0] ^= 1;
  memset(out, 0xa5, sizeof out);
  CHECK(crypto_sign_open(out, &mlen, sm, smlen, ctx, 255, pk) == -1);
  CHECK(mlen == SIZE_MAX && all_bytes(out, smlen, 0));
  CHECK(all_bytes(out + smlen, GUARD_BYTES, 0xa5));
  sm[0] ^= 1;
  memset(out, 0xa5, sizeof out);
  CHECK(crypto_sign_open(out, &mlen, sm, smlen, NULL, 256, pk) == -1);
  CHECK(mlen == SIZE_MAX && all_bytes(out, smlen, 0));
  CHECK(all_bytes(out + smlen, GUARD_BYTES, 0xa5));
  memset(out, 0xa5, sizeof out);
  CHECK(crypto_sign_open(out, &mlen, NULL, CRYPTO_BYTES - 1, NULL, 0, NULL) == -1);
  CHECK(mlen == SIZE_MAX && all_bytes(out, CRYPTO_BYTES - 1, 0));
  CHECK(all_bytes(out + CRYPTO_BYTES - 1, sizeof out - CRYPTO_BYTES + 1, 0xa5));
  CHECK(crypto_sign_open(NULL, &mlen, NULL, 0, NULL, 0, NULL) == -1);
  CHECK(mlen == SIZE_MAX);

  /* Match the upstream attached API's observable invalid-context behavior. */
  memset(sm, 0xa5, sizeof sm);
  smlen = 19;
  CHECK(crypto_sign(sm, &smlen, msg, sizeof msg, NULL, 256, NULL) == -1);
  CHECK(smlen == 19 + sizeof msg);
  CHECK(all_bytes(sm, CRYPTO_BYTES, 0xa5));
  CHECK(memcmp(sm + CRYPTO_BYTES, msg, sizeof msg) == 0);
  CHECK(all_bytes(sm + CRYPTO_BYTES + sizeof msg, GUARD_BYTES, 0xa5));

  CHECK(crypto_sign_keypair(pk, sk) == 0);
  CHECK(crypto_sign_signature(sig, &siglen, NULL, 0, NULL, 0, sk) == 0);
  CHECK(crypto_sign_verify(sig, siglen, NULL, 0, NULL, 0, pk) == 0);
  CHECK(crypto_sign(sm, &smlen, NULL, 0, NULL, 0, sk) == 0);
  CHECK(smlen == CRYPTO_BYTES);
  memset(out, 0xa5, sizeof out);
  CHECK(crypto_sign_open(out, &mlen, sm, smlen, NULL, 0, pk) == 0);
  CHECK(mlen == 0 && all_bytes(out, sizeof out, 0xa5));

  printf("%s API: deterministic, context, overlap, and rejection checks passed\n",
         CRYPTO_ALGNAME);
  return 0;
}
