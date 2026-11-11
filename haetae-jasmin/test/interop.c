// SPDX-License-Identifier: MIT

#include "api.h"

#include <stdio.h>
#include <string.h>

/* These are the pinned upstream API declarations, with a separate namespace.
 * The test links the original reference .c files, never reference wrappers. */
#define REFERENCE_PREFIX \
  HAETAE_CONCAT(reference_haetae_, HAETAE_CONFIG_MODE_STRING)
#define REFERENCE(name) \
  HAETAE_CONCAT(REFERENCE_PREFIX, HAETAE_CONCAT(_, name))

int REFERENCE(keypair)(uint8_t *vk, uint8_t *sk);
int REFERENCE(keypair_internal)(uint8_t *vk, uint8_t *sk,
                                uint8_t seed[HAETAE_SEEDBYTES]);
int REFERENCE(signature_internal)(uint8_t *sig, size_t *siglen,
                                  const uint8_t *m, size_t mlen,
                                  const uint8_t *pre, size_t prelen,
                                  const uint8_t rnd[HAETAE_SEEDBYTES],
                                  const uint8_t *sk);
int REFERENCE(signature)(uint8_t *sig, size_t *siglen, const uint8_t *m,
                         size_t mlen, const uint8_t *ctx, size_t ctxlen,
                         const uint8_t *sk);
int REFERENCE(sign)(uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen,
                    const uint8_t *ctx, size_t ctxlen, const uint8_t *sk);
int REFERENCE(verify_internal)(const uint8_t *sig, size_t siglen,
                               const uint8_t *m, size_t mlen,
                               const uint8_t *pre, size_t prelen,
                               const uint8_t *vk);
int REFERENCE(verify)(const uint8_t *sig, size_t siglen, const uint8_t *m,
                      size_t mlen, const uint8_t *ctx, size_t ctxlen,
                      const uint8_t *vk);
int REFERENCE(open)(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen,
                    const uint8_t *ctx, size_t ctxlen, const uint8_t *vk);

#define MESSAGE_BYTES 4097
#define CHECK(condition)                                                       \
  do {                                                                         \
    if (!(condition)) {                                                        \
      fprintf(stderr, "%s %s:%d: %s failed\n", CRYPTO_ALGNAME, __FILE__,       \
              __LINE__, #condition);                                         \
      return 1;                                                                \
    }                                                                          \
  } while (0)

struct keypair {
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
};

static void fill_bytes(uint8_t *out, size_t len, unsigned int salt) {
  for (size_t i = 0; i < len; ++i)
    out[i] = (uint8_t)(i * i + 17 * i + salt);
}

static int keypairs_match_reference(struct keypair *key) {
  struct keypair reference;
  uint8_t seed[HAETAE_SEEDBYTES], reference_seed[HAETAE_SEEDBYTES];

  for (unsigned int i = 0; i < 3; ++i) {
    fill_bytes(seed, sizeof seed, 23 + 41 * i);
    memcpy(reference_seed, seed, sizeof seed);
    CHECK(crypto_sign_keypair_internal(key->pk, key->sk, seed) == 0);
    CHECK(REFERENCE(keypair_internal)(reference.pk, reference.sk,
                                      reference_seed) == 0);
    CHECK(memcmp(key->pk, reference.pk, sizeof key->pk) == 0);
    CHECK(memcmp(key->sk, reference.sk, sizeof key->sk) == 0);
  }
  return 0;
}

static int signatures_match_reference(const struct keypair *key,
                                     const uint8_t *msg, size_t mlen,
                                     const uint8_t *pre, size_t prelen,
                                     const uint8_t *rnd, uint8_t *sig) {
  uint8_t reference_sig[CRYPTO_BYTES];
  size_t siglen = 0, reference_siglen = 0;

  CHECK(crypto_sign_signature_internal(sig, &siglen, msg, mlen, pre, prelen,
                                       rnd, key->sk) == 0);
  CHECK(REFERENCE(signature_internal)(reference_sig, &reference_siglen,
                                      msg, mlen, pre, prelen, rnd,
                                      key->sk) == 0);
  CHECK(siglen == CRYPTO_BYTES && reference_siglen == CRYPTO_BYTES);
  CHECK(memcmp(sig, reference_sig, siglen) == 0);
  CHECK(REFERENCE(verify_internal)(sig, siglen, msg, mlen, pre, prelen,
                                   key->pk) == 0);
  CHECK(crypto_sign_verify_internal(reference_sig, reference_siglen, msg,
                                    mlen, pre, prelen, key->pk) == 0);
  return 0;
}

static int fixed_randomness_matches_reference(const struct keypair *key,
                                             const uint8_t *msg,
                                             const uint8_t *ctx) {
  static const struct {
    size_t mlen, ctxlen;
  } cases[] = {
      {0, 0}, {1, 1}, {135, 134}, {136, 135}, {137, 136},
      {MESSAGE_BYTES, 255},
  };
  uint8_t sig[CRYPTO_BYTES], pre[301], rnd[HAETAE_SEEDBYTES];

  fill_bytes(rnd, sizeof rnd, 71);
  for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
    size_t mlen = cases[i].mlen, ctxlen = cases[i].ctxlen;
    pre[0] = (uint8_t)ctxlen;
    memcpy(pre + 1, ctx, ctxlen);
    if (signatures_match_reference(key, msg, mlen, pre, ctxlen + 1, rnd, sig)) {
      fprintf(stderr, "fixed-randomness case: mlen=%zu, ctxlen=%zu\n",
              mlen, ctxlen);
      return 1;
    }
    CHECK(REFERENCE(verify)(sig, CRYPTO_BYTES, msg, mlen, ctx, ctxlen,
                            key->pk) == 0);
    CHECK(crypto_sign_verify(sig, CRYPTO_BYTES, msg, mlen, ctx, ctxlen,
                             key->pk) == 0);
  }

  /* Internal prefixes are raw strings and may exceed the public context cap. */
  fill_bytes(pre, sizeof pre, 149);
  CHECK(signatures_match_reference(key, msg, MESSAGE_BYTES, pre, sizeof pre,
                                   rnd, sig) == 0);
  pre[sizeof pre - 1] ^= 1;
  CHECK(REFERENCE(verify_internal)(sig, CRYPTO_BYTES, msg, MESSAGE_BYTES,
                                   pre, sizeof pre, key->pk) == -1);
  CHECK(crypto_sign_verify_internal(sig, CRYPTO_BYTES, msg, MESSAGE_BYTES,
                                    pre, sizeof pre, key->pk) == -1);
  return 0;
}

static int randomized_signatures_interoperate(const uint8_t *msg,
                                              const uint8_t *ctx) {
  struct keypair key;
  uint8_t sig[CRYPTO_BYTES];
  size_t siglen = 0;

  CHECK(REFERENCE(keypair)(key.pk, key.sk) == 0);
  CHECK(crypto_sign_signature(sig, &siglen, msg, MESSAGE_BYTES, ctx, 255,
                              key.sk) == 0);
  CHECK(siglen == CRYPTO_BYTES);
  CHECK(REFERENCE(verify)(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                          key.pk) == 0);

  CHECK(crypto_sign_keypair(key.pk, key.sk) == 0);
  CHECK(REFERENCE(signature)(sig, &siglen, msg, MESSAGE_BYTES, ctx, 255,
                             key.sk) == 0);
  CHECK(siglen == CRYPTO_BYTES);
  CHECK(crypto_sign_verify(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                           key.pk) == 0);
  return 0;
}

static int attached_signatures_interoperate(const struct keypair *key,
                                            const uint8_t *msg,
                                            const uint8_t *ctx) {
  uint8_t sm[CRYPTO_BYTES + MESSAGE_BYTES], out[sizeof sm];
  size_t smlen = 0, outlen = 0;

  for (unsigned int i = 0; i < 2; ++i) {
    size_t mlen = i ? MESSAGE_BYTES : 0, ctxlen = i ? 255 : 0;
    CHECK(crypto_sign(sm, &smlen, msg, mlen, ctx, ctxlen, key->sk) == 0);
    CHECK(smlen == CRYPTO_BYTES + mlen);
    CHECK(REFERENCE(open)(out, &outlen, sm, smlen, ctx, ctxlen,
                           key->pk) == 0);
    CHECK(outlen == mlen && memcmp(out, msg, mlen) == 0);

    CHECK(REFERENCE(sign)(sm, &smlen, msg, mlen, ctx, ctxlen, key->sk) == 0);
    CHECK(smlen == CRYPTO_BYTES + mlen);
    CHECK(crypto_sign_open(out, &outlen, sm, smlen, ctx, ctxlen,
                           key->pk) == 0);
    CHECK(outlen == mlen && memcmp(out, msg, mlen) == 0);
  }

  sm[0] ^= 1;
  CHECK(crypto_sign_open(out, &outlen, sm, smlen, ctx, 255, key->pk) == -1);
  CHECK(outlen == SIZE_MAX);
  CHECK(REFERENCE(open)(out, &outlen, sm, smlen, ctx, 255, key->pk) == -1);
  CHECK(outlen == SIZE_MAX);
  return 0;
}

static int malformed_signatures_are_rejected(const struct keypair *key,
                                             uint8_t *msg, uint8_t *ctx) {
  uint8_t sig[CRYPTO_BYTES + 1];
  size_t siglen = 0;

  CHECK(REFERENCE(signature)(sig, &siglen, msg, MESSAGE_BYTES, ctx, 255,
                             key->sk) == 0);
  CHECK(siglen == CRYPTO_BYTES);
  CHECK(crypto_sign_verify(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                           key->pk) == 0);

  sig[CRYPTO_BYTES] = 0;
  const size_t bad_lengths[] = {0, CRYPTO_BYTES - 1, CRYPTO_BYTES + 1};
  for (size_t i = 0; i < sizeof bad_lengths / sizeof bad_lengths[0]; ++i) {
    CHECK(crypto_sign_verify(sig, bad_lengths[i], msg, MESSAGE_BYTES, ctx,
                             255, key->pk) == -1);
    CHECK(REFERENCE(verify)(sig, bad_lengths[i], msg, MESSAGE_BYTES, ctx,
                            255, key->pk) == -1);
  }
  CHECK(crypto_sign_verify(sig, siglen, msg, MESSAGE_BYTES, ctx, 256,
                           key->pk) == -1);
  CHECK(REFERENCE(verify)(sig, siglen, msg, MESSAGE_BYTES, ctx, 256,
                          key->pk) == -1);

  ctx[0] ^= 1;
  CHECK(crypto_sign_verify(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                           key->pk) == -1);
  CHECK(REFERENCE(verify)(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                          key->pk) == -1);
  ctx[0] ^= 1;

  msg[MESSAGE_BYTES - 1] ^= 1;
  CHECK(crypto_sign_verify(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                           key->pk) == -1);
  CHECK(REFERENCE(verify)(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                          key->pk) == -1);
  msg[MESSAGE_BYTES - 1] ^= 1;

  sig[0] ^= 1;
  CHECK(crypto_sign_verify(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                           key->pk) == -1);
  CHECK(REFERENCE(verify)(sig, siglen, msg, MESSAGE_BYTES, ctx, 255,
                          key->pk) == -1);
  return 0;
}

int main(void) {
  struct keypair key;
  uint8_t msg[MESSAGE_BYTES], ctx[256];

  fill_bytes(msg, sizeof msg, 97);
  fill_bytes(ctx, sizeof ctx, 181);
  CHECK(keypairs_match_reference(&key) == 0);
  CHECK(fixed_randomness_matches_reference(&key, msg, ctx) == 0);
  CHECK(randomized_signatures_interoperate(msg, ctx) == 0);
  CHECK(attached_signatures_interoperate(&key, msg, ctx) == 0);
  CHECK(malformed_signatures_are_rejected(&key, msg, ctx) == 0);
  printf("%s C/Jasmin interoperability: keys, fixed-randomness signatures, "
         "cross-verification, attached messages, and rejection checks passed\n",
         CRYPTO_ALGNAME);
  return 0;
}
