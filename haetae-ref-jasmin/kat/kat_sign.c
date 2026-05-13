// SPDX-License-Identifier: MIT

#include "api.h"
#include "kat_api.h"

int HAETAE_NAMESPACE(keypair_internal)(uint8_t *vk, uint8_t *sk,
                                       uint8_t seed[HAETAE_SEEDBYTES]);
int HAETAE_NAMESPACE(signature_internal_desc)(
    uint8_t *sig, size_t *siglen, const uint8_t rnd[HAETAE_SEEDBYTES],
    const uint8_t *sk, const uint64_t desc[4]);
int HAETAE_NAMESPACE(verify_internal_desc)(const uint8_t *sig,
                                           const uint8_t *vk,
                                           const uint64_t desc[5]);

int kat_crypto_sign_keypair(uint8_t *pk, uint8_t *sk, uint8_t *seed) {
  return HAETAE_NAMESPACE(keypair_internal)(pk, sk, seed);
}

int kat_crypto_sign(uint8_t *sig, size_t *siglen, const uint8_t *m,
                    size_t mlen, const uint8_t *pre, size_t prelen,
                    const uint8_t *rnd, const uint8_t *sk) {
  const uint64_t desc[4] = {
      (uint64_t)(uintptr_t)pre,
      (uint64_t)prelen,
      (uint64_t)(uintptr_t)m,
      (uint64_t)mlen,
  };
  return HAETAE_NAMESPACE(signature_internal_desc)(sig, siglen, rnd, sk, desc);
}

int kat_crypto_sign_verify(const uint8_t *sig, size_t siglen, const uint8_t *m,
                           size_t mlen, const uint8_t *pre, size_t prelen,
                           const uint8_t *pk) {
  const uint64_t desc[5] = {
      (uint64_t)siglen,       (uint64_t)(uintptr_t)m,
      (uint64_t)mlen,         (uint64_t)(uintptr_t)pre,
      (uint64_t)prelen,
  };
  return HAETAE_NAMESPACE(verify_internal_desc)(sig, pk, desc);
}
