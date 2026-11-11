// SPDX-License-Identifier: MIT

#ifndef HAETAE_API_H
#define HAETAE_API_H

#include "params.h"

#include <stddef.h>
#include <stdint.h>

#define CRYPTO_ALGNAME HAETAE_CRYPTO_ALGNAME
#define CRYPTO_SECRETKEYBYTES HAETAE_CRYPTO_SECRETKEYBYTES
#define CRYPTO_PUBLICKEYBYTES HAETAE_CRYPTO_PUBLICKEYBYTES
#define CRYPTO_BYTES HAETAE_CRYPTO_BYTES

#define crypto_sign_keypair HAETAE_NAMESPACE(keypair)
int crypto_sign_keypair(uint8_t *vk, uint8_t *sk);

#define crypto_sign_keypair_internal HAETAE_NAMESPACE(keypair_internal)
int crypto_sign_keypair_internal(uint8_t *vk, uint8_t *sk,
                                 uint8_t seed[HAETAE_SEEDBYTES]);

/* Jasmin's x86-64 exports accept at most six arguments. These wrappers only
 * marshal the longer reference API calls; all processing stays in Jasmin. */
static inline int HAETAE_NAMESPACE(signature_internal)(
    uint8_t *sig, size_t *siglen, const uint8_t *m, size_t mlen,
    const uint8_t *pre, size_t prelen,
    const uint8_t rnd[HAETAE_SEEDBYTES], const uint8_t *sk) {
  extern int HAETAE_NAMESPACE(signature_internal_desc)(
      uint8_t *sig, size_t *siglen, const uint8_t *rnd,
      const uint8_t *sk, const uint64_t desc[4]);
  const uint64_t desc[4] = {
      (uint64_t)(uintptr_t)pre, (uint64_t)prelen,
      (uint64_t)(uintptr_t)m, (uint64_t)mlen,
  };
  return HAETAE_NAMESPACE(signature_internal_desc)(sig, siglen, rnd, sk, desc);
}
#define crypto_sign_signature_internal HAETAE_NAMESPACE(signature_internal)

static inline int HAETAE_NAMESPACE(signature)(uint8_t *sig, size_t *siglen,
                                              const uint8_t *m, size_t mlen,
                                              const uint8_t *ctx, size_t ctxlen,
                                              const uint8_t *sk) {
  extern int HAETAE_NAMESPACE(signature_desc)(uint8_t *sig, size_t *siglen,
                                             const uint8_t *sk,
                                             const uint64_t desc[4]);
  const uint64_t desc[4] = {
      (uint64_t)(uintptr_t)m,
      (uint64_t)mlen,
      (uint64_t)(uintptr_t)ctx,
      (uint64_t)ctxlen,
  };
  return HAETAE_NAMESPACE(signature_desc)(sig, siglen, sk, desc);
}
#define crypto_sign_signature HAETAE_NAMESPACE(signature)

static inline int HAETAE_NAMESPACE(sign)(uint8_t *sm, size_t *smlen,
                                         const uint8_t *m, size_t mlen,
                                         const uint8_t *ctx, size_t ctxlen,
                                         const uint8_t *sk) {
  extern int HAETAE_NAMESPACE(sign_desc)(uint8_t *sm, size_t *smlen,
                                        const uint8_t *sk,
                                        const uint64_t desc[4]);
  const uint64_t desc[4] = {
      (uint64_t)(uintptr_t)m, (uint64_t)mlen,
      (uint64_t)(uintptr_t)ctx, (uint64_t)ctxlen,
  };
  return HAETAE_NAMESPACE(sign_desc)(sm, smlen, sk, desc);
}
#define crypto_sign HAETAE_NAMESPACE(sign)

static inline int HAETAE_NAMESPACE(verify_internal)(
    const uint8_t *sig, size_t siglen, const uint8_t *m, size_t mlen,
    const uint8_t *pre, size_t prelen, const uint8_t *vk) {
  extern int HAETAE_NAMESPACE(verify_internal_desc)(
      const uint8_t *sig, const uint8_t *vk, const uint64_t desc[5]);
  const uint64_t desc[5] = {
      (uint64_t)siglen, (uint64_t)(uintptr_t)m, (uint64_t)mlen,
      (uint64_t)(uintptr_t)pre, (uint64_t)prelen,
  };
  return HAETAE_NAMESPACE(verify_internal_desc)(sig, vk, desc);
}
#define crypto_sign_verify_internal HAETAE_NAMESPACE(verify_internal)

static inline int HAETAE_NAMESPACE(verify)(const uint8_t *sig, size_t siglen,
                                           const uint8_t *m, size_t mlen,
                                           const uint8_t *ctx, size_t ctxlen,
                                           const uint8_t *vk) {
  extern int HAETAE_NAMESPACE(verify_desc)(const uint8_t *sig,
                                          const uint8_t *vk,
                                          const uint64_t desc[5]);
  const uint64_t desc[5] = {
      (uint64_t)siglen,       (uint64_t)(uintptr_t)m,
      (uint64_t)mlen,         (uint64_t)(uintptr_t)ctx,
      (uint64_t)ctxlen,
  };
  return HAETAE_NAMESPACE(verify_desc)(sig, vk, desc);
}
#define crypto_sign_verify HAETAE_NAMESPACE(verify)

static inline int HAETAE_NAMESPACE(open)(uint8_t *m, size_t *mlen,
                                         const uint8_t *sm, size_t smlen,
                                         const uint8_t *ctx, size_t ctxlen,
                                         const uint8_t *vk) {
  extern int HAETAE_NAMESPACE(open_desc)(uint8_t *m, size_t *mlen,
                                        const uint8_t *sm, const uint8_t *vk,
                                        const uint64_t desc[3]);
  const uint64_t desc[3] = {
      (uint64_t)smlen, (uint64_t)(uintptr_t)ctx, (uint64_t)ctxlen,
  };
  return HAETAE_NAMESPACE(open_desc)(m, mlen, sm, vk, desc);
}
#define crypto_sign_open HAETAE_NAMESPACE(open)

#endif // HAETAE_API_H
