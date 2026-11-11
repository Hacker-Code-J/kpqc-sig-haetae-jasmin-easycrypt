// SPDX-License-Identifier: MIT

#include "rng.h"

#include <stdint.h>
#include <stdlib.h>

/* Jasmin's entropy syscall is backed by the KAT driver's deterministic DRBG. */
uint8_t *__jasmin_syscall_randombytes__(uint8_t *out, uint64_t outlen) {
  if (randombytes(out, (unsigned long long)outlen) != 0)
    abort();
  return out;
}
