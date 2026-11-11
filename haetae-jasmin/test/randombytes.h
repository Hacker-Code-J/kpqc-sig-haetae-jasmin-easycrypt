// SPDX-License-Identifier: MIT

#ifndef HAETAE_TEST_RANDOMBYTES_H
#define HAETAE_TEST_RANDOMBYTES_H

#include <stddef.h>
#include <stdint.h>

int randombytes(uint8_t *out, size_t outlen);
uint8_t *__jasmin_syscall_randombytes__(uint8_t *out, uint64_t outlen);

#endif /* !HAETAE_TEST_RANDOMBYTES_H */
