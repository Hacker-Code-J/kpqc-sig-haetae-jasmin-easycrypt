// SPDX-License-Identifier: MIT

#ifndef HAETAE_POLY_H
#define HAETAE_POLY_H

#include "params.h"

#include <stdint.h>

typedef struct {
  int32_t coeffs[HAETAE_N];
} poly;

#define poly_pointwise_montgomery HAETAE_NAMESPACE(poly_pointwise_montgomery)
void poly_pointwise_montgomery(poly *c, const poly *a, const poly *b);

#define poly_ntt HAETAE_NAMESPACE(poly_ntt)
void poly_ntt(poly *a);
#define poly_invntt_tomont HAETAE_NAMESPACE(poly_invntt_tomont)
void poly_invntt_tomont(poly *a);

#endif /* !HAETAE_POLY_H */
