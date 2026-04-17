// SPDX-License-Identifier: MIT

#include "poly.h"
// #include "decompose.h"
#include "ntt.h"
#include "params.h"
#include "reduce.h"
// #include "sampler.h"
// #include "symmetric.h"

#include <stdint.h>

/*************************************************
 * Name:        poly_pointwise_montgomery
 *
 * Description: Pointwise multiplication of polynomials in NTT domain
 *              representation and multiplication of resulting polynomial
 *              by 2^{-32}.
 *
 * Arguments:   - poly *c: pointer to output polynomial
 *              - const poly *a: pointer to first input polynomial
 *              - const poly *b: pointer to second input polynomial
 **************************************************/
void poly_pointwise_montgomery(poly *c, const poly *a, const poly *b) {
  unsigned int i;

  for (i = 0; i < HAETAE_N; ++i)
    c->coeffs[i] = montgomery_reduce((int64_t)a->coeffs[i] * b->coeffs[i]);
}

void poly_ntt(poly *a) { ntt(&a->coeffs[0]); }

void poly_invntt_tomont(poly *a) { invntt_tomont(&a->coeffs[0]); }
