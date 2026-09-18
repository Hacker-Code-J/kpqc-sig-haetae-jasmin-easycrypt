// SPDX-License-Identifier: MIT
/* Test-only oracle for prescribed candidate streams, not SHAKE seed inputs.
 * Include the pinned implementation so its static numerical helpers are used.
 * No replacement of production randomness is linked into the scheme library. */
#include <stdint.h>

#include "../../HAETAE-1.2.0/reference_implementation/src/fixpoint.c"
#include "../../HAETAE-1.2.0/reference_implementation/src/sampler.c"

struct hyperball_boundary_result {
  uint64_t accepted, sample;
  uint64_t square[2], half[2], first[2], inverse[2], scale[2];
  uint64_t coefficient, norm;
};

void hyperball_boundary_constants(uint64_t out[8]) {
  out[0] = HAETAE_N * (HAETAE_K + HAETAE_L);
  out[1] = HAETAE_N * HAETAE_L;
  out[2] = (uint64_t)(HAETAE_B0 * HAETAE_LN + HAETAE_SQNM / 2) << 15;
  out[3] = HAETAE_B0SQ * HAETAE_LN * HAETAE_LN;
  out[4] = start_cube.limb48[0];
  out[5] = start_cube.limb48[1];
  out[6] = start_times_threehalves.limb48[0];
  out[7] = start_times_threehalves.limb48[1];
}

void hyperball_boundary_probe(const uint8_t candidate[26],
                             struct hyperball_boundary_result *out) {
  const unsigned count = HAETAE_N * (HAETAE_K + HAETAE_L);
  uint64_t sample;
  fp96_76 square, half, first, tmp, inverse, scale;
  out->accepted = sample_gauss_sigma76(&sample, &square, candidate);
  out->sample = sample;
  out->square[0] = square.limb48[0];
  out->square[1] = square.limb48[1];

  /* Hyperball's first two streams consume 257 accepted events but store 256
   * samples each. Repeating one event therefore contributes count + 2 squares.
   * The limbs of these fixed fixtures fit before and after normalization. */
  half.limb48[0] = square.limb48[0] * (count + 2);
  half.limb48[1] = square.limb48[1] * (count + 2);
  renormalize(&half);

  /* The rounding sequence in reference src/polyfix.c:261-267. */
  half.limb48[0] = (half.limb48[0] + 1) >> 1;
  half.limb48[0] += (half.limb48[1] & 1) << 47;
  half.limb48[1] >>= 1;
  renormalize(&half);
  out->half[0] = half.limb48[0];
  out->half[1] = half.limb48[1];

  fixpoint_mul(&tmp, &half, &start_cube);
  fixpoint_sub(&first, &start_times_threehalves, &tmp);
  out->first[0] = first.limb48[0];
  out->first[1] = first.limb48[1];
  fixpoint_newton_invsqrt(&inverse, &half);
  out->inverse[0] = inverse.limb48[0];
  out->inverse[1] = inverse.limb48[1];

  fixpoint_mul_high(&scale, &inverse,
      (uint64_t)(HAETAE_B0 * HAETAE_LN + HAETAE_SQNM / 2) << 15);
  out->scale[0] = scale.limb48[0];
  out->scale[1] = scale.limb48[1];
  const int32_t coefficient = fixpoint_mul_rnd13(sample, &scale, 0);
  out->coefficient = (uint32_t)coefficient;
  /* Repeated uint64_t addition in polyfixveclk_sqnorm2 has this residue. */
  out->norm = (uint64_t)count * (uint64_t)((int64_t)coefficient * coefficient);
}
