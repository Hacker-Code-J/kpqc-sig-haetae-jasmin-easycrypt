require import AllCore DList Distr Finite IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety
  KeygenM23SingularFFTSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze.

(* This file adds only symbolic eighth-moment Markov tail bounds for the
   fixed-context full-row ideal residual odd DFT. It reuses the existing
   headroom and bad-event bridges, keeps the exact profile8 expressions, and
   does not claim any numeric certificate, union bound, or security level. *)

lemma eighth_power_nonnegative (x : real) :
  0%r <= x ^ 8.
proof.
have -> : 8 = 4 * 2 by trivial.
rewrite RField.exprM.
exact (ge0_sqr (x ^ 4)).
qed.

lemma norm_eighth_power (x : real) :
  `|x| ^ 8 = x ^ 8.
proof.
rewrite -normrX_nat 1:/#.
rewrite ger0_norm 1:eighth_power_nonnegative.
trivial.
qed.

lemma finite_eighth_moment_markov ['a]
    (d : 'a distr) (f : 'a -> real) (t : real) :
  is_finite (support d) =>
  0%r < t =>
  mu d (fun x => t <= `|f x|) <=
  E d (fun x => f x ^ 8) / (t ^ 8).
proof.
move=> hfin ht.
have ht8 : 0%r < t ^ 8 by exact (expr_gt0 8 t ht).
have hindicator :
    E d (fun x => if t <= `|f x| then t ^ 8 else 0%r) <=
    E d (fun x => f x ^ 8).
+ apply (ler_exp d
    (fun x => if t <= `|f x| then t ^ 8 else 0%r)
    (fun x => f x ^ 8)).
  + exact (hasE_finite _ _ hfin).
  + exact (hasE_finite _ _ hfin).
  move=> x.
  case: (t <= `|f x|) => htail.
  + rewrite ifT 1:htail.
    have hn8 : 0 <= 8 by trivial.
    have ht0 : 0%r <= t by smt().
    have hrange : 0%r <= t <= `|f x| by smt().
    have hpow := ler_pexp 8 t `|f x| hn8 hrange.
    rewrite norm_eighth_power in hpow.
    exact hpow.
  + rewrite ifF 1:htail.
    + trivial.
    exact (eighth_power_nonnegative (f x)).
rewrite expC_cond in hindicator.
rewrite (ler_pdivl_mulr (t ^ 8)) 1:ht8.
rewrite (RField.mulrC (mu d (fun x => t <= `|f x|)) (t ^ 8)).
exact hindicator.
qed.

lemma ideal_final_s2_full_row_residual_fft_real_headroom_tail_markov8
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k <=
      `|creal z|) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8).
proof.
move=> hctx hrow hk.
have hfin :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_fft_finite
      pre_bp avec row k hrow.
have hheadroom :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom_gt0
      pre_bp avec row k hctx hrow hk.
have htail :=
  finite_eighth_moment_markov
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    creal
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k)
    hfin hheadroom.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_full_row_residual_fft_real_moment8E
      pre_bp avec row k hrow) in htail.
exact htail.
qed.

lemma ideal_final_s2_full_row_bias_residual_real_bad_mu_le_markov8
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
        `|creal
            (cadd
              (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
                .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
              z)| +
          KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8).
proof.
move=> hctx hrow hk.
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)
      (fun z =>
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k <=
        `|creal z|))).
+ apply mu_le => z hz hbad.
  exact
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_real_bad_implies_residual_tail
        pre_bp avec row k z hbad).
exact
  (ideal_final_s2_full_row_residual_fft_real_headroom_tail_markov8
    pre_bp avec row k hctx hrow hk).
qed.

lemma ideal_final_s2_full_row_residual_fft_imag_headroom_tail_markov8
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k <=
      `|cimag z|) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8).
proof.
move=> hctx hrow hk.
have hfin :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_fft_finite
      pre_bp avec row k hrow.
have hheadroom :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom_gt0
      pre_bp avec row k hctx hrow hk.
have htail :=
  finite_eighth_moment_markov
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    cimag
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k)
    hfin hheadroom.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_full_row_residual_fft_imag_moment8E
      pre_bp avec row k hrow) in htail.
exact htail.
qed.

lemma ideal_final_s2_full_row_bias_residual_imag_bad_mu_le_markov8
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
        `|cimag
            (cadd
              (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
                .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
              z)| +
          KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8).
proof.
move=> hctx hrow hk.
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)
      (fun z =>
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k <=
        `|cimag z|))).
+ apply mu_le => z hz hbad.
  exact
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_imag_bad_implies_residual_tail
        pre_bp avec row k z hbad).
exact
  (ideal_final_s2_full_row_residual_fft_imag_headroom_tail_markov8
    pre_bp avec row k hctx hrow hk).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze.
