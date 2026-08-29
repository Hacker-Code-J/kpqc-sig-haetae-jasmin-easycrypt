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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze.

(* This file records the paper-facing limitation of the symbolic eighth-moment
   certificate: after replacing the exact fixed-context headroom and profile
   with context-independent worst cases, the resulting ratio exceeds the
   trivial probability ceiling 1. It does not claim any union bound, numeric
   root certificate, or concrete security statement. *)

op ideal_final_s2_uniform_min_headroom : real =
  KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap -
  KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps -
  256%r / 3%r.

op ideal_final_s2_uniform_profile8_cap : real =
  49301448283783168%r / 2187%r.

op ideal_final_s2_uniform_profile8_ratio : real =
  ideal_final_s2_uniform_profile8_cap /
  (ideal_final_s2_uniform_min_headroom ^ 8).

lemma ideal_final_s2_uniform_min_headroom_exact :
  ideal_final_s2_uniform_min_headroom = 8057501%r / 196608%r.
proof.
rewrite /ideal_final_s2_uniform_min_headroom
        /KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap
        /KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps.
field; trivial.
qed.

lemma ideal_final_s2_uniform_min_headroom_gt0 :
  0%r < ideal_final_s2_uniform_min_headroom.
proof.
rewrite ideal_final_s2_uniform_min_headroom_exact.
smt().
qed.

lemma ideal_final_s2_uniform_min_headroom_lt_41 :
  ideal_final_s2_uniform_min_headroom < 41%r.
proof.
rewrite ideal_final_s2_uniform_min_headroom_exact.
smt().
qed.

lemma ideal_final_s2_uniform_profile8_cap_gt_41_eighth :
  41%r ^ 8 < ideal_final_s2_uniform_profile8_cap.
proof.
rewrite /ideal_final_s2_uniform_profile8_cap.
have -> : 41%r ^ 8 = 7984925229121%r by ring.
smt().
qed.

lemma ideal_final_s2_uniform_profile8_ratio_gt_one :
  1%r < ideal_final_s2_uniform_profile8_ratio.
proof.
have hhpos := ideal_final_s2_uniform_min_headroom_gt0.
have hh41 := ideal_final_s2_uniform_min_headroom_lt_41.
have hpowpos : 0%r < ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 ideal_final_s2_uniform_min_headroom hhpos).
have hrange : 0%r <= ideal_final_s2_uniform_min_headroom <= 41%r.
+ split.
  + smt().
  smt().
have hp := ler_pexp 8 ideal_final_s2_uniform_min_headroom 41%r _ hrange.
+ trivial.
have hc := ideal_final_s2_uniform_profile8_cap_gt_41_eighth.
have hlt : ideal_final_s2_uniform_min_headroom ^ 8 <
            ideal_final_s2_uniform_profile8_cap by smt().
rewrite /ideal_final_s2_uniform_profile8_ratio.
rewrite (ltr_pdivl_mulr (ideal_final_s2_uniform_min_headroom ^ 8)) 1:hpowpos.
exact hlt.
qed.

lemma ideal_final_s2_uniform_profile8_ratio_worse_than_trivial_ceiling :
  1%r <= ideal_final_s2_uniform_profile8_ratio.
proof.
have h := ideal_final_s2_uniform_profile8_ratio_gt_one.
smt().
qed.

lemma ideal_final_s2_uniform_min_headroom_le_real_headroom
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  ideal_final_s2_uniform_min_headroom <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k.
proof.
move=> hctx hrow hk.
have [hre _] :=
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_fft_component_bounds
      pre_bp avec row k hctx hrow hk.
rewrite /ideal_final_s2_uniform_min_headroom
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_full_row_residual_real_headroom
        /KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap
        /KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps.
smt().
qed.

lemma ideal_final_s2_uniform_min_headroom_le_imag_headroom
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  ideal_final_s2_uniform_min_headroom <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k.
proof.
move=> hctx hrow hk.
have [_ him] :=
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_fft_component_bounds
      pre_bp avec row k hctx hrow hk.
rewrite /ideal_final_s2_uniform_min_headroom
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_full_row_residual_imag_headroom
        /KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap
        /KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps.
smt().
qed.

lemma ideal_final_s2_uniform_profile8_cap_nonnegative :
  0%r <= ideal_final_s2_uniform_profile8_cap.
proof.
rewrite /ideal_final_s2_uniform_profile8_cap.
smt().
qed.

lemma ideal_final_s2_uniform_profile8_ratio_nonnegative :
  0%r <= ideal_final_s2_uniform_profile8_ratio.
proof.
rewrite /ideal_final_s2_uniform_profile8_ratio.
have hc : 0%r <= ideal_final_s2_uniform_profile8_cap by
  exact ideal_final_s2_uniform_profile8_cap_nonnegative.
have hh : 0%r < ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 ideal_final_s2_uniform_min_headroom
    ideal_final_s2_uniform_min_headroom_gt0).
smt().
qed.

lemma ideal_final_s2_uniform_div_bound (a c h m : real) :
  0%r < m =>
  m <= h =>
  0%r <= c =>
  a <= c =>
  a / h <= c / m.
proof.
move=> hm hmh hc hac.
have hh : 0%r < h by smt().
apply (ler_trans (c / h)).
+ rewrite ler_pdivr_mulr 1:hh.
  have hcancel : c / h * h = c.
  + field; smt().
  rewrite hcancel.
  exact hac.
rewrite ler_pdivl_mulr 1:hm.
have -> : c / h * m = (c * m) / h by ring.
rewrite ler_pdivr_mulr 1:hh.
exact (ler_wpmul2l c hc m h hmh).
qed.

lemma ideal_final_s2_full_row_residual_fft_real_headroom_tail_uniform
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
  ideal_final_s2_uniform_profile8_ratio.
proof.
move=> hctx hrow hk.
have hmarkov :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .ideal_final_s2_full_row_residual_fft_real_headroom_tail_markov8
      pre_bp avec row k hctx hrow hk.
apply (ler_trans _ _ _ hmarkov).
have hprofile :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
    .ideal_final_s2_row_residual_profile8_256_le
      pre_bp avec row k hctx hrow hk.
move: hprofile => [hre _].
have hhead :=
  ideal_final_s2_uniform_min_headroom_le_real_headroom
    pre_bp avec row k hctx hrow hk.
have hhpos :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom_gt0
      pre_bp avec row k hctx hrow hk.
have hhminpos := ideal_final_s2_uniform_min_headroom_gt0.
have hhpow : 0%r < (
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8) by
  exact (expr_gt0 8 _ hhpos).
have hhminpow : 0%r < ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 _ hhminpos).
have hrange :
    0%r <= ideal_final_s2_uniform_min_headroom <=
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k.
+ smt().
have hpowmono :=
  ler_pexp 8 ideal_final_s2_uniform_min_headroom
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k) _ hrange.
+ trivial.
exact
  (ideal_final_s2_uniform_div_bound
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256)
    ideal_final_s2_uniform_profile8_cap
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8)
    (ideal_final_s2_uniform_min_headroom ^ 8)
    hhminpow hpowmono
    ideal_final_s2_uniform_profile8_cap_nonnegative
    hre).
qed.

lemma ideal_final_s2_full_row_bias_residual_real_bad_mu_le_uniform
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
  ideal_final_s2_uniform_profile8_ratio.
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
  (ideal_final_s2_full_row_residual_fft_real_headroom_tail_uniform
    pre_bp avec row k hctx hrow hk).
qed.

lemma ideal_final_s2_full_row_residual_fft_imag_headroom_tail_uniform
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
  ideal_final_s2_uniform_profile8_ratio.
proof.
move=> hctx hrow hk.
have hmarkov :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .ideal_final_s2_full_row_residual_fft_imag_headroom_tail_markov8
      pre_bp avec row k hctx hrow hk.
apply (ler_trans _ _ _ hmarkov).
have hprofile :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
    .ideal_final_s2_row_residual_profile8_256_le
      pre_bp avec row k hctx hrow hk.
move: hprofile => [_ him].
have hhead :=
  ideal_final_s2_uniform_min_headroom_le_imag_headroom
    pre_bp avec row k hctx hrow hk.
have hhpos :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom_gt0
      pre_bp avec row k hctx hrow hk.
have hhminpos := ideal_final_s2_uniform_min_headroom_gt0.
have hhpow : 0%r < (
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8) by
  exact (expr_gt0 8 _ hhpos).
have hhminpow : 0%r < ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 _ hhminpos).
have hrange :
    0%r <= ideal_final_s2_uniform_min_headroom <=
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k.
+ smt().
have hpowmono :=
  ler_pexp 8 ideal_final_s2_uniform_min_headroom
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k) _ hrange.
+ trivial.
exact
  (ideal_final_s2_uniform_div_bound
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256)
    ideal_final_s2_uniform_profile8_cap
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8)
    (ideal_final_s2_uniform_min_headroom ^ 8)
    hhminpow hpowmono
    ideal_final_s2_uniform_profile8_cap_nonnegative
    him).
qed.

lemma ideal_final_s2_full_row_bias_residual_imag_bad_mu_le_uniform
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
  ideal_final_s2_uniform_profile8_ratio.
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
  (ideal_final_s2_full_row_residual_fft_imag_headroom_tail_uniform
    pre_bp avec row k hctx hrow hk).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze.
