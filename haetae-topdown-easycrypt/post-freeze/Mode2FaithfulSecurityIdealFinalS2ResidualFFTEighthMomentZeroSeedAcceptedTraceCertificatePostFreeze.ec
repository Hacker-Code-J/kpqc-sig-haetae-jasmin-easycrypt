require import AllCore DList Distr Finite IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  KeygenM23ComplexReal
  KeygenM23SingularFFTSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.

(* The two lists are the deterministic raw_seed=0 reference-C accepted
   attempt (attempt 2, eta counter 10) trace. The companion C/Python artifacts
   reproduce them. Equality with an EasyCrypt [pre_bp, avec] row and the
   closed numeric calculation both remain explicit premises. *)

op zero_seed_accepted_row0_classes : int list = [
  5;4;4;4;3;2;5;3;4;2;4;2;5;2;2;3;2;4;3;2;5;2;5;4;2;4;3;3;5;2;3;4;
  5;4;4;4;2;3;5;5;2;5;4;5;2;3;5;2;3;2;4;5;5;3;5;5;2;2;5;2;3;3;5;3;
  5;2;3;5;4;3;5;3;4;4;5;4;3;5;5;5;3;4;5;5;2;3;2;4;5;4;2;4;4;3;4;5;
  2;3;4;5;3;5;3;4;5;5;2;4;5;5;5;4;5;2;5;3;3;5;3;4;4;3;2;4;2;5;4;2;
  5;5;4;3;5;5;4;4;3;3;5;3;4;3;4;4;2;4;5;5;3;2;3;5;2;3;2;3;3;3;4;5;
  3;4;5;2;5;4;3;3;4;2;4;2;2;4;2;2;3;4;2;2;2;2;2;2;3;3;5;4;5;3;5;3;
  5;2;4;5;5;3;5;2;2;2;4;5;4;2;4;3;3;4;4;3;4;2;5;3;2;2;4;2;2;2;5;4;
  5;2;3;5;4;4;4;2;2;4;2;2;2;5;3;2;3;4;4;4;3;5;4;4;5;4;4;4;4;2;3;2
].

op zero_seed_accepted_row1_classes : int list = [
  2;3;4;4;2;4;2;5;2;2;3;4;3;3;4;4;3;5;5;3;2;4;2;3;3;2;4;2;3;4;5;3;
  3;5;4;4;3;4;5;2;4;5;2;4;5;3;2;5;3;3;2;4;3;2;3;5;2;5;4;5;5;5;2;2;
  2;3;4;2;3;3;3;4;2;2;2;4;3;5;4;3;4;4;4;2;5;3;5;2;2;3;4;2;4;2;2;3;
  2;2;4;5;2;5;4;4;4;3;5;5;5;3;4;5;3;5;4;5;2;5;4;4;5;3;3;2;3;3;5;2;
  5;3;4;2;3;2;4;5;2;3;5;5;5;2;5;4;2;5;2;2;4;4;2;2;2;2;2;4;2;2;2;5;
  4;2;5;3;4;3;5;3;3;5;3;4;4;4;2;2;2;5;4;3;5;5;3;4;4;2;5;4;3;3;4;4;
  5;3;5;5;4;4;5;2;2;4;4;2;4;5;2;2;2;2;3;5;4;2;4;2;4;2;2;4;4;4;2;4;
  3;4;3;3;2;2;5;2;3;2;5;5;5;3;5;4;2;5;3;4;2;4;4;5;4;3;3;5;3;3;3;5
].

op zero_seed_accepted_trace (row j : int) : int =
  if row = 0 then nth 0 zero_seed_accepted_row0_classes j
  else if row = 1 then nth 0 zero_seed_accepted_row1_classes j
  else 0.

op zero_seed_accepted_ceiling (row : int) : real =
  if row = 0 then 67171862309%r
  else if row = 1 then 66096296038%r
  else 0%r.

op zero_seed_accepted_uniform_improvement_floor (row : int) : real =
  if row = 0 then 335%r
  else if row = 1 then 341%r
  else 0%r.

op zero_seed_accepted_re_profile8_interval (row k : int) : rinterval =
  state_profile8
    (profile8_interval_eval (zero_seed_accepted_trace row)
      (certified_odd_root_re_interval k) 256).

op zero_seed_accepted_im_profile8_interval (row k : int) : rinterval =
  state_profile8
    (profile8_interval_eval (zero_seed_accepted_trace row)
      (certified_odd_root_im_interval k) 256).

op zero_seed_accepted_numeric_certificate : bool =
  forall row k,
    0 <= row < 2 =>
    0 <= k < 256 =>
    interval_abs_upper (zero_seed_accepted_re_profile8_interval row k) <=
      zero_seed_accepted_ceiling row /\
    interval_abs_upper (zero_seed_accepted_im_profile8_interval row k) <=
      zero_seed_accepted_ceiling row.

lemma zero_seed_accepted_trace_sizes :
  size zero_seed_accepted_row0_classes = 256 /\
  size zero_seed_accepted_row1_classes = 256.
proof.
rewrite /zero_seed_accepted_row0_classes /zero_seed_accepted_row1_classes.
trivial.
qed.

lemma zero_seed_accepted_re_profile8_intervalE row k :
  zero_seed_accepted_re_profile8_interval row k =
  certified_class_re_profile8_interval (zero_seed_accepted_trace row) k 256.
proof.
rewrite /zero_seed_accepted_re_profile8_interval
        /certified_class_re_profile8_interval.
have h256 : 0 <= 256 by smt().
have he := profile8_interval_evalE (zero_seed_accepted_trace row)
  (certified_odd_root_re_interval k) 256 h256.
rewrite he /profile8_interval_expected_state /state_profile8 /=.
trivial.
qed.

lemma zero_seed_accepted_im_profile8_intervalE row k :
  zero_seed_accepted_im_profile8_interval row k =
  certified_class_im_profile8_interval (zero_seed_accepted_trace row) k 256.
proof.
rewrite /zero_seed_accepted_im_profile8_interval
        /certified_class_im_profile8_interval.
have h256 : 0 <= 256 by smt().
have he := profile8_interval_evalE (zero_seed_accepted_trace row)
  (certified_odd_root_im_interval k) 256 h256.
rewrite he /profile8_interval_expected_state /state_profile8 /=.
trivial.
qed.

lemma ideal_final_s2_row_residual_profile8_zero_seed_accepted_numeric
    pre_bp avec row k :
  zero_seed_accepted_numeric_certificate =>
  0 <= row < 2 =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row = zero_seed_accepted_trace row =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256| <=
    zero_seed_accepted_ceiling row /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256| <=
    zero_seed_accepted_ceiling row.
proof.
rewrite /zero_seed_accepted_numeric_certificate.
move=> hnumeric hrow hk htrace.
have hk0 : 0 <= k by smt().
have h :=
  ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
    pre_bp avec row k 256 hk0.
rewrite htrace in h.
rewrite -zero_seed_accepted_re_profile8_intervalE
        -zero_seed_accepted_im_profile8_intervalE in h.
have [hure huim] := hnumeric row k hrow hk.
move: h => [hre him].
split.
+ apply (ler_trans
    (interval_abs_upper (zero_seed_accepted_re_profile8_interval row k))).
  + exact hre.
  exact hure.
apply (ler_trans
  (interval_abs_upper (zero_seed_accepted_im_profile8_interval row k))).
+ exact him.
exact huim.
qed.

lemma zero_seed_accepted_ceiling_improvement row :
  0 <= row < 2 =>
  zero_seed_accepted_uniform_improvement_floor row *
    zero_seed_accepted_ceiling row <
  49301448283783168%r / 2187%r.
proof.
move=> hrow.
rewrite /zero_seed_accepted_uniform_improvement_floor
        /zero_seed_accepted_ceiling.
case (row = 0) => hrow0.
+ smt().
have -> : row = 1 by smt().
smt().
qed.

lemma zero_seed_accepted_ceiling_hundred_below_min_headroom8 row :
  0 <= row < 2 =>
  100%r * zero_seed_accepted_ceiling row <
  (8057501%r / 196608%r) ^ 8.
proof.
move=> hrow.
have -> :
  (8057501%r / 196608%r) ^ 8 =
  17766543545077793661285552022136707710355048352639460001%r /
  2232592609368277258783200799359831235362816%r.
+ field; smt().
rewrite /zero_seed_accepted_ceiling.
case (row = 0) => hrow0.
+ smt().
have -> : row = 1 by smt().
smt().
qed.

lemma zero_seed_accepted_ceiling_markov_ratio_lt_one_hundred row :
  0 <= row < 2 =>
  zero_seed_accepted_ceiling row /
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8) <
  1%r / 100%r.
proof.
move=> hrow.
have hmpos :
    0%r <
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 _
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom_gt0).
have hhundred :=
  zero_seed_accepted_ceiling_hundred_below_min_headroom8 row hrow.
rewrite -Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
  .ideal_final_s2_uniform_min_headroom_exact in hhundred.
rewrite ltr_pdivr_mulr 1:hmpos.
have -> :
    1%r / 100%r *
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom ^ 8) =
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8) / 100%r by ring.
rewrite ltr_pdivl_mulr 1:/#.
have -> :
    zero_seed_accepted_ceiling row * 100%r =
    100%r * zero_seed_accepted_ceiling row by ring.
exact hhundred.
qed.

lemma ideal_final_s2_full_row_residual_fft_real_tail_zero_seed_accepted
    pre_bp avec row k :
  zero_seed_accepted_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < 2 =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row = zero_seed_accepted_trace row =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k <=
      `|creal z|) <
  1%r / 100%r.
proof.
move=> hnumeric hctx hrow hk htrace.
have hmarkov :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .ideal_final_s2_full_row_residual_fft_real_headroom_tail_markov8
      pre_bp avec row k hctx hrow hk.
have [hre _] :=
  ideal_final_s2_row_residual_profile8_zero_seed_accepted_numeric
    pre_bp avec row k hnumeric hrow hk htrace.
have hprofile :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 <=
    zero_seed_accepted_ceiling row.
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact hre.
have hhead :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom_le_real_headroom
      pre_bp avec row k hctx hrow hk.
have hmpos :
    0%r <
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 _
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom_gt0).
have hrange :
    0%r <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k by
  smt().
have hpowmono :=
  ler_pexp 8
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k)
    _ hrange.
+ trivial.
have hdiv :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_div_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256)
      (zero_seed_accepted_ceiling row)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom ^ 8)
      hmpos hpowmono _ hprofile.
+ rewrite /zero_seed_accepted_ceiling.
  case (row = 0); smt().
apply (ler_lt_trans
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8))).
+ exact hmarkov.
apply (ler_lt_trans
  (zero_seed_accepted_ceiling row /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom ^ 8))).
+ exact hdiv.
exact (zero_seed_accepted_ceiling_markov_ratio_lt_one_hundred row hrow).
qed.

lemma ideal_final_s2_full_row_residual_fft_imag_tail_zero_seed_accepted
    pre_bp avec row k :
  zero_seed_accepted_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < 2 =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row = zero_seed_accepted_trace row =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k <=
      `|cimag z|) <
  1%r / 100%r.
proof.
move=> hnumeric hctx hrow hk htrace.
have hmarkov :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .ideal_final_s2_full_row_residual_fft_imag_headroom_tail_markov8
      pre_bp avec row k hctx hrow hk.
have [_ him] :=
  ideal_final_s2_row_residual_profile8_zero_seed_accepted_numeric
    pre_bp avec row k hnumeric hrow hk htrace.
have hprofile :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 <=
    zero_seed_accepted_ceiling row.
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact him.
have hhead :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom_le_imag_headroom
      pre_bp avec row k hctx hrow hk.
have hmpos :
    0%r <
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 _
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom_gt0).
have hrange :
    0%r <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k by
  smt().
have hpowmono :=
  ler_pexp 8
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k)
    _ hrange.
+ trivial.
have hdiv :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_div_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256)
      (zero_seed_accepted_ceiling row)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom ^ 8)
      hmpos hpowmono _ hprofile.
+ rewrite /zero_seed_accepted_ceiling.
  case (row = 0); smt().
apply (ler_lt_trans
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8))).
+ exact hmarkov.
apply (ler_lt_trans
  (zero_seed_accepted_ceiling row /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom ^ 8))).
+ exact hdiv.
exact (zero_seed_accepted_ceiling_markov_ratio_lt_one_hundred row hrow).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.
