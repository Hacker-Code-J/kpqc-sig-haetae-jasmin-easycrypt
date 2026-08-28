require import AllCore Distr IntDiv Real StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23MatrixSpec
  KeygenM23SingularIntegerSemantics
  Mode2KeygenCoreEquation
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.

import RealOrder.

theory Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze.

(* This layer only decomposes each active mode-2 finalized [s2] coefficient
   into a fixed-context scalar bias plus a centered residual.  It does not
   claim any context distribution, joint independence across indices, FFT
   concentration, or SHAKE idealization. *)

op ideal_final_s2_distribution_at
    (pre_bp avec : BArray8192.t) (i : int) : int distr =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_distribution
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_class_at
    (pre_bp avec : BArray8192.t) (i : int) : int =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_index
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_bias_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_mean
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_centered_residual_at
    (pre_bp avec : BArray8192.t) (i : int) (x : int) : real =
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
     .math_output
       (BArray8192.get32 pre_bp i)
       (BArray8192.get32 avec i)
       x)%r -
  ideal_final_s2_bias_at pre_bp avec i.

op ideal_final_s2_raw_moment2_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_raw_moment2
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_raw_moment4_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_raw_moment4
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_raw_moment8_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_raw_moment8
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_centered_moment2_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_centered_moment2
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_centered_moment3_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_centered_moment3
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_centered_moment4_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_centered_moment4
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

op ideal_final_s2_centered_moment8_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_centered_moment8
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).

lemma ideal_mode2_finalize_context_valid_at
    (pre_bp avec : BArray8192.t) i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .context_valid
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i).
proof.
move=> [hbp havec] hi.
rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.context_valid.
split.
+ exact (hbp i hi).
exact (havec i hi).
qed.

lemma centered_s2_active_source_trit_support
    (sampled_s2 : BArray8192.t) i :
  Mode2KeygenCoreEquation.centered_s2_active sampled_s2 =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  W32.to_sint (BArray8192.get32 sampled_s2 i) \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution.
proof.
move=> hs2 hi.
have hword := hs2 i hi.
rewrite
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_support.
smt().
qed.

lemma pure_final_s2_active_math_output
    (pre_bp sampled_s2 avec : BArray8192.t) i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  Mode2KeygenCoreEquation.centered_s2_active sampled_s2 =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  W32.to_sint
    (BArray8192.get32
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .pure_final_s2 pre_bp sampled_s2 avec) i) =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.math_output
    (BArray8192.get32 pre_bp i)
    (BArray8192.get32 avec i)
    (W32.to_sint (BArray8192.get32 sampled_s2 i)).
proof.
move=> hctx hs2 hi.
have hx :
    W32.to_sint (BArray8192.get32 sampled_s2 i) \in
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution.
+ exact (centered_s2_active_source_trit_support sampled_s2 i hs2 hi).
have hscalar :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .finalize_s2_word_decode_math_output
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i)
      (W32.to_sint (BArray8192.get32 sampled_s2 i))
      (ideal_mode2_finalize_context_valid_at pre_bp avec i hctx hi)
      hx.
rewrite
  (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .pure_final_s2_get32_active pre_bp sampled_s2 avec i hi).
rewrite KeygenM23SingularIntegerSemantics.w32_of_sintK in hscalar.
exact hscalar.
qed.

lemma pure_final_s2_bias_residual_decomposition
    (pre_bp sampled_s2 avec : BArray8192.t) i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  Mode2KeygenCoreEquation.centered_s2_active sampled_s2 =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  (W32.to_sint
     (BArray8192.get32
       (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
         .pure_final_s2 pre_bp sampled_s2 avec) i))%r =
  ideal_final_s2_bias_at pre_bp avec i +
  ideal_final_s2_centered_residual_at
    pre_bp avec i
    (W32.to_sint (BArray8192.get32 sampled_s2 i)).
proof.
move=> hctx hs2 hi.
rewrite /ideal_final_s2_centered_residual_at.
rewrite (pure_final_s2_active_math_output pre_bp sampled_s2 avec i hctx hs2 hi).
ring.
qed.

lemma ideal_final_s2_residual_three_point_average_zero
    (pre_bp avec : BArray8192.t) i :
  (* The ideal source trit gives each of [-1,0,1] mass [1/3], so this is
     the exact fixed-context conditional residual mean. *)
  ((ideal_final_s2_centered_residual_at pre_bp avec i (-1)) +
   (ideal_final_s2_centered_residual_at pre_bp avec i 0) +
   (ideal_final_s2_centered_residual_at pre_bp avec i 1)) / 3%r = 0%r.
proof.
rewrite /ideal_final_s2_centered_residual_at /ideal_final_s2_bias_at.
rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.ideal_final_s2_mean.
field; trivial.
qed.

lemma ideal_final_s2_bias_abs_bound_at
    (pre_bp avec : BArray8192.t) i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  `|ideal_final_s2_bias_at pre_bp avec i| <= 1%r / 3%r.
proof.
move=> hctx hi.
exact
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_mean_abs_le_one_third
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i)
      (ideal_mode2_finalize_context_valid_at pre_bp avec i hctx hi)).
qed.

lemma ideal_final_s2_moment_bounds_at
    (pre_bp avec : BArray8192.t) i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  ideal_final_s2_raw_moment2_at pre_bp avec i <= 8%r / 3%r /\
  ideal_final_s2_centered_moment2_at pre_bp avec i <= 8%r / 3%r /\
  ideal_final_s2_raw_moment4_at pre_bp avec i <= 32%r / 3%r /\
  ideal_final_s2_centered_moment4_at pre_bp avec i <= 32%r / 3%r /\
  ideal_final_s2_raw_moment8_at pre_bp avec i <= 512%r / 3%r /\
  ideal_final_s2_centered_moment8_at pre_bp avec i <= 512%r / 3%r.
proof.
move=> hctx hi.
exact
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_moment_bounds
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i)
      (ideal_mode2_finalize_context_valid_at pre_bp avec i hctx hi)).
qed.

lemma ideal_final_s2_mod1_bias_and_skew_at
    (pre_bp avec : BArray8192.t) i :
  ideal_final_s2_class_at pre_bp avec i = 3 =>
  ideal_final_s2_bias_at pre_bp avec i = -1%r / 3%r /\
  ideal_final_s2_centered_moment3_at pre_bp avec i = 16%r / 27%r.
proof.
move=> hclass.
have hmod1 :
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .ideal_final_s2_class_mod1
        (BArray8192.get32 pre_bp i)
        (BArray8192.get32 avec i).
+ rewrite /ideal_final_s2_class_at in hclass.
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_mod1.
  exact hclass.
exact
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_mean_zero_false_mod1
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i)
      hmod1).
qed.

lemma ideal_final_s2_distribution_at_lossless
    (pre_bp avec : BArray8192.t) i :
  is_lossless (ideal_final_s2_distribution_at pre_bp avec i).
proof.
rewrite /ideal_final_s2_distribution_at.
exact
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_distribution_lossless
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i)).
qed.

lemma ideal_final_s2_distribution_at_support
    (pre_bp avec : BArray8192.t) i y :
  y \in ideal_final_s2_distribution_at pre_bp avec i <=>
  exists x,
    x \in
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution /\
    y =
      Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
        .math_output
          (BArray8192.get32 pre_bp i)
          (BArray8192.get32 avec i) x.
proof.
rewrite /ideal_final_s2_distribution_at.
exact
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_distribution_support
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i) y).
qed.

lemma ideal_final_s2_distribution_at_class_table
    (pre_bp avec : BArray8192.t) i :
  ideal_final_s2_distribution_at pre_bp avec i =
  dmap
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .class_output_table
        (BArray8192.get32 pre_bp i)
        (BArray8192.get32 avec i)).
proof.
rewrite /ideal_final_s2_distribution_at.
exact
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_distribution_class_table
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i)).
qed.

lemma ideal_final_s2_active_bias_profile
    (pre_bp sampled_s2 avec : BArray8192.t) :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  Mode2KeygenCoreEquation.centered_s2_active sampled_s2 =>
  forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .context_valid
        (BArray8192.get32 pre_bp i)
        (BArray8192.get32 avec i) /\
    W32.to_sint (BArray8192.get32 sampled_s2 i) \in
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution /\
    (W32.to_sint
       (BArray8192.get32
         (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
           .pure_final_s2 pre_bp sampled_s2 avec) i))%r =
      ideal_final_s2_bias_at pre_bp avec i +
      ideal_final_s2_centered_residual_at
        pre_bp avec i
        (W32.to_sint (BArray8192.get32 sampled_s2 i)) /\
    ((ideal_final_s2_centered_residual_at pre_bp avec i (-1)) +
     (ideal_final_s2_centered_residual_at pre_bp avec i 0) +
     (ideal_final_s2_centered_residual_at pre_bp avec i 1)) / 3%r = 0%r /\
    `|ideal_final_s2_bias_at pre_bp avec i| <= 1%r / 3%r /\
    ideal_final_s2_raw_moment2_at pre_bp avec i <= 8%r / 3%r /\
    ideal_final_s2_centered_moment2_at pre_bp avec i <= 8%r / 3%r /\
    ideal_final_s2_raw_moment4_at pre_bp avec i <= 32%r / 3%r /\
    ideal_final_s2_centered_moment4_at pre_bp avec i <= 32%r / 3%r /\
    ideal_final_s2_raw_moment8_at pre_bp avec i <= 512%r / 3%r /\
    ideal_final_s2_centered_moment8_at pre_bp avec i <= 512%r / 3%r.
proof.
move=> hctx hs2 i hi.
have hmoment := ideal_final_s2_moment_bounds_at pre_bp avec i hctx hi.
split.
+ exact (ideal_mode2_finalize_context_valid_at pre_bp avec i hctx hi).
split.
+ exact (centered_s2_active_source_trit_support sampled_s2 i hs2 hi).
split.
+ exact
    (pure_final_s2_bias_residual_decomposition
      pre_bp sampled_s2 avec i hctx hs2 hi).
split.
+ exact (ideal_final_s2_residual_three_point_average_zero pre_bp avec i).
split.
+ exact (ideal_final_s2_bias_abs_bound_at pre_bp avec i hctx hi).
move: hmoment.
smt().
qed.

end Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze.
