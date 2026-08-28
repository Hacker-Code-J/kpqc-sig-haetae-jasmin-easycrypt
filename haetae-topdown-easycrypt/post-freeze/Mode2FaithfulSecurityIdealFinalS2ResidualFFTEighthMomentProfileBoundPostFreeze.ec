require import AllCore DList Distr Finite IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23MatrixSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze.

(* This file places root-independent rational envelopes over the exact
   fixed-context residual FFT moment profiles. Signed third and fifth profiles
   remain under absolute values. It does not claim a numerical tail, union
   bound, random-context law, actual/fixed-point FFT result, or security level. *)

op ideal_final_s2_residual_moment2_cap : real = 8%r / 3%r.
op ideal_final_s2_residual_moment3_cap : real = 16%r / 27%r.
op ideal_final_s2_residual_moment4_cap : real = 32%r / 3%r.
op ideal_final_s2_residual_moment5_cap : real = 320%r / 243%r.
op ideal_final_s2_residual_moment6_cap : real = 128%r / 3%r.
op ideal_final_s2_residual_moment8_cap : real = 512%r / 3%r.

op ideal_final_s2_residual_profile2_envelope (n : int) : real = (n)%r * ideal_final_s2_residual_moment2_cap.
op ideal_final_s2_residual_profile3_envelope (n : int) : real = (n)%r * ideal_final_s2_residual_moment3_cap.
op ideal_final_s2_residual_profile4_envelope (n : int) : real =
  (n)%r * ideal_final_s2_residual_moment4_cap + 3%r * (n)%r * (n - 1)%r * ideal_final_s2_residual_moment2_cap ^ 2.
op ideal_final_s2_residual_profile5_envelope (n : int) : real =
  (n)%r * ideal_final_s2_residual_moment5_cap + 10%r * (n)%r * (n - 1)%r * ideal_final_s2_residual_moment3_cap * ideal_final_s2_residual_moment2_cap.
op ideal_final_s2_residual_profile6_envelope (n : int) : real =
  (n)%r * ideal_final_s2_residual_moment6_cap +
  15%r * (n)%r * (n - 1)%r * ideal_final_s2_residual_moment4_cap * ideal_final_s2_residual_moment2_cap +
  10%r * (n)%r * (n - 1)%r * ideal_final_s2_residual_moment3_cap ^ 2 +
  15%r * (n)%r * (n - 1)%r * (n - 2)%r * ideal_final_s2_residual_moment2_cap ^ 3.
op ideal_final_s2_residual_profile8_envelope (n : int) : real =
  (n)%r * ideal_final_s2_residual_moment8_cap +
  28%r * (n)%r * (n - 1)%r * ideal_final_s2_residual_moment6_cap * ideal_final_s2_residual_moment2_cap +
  56%r * (n)%r * (n - 1)%r * ideal_final_s2_residual_moment5_cap * ideal_final_s2_residual_moment3_cap +
  35%r * (n)%r * (n - 1)%r * ideal_final_s2_residual_moment4_cap ^ 2 +
  210%r * (n)%r * (n - 1)%r * (n - 2)%r * ideal_final_s2_residual_moment4_cap * ideal_final_s2_residual_moment2_cap ^ 2 +
  280%r * (n)%r * (n - 1)%r * (n - 2)%r * ideal_final_s2_residual_moment3_cap ^ 2 * ideal_final_s2_residual_moment2_cap +
  105%r * (n)%r * (n - 1)%r * (n - 2)%r * (n - 3)%r * ideal_final_s2_residual_moment2_cap ^ 4.

lemma ideal_final_s2_residual_profile2_envelope_succ n : ideal_final_s2_residual_profile2_envelope (n + 1) = ideal_final_s2_residual_profile2_envelope n + ideal_final_s2_residual_moment2_cap.
proof.
rewrite /ideal_final_s2_residual_profile2_envelope.
ring.
qed.

lemma ideal_final_s2_residual_profile3_envelope_succ n : ideal_final_s2_residual_profile3_envelope (n + 1) = ideal_final_s2_residual_profile3_envelope n + ideal_final_s2_residual_moment3_cap.
proof.
rewrite /ideal_final_s2_residual_profile3_envelope.
ring.
qed.

lemma ideal_final_s2_residual_profile4_envelope_succ n :
  ideal_final_s2_residual_profile4_envelope (n + 1) = ideal_final_s2_residual_profile4_envelope n + 6%r * ideal_final_s2_residual_profile2_envelope n * ideal_final_s2_residual_moment2_cap + ideal_final_s2_residual_moment4_cap.
proof.
rewrite /ideal_final_s2_residual_profile4_envelope /ideal_final_s2_residual_profile2_envelope.
ring.
qed.

lemma ideal_final_s2_residual_profile5_envelope_succ n :
  ideal_final_s2_residual_profile5_envelope (n + 1) =
  ideal_final_s2_residual_profile5_envelope n + 10%r * ideal_final_s2_residual_profile3_envelope n * ideal_final_s2_residual_moment2_cap + 10%r * ideal_final_s2_residual_profile2_envelope n * ideal_final_s2_residual_moment3_cap + ideal_final_s2_residual_moment5_cap.
proof.
rewrite /ideal_final_s2_residual_profile5_envelope /ideal_final_s2_residual_profile3_envelope /ideal_final_s2_residual_profile2_envelope.
ring.
qed.

lemma ideal_final_s2_residual_profile6_envelope_succ n :
  ideal_final_s2_residual_profile6_envelope (n + 1) =
  ideal_final_s2_residual_profile6_envelope n + 15%r * ideal_final_s2_residual_profile4_envelope n * ideal_final_s2_residual_moment2_cap + 20%r * ideal_final_s2_residual_profile3_envelope n * ideal_final_s2_residual_moment3_cap +
  15%r * ideal_final_s2_residual_profile2_envelope n * ideal_final_s2_residual_moment4_cap + ideal_final_s2_residual_moment6_cap.
proof.
rewrite /ideal_final_s2_residual_profile6_envelope /ideal_final_s2_residual_profile4_envelope /ideal_final_s2_residual_profile3_envelope /ideal_final_s2_residual_profile2_envelope.
ring.
qed.

lemma ideal_final_s2_residual_profile8_envelope_succ n :
  ideal_final_s2_residual_profile8_envelope (n + 1) =
  ideal_final_s2_residual_profile8_envelope n + 28%r * ideal_final_s2_residual_profile6_envelope n * ideal_final_s2_residual_moment2_cap + 56%r * ideal_final_s2_residual_profile5_envelope n * ideal_final_s2_residual_moment3_cap +
  70%r * ideal_final_s2_residual_profile4_envelope n * ideal_final_s2_residual_moment4_cap + 56%r * ideal_final_s2_residual_profile3_envelope n * ideal_final_s2_residual_moment5_cap +
  28%r * ideal_final_s2_residual_profile2_envelope n * ideal_final_s2_residual_moment6_cap + ideal_final_s2_residual_moment8_cap.
proof.
rewrite /ideal_final_s2_residual_profile8_envelope /ideal_final_s2_residual_profile6_envelope /ideal_final_s2_residual_profile5_envelope /ideal_final_s2_residual_profile4_envelope /ideal_final_s2_residual_profile3_envelope /ideal_final_s2_residual_profile2_envelope.
ring.
qed.

lemma ideal_final_s2_residual_profile8_envelope_256_exact : ideal_final_s2_residual_profile8_envelope 256 = 49301448283783168%r / 2187%r.
proof.
rewrite /ideal_final_s2_residual_profile8_envelope /ideal_final_s2_residual_moment2_cap /ideal_final_s2_residual_moment3_cap /ideal_final_s2_residual_moment4_cap /ideal_final_s2_residual_moment5_cap /ideal_final_s2_residual_moment6_cap /ideal_final_s2_residual_moment8_cap.
field; trivial.
qed.

lemma profile_abs_add_bound (x y bx cy : real) :
  `|x| <= bx =>
  `|y| <= cy =>
  `|x + y| <= bx + cy.
proof.
move=> hx hy.
apply (ler_trans (`|x| + `|y|)).
+ exact (ler_norm_add x y).
apply ler_add.
+ exact hx.
exact hy.
qed.

lemma profile_abs_mul_bound (x y bx cy : real) :
  0%r <= bx =>
  0%r <= cy =>
  `|x| <= bx =>
  `|y| <= cy =>
  `|x * y| <= bx * cy.
proof.
move=> hbx hby hx hy.
rewrite normrM.
apply (ler_trans (bx * `|y|)).
+ apply ler_wpmul2r.
  + exact (normr_ge0 y).
  exact hx.
apply ler_wpmul2l.
+ exact hbx.
exact hy.
qed.

lemma profile_abs_scale_bound (c x bx : real) :
  0%r <= c =>
  0%r <= bx =>
  `|x| <= bx =>
  `|c * x| <= c * bx.
proof.
move=> hc hbx hx.
have hcabs : `|c| = c by rewrite ger0_norm.
rewrite normrM hcabs.
apply ler_wpmul2l => //.
qed.

lemma profile_abs_scale_mul_bound (c x y bx cy : real) :
  0%r <= c =>
  0%r <= bx =>
  0%r <= cy =>
  `|x| <= bx =>
  `|y| <= cy =>
  `|c * x * y| <= c * bx * cy.
proof.
move=> hc hbx hcy hx hy.
have hxy := profile_abs_mul_bound x y bx cy hbx hcy hx hy.
have hbxy : 0%r <= bx * cy by apply mulr_ge0.
have hs := profile_abs_scale_bound c (x * y) (bx * cy) hc hbxy hxy.
have -> : c * x * y = c * (x * y) by ring.
have -> : c * bx * cy = c * (bx * cy) by ring.
exact hs.
qed.

lemma profile_abs_add3_bound
    (x1 x2 x3 b1 b2 b3 : real) :
  `|x1| <= b1 => `|x2| <= b2 => `|x3| <= b3 =>
  `|x1 + x2 + x3| <= b1 + b2 + b3.
proof.
move=> h1 h2 h3.
apply profile_abs_add_bound.
+ exact (profile_abs_add_bound x1 x2 b1 b2 h1 h2).
exact h3.
qed.

lemma profile_abs_add4_bound
    (x1 x2 x3 x4 b1 b2 b3 b4 : real) :
  `|x1| <= b1 => `|x2| <= b2 => `|x3| <= b3 => `|x4| <= b4 =>
  `|x1 + x2 + x3 + x4| <= b1 + b2 + b3 + b4.
proof.
move=> h1 h2 h3 h4.
apply profile_abs_add_bound.
+ exact (profile_abs_add3_bound x1 x2 x3 b1 b2 b3 h1 h2 h3).
exact h4.
qed.

lemma profile_abs_add6_bound
    (x1 x2 x3 x4 x5 x6 b1 b2 b3 b4 b5 b6 : real) :
  `|x1| <= b1 => `|x2| <= b2 => `|x3| <= b3 =>
  `|x4| <= b4 => `|x5| <= b5 => `|x6| <= b6 =>
  `|x1 + x2 + x3 + x4 + x5 + x6| <=
  b1 + b2 + b3 + b4 + b5 + b6.
proof.
move=> h1 h2 h3 h4 h5 h6.
apply profile_abs_add_bound.
+ apply profile_abs_add_bound.
  + exact (profile_abs_add4_bound x1 x2 x3 x4 b1 b2 b3 b4 h1 h2 h3 h4).
  exact h5.
exact h6.
qed.

lemma profile_abs_power_le_one (x : real) q :
  0 <= q =>
  `|x| <= 1%r =>
  `|x ^ q| <= 1%r.
proof.
move=> hq hx.
rewrite normrX_nat 1:hq.
have hrange : 0%r <= `|x| <= 1%r by
  split; first exact (normr_ge0 x); exact hx.
have hp := ler_pexp q `|x| 1%r hq hrange.
rewrite RField.expr1z in hp.
exact hp.
qed.


lemma ideal_final_s2_centered_moment3_abs_bound b a :
  `|Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .ideal_final_s2_centered_moment3 b a| <= 16%r / 27%r.
proof.
have hexh :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_exhaustive b a.
move: hexh => [h0 | [h1 | [h2 | [h3 | [h4 | h5]]]]].
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_rho0 b a h0.
  move: hm => [_ [_ [_ [_ [hm3 _]]]]].
  rewrite hm3 normrN ger0_norm 1:/#.
  smt().
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_rhoq1 b a h1.
  move: hm => [_ [_ [_ [_ [hm3 _]]]]].
  rewrite hm3 ger0_norm 1:/#.
  smt().
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_mod0 b a h2.
  move: hm => [_ [_ [_ [_ [hm3 _]]]]].
  rewrite hm3 normr0.
  smt().
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_mod1 b a h3.
  move: hm => [_ [_ [_ [_ [hm3 _]]]]].
  rewrite hm3 ger0_norm 1:/#.
  smt().
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_mod2 b a h4.
  move: hm => [_ [_ [_ [_ [hm3 _]]]]].
  rewrite hm3 normr0.
  smt().
have hm :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .moments_mod3 b a h5.
move: hm => [_ [_ [_ [_ [hm3 _]]]]].
rewrite hm3 normrN ger0_norm 1:/#.
smt().
qed.

lemma ideal_final_s2_residual_moment3_abs_bound_at pre_bp avec i :
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
      .ideal_final_s2_residual_moment3_at pre_bp avec i| <= 16%r / 27%r.
proof.
rewrite
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_residual_moment3_bridge.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_centered_moment3_at.
exact
  (ideal_final_s2_centered_moment3_abs_bound
    (BArray8192.get32 pre_bp i) (BArray8192.get32 avec i)).
qed.

lemma profile_square_nonnegative (x : real) :
  0%r <= x ^ 2.
proof.
exact (ge0_sqr x).
qed.

lemma profile_fourth_power_nonnegative (x : real) :
  0%r <= x ^ 4.
proof.
have -> : 4 = 2 * 2 by trivial.
rewrite RField.exprM.
exact (ge0_sqr (x ^ 2)).
qed.

lemma profile_eighth_power_nonnegative (x : real) :
  0%r <= x ^ 8.
proof.
have -> : 8 = 4 * 2 by trivial.
rewrite RField.exprM.
exact (ge0_sqr (x ^ 4)).
qed.

lemma ideal_final_s2_residual_moment2_nonnegative_at pre_bp avec i :
  0%r <=
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment2_at pre_bp avec i.
proof.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment2_at.
have hneg :=
  profile_square_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i (-1)).
have hzero :=
  profile_square_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i 0).
have hone :=
  profile_square_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i 1).
smt().
qed.

lemma ideal_final_s2_residual_moment4_nonnegative_at pre_bp avec i :
  0%r <=
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment4_at pre_bp avec i.
proof.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment4_at.
have hneg :=
  profile_fourth_power_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i (-1)).
have hzero :=
  profile_fourth_power_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i 0).
have hone :=
  profile_fourth_power_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i 1).
smt().
qed.

lemma ideal_final_s2_residual_moment8_nonnegative_at pre_bp avec i :
  0%r <=
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment8_at pre_bp avec i.
proof.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment8_at.
have hneg :=
  profile_eighth_power_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i (-1)).
have hzero :=
  profile_eighth_power_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i 0).
have hone :=
  profile_eighth_power_nonnegative
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec i 1).
smt().
qed.

lemma ideal_final_s2_residual_moment248_abs_bounds_at pre_bp avec i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  `|Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_moment2_at pre_bp avec i| <=
    ideal_final_s2_residual_moment2_cap /\
  `|Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_moment4_at pre_bp avec i| <=
    ideal_final_s2_residual_moment4_cap /\
  `|Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_moment8_at pre_bp avec i| <=
    ideal_final_s2_residual_moment8_cap.
proof.
move=> hctx hi.
have hm :=
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment_bounds_at pre_bp avec i hctx hi.
move: hm => [hm2 [hm4 hm8]].
have h2 := ideal_final_s2_residual_moment2_nonnegative_at pre_bp avec i.
have h4 := ideal_final_s2_residual_moment4_nonnegative_at pre_bp avec i.
have h8 := ideal_final_s2_residual_moment8_nonnegative_at pre_bp avec i.
rewrite ger0_norm 1:h2 ger0_norm 1:h4 ger0_norm 1:h8.
rewrite /ideal_final_s2_residual_moment2_cap
        /ideal_final_s2_residual_moment4_cap
        /ideal_final_s2_residual_moment8_cap.
split; first exact hm2.
split; first exact hm4.
exact hm8.
qed.

lemma profile_weighted_moment_abs_bound
    (w : real) q (m cap : real) :
  0 <= q =>
  0%r <= cap =>
  `|w| <= 1%r =>
  `|m| <= cap =>
  `|w ^ q * m| <= cap.
proof.
move=> hq hcap hw hm.
have hwp := profile_abs_power_le_one w q hq hw.
have hmul :=
  profile_abs_mul_bound (w ^ q) m 1%r cap _ hcap hwp hm.
+ trivial.
exact hmul.
qed.

lemma ideal_final_s2_row_residual_re_term_abs_bounds
    pre_bp avec row k j :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= j < 256 =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment2_cap /\
  `|ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment3_cap /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment4_cap /\
  `|ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment5_cap /\
  `|ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment6_cap /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_moment8_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment8_cap.
proof.
move=> hctx hrow hk hj.
have hj256 : 0 <= j < KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; exact hj.
have hidx := ideal_final_s2_row_index_range row j hrow hj256.
have [hm2 [hm4 hm8]] :=
  ideal_final_s2_residual_moment248_abs_bounds_at
    pre_bp avec (ideal_final_s2_row_index row j) hctx hidx.
have hm3 :=
  ideal_final_s2_residual_moment3_abs_bound_at
    pre_bp avec (ideal_final_s2_row_index row j).
have [hm5 [hm6ge hm6]] :=
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment56_bounds_at
      pre_bp avec (ideal_final_s2_row_index row j) hctx hidx.
have [hw _] :=
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .odd_kernel_coordinate_bound1 k j hk hj.
have hq2 : 0 <= 2 by trivial.
have hq3 : 0 <= 3 by trivial.
have hq4 : 0 <= 4 by trivial.
have hq5 : 0 <= 5 by trivial.
have hq6 : 0 <= 6 by trivial.
have hq8 : 0 <= 8 by trivial.
have hc2 : 0%r <= ideal_final_s2_residual_moment2_cap by
  rewrite /ideal_final_s2_residual_moment2_cap; smt().
have hc3 : 0%r <= ideal_final_s2_residual_moment3_cap by
  rewrite /ideal_final_s2_residual_moment3_cap; smt().
have hc4 : 0%r <= ideal_final_s2_residual_moment4_cap by
  rewrite /ideal_final_s2_residual_moment4_cap; smt().
have hc5 : 0%r <= ideal_final_s2_residual_moment5_cap by
  rewrite /ideal_final_s2_residual_moment5_cap; smt().
have hc6 : 0%r <= ideal_final_s2_residual_moment6_cap by
  rewrite /ideal_final_s2_residual_moment6_cap; smt().
have hc8 : 0%r <= ideal_final_s2_residual_moment8_cap by
  rewrite /ideal_final_s2_residual_moment8_cap; smt().
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_moment2_term
  /ideal_final_s2_row_residual_re_moment3_term
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_moment4_term
  /ideal_final_s2_row_residual_re_moment5_term
  /ideal_final_s2_row_residual_re_moment6_term
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_moment8_term.
split.
+ exact (profile_weighted_moment_abs_bound
    (creal (cpow (odd_root k) j)) 2
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_moment2_at
        pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment2_cap hq2 hc2 hw hm2).
split.
+ exact (profile_weighted_moment_abs_bound
    (creal (cpow (odd_root k) j)) 3
    (ideal_final_s2_residual_moment3_at
      pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment3_cap hq3 hc3 hw hm3).
split.
+ exact (profile_weighted_moment_abs_bound
    (creal (cpow (odd_root k) j)) 4
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_moment4_at
        pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment4_cap hq4 hc4 hw hm4).
split.
+ exact (profile_weighted_moment_abs_bound
    (creal (cpow (odd_root k) j)) 5
    (Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .ideal_final_s2_residual_moment5_at
        pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment5_cap hq5 hc5 hw hm5).
split.
+ have hm6abs :
      `|Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
          .ideal_final_s2_residual_moment6_at
            pre_bp avec (ideal_final_s2_row_index row j)| <=
      ideal_final_s2_residual_moment6_cap.
  + rewrite ger0_norm 1:hm6ge.
    rewrite /ideal_final_s2_residual_moment6_cap.
    exact hm6.
  exact (profile_weighted_moment_abs_bound
    (creal (cpow (odd_root k) j)) 6
    (Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .ideal_final_s2_residual_moment6_at
        pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment6_cap hq6 hc6 hw hm6abs).
exact (profile_weighted_moment_abs_bound
  (creal (cpow (odd_root k) j)) 8
  (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment8_at
      pre_bp avec (ideal_final_s2_row_index row j))
  ideal_final_s2_residual_moment8_cap hq8 hc8 hw hm8).
qed.


lemma ideal_final_s2_row_residual_im_term_abs_bounds
    pre_bp avec row k j :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= j < 256 =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment2_cap /\
  `|ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment3_cap /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment4_cap /\
  `|ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment5_cap /\
  `|ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment6_cap /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_moment8_term pre_bp avec row k j| <=
    ideal_final_s2_residual_moment8_cap.
proof.
move=> hctx hrow hk hj.
have hj256 : 0 <= j < KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; exact hj.
have hidx := ideal_final_s2_row_index_range row j hrow hj256.
have [hm2 [hm4 hm8]] :=
  ideal_final_s2_residual_moment248_abs_bounds_at
    pre_bp avec (ideal_final_s2_row_index row j) hctx hidx.
have hm3 :=
  ideal_final_s2_residual_moment3_abs_bound_at
    pre_bp avec (ideal_final_s2_row_index row j).
have [hm5 [hm6ge hm6]] :=
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment56_bounds_at
      pre_bp avec (ideal_final_s2_row_index row j) hctx hidx.
have [_ hw] :=
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .odd_kernel_coordinate_bound1 k j hk hj.
have hq2 : 0 <= 2 by trivial.
have hq3 : 0 <= 3 by trivial.
have hq4 : 0 <= 4 by trivial.
have hq5 : 0 <= 5 by trivial.
have hq6 : 0 <= 6 by trivial.
have hq8 : 0 <= 8 by trivial.
have hc2 : 0%r <= ideal_final_s2_residual_moment2_cap by
  rewrite /ideal_final_s2_residual_moment2_cap; smt().
have hc3 : 0%r <= ideal_final_s2_residual_moment3_cap by
  rewrite /ideal_final_s2_residual_moment3_cap; smt().
have hc4 : 0%r <= ideal_final_s2_residual_moment4_cap by
  rewrite /ideal_final_s2_residual_moment4_cap; smt().
have hc5 : 0%r <= ideal_final_s2_residual_moment5_cap by
  rewrite /ideal_final_s2_residual_moment5_cap; smt().
have hc6 : 0%r <= ideal_final_s2_residual_moment6_cap by
  rewrite /ideal_final_s2_residual_moment6_cap; smt().
have hc8 : 0%r <= ideal_final_s2_residual_moment8_cap by
  rewrite /ideal_final_s2_residual_moment8_cap; smt().
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_moment2_term
  /ideal_final_s2_row_residual_im_moment3_term
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_moment4_term
  /ideal_final_s2_row_residual_im_moment5_term
  /ideal_final_s2_row_residual_im_moment6_term
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_moment8_term.
split.
+ exact (profile_weighted_moment_abs_bound
    (cimag (cpow (odd_root k) j)) 2
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_moment2_at
        pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment2_cap hq2 hc2 hw hm2).
split.
+ exact (profile_weighted_moment_abs_bound
    (cimag (cpow (odd_root k) j)) 3
    (ideal_final_s2_residual_moment3_at
      pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment3_cap hq3 hc3 hw hm3).
split.
+ exact (profile_weighted_moment_abs_bound
    (cimag (cpow (odd_root k) j)) 4
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_moment4_at
        pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment4_cap hq4 hc4 hw hm4).
split.
+ exact (profile_weighted_moment_abs_bound
    (cimag (cpow (odd_root k) j)) 5
    (Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .ideal_final_s2_residual_moment5_at
        pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment5_cap hq5 hc5 hw hm5).
split.
+ have hm6abs :
      `|Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
          .ideal_final_s2_residual_moment6_at
            pre_bp avec (ideal_final_s2_row_index row j)| <=
      ideal_final_s2_residual_moment6_cap.
  + rewrite ger0_norm 1:hm6ge.
    rewrite /ideal_final_s2_residual_moment6_cap.
    exact hm6.
  exact (profile_weighted_moment_abs_bound
    (cimag (cpow (odd_root k) j)) 6
    (Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .ideal_final_s2_residual_moment6_at
        pre_bp avec (ideal_final_s2_row_index row j))
    ideal_final_s2_residual_moment6_cap hq6 hc6 hw hm6abs).
exact (profile_weighted_moment_abs_bound
  (cimag (cpow (odd_root k) j)) 8
  (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment8_at
      pre_bp avec (ideal_final_s2_row_index row j))
  ideal_final_s2_residual_moment8_cap hq8 hc8 hw hm8).
qed.

lemma ideal_final_s2_row_residual_re_profile2_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|ideal_final_s2_row_residual_re_profile pre_bp avec row k n| <=
  ideal_final_s2_residual_profile2_envelope n.
proof.
move=> hctx hrow hk hn.
rewrite /ideal_final_s2_row_residual_re_profile.
change
  (`|BRA.big predT
      (fun j =>
        creal (cpow (odd_root k) j) ^ 2 *
        Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_moment2_at
            pre_bp avec (ideal_final_s2_row_index row j))
      (range 0 n)| <=
   ideal_final_s2_residual_profile2_envelope n).
apply
  (ler_trans
    (BRA.big predT
      (fun j =>
        `|creal (cpow (odd_root k) j) ^ 2 *
          Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
            .ideal_final_s2_residual_moment2_at
              pre_bp avec (ideal_final_s2_row_index row j)|)
      (range 0 n))).
+ exact
    (big_normr predT
      (fun j =>
        creal (cpow (odd_root k) j) ^ 2 *
        Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_moment2_at
            pre_bp avec (ideal_final_s2_row_index row j))
      (range 0 n)).
apply
  (ler_trans
    (BRA.big predT
      (fun _ : int => ideal_final_s2_residual_moment2_cap)
      (range 0 n))).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have [ht2 _] :=
    ideal_final_s2_row_residual_re_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  exact ht2.
rewrite Bigreal.sumr_const count_predT size_range /=.
rewrite /ideal_final_s2_residual_profile2_envelope.
have -> : max 0 (n - 0) = n by smt().
trivial.
qed.


lemma ideal_final_s2_row_residual_im_profile2_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|ideal_final_s2_row_residual_im_profile pre_bp avec row k n| <=
  ideal_final_s2_residual_profile2_envelope n.
proof.
move=> hctx hrow hk hn.
rewrite /ideal_final_s2_row_residual_im_profile.
change
  (`|BRA.big predT
      (fun j =>
        cimag (cpow (odd_root k) j) ^ 2 *
        Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_moment2_at
            pre_bp avec (ideal_final_s2_row_index row j))
      (range 0 n)| <=
   ideal_final_s2_residual_profile2_envelope n).
apply
  (ler_trans
    (BRA.big predT
      (fun j =>
        `|cimag (cpow (odd_root k) j) ^ 2 *
          Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
            .ideal_final_s2_residual_moment2_at
              pre_bp avec (ideal_final_s2_row_index row j)|)
      (range 0 n))).
+ exact
    (big_normr predT
      (fun j =>
        cimag (cpow (odd_root k) j) ^ 2 *
        Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_moment2_at
            pre_bp avec (ideal_final_s2_row_index row j))
      (range 0 n)).
apply
  (ler_trans
    (BRA.big predT
      (fun _ : int => ideal_final_s2_residual_moment2_cap)
      (range 0 n))).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have [ht2 _] :=
    ideal_final_s2_row_residual_im_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  exact ht2.
rewrite Bigreal.sumr_const count_predT size_range /=.
rewrite /ideal_final_s2_residual_profile2_envelope.
have -> : max 0 (n - 0) = n by smt().
trivial.
qed.


lemma ideal_final_s2_row_residual_re_profile3_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|ideal_final_s2_row_residual_re_profile3 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile3_envelope n.
proof.
move=> hctx hrow hk hn.
rewrite /ideal_final_s2_row_residual_re_profile3.
change
  (`|BRA.big predT
      (fun j =>
        creal (cpow (odd_root k) j) ^ 3 *
        ideal_final_s2_residual_moment3_at
            pre_bp avec (ideal_final_s2_row_index row j))
      (range 0 n)| <=
   ideal_final_s2_residual_profile3_envelope n).
apply
  (ler_trans
    (BRA.big predT
      (fun j =>
        `|creal (cpow (odd_root k) j) ^ 3 *
          ideal_final_s2_residual_moment3_at
              pre_bp avec (ideal_final_s2_row_index row j)|)
      (range 0 n))).
+ exact
    (big_normr predT
      (fun j =>
        creal (cpow (odd_root k) j) ^ 3 *
        ideal_final_s2_residual_moment3_at
            pre_bp avec (ideal_final_s2_row_index row j))
      (range 0 n)).
apply
  (ler_trans
    (BRA.big predT
      (fun _ : int => ideal_final_s2_residual_moment3_cap)
      (range 0 n))).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have [_ [ht3 _]] :=
    ideal_final_s2_row_residual_re_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  exact ht3.
rewrite Bigreal.sumr_const count_predT size_range /=.
rewrite /ideal_final_s2_residual_profile3_envelope.
have -> : max 0 (n - 0) = n by smt().
trivial.
qed.


lemma ideal_final_s2_row_residual_im_profile3_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|ideal_final_s2_row_residual_im_profile3 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile3_envelope n.
proof.
move=> hctx hrow hk hn.
rewrite /ideal_final_s2_row_residual_im_profile3.
change
  (`|BRA.big predT
      (fun j =>
        cimag (cpow (odd_root k) j) ^ 3 *
        ideal_final_s2_residual_moment3_at
            pre_bp avec (ideal_final_s2_row_index row j))
      (range 0 n)| <=
   ideal_final_s2_residual_profile3_envelope n).
apply
  (ler_trans
    (BRA.big predT
      (fun j =>
        `|cimag (cpow (odd_root k) j) ^ 3 *
          ideal_final_s2_residual_moment3_at
              pre_bp avec (ideal_final_s2_row_index row j)|)
      (range 0 n))).
+ exact
    (big_normr predT
      (fun j =>
        cimag (cpow (odd_root k) j) ^ 3 *
        ideal_final_s2_residual_moment3_at
            pre_bp avec (ideal_final_s2_row_index row j))
      (range 0 n)).
apply
  (ler_trans
    (BRA.big predT
      (fun _ : int => ideal_final_s2_residual_moment3_cap)
      (range 0 n))).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have [_ [ht3 _]] :=
    ideal_final_s2_row_residual_im_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  exact ht3.
rewrite Bigreal.sumr_const count_predT size_range /=.
rewrite /ideal_final_s2_residual_profile3_envelope.
have -> : max 0 (n - 0) = n by smt().
trivial.
qed.

lemma ideal_final_s2_residual_profile4_envelope_big n :
  0 <= n =>
  BRA.bigi predT
    (fun j =>
      6%r * ideal_final_s2_residual_profile2_envelope j *
        ideal_final_s2_residual_moment2_cap +
      ideal_final_s2_residual_moment4_cap)
    0 n =
  ideal_final_s2_residual_profile4_envelope n.
proof.
move=> hn.
elim/natind: n hn => [n hnle0|n hnge0 ih].
+ move=> hn0.
  have -> : n = 0 by smt().
  rewrite BRA.big_geq 1:/#.
  rewrite /ideal_final_s2_residual_profile4_envelope.
  ring.
move=> hnnext.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT ifT //.
rewrite (ih hnge0).
rewrite ideal_final_s2_residual_profile4_envelope_succ.
ring.
qed.

lemma ideal_final_s2_row_residual_re_profile4_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile4_envelope n.
proof.
move=> hctx hrow hk hn.
have hn0 : 0 <= n by smt().
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile4.
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        `|6%r *
          ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j|)
      0 n)).
+ change
    (`|BRA.big predT
        (fun j =>
          6%r *
            ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_moment2_term
                pre_bp avec row k j +
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j)
        (range 0 n)| <=
     BRA.big predT
       (fun j =>
         `|6%r *
           ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_moment2_term
               pre_bp avec row k j +
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j|)
       (range 0 n)).
  exact (big_normr predT _ (range 0 n)).
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        6%r * ideal_final_s2_residual_profile2_envelope j *
          ideal_final_s2_residual_moment2_cap +
        ideal_final_s2_residual_moment4_cap)
      0 n)).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have hjbound : 0 <= j <= 256 by smt().
  have hp2 :=
    ideal_final_s2_row_residual_re_profile2_abs_le
      pre_bp avec row k j hctx hrow hk hjbound.
  have [ht2 [_ [ht4 _]]] :=
    ideal_final_s2_row_residual_re_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  have hq2 : 0%r <= ideal_final_s2_residual_profile2_envelope j by
    have hnorm :=
      normr_ge0
        (ideal_final_s2_row_residual_re_profile pre_bp avec row k j);
    smt().
  have hc2 : 0%r <= ideal_final_s2_residual_moment2_cap by
    rewrite /ideal_final_s2_residual_moment2_cap; smt().
  have hc4 : 0%r <= ideal_final_s2_residual_moment4_cap by
    rewrite /ideal_final_s2_residual_moment4_cap; smt().
  have hmul :=
    profile_abs_scale_mul_bound 6%r
      (ideal_final_s2_row_residual_re_profile pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j)
      (ideal_final_s2_residual_profile2_envelope j)
      ideal_final_s2_residual_moment2_cap _ hq2 hc2 hp2 ht2.
  + trivial.
  exact
    (profile_abs_add_bound
      (6%r * ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j)
      (6%r * ideal_final_s2_residual_profile2_envelope j *
        ideal_final_s2_residual_moment2_cap)
      ideal_final_s2_residual_moment4_cap hmul ht4).
rewrite (ideal_final_s2_residual_profile4_envelope_big n hn0).
trivial.
qed.


lemma ideal_final_s2_row_residual_im_profile4_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile4_envelope n.
proof.
move=> hctx hrow hk hn.
have hn0 : 0 <= n by smt().
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile4.
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        `|6%r *
          ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j|)
      0 n)).
+ change
    (`|BRA.big predT
        (fun j =>
          6%r *
            ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_moment2_term
                pre_bp avec row k j +
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j)
        (range 0 n)| <=
     BRA.big predT
       (fun j =>
         `|6%r *
           ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_moment2_term
               pre_bp avec row k j +
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j|)
       (range 0 n)).
  exact (big_normr predT _ (range 0 n)).
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        6%r * ideal_final_s2_residual_profile2_envelope j *
          ideal_final_s2_residual_moment2_cap +
        ideal_final_s2_residual_moment4_cap)
      0 n)).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have hjbound : 0 <= j <= 256 by smt().
  have hp2 :=
    ideal_final_s2_row_residual_im_profile2_abs_le
      pre_bp avec row k j hctx hrow hk hjbound.
  have [ht2 [_ [ht4 _]]] :=
    ideal_final_s2_row_residual_im_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  have hq2 : 0%r <= ideal_final_s2_residual_profile2_envelope j by
    have hnorm :=
      normr_ge0
        (ideal_final_s2_row_residual_im_profile pre_bp avec row k j);
    smt().
  have hc2 : 0%r <= ideal_final_s2_residual_moment2_cap by
    rewrite /ideal_final_s2_residual_moment2_cap; smt().
  have hc4 : 0%r <= ideal_final_s2_residual_moment4_cap by
    rewrite /ideal_final_s2_residual_moment4_cap; smt().
  have hmul :=
    profile_abs_scale_mul_bound 6%r
      (ideal_final_s2_row_residual_im_profile pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j)
      (ideal_final_s2_residual_profile2_envelope j)
      ideal_final_s2_residual_moment2_cap _ hq2 hc2 hp2 ht2.
  + trivial.
  exact
    (profile_abs_add_bound
      (6%r * ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j)
      (6%r * ideal_final_s2_residual_profile2_envelope j *
        ideal_final_s2_residual_moment2_cap)
      ideal_final_s2_residual_moment4_cap hmul ht4).
rewrite (ideal_final_s2_residual_profile4_envelope_big n hn0).
trivial.
qed.

lemma ideal_final_s2_residual_profile5_envelope_big n :
  0 <= n =>
  BRA.bigi predT
    (fun j =>
      10%r * ideal_final_s2_residual_profile3_envelope j *
        ideal_final_s2_residual_moment2_cap +
      10%r * ideal_final_s2_residual_profile2_envelope j *
        ideal_final_s2_residual_moment3_cap +
      ideal_final_s2_residual_moment5_cap)
    0 n =
  ideal_final_s2_residual_profile5_envelope n.
proof.
move=> hn.
elim/natind: n hn => [n hnle0|n hnge0 ih].
+ move=> hn0.
  have -> : n = 0 by smt().
  rewrite BRA.big_geq 1:/#.
  rewrite /ideal_final_s2_residual_profile5_envelope.
  ring.
move=> hnnext.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT ifT //.
rewrite (ih hnge0).
rewrite ideal_final_s2_residual_profile5_envelope_succ.
ring.
qed.

lemma ideal_final_s2_residual_profile6_envelope_big n :
  0 <= n =>
  BRA.bigi predT
    (fun j =>
      15%r * ideal_final_s2_residual_profile4_envelope j *
        ideal_final_s2_residual_moment2_cap +
      20%r * ideal_final_s2_residual_profile3_envelope j *
        ideal_final_s2_residual_moment3_cap +
      15%r * ideal_final_s2_residual_profile2_envelope j *
        ideal_final_s2_residual_moment4_cap +
      ideal_final_s2_residual_moment6_cap)
    0 n =
  ideal_final_s2_residual_profile6_envelope n.
proof.
move=> hn.
elim/natind: n hn => [n hnle0|n hnge0 ih].
+ move=> hn0.
  have -> : n = 0 by smt().
  rewrite BRA.big_geq 1:/#.
  rewrite /ideal_final_s2_residual_profile6_envelope.
  ring.
move=> hnnext.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT ifT //.
rewrite (ih hnge0).
rewrite ideal_final_s2_residual_profile6_envelope_succ.
ring.
qed.

lemma ideal_final_s2_residual_profile8_envelope_big n :
  0 <= n =>
  BRA.bigi predT
    (fun j =>
      28%r * ideal_final_s2_residual_profile6_envelope j *
        ideal_final_s2_residual_moment2_cap +
      56%r * ideal_final_s2_residual_profile5_envelope j *
        ideal_final_s2_residual_moment3_cap +
      70%r * ideal_final_s2_residual_profile4_envelope j *
        ideal_final_s2_residual_moment4_cap +
      56%r * ideal_final_s2_residual_profile3_envelope j *
        ideal_final_s2_residual_moment5_cap +
      28%r * ideal_final_s2_residual_profile2_envelope j *
        ideal_final_s2_residual_moment6_cap +
      ideal_final_s2_residual_moment8_cap)
    0 n =
  ideal_final_s2_residual_profile8_envelope n.
proof.
move=> hn.
elim/natind: n hn => [n hnle0|n hnge0 ih].
+ move=> hn0.
  have -> : n = 0 by smt().
  rewrite BRA.big_geq 1:/#.
  rewrite /ideal_final_s2_residual_profile8_envelope.
  ring.
move=> hnnext.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT ifT //.
rewrite (ih hnge0).
rewrite ideal_final_s2_residual_profile8_envelope_succ.
ring.
qed.

lemma profile5_step_abs_bound
    (p3 p2 t2 t3 t5 q3 q2 : real) :
  0%r <= q3 => 0%r <= q2 =>
  `|p3| <= q3 => `|p2| <= q2 =>
  `|t2| <= ideal_final_s2_residual_moment2_cap =>
  `|t3| <= ideal_final_s2_residual_moment3_cap =>
  `|t5| <= ideal_final_s2_residual_moment5_cap =>
  `|10%r * p3 * t2 + 10%r * p2 * t3 + t5| <=
  10%r * q3 * ideal_final_s2_residual_moment2_cap +
  10%r * q2 * ideal_final_s2_residual_moment3_cap +
  ideal_final_s2_residual_moment5_cap.
proof.
move=> hq3 hq2 hp3 hp2 ht2 ht3 ht5.
have hc2 : 0%r <= ideal_final_s2_residual_moment2_cap by
  rewrite /ideal_final_s2_residual_moment2_cap; smt().
have hc3 : 0%r <= ideal_final_s2_residual_moment3_cap by
  rewrite /ideal_final_s2_residual_moment3_cap; smt().
have ha :=
  profile_abs_scale_mul_bound 10%r p3 t2 q3
    ideal_final_s2_residual_moment2_cap _ hq3 hc2 hp3 ht2.
+ trivial.
have hb :=
  profile_abs_scale_mul_bound 10%r p2 t3 q2
    ideal_final_s2_residual_moment3_cap _ hq2 hc3 hp2 ht3.
+ trivial.
exact
  (profile_abs_add3_bound
    (10%r * p3 * t2) (10%r * p2 * t3) t5
    (10%r * q3 * ideal_final_s2_residual_moment2_cap)
    (10%r * q2 * ideal_final_s2_residual_moment3_cap)
    ideal_final_s2_residual_moment5_cap ha hb ht5).
qed.

lemma profile6_step_abs_bound
    (p4 p3 p2 t2 t3 t4 t6 q4 q3 q2 : real) :
  0%r <= q4 => 0%r <= q3 => 0%r <= q2 =>
  `|p4| <= q4 => `|p3| <= q3 => `|p2| <= q2 =>
  `|t2| <= ideal_final_s2_residual_moment2_cap =>
  `|t3| <= ideal_final_s2_residual_moment3_cap =>
  `|t4| <= ideal_final_s2_residual_moment4_cap =>
  `|t6| <= ideal_final_s2_residual_moment6_cap =>
  `|15%r * p4 * t2 + 20%r * p3 * t3 +
    15%r * p2 * t4 + t6| <=
  15%r * q4 * ideal_final_s2_residual_moment2_cap +
  20%r * q3 * ideal_final_s2_residual_moment3_cap +
  15%r * q2 * ideal_final_s2_residual_moment4_cap +
  ideal_final_s2_residual_moment6_cap.
proof.
move=> hq4 hq3 hq2 hp4 hp3 hp2 ht2 ht3 ht4 ht6.
have hc2 : 0%r <= ideal_final_s2_residual_moment2_cap by
  rewrite /ideal_final_s2_residual_moment2_cap; smt().
have hc3 : 0%r <= ideal_final_s2_residual_moment3_cap by
  rewrite /ideal_final_s2_residual_moment3_cap; smt().
have hc4 : 0%r <= ideal_final_s2_residual_moment4_cap by
  rewrite /ideal_final_s2_residual_moment4_cap; smt().
have ha := profile_abs_scale_mul_bound 15%r p4 t2 q4
  ideal_final_s2_residual_moment2_cap _ hq4 hc2 hp4 ht2.
+ trivial.
have hb := profile_abs_scale_mul_bound 20%r p3 t3 q3
  ideal_final_s2_residual_moment3_cap _ hq3 hc3 hp3 ht3.
+ trivial.
have hc := profile_abs_scale_mul_bound 15%r p2 t4 q2
  ideal_final_s2_residual_moment4_cap _ hq2 hc4 hp2 ht4.
+ trivial.
exact
  (profile_abs_add4_bound
    (15%r * p4 * t2) (20%r * p3 * t3)
    (15%r * p2 * t4) t6
    (15%r * q4 * ideal_final_s2_residual_moment2_cap)
    (20%r * q3 * ideal_final_s2_residual_moment3_cap)
    (15%r * q2 * ideal_final_s2_residual_moment4_cap)
    ideal_final_s2_residual_moment6_cap ha hb hc ht6).
qed.

lemma profile8_step_abs_bound
    (p6 p5 p4 p3 p2 t2 t3 t4 t5 t6 t8 q6 q5 q4 q3 q2 : real) :
  0%r <= q6 => 0%r <= q5 => 0%r <= q4 =>
  0%r <= q3 => 0%r <= q2 =>
  `|p6| <= q6 => `|p5| <= q5 => `|p4| <= q4 =>
  `|p3| <= q3 => `|p2| <= q2 =>
  `|t2| <= ideal_final_s2_residual_moment2_cap =>
  `|t3| <= ideal_final_s2_residual_moment3_cap =>
  `|t4| <= ideal_final_s2_residual_moment4_cap =>
  `|t5| <= ideal_final_s2_residual_moment5_cap =>
  `|t6| <= ideal_final_s2_residual_moment6_cap =>
  `|t8| <= ideal_final_s2_residual_moment8_cap =>
  `|28%r * p6 * t2 + 56%r * p5 * t3 + 70%r * p4 * t4 +
    56%r * p3 * t5 + 28%r * p2 * t6 + t8| <=
  28%r * q6 * ideal_final_s2_residual_moment2_cap +
  56%r * q5 * ideal_final_s2_residual_moment3_cap +
  70%r * q4 * ideal_final_s2_residual_moment4_cap +
  56%r * q3 * ideal_final_s2_residual_moment5_cap +
  28%r * q2 * ideal_final_s2_residual_moment6_cap +
  ideal_final_s2_residual_moment8_cap.
proof.
move=> hq6 hq5 hq4 hq3 hq2 hp6 hp5 hp4 hp3 hp2
        ht2 ht3 ht4 ht5 ht6 ht8.
have hc2 : 0%r <= ideal_final_s2_residual_moment2_cap by
  rewrite /ideal_final_s2_residual_moment2_cap; smt().
have hc3 : 0%r <= ideal_final_s2_residual_moment3_cap by
  rewrite /ideal_final_s2_residual_moment3_cap; smt().
have hc4 : 0%r <= ideal_final_s2_residual_moment4_cap by
  rewrite /ideal_final_s2_residual_moment4_cap; smt().
have hc5 : 0%r <= ideal_final_s2_residual_moment5_cap by
  rewrite /ideal_final_s2_residual_moment5_cap; smt().
have hc6 : 0%r <= ideal_final_s2_residual_moment6_cap by
  rewrite /ideal_final_s2_residual_moment6_cap; smt().
have ha := profile_abs_scale_mul_bound 28%r p6 t2 q6
  ideal_final_s2_residual_moment2_cap _ hq6 hc2 hp6 ht2.
+ trivial.
have hb := profile_abs_scale_mul_bound 56%r p5 t3 q5
  ideal_final_s2_residual_moment3_cap _ hq5 hc3 hp5 ht3.
+ trivial.
have hc := profile_abs_scale_mul_bound 70%r p4 t4 q4
  ideal_final_s2_residual_moment4_cap _ hq4 hc4 hp4 ht4.
+ trivial.
have hd := profile_abs_scale_mul_bound 56%r p3 t5 q3
  ideal_final_s2_residual_moment5_cap _ hq3 hc5 hp3 ht5.
+ trivial.
have he := profile_abs_scale_mul_bound 28%r p2 t6 q2
  ideal_final_s2_residual_moment6_cap _ hq2 hc6 hp2 ht6.
+ trivial.
exact
  (profile_abs_add6_bound
    (28%r * p6 * t2) (56%r * p5 * t3) (70%r * p4 * t4)
    (56%r * p3 * t5) (28%r * p2 * t6) t8
    (28%r * q6 * ideal_final_s2_residual_moment2_cap)
    (56%r * q5 * ideal_final_s2_residual_moment3_cap)
    (70%r * q4 * ideal_final_s2_residual_moment4_cap)
    (56%r * q3 * ideal_final_s2_residual_moment5_cap)
    (28%r * q2 * ideal_final_s2_residual_moment6_cap)
    ideal_final_s2_residual_moment8_cap ha hb hc hd he ht8).
qed.

lemma ideal_final_s2_row_residual_re_profile5_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|ideal_final_s2_row_residual_re_profile5 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile5_envelope n.
proof.
move=> hctx hrow hk hn.
have hn0 : 0 <= n by smt().
rewrite /ideal_final_s2_row_residual_re_profile5.
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        `|10%r * ideal_final_s2_row_residual_re_profile3
            pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
          10%r * ideal_final_s2_row_residual_re_profile
            pre_bp avec row k j *
            ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
          ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j|)
      0 n)).
+ change
    (`|BRA.big predT
        (fun j =>
          10%r * ideal_final_s2_row_residual_re_profile3
            pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
          10%r * ideal_final_s2_row_residual_re_profile
            pre_bp avec row k j *
            ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
          ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j)
        (range 0 n)| <=
     BRA.big predT
       (fun j =>
         `|10%r * ideal_final_s2_row_residual_re_profile3
           pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
         10%r * ideal_final_s2_row_residual_re_profile
           pre_bp avec row k j *
           ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
         ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j|)
       (range 0 n)).
  exact (big_normr predT _ (range 0 n)).
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        10%r * ideal_final_s2_residual_profile3_envelope j *
          ideal_final_s2_residual_moment2_cap +
        10%r * ideal_final_s2_residual_profile2_envelope j *
          ideal_final_s2_residual_moment3_cap +
        ideal_final_s2_residual_moment5_cap)
      0 n)).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have hjbound : 0 <= j <= 256 by smt().
  have hp3 := ideal_final_s2_row_residual_re_profile3_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp2 := ideal_final_s2_row_residual_re_profile2_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have [ht2 [ht3 [_ [ht5 _]]]] :=
    ideal_final_s2_row_residual_re_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  have hq3 : 0%r <= ideal_final_s2_residual_profile3_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j);
    smt().
  have hq2 : 0%r <= ideal_final_s2_residual_profile2_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_re_profile pre_bp avec row k j);
    smt().
  exact
    (profile5_step_abs_bound
      (ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_profile pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j)
      (ideal_final_s2_residual_profile3_envelope j)
      (ideal_final_s2_residual_profile2_envelope j)
      hq3 hq2 hp3 hp2 ht2 ht3 ht5).
rewrite (ideal_final_s2_residual_profile5_envelope_big n hn0).
trivial.
qed.


lemma ideal_final_s2_row_residual_im_profile5_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|ideal_final_s2_row_residual_im_profile5 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile5_envelope n.
proof.
move=> hctx hrow hk hn.
have hn0 : 0 <= n by smt().
rewrite /ideal_final_s2_row_residual_im_profile5.
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        `|10%r * ideal_final_s2_row_residual_im_profile3
            pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
          10%r * ideal_final_s2_row_residual_im_profile
            pre_bp avec row k j *
            ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
          ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j|)
      0 n)).
+ change
    (`|BRA.big predT
        (fun j =>
          10%r * ideal_final_s2_row_residual_im_profile3
            pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
          10%r * ideal_final_s2_row_residual_im_profile
            pre_bp avec row k j *
            ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
          ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j)
        (range 0 n)| <=
     BRA.big predT
       (fun j =>
         `|10%r * ideal_final_s2_row_residual_im_profile3
           pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
         10%r * ideal_final_s2_row_residual_im_profile
           pre_bp avec row k j *
           ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
         ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j|)
       (range 0 n)).
  exact (big_normr predT _ (range 0 n)).
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        10%r * ideal_final_s2_residual_profile3_envelope j *
          ideal_final_s2_residual_moment2_cap +
        10%r * ideal_final_s2_residual_profile2_envelope j *
          ideal_final_s2_residual_moment3_cap +
        ideal_final_s2_residual_moment5_cap)
      0 n)).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have hjbound : 0 <= j <= 256 by smt().
  have hp3 := ideal_final_s2_row_residual_im_profile3_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp2 := ideal_final_s2_row_residual_im_profile2_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have [ht2 [ht3 [_ [ht5 _]]]] :=
    ideal_final_s2_row_residual_im_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  have hq3 : 0%r <= ideal_final_s2_residual_profile3_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j);
    smt().
  have hq2 : 0%r <= ideal_final_s2_residual_profile2_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_im_profile pre_bp avec row k j);
    smt().
  exact
    (profile5_step_abs_bound
      (ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_profile pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j)
      (ideal_final_s2_residual_profile3_envelope j)
      (ideal_final_s2_residual_profile2_envelope j)
      hq3 hq2 hp3 hp2 ht2 ht3 ht5).
rewrite (ideal_final_s2_residual_profile5_envelope_big n hn0).
trivial.
qed.

lemma ideal_final_s2_row_residual_re_profile6_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|ideal_final_s2_row_residual_re_profile6 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile6_envelope n.
proof.
move=> hctx hrow hk hn.
have hn0 : 0 <= n by smt().
rewrite /ideal_final_s2_row_residual_re_profile6.
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        `|15%r *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
        20%r * ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j *
          ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
        15%r * ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j +
        ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j|)
      0 n)).
+ change
    (`|BRA.big predT
        (fun j =>
          15%r *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
          20%r * ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j *
            ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
          15%r * ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j +
          ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j)
        (range 0 n)| <=
     BRA.big predT
       (fun j =>
         `|15%r *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
         20%r * ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j *
           ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
         15%r * ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j +
         ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j|)
       (range 0 n)).
  exact (big_normr predT _ (range 0 n)).
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        15%r * ideal_final_s2_residual_profile4_envelope j *
          ideal_final_s2_residual_moment2_cap +
        20%r * ideal_final_s2_residual_profile3_envelope j *
          ideal_final_s2_residual_moment3_cap +
        15%r * ideal_final_s2_residual_profile2_envelope j *
          ideal_final_s2_residual_moment4_cap +
        ideal_final_s2_residual_moment6_cap)
      0 n)).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have hjbound : 0 <= j <= 256 by smt().
  have hp4 := ideal_final_s2_row_residual_re_profile4_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp3 := ideal_final_s2_row_residual_re_profile3_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp2 := ideal_final_s2_row_residual_re_profile2_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have [ht2 [ht3 [ht4 [_ [ht6 _]]]]] :=
    ideal_final_s2_row_residual_re_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  have hq4 : 0%r <= ideal_final_s2_residual_profile4_envelope j by
    have hnorm := normr_ge0
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j);
    smt().
  have hq3 : 0%r <= ideal_final_s2_residual_profile3_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j);
    smt().
  have hq2 : 0%r <= ideal_final_s2_residual_profile2_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_re_profile pre_bp avec row k j);
    smt().
  exact
    (profile6_step_abs_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_profile pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j)
      (ideal_final_s2_residual_profile4_envelope j)
      (ideal_final_s2_residual_profile3_envelope j)
      (ideal_final_s2_residual_profile2_envelope j)
      hq4 hq3 hq2 hp4 hp3 hp2 ht2 ht3 ht4 ht6).
rewrite (ideal_final_s2_residual_profile6_envelope_big n hn0).
trivial.
qed.


lemma ideal_final_s2_row_residual_im_profile6_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|ideal_final_s2_row_residual_im_profile6 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile6_envelope n.
proof.
move=> hctx hrow hk hn.
have hn0 : 0 <= n by smt().
rewrite /ideal_final_s2_row_residual_im_profile6.
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        `|15%r *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
        20%r * ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j *
          ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
        15%r * ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j +
        ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j|)
      0 n)).
+ change
    (`|BRA.big predT
        (fun j =>
          15%r *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
          20%r * ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j *
            ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
          15%r * ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j +
          ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j)
        (range 0 n)| <=
     BRA.big predT
       (fun j =>
         `|15%r *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
         20%r * ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j *
           ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
         15%r * ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j +
         ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j|)
       (range 0 n)).
  exact (big_normr predT _ (range 0 n)).
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        15%r * ideal_final_s2_residual_profile4_envelope j *
          ideal_final_s2_residual_moment2_cap +
        20%r * ideal_final_s2_residual_profile3_envelope j *
          ideal_final_s2_residual_moment3_cap +
        15%r * ideal_final_s2_residual_profile2_envelope j *
          ideal_final_s2_residual_moment4_cap +
        ideal_final_s2_residual_moment6_cap)
      0 n)).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have hjbound : 0 <= j <= 256 by smt().
  have hp4 := ideal_final_s2_row_residual_im_profile4_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp3 := ideal_final_s2_row_residual_im_profile3_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp2 := ideal_final_s2_row_residual_im_profile2_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have [ht2 [ht3 [ht4 [_ [ht6 _]]]]] :=
    ideal_final_s2_row_residual_im_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  have hq4 : 0%r <= ideal_final_s2_residual_profile4_envelope j by
    have hnorm := normr_ge0
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j);
    smt().
  have hq3 : 0%r <= ideal_final_s2_residual_profile3_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j);
    smt().
  have hq2 : 0%r <= ideal_final_s2_residual_profile2_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_im_profile pre_bp avec row k j);
    smt().
  exact
    (profile6_step_abs_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_profile pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j)
      (ideal_final_s2_residual_profile4_envelope j)
      (ideal_final_s2_residual_profile3_envelope j)
      (ideal_final_s2_residual_profile2_envelope j)
      hq4 hq3 hq2 hp4 hp3 hp2 ht2 ht3 ht4 ht6).
rewrite (ideal_final_s2_residual_profile6_envelope_big n hn0).
trivial.
qed.

lemma ideal_final_s2_row_residual_re_profile8_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile8_envelope n.
proof.
move=> hctx hrow hk hn.
have hn0 : 0 <= n by smt().
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8.
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        `|28%r * ideal_final_s2_row_residual_re_profile6 pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
        56%r * ideal_final_s2_row_residual_re_profile5 pre_bp avec row k j *
          ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
        70%r *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j +
        56%r * ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j *
          ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j +
        28%r * ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
          ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j +
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_re_moment8_term pre_bp avec row k j|)
      0 n)).
+ change
    (`|BRA.big predT
        (fun j =>
          28%r * ideal_final_s2_row_residual_re_profile6 pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
          56%r * ideal_final_s2_row_residual_re_profile5 pre_bp avec row k j *
            ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
          70%r *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j +
          56%r * ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j *
            ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j +
          28%r * ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
            ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j +
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
            .ideal_final_s2_row_residual_re_moment8_term pre_bp avec row k j)
        (range 0 n)| <=
     BRA.big predT
       (fun j =>
         `|28%r * ideal_final_s2_row_residual_re_profile6 pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
         56%r * ideal_final_s2_row_residual_re_profile5 pre_bp avec row k j *
           ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
         70%r *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j +
         56%r * ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j *
           ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j +
         28%r * ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
           ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j +
         Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
           .ideal_final_s2_row_residual_re_moment8_term pre_bp avec row k j|)
       (range 0 n)).
  exact (big_normr predT _ (range 0 n)).
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        28%r * ideal_final_s2_residual_profile6_envelope j *
          ideal_final_s2_residual_moment2_cap +
        56%r * ideal_final_s2_residual_profile5_envelope j *
          ideal_final_s2_residual_moment3_cap +
        70%r * ideal_final_s2_residual_profile4_envelope j *
          ideal_final_s2_residual_moment4_cap +
        56%r * ideal_final_s2_residual_profile3_envelope j *
          ideal_final_s2_residual_moment5_cap +
        28%r * ideal_final_s2_residual_profile2_envelope j *
          ideal_final_s2_residual_moment6_cap +
        ideal_final_s2_residual_moment8_cap)
      0 n)).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have hjbound : 0 <= j <= 256 by smt().
  have hp6 := ideal_final_s2_row_residual_re_profile6_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp5 := ideal_final_s2_row_residual_re_profile5_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp4 := ideal_final_s2_row_residual_re_profile4_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp3 := ideal_final_s2_row_residual_re_profile3_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp2 := ideal_final_s2_row_residual_re_profile2_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have [ht2 [ht3 [ht4 [ht5 [ht6 ht8]]]]] :=
    ideal_final_s2_row_residual_re_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  have hq6 : 0%r <= ideal_final_s2_residual_profile6_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_re_profile6 pre_bp avec row k j);
    smt().
  have hq5 : 0%r <= ideal_final_s2_residual_profile5_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_re_profile5 pre_bp avec row k j);
    smt().
  have hq4 : 0%r <= ideal_final_s2_residual_profile4_envelope j by
    have hnorm := normr_ge0
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j);
    smt().
  have hq3 : 0%r <= ideal_final_s2_residual_profile3_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j);
    smt().
  have hq2 : 0%r <= ideal_final_s2_residual_profile2_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_re_profile pre_bp avec row k j);
    smt().
  exact
    (profile8_step_abs_bound
      (ideal_final_s2_row_residual_re_profile6 pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_profile5 pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_profile pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment8_term pre_bp avec row k j)
      (ideal_final_s2_residual_profile6_envelope j)
      (ideal_final_s2_residual_profile5_envelope j)
      (ideal_final_s2_residual_profile4_envelope j)
      (ideal_final_s2_residual_profile3_envelope j)
      (ideal_final_s2_residual_profile2_envelope j)
      hq6 hq5 hq4 hq3 hq2 hp6 hp5 hp4 hp3 hp2
      ht2 ht3 ht4 ht5 ht6 ht8).
rewrite (ideal_final_s2_residual_profile8_envelope_big n hn0).
trivial.
qed.


lemma ideal_final_s2_row_residual_im_profile8_abs_le
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0 <= n <= 256 =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n| <=
  ideal_final_s2_residual_profile8_envelope n.
proof.
move=> hctx hrow hk hn.
have hn0 : 0 <= n by smt().
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8.
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        `|28%r * ideal_final_s2_row_residual_im_profile6 pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
        56%r * ideal_final_s2_row_residual_im_profile5 pre_bp avec row k j *
          ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
        70%r *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j *
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
            .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j +
        56%r * ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j *
          ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j +
        28%r * ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
          ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j +
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_im_moment8_term pre_bp avec row k j|)
      0 n)).
+ change
    (`|BRA.big predT
        (fun j =>
          28%r * ideal_final_s2_row_residual_im_profile6 pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
          56%r * ideal_final_s2_row_residual_im_profile5 pre_bp avec row k j *
            ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
          70%r *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j *
            Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
              .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j +
          56%r * ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j *
            ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j +
          28%r * ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
            ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j +
          Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
            .ideal_final_s2_row_residual_im_moment8_term pre_bp avec row k j)
        (range 0 n)| <=
     BRA.big predT
       (fun j =>
         `|28%r * ideal_final_s2_row_residual_im_profile6 pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
         56%r * ideal_final_s2_row_residual_im_profile5 pre_bp avec row k j *
           ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
         70%r *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j *
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
             .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j +
         56%r * ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j *
           ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j +
         28%r * ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
           ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j +
         Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
           .ideal_final_s2_row_residual_im_moment8_term pre_bp avec row k j|)
       (range 0 n)).
  exact (big_normr predT _ (range 0 n)).
apply
  (ler_trans
    (BRA.bigi predT
      (fun j =>
        28%r * ideal_final_s2_residual_profile6_envelope j *
          ideal_final_s2_residual_moment2_cap +
        56%r * ideal_final_s2_residual_profile5_envelope j *
          ideal_final_s2_residual_moment3_cap +
        70%r * ideal_final_s2_residual_profile4_envelope j *
          ideal_final_s2_residual_moment4_cap +
        56%r * ideal_final_s2_residual_profile3_envelope j *
          ideal_final_s2_residual_moment5_cap +
        28%r * ideal_final_s2_residual_profile2_envelope j *
          ideal_final_s2_residual_moment6_cap +
        ideal_final_s2_residual_moment8_cap)
      0 n)).
+ apply ler_sum_seq => j hj _.
  rewrite mem_range in hj.
  have hj256 : 0 <= j < 256 by smt().
  have hjbound : 0 <= j <= 256 by smt().
  have hp6 := ideal_final_s2_row_residual_im_profile6_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp5 := ideal_final_s2_row_residual_im_profile5_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp4 := ideal_final_s2_row_residual_im_profile4_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp3 := ideal_final_s2_row_residual_im_profile3_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have hp2 := ideal_final_s2_row_residual_im_profile2_abs_le
    pre_bp avec row k j hctx hrow hk hjbound.
  have [ht2 [ht3 [ht4 [ht5 [ht6 ht8]]]]] :=
    ideal_final_s2_row_residual_im_term_abs_bounds
      pre_bp avec row k j hctx hrow hk hj256.
  have hq6 : 0%r <= ideal_final_s2_residual_profile6_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_im_profile6 pre_bp avec row k j);
    smt().
  have hq5 : 0%r <= ideal_final_s2_residual_profile5_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_im_profile5 pre_bp avec row k j);
    smt().
  have hq4 : 0%r <= ideal_final_s2_residual_profile4_envelope j by
    have hnorm := normr_ge0
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j);
    smt().
  have hq3 : 0%r <= ideal_final_s2_residual_profile3_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j);
    smt().
  have hq2 : 0%r <= ideal_final_s2_residual_profile2_envelope j by
    have hnorm := normr_ge0
      (ideal_final_s2_row_residual_im_profile pre_bp avec row k j);
    smt().
  exact
    (profile8_step_abs_bound
      (ideal_final_s2_row_residual_im_profile6 pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_profile5 pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_profile pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j)
      (ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment8_term pre_bp avec row k j)
      (ideal_final_s2_residual_profile6_envelope j)
      (ideal_final_s2_residual_profile5_envelope j)
      (ideal_final_s2_residual_profile4_envelope j)
      (ideal_final_s2_residual_profile3_envelope j)
      (ideal_final_s2_residual_profile2_envelope j)
      hq6 hq5 hq4 hq3 hq2 hp6 hp5 hp4 hp3 hp2
      ht2 ht3 ht4 ht5 ht6 ht8).
rewrite (ideal_final_s2_residual_profile8_envelope_big n hn0).
trivial.
qed.

lemma ideal_final_s2_row_residual_re_profile8_256_abs_le
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256| <=
  49301448283783168%r / 2187%r.
proof.
move=> hctx hrow hk.
have h := ideal_final_s2_row_residual_re_profile8_abs_le
  pre_bp avec row k 256 hctx hrow hk _.
+ smt().
rewrite ideal_final_s2_residual_profile8_envelope_256_exact in h.
exact h.
qed.

lemma ideal_final_s2_row_residual_im_profile8_256_abs_le
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256| <=
  49301448283783168%r / 2187%r.
proof.
move=> hctx hrow hk.
have h := ideal_final_s2_row_residual_im_profile8_abs_le
  pre_bp avec row k 256 hctx hrow hk _.
+ smt().
rewrite ideal_final_s2_residual_profile8_envelope_256_exact in h.
exact h.
qed.

lemma ideal_final_s2_row_residual_profile8_256_le
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 <=
    49301448283783168%r / 2187%r /\
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 <=
    49301448283783168%r / 2187%r.
proof.
move=> hctx hrow hk.
have hre := ideal_final_s2_row_residual_re_profile8_256_abs_le
  pre_bp avec row k hctx hrow hk.
have him := ideal_final_s2_row_residual_im_profile8_256_abs_le
  pre_bp avec row k hctx hrow hk.
split.
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
       .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact hre.
apply (ler_trans
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
     .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256|).
+ exact (ler_norm _).
exact him.
qed.


end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze.
