require import AllCore IntDiv Real Ring StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23MatrixSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze.

import RealOrder.
import
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze.

(* This file extends the fixed-context scalar finalized-[s2] profile from the
   existing centered moments to exact fifth and sixth moments, then lifts
   those values back to active array indices and residual-coordinate aliases.
   It does not start any FFT recurrence, prove random-context laws, or claim
   any tail probability. *)

op ideal_final_s2_centered_moment5 (b a : W32.t) : real =
  ((((math_output b a (-1))%r - ideal_final_s2_mean b a)^5) +
   (((math_output b a 0)%r - ideal_final_s2_mean b a)^5) +
   (((math_output b a 1)%r - ideal_final_s2_mean b a)^5)) / 3%r.

op ideal_final_s2_centered_moment6 (b a : W32.t) : real =
  ((((math_output b a (-1))%r - ideal_final_s2_mean b a)^6) +
   (((math_output b a 0)%r - ideal_final_s2_mean b a)^6) +
   (((math_output b a 1)%r - ideal_final_s2_mean b a)^6)) / 3%r.

lemma moments56_rho0 b a :
  ideal_final_s2_class_rho0 b a =>
  ideal_final_s2_centered_moment5 b a = -10%r / 243%r /\
  ideal_final_s2_centered_moment6 b a = 22%r / 729%r.
proof.
move=> hclass.
have hmean := mean_rho0 b a hclass.
have [hm1 [h0 h1]] := math_output_rho0_triple b a hclass.
rewrite /ideal_final_s2_centered_moment5
        /ideal_final_s2_centered_moment6
        hm1 h0 h1 hmean.
split; field; trivial.
qed.

lemma moments56_rhoq1 b a :
  ideal_final_s2_class_rhoq1 b a =>
  ideal_final_s2_centered_moment5 b a = 10%r / 243%r /\
  ideal_final_s2_centered_moment6 b a = 22%r / 729%r.
proof.
move=> hclass.
have hmean := mean_rhoq1 b a hclass.
have [hm1 [h0 h1]] := math_output_rhoq1_triple b a hclass.
rewrite /ideal_final_s2_centered_moment5
        /ideal_final_s2_centered_moment6
        hm1 h0 h1 hmean.
split; field; trivial.
qed.

lemma moments56_mod0 b a :
  ideal_final_s2_class_mod0 b a =>
  ideal_final_s2_centered_moment5 b a = 0%r /\
  ideal_final_s2_centered_moment6 b a = 0%r.
proof.
move=> hclass.
have hmean := mean_mod0 b a hclass.
have [hm1 [h0 h1]] := math_output_mod0_triple b a hclass.
rewrite /ideal_final_s2_centered_moment5
        /ideal_final_s2_centered_moment6
        hm1 h0 h1 hmean.
split; field; trivial.
qed.

lemma moments56_mod1 b a :
  ideal_final_s2_class_mod1 b a =>
  ideal_final_s2_centered_moment5 b a = 320%r / 243%r /\
  ideal_final_s2_centered_moment6 b a = 1408%r / 729%r.
proof.
move=> hclass.
have hmean := mean_mod1 b a hclass.
have [hm1 [h0 h1]] := math_output_mod1_triple b a hclass.
rewrite /ideal_final_s2_centered_moment5
        /ideal_final_s2_centered_moment6
        hm1 h0 h1 hmean.
split; field; trivial.
qed.

lemma moments56_mod2 b a :
  ideal_final_s2_class_mod2 b a =>
  ideal_final_s2_centered_moment5 b a = 0%r /\
  ideal_final_s2_centered_moment6 b a = 128%r / 3%r.
proof.
move=> hclass.
have hmean := mean_mod2 b a hclass.
have [hm1 [h0 h1]] := math_output_mod2_triple b a hclass.
rewrite /ideal_final_s2_centered_moment5
        /ideal_final_s2_centered_moment6
        hm1 h0 h1 hmean.
split; field; trivial.
qed.

lemma moments56_mod3 b a :
  ideal_final_s2_class_mod3 b a =>
  ideal_final_s2_centered_moment5 b a = -320%r / 243%r /\
  ideal_final_s2_centered_moment6 b a = 1408%r / 729%r.
proof.
move=> hclass.
have hmean := mean_mod3 b a hclass.
have [hm1 [h0 h1]] := math_output_mod3_triple b a hclass.
rewrite /ideal_final_s2_centered_moment5
        /ideal_final_s2_centered_moment6
        hm1 h0 h1 hmean.
split; field; trivial.
qed.

lemma ideal_final_s2_centered_moment5_sign_profile b a :
  context_valid b a =>
  (ideal_final_s2_class_rho0 b a =>
     ideal_final_s2_centered_moment5 b a = -10%r / 243%r) /\
  (ideal_final_s2_class_rhoq1 b a =>
     ideal_final_s2_centered_moment5 b a = 10%r / 243%r) /\
  (ideal_final_s2_class_mod0 b a =>
     ideal_final_s2_centered_moment5 b a = 0%r) /\
  (ideal_final_s2_class_mod1 b a =>
     ideal_final_s2_centered_moment5 b a = 320%r / 243%r) /\
  (ideal_final_s2_class_mod2 b a =>
     ideal_final_s2_centered_moment5 b a = 0%r) /\
  (ideal_final_s2_class_mod3 b a =>
     ideal_final_s2_centered_moment5 b a = -320%r / 243%r).
proof.
move=> _.
split; first by move=> h; have hm := moments56_rho0 b a h; smt().
split; first by move=> h; have hm := moments56_rhoq1 b a h; smt().
split; first by move=> h; have hm := moments56_mod0 b a h; smt().
split; first by move=> h; have hm := moments56_mod1 b a h; smt().
split; first by move=> h; have hm := moments56_mod2 b a h; smt().
by move=> h; have hm := moments56_mod3 b a h; smt().
qed.

lemma ideal_final_s2_centered_moment56_bounds b a :
  context_valid b a =>
  `|ideal_final_s2_centered_moment5 b a| <= 320%r / 243%r /\
  0%r <= ideal_final_s2_centered_moment6 b a /\
  ideal_final_s2_centered_moment6 b a <= 128%r / 3%r.
proof.
move=> _.
have hexh := ideal_final_s2_class_exhaustive b a.
move: hexh => [h0 | [h1 | [h2 | [h3 | [h4 | h5]]]]].
+ have hm := moments56_rho0 b a h0.
   move: hm => [h5m h6m].
   rewrite h5m h6m normrN.
   by rewrite ger0_norm 1:/#; smt().
+ have hm := moments56_rhoq1 b a h1.
   move: hm => [h5m h6m].
   rewrite h5m h6m.
   by rewrite ger0_norm 1:/#; smt().
+ have hm := moments56_mod0 b a h2.
   move: hm => [h5m h6m].
   rewrite h5m h6m normr0.
   smt().
+ have hm := moments56_mod1 b a h3.
   move: hm => [h5m h6m].
   rewrite h5m h6m.
   by rewrite ger0_norm 1:/#; smt().
+ have hm := moments56_mod2 b a h4.
   move: hm => [h5m h6m].
   rewrite h5m h6m normr0.
   smt().
have hm := moments56_mod3 b a h5.
move: hm => [h5m h6m].
rewrite h5m h6m normrN.
by rewrite ger0_norm 1:/#; smt().
qed.

op ideal_final_s2_centered_moment5_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  ideal_final_s2_centered_moment5
    (BArray8192.get32 pre_bp i)
    (BArray8192.get32 avec i).

op ideal_final_s2_centered_moment6_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  ideal_final_s2_centered_moment6
    (BArray8192.get32 pre_bp i)
    (BArray8192.get32 avec i).

op ideal_final_s2_centered_moment56_profile_at
    (pre_bp avec : BArray8192.t) (i : int) : real * real =
  (ideal_final_s2_centered_moment5_at pre_bp avec i,
   ideal_final_s2_centered_moment6_at pre_bp avec i).

op ideal_final_s2_residual_moment5_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  (((ideal_final_s2_residual_coord pre_bp avec i (-1)) ^ 5) +
   ((ideal_final_s2_residual_coord pre_bp avec i 0) ^ 5) +
   ((ideal_final_s2_residual_coord pre_bp avec i 1) ^ 5)) / 3%r.

op ideal_final_s2_residual_moment6_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  (((ideal_final_s2_residual_coord pre_bp avec i (-1)) ^ 6) +
   ((ideal_final_s2_residual_coord pre_bp avec i 0) ^ 6) +
   ((ideal_final_s2_residual_coord pre_bp avec i 1) ^ 6)) / 3%r.

op ideal_final_s2_residual_moment56_profile_at
    (pre_bp avec : BArray8192.t) (i : int) : real * real =
  (ideal_final_s2_residual_moment5_at pre_bp avec i,
   ideal_final_s2_residual_moment6_at pre_bp avec i).

lemma ideal_final_s2_residual_moment5_bridge pre_bp avec i :
  ideal_final_s2_residual_moment5_at pre_bp avec i =
  ideal_final_s2_centered_moment5_at pre_bp avec i.
proof.
rewrite /ideal_final_s2_residual_moment5_at
        /ideal_final_s2_residual_coord
        /ideal_final_s2_centered_moment5_at.
rewrite /ideal_final_s2_centered_moment5
        /ideal_final_s2_centered_residual_at
        /ideal_final_s2_bias_at.
trivial.
qed.

lemma ideal_final_s2_residual_moment6_bridge pre_bp avec i :
  ideal_final_s2_residual_moment6_at pre_bp avec i =
  ideal_final_s2_centered_moment6_at pre_bp avec i.
proof.
rewrite /ideal_final_s2_residual_moment6_at
        /ideal_final_s2_residual_coord
        /ideal_final_s2_centered_moment6_at.
rewrite /ideal_final_s2_centered_moment6
        /ideal_final_s2_centered_residual_at
        /ideal_final_s2_bias_at.
trivial.
qed.

lemma ideal_final_s2_centered_moment56_bounds_at pre_bp avec i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  `|ideal_final_s2_centered_moment5_at pre_bp avec i| <= 320%r / 243%r /\
  0%r <= ideal_final_s2_centered_moment6_at pre_bp avec i /\
  ideal_final_s2_centered_moment6_at pre_bp avec i <= 128%r / 3%r.
proof.
move=> hctx hi.
exact
  (ideal_final_s2_centered_moment56_bounds
    (BArray8192.get32 pre_bp i)
    (BArray8192.get32 avec i)
    (ideal_mode2_finalize_context_valid_at pre_bp avec i hctx hi)).
qed.

lemma ideal_final_s2_residual_moment56_bounds_at pre_bp avec i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  `|ideal_final_s2_residual_moment5_at pre_bp avec i| <= 320%r / 243%r /\
  0%r <= ideal_final_s2_residual_moment6_at pre_bp avec i /\
  ideal_final_s2_residual_moment6_at pre_bp avec i <= 128%r / 3%r.
proof.
move=> hctx hi.
rewrite ideal_final_s2_residual_moment5_bridge
        ideal_final_s2_residual_moment6_bridge.
exact (ideal_final_s2_centered_moment56_bounds_at pre_bp avec i hctx hi).
qed.

end Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze.
