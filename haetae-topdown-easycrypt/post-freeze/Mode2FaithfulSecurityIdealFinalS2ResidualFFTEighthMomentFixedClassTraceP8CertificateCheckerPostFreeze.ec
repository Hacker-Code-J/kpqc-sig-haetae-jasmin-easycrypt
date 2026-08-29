require import AllCore IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  KeygenM23ComplexReal
  KeygenM23SingularFFTSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalClassProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalClassProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze.

(* A linear-time fold evaluator for fixed class traces. The first closed
   stress trace below is homogeneous class 4; it is not asserted to be an
   actual or randomly distributed HAETAE context. *)

type profile8_interval_state =
  rinterval * rinterval * rinterval * rinterval * rinterval * rinterval.

op state_profile2 (s : profile8_interval_state) : rinterval = s.`1.
op state_profile3 (s : profile8_interval_state) : rinterval = s.`2.
op state_profile4 (s : profile8_interval_state) : rinterval = s.`3.
op state_profile5 (s : profile8_interval_state) : rinterval = s.`4.
op state_profile6 (s : profile8_interval_state) : rinterval = s.`5.
op state_profile8 (s : profile8_interval_state) : rinterval = s.`6.

op profile8_interval_zero_state : profile8_interval_state =
  (interval_point 0%r, interval_point 0%r, interval_point 0%r,
   interval_point 0%r, interval_point 0%r, interval_point 0%r).

op profile4_interval_increment
    (trace : int -> int) (balls : int -> rinterval)
    (p2 : rinterval) (j : int) : rinterval =
  interval_add
    (interval_scale_mul 6%r p2
      (root_class_moment2_interval trace balls j))
    (root_class_moment4_interval trace balls j).

op profile5_interval_increment
    (trace : int -> int) (balls : int -> rinterval)
    (p3 p2 : rinterval) (j : int) : rinterval =
  interval_add3
    (interval_scale_mul 10%r p3
      (root_class_moment2_interval trace balls j))
    (interval_scale_mul 10%r p2
      (root_class_moment3_interval trace balls j))
    (root_class_moment5_interval trace balls j).

op profile6_interval_increment
    (trace : int -> int) (balls : int -> rinterval)
    (p4 p3 p2 : rinterval) (j : int) : rinterval =
  interval_add4
    (interval_scale_mul 15%r p4
      (root_class_moment2_interval trace balls j))
    (interval_scale_mul 20%r p3
      (root_class_moment3_interval trace balls j))
    (interval_scale_mul 15%r p2
      (root_class_moment4_interval trace balls j))
    (root_class_moment6_interval trace balls j).

op profile8_interval_increment
    (trace : int -> int) (balls : int -> rinterval)
    (p6 p5 p4 p3 p2 : rinterval) (j : int) : rinterval =
  interval_add6
    (interval_scale_mul 28%r p6
      (root_class_moment2_interval trace balls j))
    (interval_scale_mul 56%r p5
      (root_class_moment3_interval trace balls j))
    (interval_scale_mul 70%r p4
      (root_class_moment4_interval trace balls j))
    (interval_scale_mul 56%r p3
      (root_class_moment5_interval trace balls j))
    (interval_scale_mul 28%r p2
      (root_class_moment6_interval trace balls j))
    (root_class_moment8_interval trace balls j).

op profile8_interval_state_step
    (trace : int -> int) (balls : int -> rinterval)
    (s : profile8_interval_state) (j : int) : profile8_interval_state =
  (interval_add (state_profile2 s)
      (root_class_moment2_interval trace balls j),
   interval_add (state_profile3 s)
      (root_class_moment3_interval trace balls j),
   interval_add (state_profile4 s)
      (profile4_interval_increment trace balls (state_profile2 s) j),
   interval_add (state_profile5 s)
      (profile5_interval_increment trace balls
        (state_profile3 s) (state_profile2 s) j),
   interval_add (state_profile6 s)
      (profile6_interval_increment trace balls
        (state_profile4 s) (state_profile3 s) (state_profile2 s) j),
   interval_add (state_profile8 s)
      (profile8_interval_increment trace balls
        (state_profile6 s) (state_profile5 s) (state_profile4 s)
        (state_profile3 s) (state_profile2 s) j)).

op profile8_interval_eval
    (trace : int -> int) (balls : int -> rinterval) (n : int) :
    profile8_interval_state =
  foldl (profile8_interval_state_step trace balls)
    profile8_interval_zero_state (range 0 n).

op profile8_interval_expected_state
    (trace : int -> int) (balls : int -> rinterval) (n : int) :
    profile8_interval_state =
  (root_class_profile2_interval trace balls n,
   root_class_profile3_interval trace balls n,
   root_class_profile4_interval trace balls n,
   root_class_profile5_interval trace balls n,
   root_class_profile6_interval trace balls n,
   root_class_profile8_interval trace balls n).

lemma root_class_profile2_interval0 trace balls :
  root_class_profile2_interval trace balls 0 = interval_point 0%r.
proof.
rewrite /root_class_profile2_interval /interval_bigi /interval_point.
rewrite !BRA.big_geq 1:/# 1:/#.
trivial.
qed.

lemma root_class_profile3_interval0 trace balls :
  root_class_profile3_interval trace balls 0 = interval_point 0%r.
proof.
rewrite /root_class_profile3_interval /interval_bigi /interval_point.
rewrite !BRA.big_geq 1:/# 1:/#.
trivial.
qed.

lemma root_class_profile4_interval0 trace balls :
  root_class_profile4_interval trace balls 0 = interval_point 0%r.
proof.
rewrite /root_class_profile4_interval /interval_bigi /interval_point.
rewrite !BRA.big_geq 1:/# 1:/#.
trivial.
qed.

lemma root_class_profile5_interval0 trace balls :
  root_class_profile5_interval trace balls 0 = interval_point 0%r.
proof.
rewrite /root_class_profile5_interval /interval_bigi /interval_point.
rewrite !BRA.big_geq 1:/# 1:/#.
trivial.
qed.

lemma root_class_profile6_interval0 trace balls :
  root_class_profile6_interval trace balls 0 = interval_point 0%r.
proof.
rewrite /root_class_profile6_interval /interval_bigi /interval_point.
rewrite !BRA.big_geq 1:/# 1:/#.
trivial.
qed.

lemma root_class_profile8_interval0 trace balls :
  root_class_profile8_interval trace balls 0 = interval_point 0%r.
proof.
rewrite /root_class_profile8_interval /interval_bigi /interval_point.
rewrite !BRA.big_geq 1:/# 1:/#.
trivial.
qed.

lemma root_class_profile2_intervalS trace balls n :
  0 <= n =>
  root_class_profile2_interval trace balls (n + 1) =
  interval_add (root_class_profile2_interval trace balls n)
    (root_class_moment2_interval trace balls n).
proof.
move=> hn.
rewrite /root_class_profile2_interval.
exact (interval_bigiE
  (fun j => root_class_moment2_interval trace balls j) n hn).
qed.

lemma root_class_profile3_intervalS trace balls n :
  0 <= n =>
  root_class_profile3_interval trace balls (n + 1) =
  interval_add (root_class_profile3_interval trace balls n)
    (root_class_moment3_interval trace balls n).
proof.
move=> hn.
rewrite /root_class_profile3_interval.
exact (interval_bigiE
  (fun j => root_class_moment3_interval trace balls j) n hn).
qed.

lemma root_class_profile4_intervalS trace balls n :
  0 <= n =>
  root_class_profile4_interval trace balls (n + 1) =
  interval_add (root_class_profile4_interval trace balls n)
    (root_class_profile4_interval_step trace balls n).
proof.
move=> hn.
rewrite /root_class_profile4_interval.
exact (interval_bigiE
  (fun j => root_class_profile4_interval_step trace balls j) n hn).
qed.

lemma root_class_profile5_intervalS trace balls n :
  0 <= n =>
  root_class_profile5_interval trace balls (n + 1) =
  interval_add (root_class_profile5_interval trace balls n)
    (root_class_profile5_interval_step trace balls n).
proof.
move=> hn.
rewrite /root_class_profile5_interval.
exact (interval_bigiE
  (fun j => root_class_profile5_interval_step trace balls j) n hn).
qed.

lemma root_class_profile6_intervalS trace balls n :
  0 <= n =>
  root_class_profile6_interval trace balls (n + 1) =
  interval_add (root_class_profile6_interval trace balls n)
    (root_class_profile6_interval_step trace balls n).
proof.
move=> hn.
rewrite /root_class_profile6_interval.
exact (interval_bigiE
  (fun j => root_class_profile6_interval_step trace balls j) n hn).
qed.

lemma root_class_profile8_intervalS trace balls n :
  0 <= n =>
  root_class_profile8_interval trace balls (n + 1) =
  interval_add (root_class_profile8_interval trace balls n)
    (root_class_profile8_interval_step trace balls n).
proof.
move=> hn.
rewrite /root_class_profile8_interval.
exact (interval_bigiE
  (fun j => root_class_profile8_interval_step trace balls j) n hn).
qed.

lemma profile8_interval_evalE trace balls n :
  0 <= n =>
  profile8_interval_eval trace balls n =
  profile8_interval_expected_state trace balls n.
proof.
elim/natind: n => [n hnle0|n hnge0 ih].
+ move=> hn.
  have -> : n = 0 by smt().
  rewrite /profile8_interval_eval /profile8_interval_expected_state
          /profile8_interval_zero_state.
  rewrite range_geq 1:/# /=.
  rewrite root_class_profile2_interval0
          root_class_profile3_interval0
          root_class_profile4_interval0
          root_class_profile5_interval0
          root_class_profile6_interval0
          root_class_profile8_interval0.
  trivial.
+ move=> _.
  have ihn := ih hnge0.
  rewrite /profile8_interval_eval in ihn.
  rewrite /profile8_interval_eval.
  rewrite (rangeSr 0 n) 1:/# foldl_rcons /=.
  rewrite ihn.
  rewrite /profile8_interval_expected_state
          /profile8_interval_state_step
          /state_profile2 /state_profile3 /state_profile4
          /state_profile5 /state_profile6 /state_profile8 /=.
  rewrite root_class_profile2_intervalS 1:hnge0
          root_class_profile3_intervalS 1:hnge0
          root_class_profile4_intervalS 1:hnge0
          root_class_profile5_intervalS 1:hnge0
          root_class_profile6_intervalS 1:hnge0
          root_class_profile8_intervalS 1:hnge0.
  rewrite /profile4_interval_increment
          /profile5_interval_increment
          /profile6_interval_increment
          /profile8_interval_increment
          /root_class_profile4_interval_step
          /root_class_profile5_interval_step
          /root_class_profile6_interval_step
          /root_class_profile8_interval_step.
  trivial.
qed.

op homogeneous_class4_trace (_ : int) : int = 4.

op homogeneous_class4_re_state (k : int) : profile8_interval_state =
  profile8_interval_eval homogeneous_class4_trace
    (certified_odd_root_re_interval k) 256.

op homogeneous_class4_im_state (k : int) : profile8_interval_state =
  profile8_interval_eval homogeneous_class4_trace
    (certified_odd_root_im_interval k) 256.

op homogeneous_class4_re_profile8_interval (k : int) : rinterval =
  state_profile8 (homogeneous_class4_re_state k).

op homogeneous_class4_im_profile8_interval (k : int) : rinterval =
  state_profile8 (homogeneous_class4_im_state k).

lemma homogeneous_class4_re_profile8_intervalE k :
  homogeneous_class4_re_profile8_interval k =
  certified_class_re_profile8_interval homogeneous_class4_trace k 256.
proof.
rewrite /homogeneous_class4_re_profile8_interval
        /homogeneous_class4_re_state
        /certified_class_re_profile8_interval.
have h256 : 0 <= 256 by smt().
have he := profile8_interval_evalE homogeneous_class4_trace
  (certified_odd_root_re_interval k) 256 h256.
rewrite he /profile8_interval_expected_state /state_profile8 /=.
trivial.
qed.

lemma homogeneous_class4_im_profile8_intervalE k :
  homogeneous_class4_im_profile8_interval k =
  certified_class_im_profile8_interval homogeneous_class4_trace k 256.
proof.
rewrite /homogeneous_class4_im_profile8_interval
        /homogeneous_class4_im_state
        /certified_class_im_profile8_interval.
have h256 : 0 <= 256 by smt().
have he := profile8_interval_evalE homogeneous_class4_trace
  (certified_odd_root_im_interval k) 256 h256.
rewrite he /profile8_interval_expected_state /state_profile8 /=.
trivial.
qed.

lemma ideal_final_s2_row_residual_profile8_homogeneous_class4_conditional
    pre_bp avec row k :
  0 <= k =>
  ideal_final_s2_row_class_trace pre_bp avec row = homogeneous_class4_trace =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256| <=
    interval_abs_upper (homogeneous_class4_re_profile8_interval k) /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256| <=
    interval_abs_upper (homogeneous_class4_im_profile8_interval k).
proof.
move=> hk htrace.
have h :=
  ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
    pre_bp avec row k 256 hk.
rewrite htrace in h.
rewrite homogeneous_class4_re_profile8_intervalE
        homogeneous_class4_im_profile8_intervalE.
exact h.
qed.

op homogeneous_class4_p8_ceiling : real = 1400416448854%r.

(* The companion exact-Fraction checker validates this closed computation.
   It remains an explicit premise inside EasyCrypt: this file does not turn
   an external computation into an unconditional logical fact. *)
op homogeneous_class4_numeric_certificate : bool =
  forall k, 0 <= k < 256 =>
    interval_abs_upper (homogeneous_class4_re_profile8_interval k) <=
      homogeneous_class4_p8_ceiling /\
    interval_abs_upper (homogeneous_class4_im_profile8_interval k) <=
      homogeneous_class4_p8_ceiling.

lemma ideal_final_s2_row_residual_profile8_homogeneous_class4_numeric
    pre_bp avec row k :
  homogeneous_class4_numeric_certificate =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row = homogeneous_class4_trace =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256| <=
    homogeneous_class4_p8_ceiling /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256| <=
    homogeneous_class4_p8_ceiling.
proof.
rewrite /homogeneous_class4_numeric_certificate.
move=> hnumeric hk htrace.
have hk0 : 0 <= k by smt().
have [hre him] :=
  ideal_final_s2_row_residual_profile8_homogeneous_class4_conditional
    pre_bp avec row k hk0 htrace.
have [hure huim] := hnumeric k hk.
split.
+ apply (ler_trans
    (interval_abs_upper (homogeneous_class4_re_profile8_interval k))).
  + exact hre.
  exact hure.
apply (ler_trans
  (interval_abs_upper (homogeneous_class4_im_profile8_interval k))).
+ exact him.
exact huim.
qed.

lemma homogeneous_class4_ceiling_improves_uniform_envelope_by_16 :
  16%r * homogeneous_class4_p8_ceiling <
  49301448283783168%r / 2187%r.
proof.
rewrite /homogeneous_class4_p8_ceiling.
smt().
qed.

lemma homogeneous_class4_ceiling_five_below_min_headroom8 :
  5%r * homogeneous_class4_p8_ceiling <
  (8057501%r / 196608%r) ^ 8.
proof.
rewrite /homogeneous_class4_p8_ceiling.
have -> :
  (8057501%r / 196608%r) ^ 8 =
  17766543545077793661285552022136707710355048352639460001%r /
  2232592609368277258783200799359831235362816%r.
+ field; smt().
smt().
qed.

lemma homogeneous_class4_ceiling_markov_ratio_lt_one_fifth :
  homogeneous_class4_p8_ceiling /
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8) <
  1%r / 5%r.
proof.
have hmpos :
    0%r <
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 _
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom_gt0).
have hfive := homogeneous_class4_ceiling_five_below_min_headroom8.
rewrite -Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
  .ideal_final_s2_uniform_min_headroom_exact in hfive.
rewrite ltr_pdivr_mulr 1:hmpos.
have -> :
    1%r / 5%r *
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom ^ 8) =
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8) / 5%r by ring.
rewrite ltr_pdivl_mulr 1:/#.
exact hfive.
qed.

lemma ideal_final_s2_full_row_residual_fft_real_tail_homogeneous_class4
    pre_bp avec row k :
  homogeneous_class4_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row = homogeneous_class4_trace =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k <=
      `|creal z|) <
  1%r / 5%r.
proof.
move=> hnumeric hctx hrow hk htrace.
have hmarkov :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .ideal_final_s2_full_row_residual_fft_real_headroom_tail_markov8
      pre_bp avec row k hctx hrow hk.
have [hre _] :=
  ideal_final_s2_row_residual_profile8_homogeneous_class4_numeric
    pre_bp avec row k hnumeric hk htrace.
have hprofile :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 <=
    homogeneous_class4_p8_ceiling.
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact hre.
have hhead :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom_le_real_headroom
      pre_bp avec row k hctx hrow hk.
have hhpos :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom_gt0
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
      homogeneous_class4_p8_ceiling
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom ^ 8)
      hmpos hpowmono _ hprofile.
+ rewrite /homogeneous_class4_p8_ceiling; smt().
apply (ler_lt_trans
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8))).
+ exact hmarkov.
apply (ler_lt_trans
  (homogeneous_class4_p8_ceiling /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom ^ 8))).
+ exact hdiv.
exact homogeneous_class4_ceiling_markov_ratio_lt_one_fifth.
qed.

lemma ideal_final_s2_full_row_residual_fft_imag_tail_homogeneous_class4
    pre_bp avec row k :
  homogeneous_class4_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row = homogeneous_class4_trace =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k <=
      `|cimag z|) <
  1%r / 5%r.
proof.
move=> hnumeric hctx hrow hk htrace.
have hmarkov :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .ideal_final_s2_full_row_residual_fft_imag_headroom_tail_markov8
      pre_bp avec row k hctx hrow hk.
have [_ him] :=
  ideal_final_s2_row_residual_profile8_homogeneous_class4_numeric
    pre_bp avec row k hnumeric hk htrace.
have hprofile :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 <=
    homogeneous_class4_p8_ceiling.
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact him.
have hhead :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom_le_imag_headroom
      pre_bp avec row k hctx hrow hk.
have hhpos :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom_gt0
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
      homogeneous_class4_p8_ceiling
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom ^ 8)
      hmpos hpowmono _ hprofile.
+ rewrite /homogeneous_class4_p8_ceiling; smt().
apply (ler_lt_trans
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8))).
+ exact hmarkov.
apply (ler_lt_trans
  (homogeneous_class4_p8_ceiling /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom ^ 8))).
+ exact hdiv.
exact homogeneous_class4_ceiling_markov_ratio_lt_one_fifth.
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze.
