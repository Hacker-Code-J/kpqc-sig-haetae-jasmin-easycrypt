require import AllCore DList Distr Finite IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety
  KeygenM23SingularFFTSpec
  KeygenM23SingularSpec
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze.

(* This file extends the fixed-context, row-local ideal residual odd-DFT
   analysis from second moments to exact fourth moments.  The [pre_bp] and
   [avec] arrays are parameters, so the only randomness is the iid centered
   trit source on one 256-word row (or its deterministic pushforward into the
   full 512-coordinate carrier).  It does not claim random-context laws,
   actual/fixed-point FFT behavior, SHAKE coupling, numerical security levels,
   five-slot accumulator probabilities, or any prefix-energy safety statement.
   Its final Markov certificates retain the exact fixed-context bias and
   fourth-moment profile rather than collapsing either to a global constant. *)

op ideal_final_s2_row_residual_re_moment2_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (creal (cpow (odd_root k) j) ^ 2) *
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment2_at
      pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_im_moment2_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (cimag (cpow (odd_root k) j) ^ 2) *
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment2_at
      pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_re_moment4_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (creal (cpow (odd_root k) j) ^ 4) *
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment4_at
      pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_im_moment4_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (cimag (cpow (odd_root k) j) ^ 4) *
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment4_at
      pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_re_profile4
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
    (fun j =>
      6%r *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
        ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
      ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j)
    0 n.

op ideal_final_s2_row_residual_im_profile4
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
    (fun j =>
      6%r *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
        ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
      ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j)
    0 n.

op ideal_final_s2_full_row_residual_real_headroom
    (pre_bp avec : BArray8192.t) (row k : int) : real =
  KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap -
  KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps -
  `|creal
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)|.

op ideal_final_s2_full_row_residual_imag_headroom
    (pre_bp avec : BArray8192.t) (row k : int) : real =
  KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap -
  KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps -
  `|cimag
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)|.

lemma exp_dprod_centered_fourth_step ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  weight da = 1%r =>
  weight db = 1%r =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 4) =
  E da (fun a => f a ^ 4) +
  6%r * E da (fun a => f a ^ 2) * E db (fun b => g b ^ 2) +
  E db (fun b => g b ^ 4).
proof.
move=> hfina hfinb hwda hwdb hEf0 hEg0.
have hfinprod : is_finite (support (da `*` db)).
+ apply finite_dprod => //.
rewrite
  (eq_exp
    (da `*` db)
    (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 4)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 4 +
      4%r * (f ab.`1 ^ 3 * g ab.`2) +
      6%r * (f ab.`1 ^ 2 * g ab.`2 ^ 2) +
      4%r * (f ab.`1 * g ab.`2 ^ 3) +
      g ab.`2 ^ 4)).
+ move=> [a b] hab /=.
   ring.
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 4 +
      4%r * (f ab.`1 ^ 3 * g ab.`2) +
      6%r * (f ab.`1 ^ 2 * g ab.`2 ^ 2) +
      4%r * (f ab.`1 * g ab.`2 ^ 3))
    (fun (ab : 'a * 'b) => g ab.`2 ^ 4)
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 4 +
      4%r * (f ab.`1 ^ 3 * g ab.`2) +
      6%r * (f ab.`1 ^ 2 * g ab.`2 ^ 2))
    (fun (ab : 'a * 'b) => 4%r * (f ab.`1 * g ab.`2 ^ 3))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 4 + 4%r * (f ab.`1 ^ 3 * g ab.`2))
    (fun (ab : 'a * 'b) => 6%r * (f ab.`1 ^ 2 * g ab.`2 ^ 2))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) => f ab.`1 ^ 4)
    (fun (ab : 'a * 'b) => 4%r * (f ab.`1 ^ 3 * g ab.`2))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_left_finite
      da db (fun a => f a ^ 4))
  1:hfina 1:hfinb.
rewrite hwdb.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_right_finite
      da db (fun b => g b ^ 4))
  1:hfina 1:hfinb.
rewrite hwda.
have -> :
    (fun (ab : 'a * 'b) => 4%r * (f ab.`1 ^ 3 * g ab.`2)) =
    (fun (ab : 'a * 'b) => 4%r * ((f ab.`1 ^ 3) * g ab.`2)).
+ apply fun_ext => ab.
   ring.
rewrite
  (expZ
    (da `*` db)
    4%r
    (fun (ab : 'a * 'b) => (f ab.`1 ^ 3) * g ab.`2)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_mul_factor
      da db (fun a => f a ^ 3) g)
  1:hfina 1:hfinb.
rewrite hEg0.
have -> :
    (fun (ab : 'a * 'b) => 6%r * (f ab.`1 ^ 2 * g ab.`2 ^ 2)) =
    (fun (ab : 'a * 'b) => 6%r * ((f ab.`1 ^ 2) * (g ab.`2 ^ 2))).
+ apply fun_ext => ab.
   ring.
rewrite
  (expZ
    (da `*` db)
    6%r
    (fun (ab : 'a * 'b) => (f ab.`1 ^ 2) * (g ab.`2 ^ 2))).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_mul_factor
      da db (fun a => f a ^ 2) (fun b => g b ^ 2))
  1:hfina 1:hfinb.
have -> :
    (fun (ab : 'a * 'b) => 4%r * (f ab.`1 * g ab.`2 ^ 3)) =
    (fun (ab : 'a * 'b) => 4%r * (f ab.`1 * (g ab.`2 ^ 3))).
+ apply fun_ext => ab.
   ring.
rewrite
  (expZ
    (da `*` db)
    4%r
    (fun (ab : 'a * 'b) => f ab.`1 * (g ab.`2 ^ 3))).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_mul_factor
      da db f (fun b => g b ^ 3))
  1:hfina 1:hfinb.
rewrite hEf0.
ring.
qed.

lemma exp_dprod_add_fourth_centered ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  is_lossless da =>
  is_lossless db =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 4) =
  E da (fun a => f a ^ 4) +
  6%r * E da (fun a => f a ^ 2) * E db (fun b => g b ^ 2) +
  E db (fun b => g b ^ 4).
proof.
move=> hfina hfinb hlla hllb hEf0 hEg0.
rewrite /is_lossless in hlla.
rewrite /is_lossless in hllb.
exact
  (exp_dprod_centered_fourth_step
    da db f g hfina hfinb hlla hllb hEf0 hEg0).
qed.

lemma ideal_final_s2_row_residual_re_term_exp_zero
    pre_bp avec row k j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_re_term pre_bp avec row k j) =
  0%r.
proof.
move=> hrow hj.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_re_term.
have -> :
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x *
      creal (cpow (odd_root k) j)) =
    (fun x =>
      creal (cpow (odd_root k) j) *
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x).
+ apply fun_ext => x.
   ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (creal (cpow (odd_root k) j))
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_value pre_bp avec row j)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value_exp_zero
      pre_bp avec row j hrow hj).
ring.
qed.

lemma ideal_final_s2_row_residual_im_term_exp_zero
    pre_bp avec row k j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_im_term pre_bp avec row k j) =
  0%r.
proof.
move=> hrow hj.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_im_term.
have -> :
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x *
      cimag (cpow (odd_root k) j)) =
    (fun x =>
      cimag (cpow (odd_root k) j) *
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x).
+ apply fun_ext => x.
   ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (cimag (cpow (odd_root k) j))
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_value pre_bp avec row j)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value_exp_zero
      pre_bp avec row j hrow hj).
ring.
qed.

lemma ideal_final_s2_row_residual_re_term_exp_square
    pre_bp avec row k j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_re_term pre_bp avec row k j x ^ 2) =
  ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j.
proof.
move=> hrow hj.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_re_term
  /ideal_final_s2_row_residual_re_moment2_term.
have -> :
    (fun x =>
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_residual_value pre_bp avec row j x *
       creal (cpow (odd_root k) j)) ^ 2) =
    (fun x =>
      creal (cpow (odd_root k) j) ^ 2 *
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x ^ 2).
+ apply fun_ext => x.
   ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (creal (cpow (odd_root k) j) ^ 2)
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x ^ 2)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value_exp_square
      pre_bp avec row j hrow hj).
trivial.
qed.

lemma ideal_final_s2_row_residual_im_term_exp_square
    pre_bp avec row k j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_im_term pre_bp avec row k j x ^ 2) =
  ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j.
proof.
move=> hrow hj.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_im_term
  /ideal_final_s2_row_residual_im_moment2_term.
have -> :
    (fun x =>
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_residual_value pre_bp avec row j x *
       cimag (cpow (odd_root k) j)) ^ 2) =
    (fun x =>
      cimag (cpow (odd_root k) j) ^ 2 *
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x ^ 2).
+ apply fun_ext => x.
   ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (cimag (cpow (odd_root k) j) ^ 2)
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x ^ 2)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value_exp_square
      pre_bp avec row j hrow hj).
trivial.
qed.

lemma ideal_final_s2_row_residual_re_term_exp_fourth
    pre_bp avec row k j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_re_term pre_bp avec row k j x ^ 4) =
  ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j.
proof.
move=> hrow hj.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_re_term
  /ideal_final_s2_row_residual_re_moment4_term.
have -> :
    (fun x =>
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_residual_value pre_bp avec row j x *
       creal (cpow (odd_root k) j)) ^ 4) =
    (fun x =>
      creal (cpow (odd_root k) j) ^ 4 *
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x ^ 4).
+ apply fun_ext => x.
   ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (creal (cpow (odd_root k) j) ^ 4)
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x ^ 4)).
rewrite
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_eta_centered_trit_expE.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value
  /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment4_at.
trivial.
qed.

lemma ideal_final_s2_row_residual_im_term_exp_fourth
    pre_bp avec row k j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_im_term pre_bp avec row k j x ^ 4) =
  ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j.
proof.
move=> hrow hj.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_im_term
  /ideal_final_s2_row_residual_im_moment4_term.
have -> :
    (fun x =>
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_residual_value pre_bp avec row j x *
       cimag (cpow (odd_root k) j)) ^ 4) =
    (fun x =>
      cimag (cpow (odd_root k) j) ^ 4 *
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x ^ 4).
+ apply fun_ext => x.
   ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (cimag (cpow (odd_root k) j) ^ 4)
    (fun x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x ^ 4)).
rewrite
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_eta_centered_trit_expE.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value
  /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment4_at.
trivial.
qed.

lemma ideal_final_s2_row_residual_re_prefix_fourthE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_re_prefix pre_bp avec row k n xs ^ 4) =
  ideal_final_s2_row_residual_re_profile4 pre_bp avec row k n.
proof.
move=> hrow.
elim/natind: n => [n hnle0|n hnge0 ih].
+ move=> _.
   rewrite /ideal_final_s2_row_source_distribution dlist0 1:/#.
   rewrite exp_dunit.
   simplify.
   have hrange : range 0 n = [] by
     apply range_geq; exact hnle0.
   rewrite /ideal_final_s2_row_residual_re_prefix
           /ideal_final_s2_row_residual_re_profile4.
   rewrite hrange !BRA.big_nil.
   ring.
move=> hn.
have hnprev : 0 <= n <= 256 by smt().
have hn256 : 0 <= n < KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; smt().
have hfin_n :
    is_finite (support (ideal_final_s2_row_source_distribution n)).
+ exact (ideal_final_s2_row_source_distribution_finite n hnge0).
have hfin_trit :
    is_finite
      (support
        Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
          .ideal_eta_centered_trit_distribution).
+ apply uniform_finite.
   exact
     Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
       .ideal_eta_centered_trit_uniform.
have hfin_prod :
    is_finite
      (support
        (ideal_final_s2_row_source_distribution n `*`
         Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
           .ideal_eta_centered_trit_distribution)).
+ apply finite_dprod => //.
have hfin_map :
    is_finite
      (support
        (dmap
          (ideal_final_s2_row_source_distribution n `*`
           Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
             .ideal_eta_centered_trit_distribution)
          (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))).
+ apply finite_dmap.
   exact hfin_prod.
rewrite /ideal_final_s2_row_source_distribution dlistSr 1:/#.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2)
    (fun xs =>
      ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 4)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 4) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2) ^ 4)).
+ move=> [xs x] hxs /=.
   rewrite supp_dprod in hxs.
   move: hxs => [hxs _].
   have hsize :=
     supp_dlist_size
       Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
         .ideal_eta_centered_trit_distribution
       n xs hnge0 hxs.
   rewrite /(\o)
     (ideal_final_s2_row_residual_re_prefix_rcons
       pre_bp avec row k n xs x hnge0 hsize).
   trivial.
have hll_n := ideal_final_s2_row_source_distribution_lossless n.
have hll_trit :=
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
have hmean_prefix :=
  ideal_final_s2_row_residual_re_prefix_exp_zero
    pre_bp avec row k n hrow hnprev.
have hmean_term :=
  ideal_final_s2_row_residual_re_term_exp_zero
    pre_bp avec row k n hrow hn256.
rewrite
  (exp_dprod_add_fourth_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_re_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (ideal_final_s2_row_residual_re_prefix_sqE
    pre_bp avec row k n hrow hnprev).
rewrite
  (ideal_final_s2_row_residual_re_term_exp_square
    pre_bp avec row k n hrow hn256).
rewrite
  (ideal_final_s2_row_residual_re_term_exp_fourth
    pre_bp avec row k n hrow hn256).
rewrite /ideal_final_s2_row_residual_re_profile4.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
ring.
qed.

lemma ideal_final_s2_row_residual_im_prefix_fourthE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_im_prefix pre_bp avec row k n xs ^ 4) =
  ideal_final_s2_row_residual_im_profile4 pre_bp avec row k n.
proof.
move=> hrow.
elim/natind: n => [n hnle0|n hnge0 ih].
+ move=> _.
   rewrite /ideal_final_s2_row_source_distribution dlist0 1:/#.
   rewrite exp_dunit.
   simplify.
   have hrange : range 0 n = [] by
     apply range_geq; exact hnle0.
   rewrite /ideal_final_s2_row_residual_im_prefix
           /ideal_final_s2_row_residual_im_profile4.
   rewrite hrange !BRA.big_nil.
   ring.
move=> hn.
have hnprev : 0 <= n <= 256 by smt().
have hn256 : 0 <= n < KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; smt().
have hfin_n :
    is_finite (support (ideal_final_s2_row_source_distribution n)).
+ exact (ideal_final_s2_row_source_distribution_finite n hnge0).
have hfin_trit :
    is_finite
      (support
        Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
          .ideal_eta_centered_trit_distribution).
+ apply uniform_finite.
   exact
     Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
       .ideal_eta_centered_trit_uniform.
have hfin_prod :
    is_finite
      (support
        (ideal_final_s2_row_source_distribution n `*`
         Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
           .ideal_eta_centered_trit_distribution)).
+ apply finite_dprod => //.
have hfin_map :
    is_finite
      (support
        (dmap
          (ideal_final_s2_row_source_distribution n `*`
           Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
             .ideal_eta_centered_trit_distribution)
          (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))).
+ apply finite_dmap.
   exact hfin_prod.
rewrite /ideal_final_s2_row_source_distribution dlistSr 1:/#.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2)
    (fun xs =>
      ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 4)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 4) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2) ^ 4)).
+ move=> [xs x] hxs /=.
   rewrite supp_dprod in hxs.
   move: hxs => [hxs _].
   have hsize :=
     supp_dlist_size
       Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
         .ideal_eta_centered_trit_distribution
       n xs hnge0 hxs.
   rewrite /(\o)
     (ideal_final_s2_row_residual_im_prefix_rcons
       pre_bp avec row k n xs x hnge0 hsize).
   trivial.
have hll_n := ideal_final_s2_row_source_distribution_lossless n.
have hll_trit :=
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
have hmean_prefix :=
  ideal_final_s2_row_residual_im_prefix_exp_zero
    pre_bp avec row k n hrow hnprev.
have hmean_term :=
  ideal_final_s2_row_residual_im_term_exp_zero
    pre_bp avec row k n hrow hn256.
rewrite
  (exp_dprod_add_fourth_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_im_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (ideal_final_s2_row_residual_im_prefix_sqE
    pre_bp avec row k n hrow hnprev).
rewrite
  (ideal_final_s2_row_residual_im_term_exp_square
    pre_bp avec row k n hrow hn256).
rewrite
  (ideal_final_s2_row_residual_im_term_exp_fourth
    pre_bp avec row k n hrow hn256).
rewrite /ideal_final_s2_row_residual_im_profile4.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
ring.
qed.

lemma ideal_final_s2_row_residual_fft_real_moment4E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)
    (fun z => creal z ^ 4) =
  ideal_final_s2_row_residual_re_profile4 pre_bp avec row k 256.
proof.
move=> hrow.
have hfin :
    is_finite
      (support
        (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)).
+ rewrite
     /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_residual_odd_dft256_distribution.
   apply
     Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .finite_dmap.
   exact
     (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_source_distribution_finite 256 _).
   rewrite /KeygenM23SingularSpec.singular_words_i.
   trivial.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_odd_dft256_distribution.
rewrite
  (exp_dmap
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_source_distribution 256)
    (fun xs =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k)
    (fun z => creal z ^ 4)
    (hasE_finite _ _ hfin)).
rewrite
  (eq_exp
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_source_distribution 256)
    ((fun z => creal z ^ 4) \o
     (fun xs =>
       Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k))
    (fun xs =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_re_prefix pre_bp avec row k 256 xs ^ 4)).
+ move=> xs hxs /=.
   rewrite /(\o).
   rewrite
     (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_residual_odd_dft256_sample_creal
         pre_bp avec row xs k).
   trivial.
have h256 : 0 <= 256 <= 256 by smt().
exact
  (ideal_final_s2_row_residual_re_prefix_fourthE
    pre_bp avec row k 256 hrow h256).
qed.

lemma ideal_final_s2_row_residual_fft_imag_moment4E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)
    (fun z => cimag z ^ 4) =
  ideal_final_s2_row_residual_im_profile4 pre_bp avec row k 256.
proof.
move=> hrow.
have hfin :
    is_finite
      (support
        (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)).
+ rewrite
     /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_residual_odd_dft256_distribution.
   apply
     Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .finite_dmap.
   exact
     (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_source_distribution_finite 256 _).
   rewrite /KeygenM23SingularSpec.singular_words_i.
   trivial.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_odd_dft256_distribution.
rewrite
  (exp_dmap
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_source_distribution 256)
    (fun xs =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k)
    (fun z => cimag z ^ 4)
    (hasE_finite _ _ hfin)).
rewrite
  (eq_exp
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_source_distribution 256)
    ((fun z => cimag z ^ 4) \o
     (fun xs =>
       Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k))
    (fun xs =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_im_prefix pre_bp avec row k 256 xs ^ 4)).
+ move=> xs hxs /=.
   rewrite /(\o).
   rewrite
     (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_residual_odd_dft256_sample_cimag
         pre_bp avec row xs k).
   trivial.
have h256 : 0 <= 256 <= 256 by smt().
exact
  (ideal_final_s2_row_residual_im_prefix_fourthE
    pre_bp avec row k 256 hrow h256).
qed.

lemma ideal_final_s2_full_row_residual_fft_real_moment4E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k)
    (fun z => creal z ^ 4) =
  ideal_final_s2_row_residual_re_profile4 pre_bp avec row k 256.
proof.
move=> hrow.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .ideal_final_s2_full_row_residual_odd_dft256_distributionE
      pre_bp avec row k hrow).
exact
  (ideal_final_s2_row_residual_fft_real_moment4E
    pre_bp avec row k hrow).
qed.

lemma ideal_final_s2_full_row_residual_fft_imag_moment4E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k)
    (fun z => cimag z ^ 4) =
  ideal_final_s2_row_residual_im_profile4 pre_bp avec row k 256.
proof.
move=> hrow.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .ideal_final_s2_full_row_residual_odd_dft256_distributionE
      pre_bp avec row k hrow).
exact
  (ideal_final_s2_row_residual_fft_imag_moment4E
    pre_bp avec row k hrow).
qed.

lemma fourth_power_nonnegative (x : real) :
  0%r <= x ^ 4.
proof.
have -> : 4 = 2 * 2 by trivial.
rewrite RField.exprM.
exact (ge0_sqr (x ^ 2)).
qed.

lemma norm_fourth_power (x : real) :
  `|x| ^ 4 = x ^ 4.
proof.
rewrite -normrX_nat 1:/#.
rewrite ger0_norm 1:fourth_power_nonnegative.
trivial.
qed.

lemma finite_fourth_moment_markov ['a]
    (d : 'a distr) (f : 'a -> real) (t : real) :
  is_finite (support d) =>
  0%r < t =>
  mu d (fun x => t <= `|f x|) <=
  E d (fun x => f x ^ 4) / (t ^ 4).
proof.
move=> hfin ht.
have ht4 : 0%r < t ^ 4 by exact (expr_gt0 4 t ht).
have hindicator :
    E d (fun x => if t <= `|f x| then t ^ 4 else 0%r) <=
    E d (fun x => f x ^ 4).
+ apply (ler_exp d
    (fun x => if t <= `|f x| then t ^ 4 else 0%r)
    (fun x => f x ^ 4)).
  + exact (hasE_finite _ _ hfin).
  + exact (hasE_finite _ _ hfin).
  move=> x.
  case: (t <= `|f x|) => htail.
  + rewrite ifT 1:htail.
    have hn4 : 0 <= 4 by trivial.
    have ht0 : 0%r <= t by smt().
    have hrange : 0%r <= t <= `|f x| by smt().
    have hpow := ler_pexp 4 t `|f x| hn4 hrange.
    rewrite norm_fourth_power in hpow.
    exact hpow.
  + rewrite ifF 1:htail.
    + trivial.
    exact (fourth_power_nonnegative (f x)).
rewrite expC_cond in hindicator.
rewrite (ler_pdivl_mulr (t ^ 4)) 1:ht4.
rewrite
  (RField.mulrC
    (mu d (fun x => t <= `|f x|))
    (t ^ 4)).
exact hindicator.
qed.

lemma ideal_final_s2_full_row_residual_fft_finite
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  is_finite
    (support
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)).
proof.
move=> hrow.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .ideal_final_s2_full_row_residual_odd_dft256_distributionE
      pre_bp avec row k hrow).
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_odd_dft256_distribution.
apply
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .finite_dmap.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_source_distribution_finite 256 _).
qed.

lemma ideal_final_s2_full_row_residual_real_headroom_gt0
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0%r <
    ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k.
proof.
move=> hctx hrow hk.
have [hre _] :=
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_fft_component_bounds
      pre_bp avec row k hctx hrow hk.
rewrite /ideal_final_s2_full_row_residual_real_headroom
        /KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap
        /KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps.
smt().
qed.

lemma ideal_final_s2_full_row_residual_imag_headroom_gt0
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  0%r <
    ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k.
proof.
move=> hctx hrow hk.
have [_ him] :=
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_fft_component_bounds
      pre_bp avec row k hctx hrow hk.
rewrite /ideal_final_s2_full_row_residual_imag_headroom
        /KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap
        /KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps.
smt().
qed.

lemma ideal_final_s2_full_row_real_bad_implies_residual_tail
    pre_bp avec row k z :
  KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
    `|creal
        (cadd
          (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
            .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
          z)| +
      KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps =>
  ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k <=
    `|creal z|.
proof.
move=> hbad.
have htriangle :=
  ler_norm_add
    (creal
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k))
    (creal z).
rewrite creal_add in hbad.
rewrite /ideal_final_s2_full_row_residual_real_headroom.
smt().
qed.

lemma ideal_final_s2_full_row_imag_bad_implies_residual_tail
    pre_bp avec row k z :
  KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
    `|cimag
        (cadd
          (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
            .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
          z)| +
      KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps =>
  ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k <=
    `|cimag z|.
proof.
move=> hbad.
have htriangle :=
  ler_norm_add
    (cimag
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k))
    (cimag z).
rewrite cimag_add in hbad.
rewrite /ideal_final_s2_full_row_residual_imag_headroom.
smt().
qed.

lemma ideal_final_s2_full_row_residual_fft_real_headroom_tail_markov4
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
      ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k <=
      `|creal z|) <=
  ideal_final_s2_row_residual_re_profile4 pre_bp avec row k 256 /
  (ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 4).
proof.
move=> hctx hrow hk.
have hfin :=
  ideal_final_s2_full_row_residual_fft_finite
    pre_bp avec row k hrow.
have hheadroom :=
  ideal_final_s2_full_row_residual_real_headroom_gt0
    pre_bp avec row k hctx hrow hk.
have htail :=
  finite_fourth_moment_markov
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    creal
    (ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k)
    hfin hheadroom.
rewrite
  (ideal_final_s2_full_row_residual_fft_real_moment4E
    pre_bp avec row k hrow) in htail.
exact htail.
qed.

lemma ideal_final_s2_full_row_bias_residual_real_bad_mu_le_markov4
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
  ideal_final_s2_row_residual_re_profile4 pre_bp avec row k 256 /
  (ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 4).
proof.
move=> hctx hrow hk.
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)
      (fun z =>
        ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k <=
        `|creal z|))).
+ apply mu_le => z hz hbad.
  exact
    (ideal_final_s2_full_row_real_bad_implies_residual_tail
      pre_bp avec row k z hbad).
exact
  (ideal_final_s2_full_row_residual_fft_real_headroom_tail_markov4
    pre_bp avec row k hctx hrow hk).
qed.

lemma ideal_final_s2_full_row_residual_fft_imag_headroom_tail_markov4
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
      ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k <=
      `|cimag z|) <=
  ideal_final_s2_row_residual_im_profile4 pre_bp avec row k 256 /
  (ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 4).
proof.
move=> hctx hrow hk.
have hfin :=
  ideal_final_s2_full_row_residual_fft_finite
    pre_bp avec row k hrow.
have hheadroom :=
  ideal_final_s2_full_row_residual_imag_headroom_gt0
    pre_bp avec row k hctx hrow hk.
have htail :=
  finite_fourth_moment_markov
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    cimag
    (ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k)
    hfin hheadroom.
rewrite
  (ideal_final_s2_full_row_residual_fft_imag_moment4E
    pre_bp avec row k hrow) in htail.
exact htail.
qed.

lemma ideal_final_s2_full_row_bias_residual_imag_bad_mu_le_markov4
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
  ideal_final_s2_row_residual_im_profile4 pre_bp avec row k 256 /
  (ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 4).
proof.
move=> hctx hrow hk.
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)
      (fun z =>
        ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k <=
        `|cimag z|))).
+ apply mu_le => z hz hbad.
  exact
    (ideal_final_s2_full_row_imag_bad_implies_residual_tail
      pre_bp avec row k z hbad).
exact
  (ideal_final_s2_full_row_residual_fft_imag_headroom_tail_markov4
    pre_bp avec row k hctx hrow hk).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze.
