require import AllCore DList Distr Finite IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23SingularFFTSpec
  KeygenM23SingularSpec
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze.

(* This layer fills the signed lower-moment data needed by an exact eighth
   moment recurrence for the fixed-context row-local ideal residual odd DFT.
   It keeps the third and fifth moments signed and exposes the sixth-moment
   skew cross term.  It does not claim a sixth- or eighth-moment tail bound,
   random-context independence, actual/fixed-point FFT correctness, SHAKE
   coupling, or a numerical security level. *)

op ideal_final_s2_residual_moment3_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  (((Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
       .ideal_final_s2_residual_coord pre_bp avec i (-1)) ^ 3) +
   ((Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
       .ideal_final_s2_residual_coord pre_bp avec i 0) ^ 3) +
   ((Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
       .ideal_final_s2_residual_coord pre_bp avec i 1) ^ 3)) / 3%r.

lemma ideal_final_s2_residual_moment3_bridge pre_bp avec i :
  ideal_final_s2_residual_moment3_at pre_bp avec i =
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_centered_moment3_at pre_bp avec i.
proof.
rewrite /ideal_final_s2_residual_moment3_at
        /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_coord.
rewrite /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_moment3_at
        /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
          .ideal_final_s2_centered_moment3
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_residual_at.
trivial.
qed.

op ideal_final_s2_row_residual_re_moment3_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (creal (cpow (odd_root k) j) ^ 3) *
  ideal_final_s2_residual_moment3_at
    pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_im_moment3_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (cimag (cpow (odd_root k) j) ^ 3) *
  ideal_final_s2_residual_moment3_at
    pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_re_moment5_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (creal (cpow (odd_root k) j) ^ 5) *
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment5_at
      pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_im_moment5_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (cimag (cpow (odd_root k) j) ^ 5) *
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment5_at
      pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_re_moment6_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (creal (cpow (odd_root k) j) ^ 6) *
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment6_at
      pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_im_moment6_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (cimag (cpow (odd_root k) j) ^ 6) *
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment6_at
      pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_re_profile3
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
    (fun j =>
      ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j)
    0 n.

op ideal_final_s2_row_residual_im_profile3
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
    (fun j =>
      ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j)
    0 n.

op ideal_final_s2_row_residual_re_profile5
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
    (fun j =>
      10%r * ideal_final_s2_row_residual_re_profile3 pre_bp avec row k j *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
      10%r *
        ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
        ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j +
      ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j)
    0 n.

op ideal_final_s2_row_residual_im_profile5
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
    (fun j =>
      10%r * ideal_final_s2_row_residual_im_profile3 pre_bp avec row k j *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
      10%r *
        ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
        ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j +
      ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j)
    0 n.

op ideal_final_s2_row_residual_re_profile6
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
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
    0 n.

op ideal_final_s2_row_residual_im_profile6
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
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
    0 n.

lemma exp_dprod_centered_third_step ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  weight da = 1%r =>
  weight db = 1%r =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 3) =
  E da (fun a => f a ^ 3) +
  E db (fun b => g b ^ 3).
proof.
move=> hfina hfinb hwda hwdb hEf0 hEg0.
have hfinprod : is_finite (support (da `*` db)).
+ apply finite_dprod => //.
rewrite
  (eq_exp
    (da `*` db)
    (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 3)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 3 +
      3%r * (f ab.`1 ^ 2 * g ab.`2) +
      3%r * (f ab.`1 * g ab.`2 ^ 2) +
      g ab.`2 ^ 3)).
+ move=> [a b] hab /=.
  ring.
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 3 +
      3%r * (f ab.`1 ^ 2 * g ab.`2) +
      3%r * (f ab.`1 * g ab.`2 ^ 2))
    (fun (ab : 'a * 'b) => g ab.`2 ^ 3)
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 3 +
      3%r * (f ab.`1 ^ 2 * g ab.`2))
    (fun (ab : 'a * 'b) => 3%r * (f ab.`1 * g ab.`2 ^ 2))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) => f ab.`1 ^ 3)
    (fun (ab : 'a * 'b) => 3%r * (f ab.`1 ^ 2 * g ab.`2))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_left_finite da db (fun a => f a ^ 3))
  1:hfina 1:hfinb hwdb.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_right_finite da db (fun b => g b ^ 3))
  1:hfina 1:hfinb hwda.
have -> :
    (fun (ab : 'a * 'b) => 3%r * (f ab.`1 ^ 2 * g ab.`2)) =
    (fun (ab : 'a * 'b) => 3%r * ((f ab.`1 ^ 2) * g ab.`2)).
+ apply fun_ext => ab.
  ring.
rewrite
  (expZ
    (da `*` db) 3%r
    (fun (ab : 'a * 'b) => (f ab.`1 ^ 2) * g ab.`2)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_mul_factor da db (fun a => f a ^ 2) g)
  1:hfina 1:hfinb hEg0.
have -> :
    (fun (ab : 'a * 'b) => 3%r * (f ab.`1 * g ab.`2 ^ 2)) =
    (fun (ab : 'a * 'b) => 3%r * (f ab.`1 * (g ab.`2 ^ 2))).
+ apply fun_ext => ab.
  ring.
rewrite
  (expZ
    (da `*` db) 3%r
    (fun (ab : 'a * 'b) => f ab.`1 * (g ab.`2 ^ 2))).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_mul_factor da db f (fun b => g b ^ 2))
  1:hfina 1:hfinb hEf0.
ring.
qed.

lemma exp_dprod_scaled_mul_factor ['a 'b]
    (da : 'a distr) (db : 'b distr)
    (u : 'a -> real) (v : 'b -> real) (c : real) :
  is_finite (support da) =>
  is_finite (support db) =>
  E (da `*` db)
    (fun (ab : 'a * 'b) => c * (u ab.`1 * v ab.`2)) =
  c * E da u * E db v.
proof.
move=> hfina hfinb.
rewrite
  (expZ
    (da `*` db) c
    (fun (ab : 'a * 'b) => u ab.`1 * v ab.`2)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_mul_factor da db u v)
  1:hfina 1:hfinb.
ring.
qed.

lemma exp_dprod_centered_fifth_step ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  weight da = 1%r =>
  weight db = 1%r =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 5) =
  E da (fun a => f a ^ 5) +
  10%r * E da (fun a => f a ^ 3) * E db (fun b => g b ^ 2) +
  10%r * E da (fun a => f a ^ 2) * E db (fun b => g b ^ 3) +
  E db (fun b => g b ^ 5).
proof.
move=> hfina hfinb hwda hwdb hEf0 hEg0.
have hfinprod : is_finite (support (da `*` db)).
+ apply finite_dprod => //.
rewrite
  (eq_exp
    (da `*` db)
    (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 5)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 5 +
      5%r * (f ab.`1 ^ 4 * g ab.`2) +
      10%r * (f ab.`1 ^ 3 * g ab.`2 ^ 2) +
      10%r * (f ab.`1 ^ 2 * g ab.`2 ^ 3) +
      5%r * (f ab.`1 * g ab.`2 ^ 4) +
      g ab.`2 ^ 5)).
+ move=> [a b] hab /=.
  ring.
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 5 +
      5%r * (f ab.`1 ^ 4 * g ab.`2) +
      10%r * (f ab.`1 ^ 3 * g ab.`2 ^ 2) +
      10%r * (f ab.`1 ^ 2 * g ab.`2 ^ 3) +
      5%r * (f ab.`1 * g ab.`2 ^ 4))
    (fun (ab : 'a * 'b) => g ab.`2 ^ 5)
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 5 +
      5%r * (f ab.`1 ^ 4 * g ab.`2) +
      10%r * (f ab.`1 ^ 3 * g ab.`2 ^ 2) +
      10%r * (f ab.`1 ^ 2 * g ab.`2 ^ 3))
    (fun (ab : 'a * 'b) => 5%r * (f ab.`1 * g ab.`2 ^ 4))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 5 +
      5%r * (f ab.`1 ^ 4 * g ab.`2) +
      10%r * (f ab.`1 ^ 3 * g ab.`2 ^ 2))
    (fun (ab : 'a * 'b) => 10%r * (f ab.`1 ^ 2 * g ab.`2 ^ 3))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 5 +
      5%r * (f ab.`1 ^ 4 * g ab.`2))
    (fun (ab : 'a * 'b) => 10%r * (f ab.`1 ^ 3 * g ab.`2 ^ 2))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) => f ab.`1 ^ 5)
    (fun (ab : 'a * 'b) => 5%r * (f ab.`1 ^ 4 * g ab.`2))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_left_finite da db (fun a => f a ^ 5))
  1:hfina 1:hfinb hwdb.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_right_finite da db (fun b => g b ^ 5))
  1:hfina 1:hfinb hwda.
rewrite
  (exp_dprod_scaled_mul_factor
    da db (fun a => f a ^ 4) g 5%r hfina hfinb).
rewrite
  (exp_dprod_scaled_mul_factor
    da db (fun a => f a ^ 3) (fun b => g b ^ 2) 10%r hfina hfinb).
rewrite
  (exp_dprod_scaled_mul_factor
    da db (fun a => f a ^ 2) (fun b => g b ^ 3) 10%r hfina hfinb).
rewrite
  (exp_dprod_scaled_mul_factor
    da db f (fun b => g b ^ 4) 5%r hfina hfinb).
rewrite hEf0 hEg0.
ring.
qed.

lemma exp_dprod_centered_sixth_step ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  weight da = 1%r =>
  weight db = 1%r =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 6) =
  E da (fun a => f a ^ 6) +
  15%r * E da (fun a => f a ^ 4) * E db (fun b => g b ^ 2) +
  20%r * E da (fun a => f a ^ 3) * E db (fun b => g b ^ 3) +
  15%r * E da (fun a => f a ^ 2) * E db (fun b => g b ^ 4) +
  E db (fun b => g b ^ 6).
proof.
move=> hfina hfinb hwda hwdb hEf0 hEg0.
have hfinprod : is_finite (support (da `*` db)).
+ apply finite_dprod => //.
rewrite
  (eq_exp
    (da `*` db)
    (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 6)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 6 +
      6%r * (f ab.`1 ^ 5 * g ab.`2) +
      15%r * (f ab.`1 ^ 4 * g ab.`2 ^ 2) +
      20%r * (f ab.`1 ^ 3 * g ab.`2 ^ 3) +
      15%r * (f ab.`1 ^ 2 * g ab.`2 ^ 4) +
      6%r * (f ab.`1 * g ab.`2 ^ 5) +
      g ab.`2 ^ 6)).
+ move=> [a b] hab /=.
  ring.
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 6 +
      6%r * (f ab.`1 ^ 5 * g ab.`2) +
      15%r * (f ab.`1 ^ 4 * g ab.`2 ^ 2) +
      20%r * (f ab.`1 ^ 3 * g ab.`2 ^ 3) +
      15%r * (f ab.`1 ^ 2 * g ab.`2 ^ 4) +
      6%r * (f ab.`1 * g ab.`2 ^ 5))
    (fun (ab : 'a * 'b) => g ab.`2 ^ 6)
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 6 +
      6%r * (f ab.`1 ^ 5 * g ab.`2) +
      15%r * (f ab.`1 ^ 4 * g ab.`2 ^ 2) +
      20%r * (f ab.`1 ^ 3 * g ab.`2 ^ 3) +
      15%r * (f ab.`1 ^ 2 * g ab.`2 ^ 4))
    (fun (ab : 'a * 'b) => 6%r * (f ab.`1 * g ab.`2 ^ 5))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 6 +
      6%r * (f ab.`1 ^ 5 * g ab.`2) +
      15%r * (f ab.`1 ^ 4 * g ab.`2 ^ 2) +
      20%r * (f ab.`1 ^ 3 * g ab.`2 ^ 3))
    (fun (ab : 'a * 'b) => 15%r * (f ab.`1 ^ 2 * g ab.`2 ^ 4))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 6 +
      6%r * (f ab.`1 ^ 5 * g ab.`2) +
      15%r * (f ab.`1 ^ 4 * g ab.`2 ^ 2))
    (fun (ab : 'a * 'b) => 20%r * (f ab.`1 ^ 3 * g ab.`2 ^ 3))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 6 +
      6%r * (f ab.`1 ^ 5 * g ab.`2))
    (fun (ab : 'a * 'b) => 15%r * (f ab.`1 ^ 4 * g ab.`2 ^ 2))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) => f ab.`1 ^ 6)
    (fun (ab : 'a * 'b) => 6%r * (f ab.`1 ^ 5 * g ab.`2))
    (hasE_finite _ _ hfinprod) (hasE_finite _ _ hfinprod)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_left_finite da db (fun a => f a ^ 6))
  1:hfina 1:hfinb hwdb.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_right_finite da db (fun b => g b ^ 6))
  1:hfina 1:hfinb hwda.
rewrite
  (exp_dprod_scaled_mul_factor
    da db (fun a => f a ^ 5) g 6%r hfina hfinb).
rewrite
  (exp_dprod_scaled_mul_factor
    da db (fun a => f a ^ 4) (fun b => g b ^ 2) 15%r hfina hfinb).
rewrite
  (exp_dprod_scaled_mul_factor
    da db (fun a => f a ^ 3) (fun b => g b ^ 3) 20%r hfina hfinb).
rewrite
  (exp_dprod_scaled_mul_factor
    da db (fun a => f a ^ 2) (fun b => g b ^ 4) 15%r hfina hfinb).
rewrite
  (exp_dprod_scaled_mul_factor
    da db f (fun b => g b ^ 5) 6%r hfina hfinb).
rewrite hEf0 hEg0.
ring.
qed.

lemma exp_dprod_add_third_centered ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  is_lossless da =>
  is_lossless db =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 3) =
  E da (fun a => f a ^ 3) +
  E db (fun b => g b ^ 3).
proof.
move=> hfina hfinb hlla hllb hEf0 hEg0.
rewrite /is_lossless in hlla.
rewrite /is_lossless in hllb.
exact
  (exp_dprod_centered_third_step
    da db f g hfina hfinb hlla hllb hEf0 hEg0).
qed.

lemma exp_dprod_add_fifth_centered ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  is_lossless da =>
  is_lossless db =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 5) =
  E da (fun a => f a ^ 5) +
  10%r * E da (fun a => f a ^ 3) * E db (fun b => g b ^ 2) +
  10%r * E da (fun a => f a ^ 2) * E db (fun b => g b ^ 3) +
  E db (fun b => g b ^ 5).
proof.
move=> hfina hfinb hlla hllb hEf0 hEg0.
rewrite /is_lossless in hlla.
rewrite /is_lossless in hllb.
exact
  (exp_dprod_centered_fifth_step
    da db f g hfina hfinb hlla hllb hEf0 hEg0).
qed.

lemma exp_dprod_add_sixth_centered ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  is_lossless da =>
  is_lossless db =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 6) =
  E da (fun a => f a ^ 6) +
  15%r * E da (fun a => f a ^ 4) * E db (fun b => g b ^ 2) +
  20%r * E da (fun a => f a ^ 3) * E db (fun b => g b ^ 3) +
  15%r * E da (fun a => f a ^ 2) * E db (fun b => g b ^ 4) +
  E db (fun b => g b ^ 6).
proof.
move=> hfina hfinb hlla hllb hEf0 hEg0.
rewrite /is_lossless in hlla.
rewrite /is_lossless in hllb.
exact
  (exp_dprod_centered_sixth_step
    da db f g hfina hfinb hlla hllb hEf0 hEg0).
qed.

lemma ideal_final_s2_row_residual_scaled_exp_cube
    pre_bp avec row j (w : real) :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => (ideal_final_s2_row_residual_value pre_bp avec row j x * w) ^ 3) =
  w ^ 3 *
    ideal_final_s2_residual_moment3_at
      pre_bp avec (ideal_final_s2_row_index row j).
proof.
have -> :
    (fun x => (ideal_final_s2_row_residual_value pre_bp avec row j x * w) ^ 3) =
    (fun x =>
      w ^ 3 * ideal_final_s2_row_residual_value pre_bp avec row j x ^ 3).
+ apply fun_ext => x.
  ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (w ^ 3)
    (fun x => ideal_final_s2_row_residual_value pre_bp avec row j x ^ 3)).
rewrite
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_eta_centered_trit_expE.
rewrite /ideal_final_s2_row_residual_value
        /ideal_final_s2_residual_moment3_at.
trivial.
qed.

lemma ideal_final_s2_row_residual_scaled_exp_fifth
    pre_bp avec row j (w : real) :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => (ideal_final_s2_row_residual_value pre_bp avec row j x * w) ^ 5) =
  w ^ 5 *
    Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .ideal_final_s2_residual_moment5_at
        pre_bp avec (ideal_final_s2_row_index row j).
proof.
have -> :
    (fun x => (ideal_final_s2_row_residual_value pre_bp avec row j x * w) ^ 5) =
    (fun x =>
      w ^ 5 * ideal_final_s2_row_residual_value pre_bp avec row j x ^ 5).
+ apply fun_ext => x.
  ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (w ^ 5)
    (fun x => ideal_final_s2_row_residual_value pre_bp avec row j x ^ 5)).
rewrite
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_eta_centered_trit_expE.
rewrite /ideal_final_s2_row_residual_value
        /Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
          .ideal_final_s2_residual_moment5_at.
trivial.
qed.

lemma ideal_final_s2_row_residual_scaled_exp_sixth
    pre_bp avec row j (w : real) :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => (ideal_final_s2_row_residual_value pre_bp avec row j x * w) ^ 6) =
  w ^ 6 *
    Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .ideal_final_s2_residual_moment6_at
        pre_bp avec (ideal_final_s2_row_index row j).
proof.
have -> :
    (fun x => (ideal_final_s2_row_residual_value pre_bp avec row j x * w) ^ 6) =
    (fun x =>
      w ^ 6 * ideal_final_s2_row_residual_value pre_bp avec row j x ^ 6).
+ apply fun_ext => x.
  ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (w ^ 6)
    (fun x => ideal_final_s2_row_residual_value pre_bp avec row j x ^ 6)).
rewrite
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_eta_centered_trit_expE.
rewrite /ideal_final_s2_row_residual_value
        /Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
          .ideal_final_s2_residual_moment6_at.
trivial.
qed.

lemma ideal_final_s2_row_residual_re_term_exp_cube
    pre_bp avec row k j :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_re_term pre_bp avec row k j x ^ 3) =
  ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j.
proof.
rewrite /ideal_final_s2_row_residual_re_term
        /ideal_final_s2_row_residual_re_moment3_term.
exact
  (ideal_final_s2_row_residual_scaled_exp_cube
    pre_bp avec row j (creal (cpow (odd_root k) j))).
qed.

lemma ideal_final_s2_row_residual_im_term_exp_cube
    pre_bp avec row k j :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_im_term pre_bp avec row k j x ^ 3) =
  ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j.
proof.
rewrite /ideal_final_s2_row_residual_im_term
        /ideal_final_s2_row_residual_im_moment3_term.
exact
  (ideal_final_s2_row_residual_scaled_exp_cube
    pre_bp avec row j (cimag (cpow (odd_root k) j))).
qed.

lemma ideal_final_s2_row_residual_re_term_exp_fifth
    pre_bp avec row k j :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_re_term pre_bp avec row k j x ^ 5) =
  ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j.
proof.
rewrite /ideal_final_s2_row_residual_re_term
        /ideal_final_s2_row_residual_re_moment5_term.
exact
  (ideal_final_s2_row_residual_scaled_exp_fifth
    pre_bp avec row j (creal (cpow (odd_root k) j))).
qed.

lemma ideal_final_s2_row_residual_im_term_exp_fifth
    pre_bp avec row k j :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_im_term pre_bp avec row k j x ^ 5) =
  ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j.
proof.
rewrite /ideal_final_s2_row_residual_im_term
        /ideal_final_s2_row_residual_im_moment5_term.
exact
  (ideal_final_s2_row_residual_scaled_exp_fifth
    pre_bp avec row j (cimag (cpow (odd_root k) j))).
qed.

lemma ideal_final_s2_row_residual_re_term_exp_sixth
    pre_bp avec row k j :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_re_term pre_bp avec row k j x ^ 6) =
  ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j.
proof.
rewrite /ideal_final_s2_row_residual_re_term
        /ideal_final_s2_row_residual_re_moment6_term.
exact
  (ideal_final_s2_row_residual_scaled_exp_sixth
    pre_bp avec row j (creal (cpow (odd_root k) j))).
qed.

lemma ideal_final_s2_row_residual_im_term_exp_sixth
    pre_bp avec row k j :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_im_term pre_bp avec row k j x ^ 6) =
  ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j.
proof.
rewrite /ideal_final_s2_row_residual_im_term
        /ideal_final_s2_row_residual_im_moment6_term.
exact
  (ideal_final_s2_row_residual_scaled_exp_sixth
    pre_bp avec row j (cimag (cpow (odd_root k) j))).
qed.

lemma ideal_final_s2_row_residual_re_prefix_thirdE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_re_prefix pre_bp avec row k n xs ^ 3) =
  ideal_final_s2_row_residual_re_profile3 pre_bp avec row k n.
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
          /ideal_final_s2_row_residual_re_profile3.
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
      ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 3)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 3) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2) ^ 3)).
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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_term_exp_zero
      pre_bp avec row k n hrow hn256.
rewrite
  (exp_dprod_add_third_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_re_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (ideal_final_s2_row_residual_re_term_exp_cube pre_bp avec row k n).
rewrite /ideal_final_s2_row_residual_re_profile3.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
qed.

lemma ideal_final_s2_row_residual_im_prefix_thirdE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_im_prefix pre_bp avec row k n xs ^ 3) =
  ideal_final_s2_row_residual_im_profile3 pre_bp avec row k n.
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
          /ideal_final_s2_row_residual_im_profile3.
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
      ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 3)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 3) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2) ^ 3)).
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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_term_exp_zero
      pre_bp avec row k n hrow hn256.
rewrite
  (exp_dprod_add_third_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_im_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (ideal_final_s2_row_residual_im_term_exp_cube pre_bp avec row k n).
rewrite /ideal_final_s2_row_residual_im_profile3.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
qed.

lemma ideal_final_s2_row_residual_re_prefix_fifthE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_re_prefix pre_bp avec row k n xs ^ 5) =
  ideal_final_s2_row_residual_re_profile5 pre_bp avec row k n.
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
          /ideal_final_s2_row_residual_re_profile5.
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
      ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 5)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 5) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2) ^ 5)).
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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_term_exp_zero
      pre_bp avec row k n hrow hn256.
rewrite
  (exp_dprod_add_fifth_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_re_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (ideal_final_s2_row_residual_re_prefix_thirdE
    pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_term_exp_square
      pre_bp avec row k n hrow hn256).
rewrite
  (ideal_final_s2_row_residual_re_prefix_sqE
    pre_bp avec row k n hrow hnprev).
rewrite
  (ideal_final_s2_row_residual_re_term_exp_cube pre_bp avec row k n).
rewrite
  (ideal_final_s2_row_residual_re_term_exp_fifth pre_bp avec row k n).
rewrite /ideal_final_s2_row_residual_re_profile5.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
ring.
qed.

lemma ideal_final_s2_row_residual_im_prefix_fifthE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_im_prefix pre_bp avec row k n xs ^ 5) =
  ideal_final_s2_row_residual_im_profile5 pre_bp avec row k n.
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
          /ideal_final_s2_row_residual_im_profile5.
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
      ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 5)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 5) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2) ^ 5)).
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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_term_exp_zero
      pre_bp avec row k n hrow hn256.
rewrite
  (exp_dprod_add_fifth_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_im_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (ideal_final_s2_row_residual_im_prefix_thirdE
    pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_term_exp_square
      pre_bp avec row k n hrow hn256).
rewrite
  (ideal_final_s2_row_residual_im_prefix_sqE
    pre_bp avec row k n hrow hnprev).
rewrite
  (ideal_final_s2_row_residual_im_term_exp_cube pre_bp avec row k n).
rewrite
  (ideal_final_s2_row_residual_im_term_exp_fifth pre_bp avec row k n).
rewrite /ideal_final_s2_row_residual_im_profile5.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
ring.
qed.

lemma ideal_final_s2_row_residual_re_prefix_sixthE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_re_prefix pre_bp avec row k n xs ^ 6) =
  ideal_final_s2_row_residual_re_profile6 pre_bp avec row k n.
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
          /ideal_final_s2_row_residual_re_profile6.
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
      ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 6)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 6) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2) ^ 6)).
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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_term_exp_zero
      pre_bp avec row k n hrow hn256.
rewrite
  (exp_dprod_add_sixth_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_re_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_prefix_fourthE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_term_exp_square
      pre_bp avec row k n hrow hn256).
rewrite
  (ideal_final_s2_row_residual_re_prefix_thirdE
    pre_bp avec row k n hrow hnprev).
rewrite
  (ideal_final_s2_row_residual_re_term_exp_cube pre_bp avec row k n).
rewrite
  (ideal_final_s2_row_residual_re_prefix_sqE
    pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_term_exp_fourth
      pre_bp avec row k n hrow hn256).
rewrite
  (ideal_final_s2_row_residual_re_term_exp_sixth pre_bp avec row k n).
rewrite /ideal_final_s2_row_residual_re_profile6.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
ring.
qed.

lemma ideal_final_s2_row_residual_im_prefix_sixthE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_im_prefix pre_bp avec row k n xs ^ 6) =
  ideal_final_s2_row_residual_im_profile6 pre_bp avec row k n.
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
          /ideal_final_s2_row_residual_im_profile6.
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
      ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 6)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 6) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2) ^ 6)).
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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_term_exp_zero
      pre_bp avec row k n hrow hn256.
rewrite
  (exp_dprod_add_sixth_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_im_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_prefix_fourthE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_term_exp_square
      pre_bp avec row k n hrow hn256).
rewrite
  (ideal_final_s2_row_residual_im_prefix_thirdE
    pre_bp avec row k n hrow hnprev).
rewrite
  (ideal_final_s2_row_residual_im_term_exp_cube pre_bp avec row k n).
rewrite
  (ideal_final_s2_row_residual_im_prefix_sqE
    pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_term_exp_fourth
      pre_bp avec row k n hrow hn256).
rewrite
  (ideal_final_s2_row_residual_im_term_exp_sixth pre_bp avec row k n).
rewrite /ideal_final_s2_row_residual_im_profile6.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
ring.
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze.
