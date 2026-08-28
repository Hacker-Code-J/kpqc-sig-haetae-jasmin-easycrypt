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
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze.

(* This layer closes the fixed-context row-local ideal residual odd-DFT
   eighth-moment recurrence using the already established signed third/fifth
   and exact sixth-moment profiles.  It does not claim any tail bound, random-
   context law, actual/fixed-point FFT behavior, SHAKE coupling, or numerical
   security level. *)

op ideal_final_s2_row_residual_re_moment8_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (creal (cpow (odd_root k) j) ^ 8) *
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment8_at
      pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_im_moment8_term
    (pre_bp avec : BArray8192.t) (row k j : int) : real =
  (cimag (cpow (odd_root k) j) ^ 8) *
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment8_at
      pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_row_residual_re_profile8
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
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
      ideal_final_s2_row_residual_re_moment8_term pre_bp avec row k j)
    0 n.

op ideal_final_s2_row_residual_im_profile8
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
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
      ideal_final_s2_row_residual_im_moment8_term pre_bp avec row k j)
    0 n.

lemma exp_dprod_centered_eighth_step ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  weight da = 1%r =>
  weight db = 1%r =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 8) =
  E da (fun a => f a ^ 8) +
  28%r * E da (fun a => f a ^ 6) * E db (fun b => g b ^ 2) +
  56%r * E da (fun a => f a ^ 5) * E db (fun b => g b ^ 3) +
  70%r * E da (fun a => f a ^ 4) * E db (fun b => g b ^ 4) +
  56%r * E da (fun a => f a ^ 3) * E db (fun b => g b ^ 5) +
  28%r * E da (fun a => f a ^ 2) * E db (fun b => g b ^ 6) +
  E db (fun b => g b ^ 8).
proof.
move=> hfina hfinb hwda hwdb hEf0 hEg0.
have hfinprod : is_finite (support (da `*` db)).
+ apply finite_dprod => //.
rewrite
  (eq_exp
    (da `*` db)
    (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 8)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 8 +
      8%r * (f ab.`1 ^ 7 * g ab.`2) +
      28%r * (f ab.`1 ^ 6 * g ab.`2 ^ 2) +
      56%r * (f ab.`1 ^ 5 * g ab.`2 ^ 3) +
      70%r * (f ab.`1 ^ 4 * g ab.`2 ^ 4) +
      56%r * (f ab.`1 ^ 3 * g ab.`2 ^ 5) +
      28%r * (f ab.`1 ^ 2 * g ab.`2 ^ 6) +
      8%r * (f ab.`1 * g ab.`2 ^ 7) +
      g ab.`2 ^ 8)).
+ move=> [a b] hab /=.
   ring.
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 8 +
      8%r * (f ab.`1 ^ 7 * g ab.`2) +
      28%r * (f ab.`1 ^ 6 * g ab.`2 ^ 2) +
      56%r * (f ab.`1 ^ 5 * g ab.`2 ^ 3) +
      70%r * (f ab.`1 ^ 4 * g ab.`2 ^ 4) +
      56%r * (f ab.`1 ^ 3 * g ab.`2 ^ 5) +
      28%r * (f ab.`1 ^ 2 * g ab.`2 ^ 6) +
      8%r * (f ab.`1 * g ab.`2 ^ 7))
    (fun (ab : 'a * 'b) => g ab.`2 ^ 8)
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 8 +
      8%r * (f ab.`1 ^ 7 * g ab.`2) +
      28%r * (f ab.`1 ^ 6 * g ab.`2 ^ 2) +
      56%r * (f ab.`1 ^ 5 * g ab.`2 ^ 3) +
      70%r * (f ab.`1 ^ 4 * g ab.`2 ^ 4) +
      56%r * (f ab.`1 ^ 3 * g ab.`2 ^ 5) +
      28%r * (f ab.`1 ^ 2 * g ab.`2 ^ 6))
    (fun (ab : 'a * 'b) => 8%r * (f ab.`1 * g ab.`2 ^ 7))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 8 +
      8%r * (f ab.`1 ^ 7 * g ab.`2) +
      28%r * (f ab.`1 ^ 6 * g ab.`2 ^ 2) +
      56%r * (f ab.`1 ^ 5 * g ab.`2 ^ 3) +
      70%r * (f ab.`1 ^ 4 * g ab.`2 ^ 4) +
      56%r * (f ab.`1 ^ 3 * g ab.`2 ^ 5))
    (fun (ab : 'a * 'b) => 28%r * (f ab.`1 ^ 2 * g ab.`2 ^ 6))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 8 +
      8%r * (f ab.`1 ^ 7 * g ab.`2) +
      28%r * (f ab.`1 ^ 6 * g ab.`2 ^ 2) +
      56%r * (f ab.`1 ^ 5 * g ab.`2 ^ 3) +
      70%r * (f ab.`1 ^ 4 * g ab.`2 ^ 4))
    (fun (ab : 'a * 'b) => 56%r * (f ab.`1 ^ 3 * g ab.`2 ^ 5))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 8 +
      8%r * (f ab.`1 ^ 7 * g ab.`2) +
      28%r * (f ab.`1 ^ 6 * g ab.`2 ^ 2) +
      56%r * (f ab.`1 ^ 5 * g ab.`2 ^ 3))
    (fun (ab : 'a * 'b) => 70%r * (f ab.`1 ^ 4 * g ab.`2 ^ 4))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 8 +
      8%r * (f ab.`1 ^ 7 * g ab.`2) +
      28%r * (f ab.`1 ^ 6 * g ab.`2 ^ 2))
    (fun (ab : 'a * 'b) => 56%r * (f ab.`1 ^ 5 * g ab.`2 ^ 3))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) =>
      f ab.`1 ^ 8 +
      8%r * (f ab.`1 ^ 7 * g ab.`2))
    (fun (ab : 'a * 'b) => 28%r * (f ab.`1 ^ 6 * g ab.`2 ^ 2))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (expD
    (da `*` db)
    (fun (ab : 'a * 'b) => f ab.`1 ^ 8)
    (fun (ab : 'a * 'b) => 8%r * (f ab.`1 ^ 7 * g ab.`2))
    (hasE_finite _ _ hfinprod)
    (hasE_finite _ _ hfinprod)).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_left_finite da db (fun a => f a ^ 8))
  1:hfina 1:hfinb hwdb.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .exp_dprod_right_finite da db (fun b => g b ^ 8))
  1:hfina 1:hfinb hwda.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .exp_dprod_scaled_mul_factor
      da db (fun a => f a ^ 7) g 8%r hfina hfinb).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .exp_dprod_scaled_mul_factor
      da db (fun a => f a ^ 6) (fun b => g b ^ 2) 28%r hfina hfinb).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .exp_dprod_scaled_mul_factor
      da db (fun a => f a ^ 5) (fun b => g b ^ 3) 56%r hfina hfinb).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .exp_dprod_scaled_mul_factor
      da db (fun a => f a ^ 4) (fun b => g b ^ 4) 70%r hfina hfinb).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .exp_dprod_scaled_mul_factor
      da db (fun a => f a ^ 3) (fun b => g b ^ 5) 56%r hfina hfinb).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .exp_dprod_scaled_mul_factor
      da db (fun a => f a ^ 2) (fun b => g b ^ 6) 28%r hfina hfinb).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .exp_dprod_scaled_mul_factor
      da db f (fun b => g b ^ 7) 8%r hfina hfinb).
rewrite hEf0 hEg0.
ring.
qed.

lemma exp_dprod_add_eighth_centered ['a 'b]
    (da : 'a distr) (db : 'b distr) (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  is_lossless da =>
  is_lossless db =>
  E da f = 0%r =>
  E db g = 0%r =>
  E (da `*` db) (fun (ab : 'a * 'b) => (f ab.`1 + g ab.`2) ^ 8) =
  E da (fun a => f a ^ 8) +
  28%r * E da (fun a => f a ^ 6) * E db (fun b => g b ^ 2) +
  56%r * E da (fun a => f a ^ 5) * E db (fun b => g b ^ 3) +
  70%r * E da (fun a => f a ^ 4) * E db (fun b => g b ^ 4) +
  56%r * E da (fun a => f a ^ 3) * E db (fun b => g b ^ 5) +
  28%r * E da (fun a => f a ^ 2) * E db (fun b => g b ^ 6) +
  E db (fun b => g b ^ 8).
proof.
move=> hfina hfinb hlla hllb hEf0 hEg0.
rewrite /is_lossless in hlla.
rewrite /is_lossless in hllb.
exact
  (exp_dprod_centered_eighth_step
    da db f g hfina hfinb hlla hllb hEf0 hEg0).
qed.

lemma ideal_final_s2_row_residual_scaled_exp_eighth
    pre_bp avec row j (w : real) :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x =>
      (ideal_final_s2_row_residual_value pre_bp avec row j x * w) ^ 8) =
  w ^ 8 *
    Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_moment8_at
        pre_bp avec (ideal_final_s2_row_index row j).
proof.
have -> :
    (fun x =>
      (ideal_final_s2_row_residual_value pre_bp avec row j x * w) ^ 8) =
    (fun x =>
      w ^ 8 * ideal_final_s2_row_residual_value pre_bp avec row j x ^ 8).
+ apply fun_ext => x.
  ring.
rewrite
  (expZ
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (w ^ 8)
    (fun x => ideal_final_s2_row_residual_value pre_bp avec row j x ^ 8)).
rewrite
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_eta_centered_trit_expE.
rewrite /ideal_final_s2_row_residual_value
        /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_moment8_at.
trivial.
qed.

lemma ideal_final_s2_row_residual_re_term_exp_eighth
    pre_bp avec row k j :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_re_term pre_bp avec row k j x ^ 8) =
  ideal_final_s2_row_residual_re_moment8_term pre_bp avec row k j.
proof.
rewrite /ideal_final_s2_row_residual_re_term
        /ideal_final_s2_row_residual_re_moment8_term.
exact
  (ideal_final_s2_row_residual_scaled_exp_eighth
    pre_bp avec row j (creal (cpow (odd_root k) j))).
qed.

lemma ideal_final_s2_row_residual_im_term_exp_eighth
    pre_bp avec row k j :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_im_term pre_bp avec row k j x ^ 8) =
  ideal_final_s2_row_residual_im_moment8_term pre_bp avec row k j.
proof.
rewrite /ideal_final_s2_row_residual_im_term
        /ideal_final_s2_row_residual_im_moment8_term.
exact
  (ideal_final_s2_row_residual_scaled_exp_eighth
    pre_bp avec row j (cimag (cpow (odd_root k) j))).
qed.

lemma ideal_final_s2_row_residual_re_prefix_eighthE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_re_prefix pre_bp avec row k n xs ^ 8) =
  ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n.
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
          /ideal_final_s2_row_residual_re_profile8.
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
      ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 8)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 8) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2) ^ 8)).
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
  (exp_dprod_add_eighth_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_re_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_prefix_sixthE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_term_exp_square
      pre_bp avec row k n hrow hn256).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_prefix_fifthE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_term_exp_cube
      pre_bp avec row k n).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_prefix_fourthE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_term_exp_fourth
      pre_bp avec row k n hrow hn256).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_prefix_thirdE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_term_exp_fifth
      pre_bp avec row k n).
rewrite
  (ideal_final_s2_row_residual_re_prefix_sqE
    pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_term_exp_sixth
      pre_bp avec row k n).
rewrite
  (ideal_final_s2_row_residual_re_term_exp_eighth pre_bp avec row k n).
rewrite /ideal_final_s2_row_residual_re_profile8.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
ring.
qed.

lemma ideal_final_s2_row_residual_im_prefix_eighthE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_im_prefix pre_bp avec row k n xs ^ 8) =
  ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n.
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
          /ideal_final_s2_row_residual_im_profile8.
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
      ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 8)
    (hasE_finite _ _ hfin_map)).
rewrite
  (eq_exp
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    ((fun xs =>
       ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 8) \o
     (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 +
       ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2) ^ 8)).
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
  (exp_dprod_add_eighth_centered
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n)
    (ideal_final_s2_row_residual_im_term pre_bp avec row k n)
    hfin_n hfin_trit hll_n hll_trit hmean_prefix hmean_term).
rewrite ih 1:hnprev.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_prefix_sixthE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_term_exp_square
      pre_bp avec row k n hrow hn256).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_prefix_fifthE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_term_exp_cube
      pre_bp avec row k n).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_prefix_fourthE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_term_exp_fourth
      pre_bp avec row k n hrow hn256).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_prefix_thirdE
      pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_term_exp_fifth
      pre_bp avec row k n).
rewrite
  (ideal_final_s2_row_residual_im_prefix_sqE
    pre_bp avec row k n hrow hnprev).
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_term_exp_sixth
      pre_bp avec row k n).
rewrite
  (ideal_final_s2_row_residual_im_term_exp_eighth pre_bp avec row k n).
rewrite /ideal_final_s2_row_residual_im_profile8.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
ring.
qed.

lemma ideal_final_s2_row_residual_fft_real_moment8E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)
    (fun z => creal z ^ 8) =
  ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256.
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
    (fun z => creal z ^ 8)
    (hasE_finite _ _ hfin)).
rewrite
  (eq_exp
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_source_distribution 256)
    ((fun z => creal z ^ 8) \o
     (fun xs =>
       Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k))
    (fun xs =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_re_prefix pre_bp avec row k 256 xs ^ 8)).
+ move=> xs hxs /=.
   rewrite /(\o).
   rewrite
     (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_residual_odd_dft256_sample_creal
         pre_bp avec row xs k).
   trivial.
have h256 : 0 <= 256 <= 256 by smt().
exact
  (ideal_final_s2_row_residual_re_prefix_eighthE
    pre_bp avec row k 256 hrow h256).
qed.

lemma ideal_final_s2_row_residual_fft_imag_moment8E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)
    (fun z => cimag z ^ 8) =
  ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256.
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
    (fun z => cimag z ^ 8)
    (hasE_finite _ _ hfin)).
rewrite
  (eq_exp
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_source_distribution 256)
    ((fun z => cimag z ^ 8) \o
     (fun xs =>
       Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k))
    (fun xs =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_im_prefix pre_bp avec row k 256 xs ^ 8)).
+ move=> xs hxs /=.
   rewrite /(\o).
   rewrite
     (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_residual_odd_dft256_sample_cimag
         pre_bp avec row xs k).
   trivial.
have h256 : 0 <= 256 <= 256 by smt().
exact
  (ideal_final_s2_row_residual_im_prefix_eighthE
    pre_bp avec row k 256 hrow h256).
qed.

lemma ideal_final_s2_full_row_residual_fft_real_moment8E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k)
    (fun z => creal z ^ 8) =
  ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256.
proof.
move=> hrow.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .ideal_final_s2_full_row_residual_odd_dft256_distributionE
      pre_bp avec row k hrow).
exact
  (ideal_final_s2_row_residual_fft_real_moment8E
    pre_bp avec row k hrow).
qed.

lemma ideal_final_s2_full_row_residual_fft_imag_moment8E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k)
    (fun z => cimag z ^ 8) =
  ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256.
proof.
move=> hrow.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .ideal_final_s2_full_row_residual_odd_dft256_distributionE
      pre_bp avec row k hrow).
exact
  (ideal_final_s2_row_residual_fft_imag_moment8E
    pre_bp avec row k hrow).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze.
