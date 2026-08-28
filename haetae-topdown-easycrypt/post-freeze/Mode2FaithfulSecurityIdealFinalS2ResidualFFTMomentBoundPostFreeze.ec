require import AllCore DInterval DList Distr Finite IntDiv List Real
               RealSeries Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23MatrixSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTStageErrorBridge
  KeygenM23SingularSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23SingularFFTStageErrorBridge.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.

(* This file is a fixed-context, row-local ideal residual FFT moment bridge.
   The [pre_bp] and [avec] arrays are parameters, and the only randomness is
   the iid ideal centered-trit source feeding one 256-word row.  It does not
   claim anything about random contexts, the actual/fixed-point FFT, SHAKE or
   concrete sampler streams, numerical tails, cross-row interactions, or any
   prefix-energy claim beyond the exact second-moment identity below.  A tail
   bound from the second moment alone would be correspondingly weak. *)

op ideal_final_s2_row_index (row j : int) : int =
  row * KeygenM23SingularSpec.singular_words_i + j.

op ideal_final_s2_row_source_distribution (n : int) : int list distr =
  dlist
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    n.

op ideal_final_s2_row_residual_value
    (pre_bp avec : BArray8192.t) (row j x : int) : real =
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_coord
      pre_bp avec (ideal_final_s2_row_index row j) x.

op ideal_final_s2_row_residual_re_term
    (pre_bp avec : BArray8192.t) (row k j x : int) : real =
  ideal_final_s2_row_residual_value pre_bp avec row j x *
  creal (cpow (odd_root k) j).

op ideal_final_s2_row_residual_im_term
    (pre_bp avec : BArray8192.t) (row k j x : int) : real =
  ideal_final_s2_row_residual_value pre_bp avec row j x *
  cimag (cpow (odd_root k) j).

op ideal_final_s2_row_residual_re_prefix
    (pre_bp avec : BArray8192.t) (row k n : int) (xs : int list) : real =
  BRA.bigi predT
    (fun j =>
      ideal_final_s2_row_residual_re_term
        pre_bp avec row k j (nth 0 xs j))
    0 n.

op ideal_final_s2_row_residual_im_prefix
    (pre_bp avec : BArray8192.t) (row k n : int) (xs : int list) : real =
  BRA.bigi predT
    (fun j =>
      ideal_final_s2_row_residual_im_term
        pre_bp avec row k j (nth 0 xs j))
    0 n.

op ideal_final_s2_row_residual_re_profile
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
    (fun j =>
      (creal (cpow (odd_root k) j) ^ 2) *
      Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_residual_moment2_at
          pre_bp avec (ideal_final_s2_row_index row j))
    0 n.

op ideal_final_s2_row_residual_im_profile
    (pre_bp avec : BArray8192.t) (row k n : int) : real =
  BRA.bigi predT
    (fun j =>
      (cimag (cpow (odd_root k) j) ^ 2) *
      Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_residual_moment2_at
          pre_bp avec (ideal_final_s2_row_index row j))
    0 n.

op ideal_final_s2_row_residual_slice
    (pre_bp avec : BArray8192.t) (row : int) (xs : int list) : int -> complex =
  fun j =>
    cof_real
      (ideal_final_s2_row_residual_value
        pre_bp avec row j (nth 0 xs j)).

op ideal_final_s2_row_residual_odd_dft256_sample
    (pre_bp avec : BArray8192.t) (row : int) (xs : int list) (k : int) :
    complex =
  odd_dft256 (ideal_final_s2_row_residual_slice pre_bp avec row xs) k.

op ideal_final_s2_row_residual_odd_dft256_distribution
    (pre_bp avec : BArray8192.t) (row k : int) : complex distr =
  dmap
    (ideal_final_s2_row_source_distribution 256)
    (fun xs => ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k).

lemma finite_dmap ['a 'b] (d : 'a distr) (f : 'a -> 'b) :
  is_finite (support d) =>
  is_finite (support (dmap d f)).
proof.
move=> hfin.
rewrite /dmap.
apply finite_dlet => // x hx.
apply finite_dunit.
qed.

lemma exp_dprod_finite ['a 'b] (da : 'a distr) (db : 'b distr) (f : 'a * 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  E (da `*` db) f =
  E da (fun a => E db (fun b => f (a, b))).
proof.
move=> hfina hfinb.
rewrite dprod_dlet.
rewrite exp_dlet.
+ apply hasE_finite.
   apply finite_dlet; first exact hfina.
   move=> a ha.
   apply finite_dlet; first exact hfinb.
   move=> b hb.
   apply finite_dunit.
apply eq_exp => a ha /=.
rewrite exp_dlet.
+ apply hasE_finite.
   apply finite_dlet; first exact hfinb.
   move=> b hb.
   apply finite_dunit.
apply eq_exp => b hb /=.
rewrite exp_dunit.
trivial.
qed.

lemma exp_dprod_left_finite ['a 'b] (da : 'a distr) (db : 'b distr) (f : 'a -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  E (da `*` db) (fun (ab : 'a * 'b) => f ab.`1) = weight db * E da f.
proof.
move=> hfina hfinb.
rewrite
  (exp_dprod_finite da db (fun (ab : 'a * 'b) => f ab.`1) hfina hfinb).
rewrite
  (eq_exp da
    (fun a => E db (fun _ => f a))
    (fun a => weight db * f a)).
+ move=> a ha.
   simplify.
   rewrite expC.
   ring.
rewrite (expZ da (weight db) f).
ring.
qed.

lemma exp_dprod_right_finite ['a 'b] (da : 'a distr) (db : 'b distr) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  E (da `*` db) (fun (ab : 'a * 'b) => g ab.`2) = weight da * E db g.
proof.
move=> hfina hfinb.
rewrite
  (exp_dprod_finite da db (fun (ab : 'a * 'b) => g ab.`2) hfina hfinb).
rewrite
  (eq_exp da
    (fun a => E db g)
    (fun _ => E db g)).
+ move=> a ha.
   simplify.
   trivial.
rewrite expC.
ring.
qed.

lemma exp_dprod_mul_factor ['a 'b] (da : 'a distr) (db : 'b distr)
    (f : 'a -> real) (g : 'b -> real) :
  is_finite (support da) =>
  is_finite (support db) =>
  E (da `*` db) (fun (ab : 'a * 'b) => f ab.`1 * g ab.`2) =
  E da f * E db g.
proof.
move=> hfina hfinb.
have hEf : hasE da f by exact (hasE_finite da f hfina).
have hEg : hasE db g by exact (hasE_finite db g hfinb).
rewrite
  (exp_dprod_finite da db
    (fun (ab : 'a * 'b) => f ab.`1 * g ab.`2)
    hfina hfinb).
rewrite
  (eq_exp da
    (fun a => E db (fun b => f a * g b))
    (fun a => f a * E db g)).
+ move=> a ha.
   simplify.
   rewrite (expZ db (f a) g) //.
   trivial.
have -> :
    (fun a => f a * E db g) =
    (fun a => E db g * f a).
+ apply fun_ext => a.
  ring.
rewrite (expZ da (E db g) f).
ring.
qed.

lemma ideal_eta_centered_trit_expE (f : int -> real) :
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    f =
  (f (-1) + f 0 + f 1) / 3%r.
proof.
rewrite /E.
rewrite (@sumE_fin _ [-1; 0; 1]) //=.
+ move=> x hprod.
   rewrite RField.mulf_eq0 negb_or in hprod.
   move: hprod => [_ hmu].
   move/supportP: hmu.
   rewrite
     Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
       .ideal_eta_centered_trit_support.
   move=> hx.
   exact hx.
rewrite !BRA.big_consT BRA.big_nil /=.
rewrite
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_point_neg1
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_point_zero
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_point_one.
field.
trivial.
qed.

lemma ideal_final_s2_row_index_range row j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  0 <= ideal_final_s2_row_index row j <
    KeygenM23MatrixSpec.mode2_b_words_i.
proof.
rewrite /ideal_final_s2_row_index
        /KeygenM23SingularFFTSpec.mode2_s2_count_i
        /KeygenM23SingularSpec.singular_words_i
        /KeygenM23MatrixSpec.mode2_b_words_i
        /KeygenM23MatrixSpec.mode2_rows_i
        /KeygenM23MatrixSpec.poly_words_i.
smt().
qed.

lemma ideal_final_s2_row_source_distribution_lossless n :
  is_lossless (ideal_final_s2_row_source_distribution n).
proof.
rewrite /ideal_final_s2_row_source_distribution.
apply dlist_ll.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
qed.

lemma ideal_final_s2_row_source_distribution_finite n :
  0 <= n =>
  is_finite (support (ideal_final_s2_row_source_distribution n)).
proof.
move=> hn.
rewrite /ideal_final_s2_row_source_distribution.
apply uniform_finite.
apply dlist_uni.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_uniform.
qed.

lemma ideal_final_s2_row_residual_value_exp_zero
    pre_bp avec row j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_value pre_bp avec row j) =
  0%r.
proof.
move=> hrow hj.
rewrite ideal_eta_centered_trit_expE.
have hmean :=
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_three_point_mean_zero_at
      pre_bp avec (ideal_final_s2_row_index row j).
move: hmean.
rewrite /ideal_final_s2_row_residual_value.
exact.
qed.

lemma ideal_final_s2_row_residual_value_exp_square
    pre_bp avec row j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  E
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (fun x => ideal_final_s2_row_residual_value pre_bp avec row j x ^ 2) =
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment2_at
      pre_bp avec (ideal_final_s2_row_index row j).
proof.
move=> hrow hj.
rewrite ideal_eta_centered_trit_expE.
rewrite /ideal_final_s2_row_residual_value.
rewrite /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_moment2_at.
trivial.
qed.

lemma creal_csum (xs : complex list) :
  creal (csum xs) = BRA.big predT creal xs.
proof.
elim: xs => [|z zs ih].
+ rewrite /csum /= BRA.big_nil creal_zero.
   trivial.
rewrite /csum /= BRA.big_cons /= creal_add ih.
trivial.
qed.

lemma cimag_csum (xs : complex list) :
  cimag (csum xs) = BRA.big predT cimag xs.
proof.
elim: xs => [|z zs ih].
+ rewrite /csum /= BRA.big_nil cimag_zero.
   trivial.
rewrite /csum /= BRA.big_cons /= cimag_add ih.
trivial.
qed.

lemma creal_csum256 (f : int -> complex) :
  creal (csum256 f) = BRA.bigi predT (fun j => creal (f j)) 0 256.
proof.
rewrite /csum256 creal_csum BRA.big_mapT /(\o).
trivial.
qed.

lemma cimag_csum256 (f : int -> complex) :
  cimag (csum256 f) = BRA.bigi predT (fun j => cimag (f j)) 0 256.
proof.
rewrite /csum256 cimag_csum BRA.big_mapT /(\o).
trivial.
qed.

lemma ideal_final_s2_row_residual_re_prefix_rcons
    pre_bp avec row k n xs x :
  0 <= n =>
  size xs = n =>
  ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) (rcons xs x) =
  ideal_final_s2_row_residual_re_prefix pre_bp avec row k n xs +
  ideal_final_s2_row_residual_re_term pre_bp avec row k n x.
proof.
move=> hn hsize.
rewrite /ideal_final_s2_row_residual_re_prefix.
rewrite (rangeSr 0 n) 1:/#.
rewrite BRA.big_rcons /=.
rewrite /predT /=.
congr.
+ apply BRA.eq_big_seq => j hj.
  rewrite mem_range in hj.
  simplify.
  rewrite nth_rcons hsize.
  rewrite ifT 1:/#.
  trivial.
rewrite nth_rcons hsize.
rewrite ifF 1:/# ifT 1:/#.
trivial.
qed.

lemma ideal_final_s2_row_residual_im_prefix_rcons
    pre_bp avec row k n xs x :
  0 <= n =>
  size xs = n =>
  ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) (rcons xs x) =
  ideal_final_s2_row_residual_im_prefix pre_bp avec row k n xs +
  ideal_final_s2_row_residual_im_term pre_bp avec row k n x.
proof.
move=> hn hsize.
rewrite /ideal_final_s2_row_residual_im_prefix.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /=.
rewrite /predT /=.
congr.
+ apply BRA.eq_big_seq => j hj.
  rewrite mem_range in hj.
  simplify.
  rewrite nth_rcons hsize.
  rewrite ifT 1:/#.
  trivial.
rewrite nth_rcons hsize.
rewrite ifF 1:/# ifT 1:/#.
trivial.
qed.

lemma ideal_final_s2_row_residual_re_prefix_exp_zero
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n) =
  0%r.
proof.
move=> hrow.
elim/natind: n => [n hnle0|n hnge0 ih].
+ move=> _.
   rewrite /ideal_final_s2_row_source_distribution dlist0 1:/#.
   rewrite exp_dunit.
   simplify.
   rewrite /ideal_final_s2_row_residual_re_prefix.
   rewrite range_geq 1:/# BRA.big_nil.
   ring.
move=> hn.
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
have hfin_map :
    is_finite
      (support
        (dmap
          (ideal_final_s2_row_source_distribution n `*`
           Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
             .ideal_eta_centered_trit_distribution)
          (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))).
+ apply finite_dmap.
   apply finite_dprod => //.
have hfin_prod :
    is_finite
      (support
        (ideal_final_s2_row_source_distribution n `*`
         Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
           .ideal_eta_centered_trit_distribution)).
+ apply finite_dprod => //.
rewrite /ideal_final_s2_row_source_distribution dlistSr 1:/#.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2)
    (ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1))
    (hasE_finite _ _ hfin_map)).
rewrite
     (eq_exp
       (ideal_final_s2_row_source_distribution n `*`
        Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
          .ideal_eta_centered_trit_distribution)
       (ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) \o
        (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
       (fun (x_xs : int list * int) =>
         ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 +
         ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2)).
+ move=> [xs x] hxs /=.
  rewrite supp_dprod in hxs.
  move: hxs => [hxs _].
  have hsize :=
    supp_dlist_size
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution
      n xs hnge0 hxs.
  rewrite /(\o).
  exact
    (ideal_final_s2_row_residual_re_prefix_rcons
      pre_bp avec row k n xs x hnge0 hsize).
rewrite
  (expD
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun (x_xs : int list * int) =>
      ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1)
    (fun (x_xs : int list * int) =>
      ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2)
    (hasE_finite _ _ hfin_prod)
    (hasE_finite _ _ hfin_prod)).
rewrite (exp_dprod_left_finite
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n))
    1:hfin_n 1:hfin_trit.
rewrite ih 1:/#.
have htritll :=
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
rewrite /is_lossless in htritll.
rewrite htritll.
rewrite (exp_dprod_right_finite
  (ideal_final_s2_row_source_distribution n)
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (ideal_final_s2_row_residual_re_term pre_bp avec row k n))
  1:hfin_n 1:hfin_trit.
rewrite ideal_final_s2_row_source_distribution_lossless.
have hn256 : 0 <= n < KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; smt().
have hmean0 :=
  ideal_final_s2_row_residual_value_exp_zero
    pre_bp avec row n hrow hn256.
rewrite /ideal_final_s2_row_residual_re_term.
have -> :
    (fun x =>
      ideal_final_s2_row_residual_value pre_bp avec row n x *
      creal (cpow (odd_root k) n)) =
    (fun x =>
      creal (cpow (odd_root k) n) *
      ideal_final_s2_row_residual_value pre_bp avec row n x).
+ apply fun_ext => x.
  ring.
rewrite (expZ
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (creal (cpow (odd_root k) n))
  (ideal_final_s2_row_residual_value pre_bp avec row n)).
rewrite hmean0.
ring.
qed.

lemma ideal_final_s2_row_residual_im_prefix_exp_zero
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n) =
  0%r.
proof.
move=> hrow.
elim/natind: n => [n hnle0|n hnge0 ih].
+ move=> _.
   rewrite /ideal_final_s2_row_source_distribution dlist0 1:/#.
   rewrite exp_dunit.
   simplify.
   rewrite /ideal_final_s2_row_residual_im_prefix.
   rewrite range_geq 1:/# BRA.big_nil.
   ring.
move=> hn.
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
have hfin_map :
    is_finite
      (support
        (dmap
          (ideal_final_s2_row_source_distribution n `*`
           Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
             .ideal_eta_centered_trit_distribution)
          (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))).
+ apply finite_dmap.
   apply finite_dprod => //.
have hfin_prod :
    is_finite
      (support
        (ideal_final_s2_row_source_distribution n `*`
         Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
           .ideal_eta_centered_trit_distribution)).
+ apply finite_dprod => //.
rewrite /ideal_final_s2_row_source_distribution dlistSr 1:/#.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2)
    (ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1))
    (hasE_finite _ _ hfin_map)).
rewrite
     (eq_exp
       (ideal_final_s2_row_source_distribution n `*`
        Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
          .ideal_eta_centered_trit_distribution)
       (ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) \o
        (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
       (fun (x_xs : int list * int) =>
         ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 +
         ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2)).
+ move=> [xs x] hxs /=.
  rewrite supp_dprod in hxs.
  move: hxs => [hxs _].
  have hsize :=
    supp_dlist_size
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution
      n xs hnge0 hxs.
  rewrite /(\o).
  exact
    (ideal_final_s2_row_residual_im_prefix_rcons
      pre_bp avec row k n xs x hnge0 hsize).
rewrite
  (expD
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun (x_xs : int list * int) =>
      ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1)
    (fun (x_xs : int list * int) =>
      ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2)
    (hasE_finite _ _ hfin_prod)
    (hasE_finite _ _ hfin_prod)).
rewrite (exp_dprod_left_finite
    (ideal_final_s2_row_source_distribution n)
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n))
    1:hfin_n 1:hfin_trit.
rewrite ih 1:/#.
have htritll :=
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
rewrite /is_lossless in htritll.
rewrite htritll.
rewrite (exp_dprod_right_finite
  (ideal_final_s2_row_source_distribution n)
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (ideal_final_s2_row_residual_im_term pre_bp avec row k n))
  1:hfin_n 1:hfin_trit.
rewrite ideal_final_s2_row_source_distribution_lossless.
have hn256 : 0 <= n < KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; smt().
have hmean0 :=
  ideal_final_s2_row_residual_value_exp_zero
    pre_bp avec row n hrow hn256.
rewrite /ideal_final_s2_row_residual_im_term.
have -> :
    (fun x =>
      ideal_final_s2_row_residual_value pre_bp avec row n x *
      cimag (cpow (odd_root k) n)) =
    (fun x =>
      cimag (cpow (odd_root k) n) *
      ideal_final_s2_row_residual_value pre_bp avec row n x).
+ apply fun_ext => x.
  ring.
rewrite (expZ
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (cimag (cpow (odd_root k) n))
  (ideal_final_s2_row_residual_value pre_bp avec row n)).
rewrite hmean0.
ring.
qed.

lemma ideal_final_s2_row_residual_re_prefix_sqE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_re_prefix pre_bp avec row k n xs ^ 2) =
  ideal_final_s2_row_residual_re_profile pre_bp avec row k n.
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
           /ideal_final_s2_row_residual_re_profile.
   rewrite hrange !BRA.big_nil.
   ring.
move=> hn.
have hnprev : 0 <= n <= 256 by smt().
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
have hfin_map :
    is_finite
      (support
        (dmap
          (ideal_final_s2_row_source_distribution n `*`
           Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
             .ideal_eta_centered_trit_distribution)
          (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))).
+ apply finite_dmap.
   apply finite_dprod => //.
have hfin_prod :
    is_finite
      (support
        (ideal_final_s2_row_source_distribution n `*`
         Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
           .ideal_eta_centered_trit_distribution)).
+ apply finite_dprod => //.
rewrite /ideal_final_s2_row_source_distribution dlistSr 1:/#.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2)
    (fun xs =>
      ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 2)
    (hasE_finite _ _ hfin_map)).
rewrite
     (eq_exp
       (ideal_final_s2_row_source_distribution n `*`
        Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
          .ideal_eta_centered_trit_distribution)
       ((fun xs =>
          ideal_final_s2_row_residual_re_prefix pre_bp avec row k (n + 1) xs ^ 2) \o
        (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
       (fun (x_xs : int list * int) =>
         (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1) ^ 2 +
         2%r *
           ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 *
           ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2 +
         (ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2) ^ 2)).
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
  ring.
rewrite
  (expD
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1) ^ 2 +
      2%r *
        ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 *
        ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2)
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2) ^ 2)
    (hasE_finite _ _ hfin_prod)
    (hasE_finite _ _ hfin_prod)).
rewrite
  (expD
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1) ^ 2)
    (fun (x_xs : int list * int) =>
      2%r *
        ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 *
        ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2)
    (hasE_finite _ _ hfin_prod)
    (hasE_finite _ _ hfin_prod)).
rewrite (exp_dprod_left_finite
  (ideal_final_s2_row_source_distribution n)
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (fun xs => ideal_final_s2_row_residual_re_prefix pre_bp avec row k n xs ^ 2))
  1:hfin_n 1:hfin_trit.
rewrite ih 1:/#.
have htritll :=
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
rewrite /is_lossless in htritll.
rewrite htritll.
have -> :
    (fun (x_xs : int list * int) =>
      2%r *
        ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 *
        ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2) =
    (fun (x_xs : int list * int) =>
      2%r *
        (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 *
         ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2)).
+ apply fun_ext => x_xs.
  ring.
rewrite (expZ
  (ideal_final_s2_row_source_distribution n `*`
   Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
     .ideal_eta_centered_trit_distribution)
  2%r
  (fun (x_xs : int list * int) =>
    ideal_final_s2_row_residual_re_prefix pre_bp avec row k n x_xs.`1 *
    ideal_final_s2_row_residual_re_term pre_bp avec row k n x_xs.`2)).
rewrite (exp_dprod_mul_factor
  (ideal_final_s2_row_source_distribution n)
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (ideal_final_s2_row_residual_re_prefix pre_bp avec row k n)
  (ideal_final_s2_row_residual_re_term pre_bp avec row k n))
  1:hfin_n 1:hfin_trit.
rewrite
  (ideal_final_s2_row_residual_re_prefix_exp_zero
    pre_bp avec row k n hrow hnprev).
rewrite (exp_dprod_right_finite
  (ideal_final_s2_row_source_distribution n)
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (fun x => ideal_final_s2_row_residual_re_term pre_bp avec row k n x ^ 2))
  1:hfin_n 1:hfin_trit.
rewrite ideal_final_s2_row_source_distribution_lossless.
have hn256 : 0 <= n < KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; smt().
rewrite /ideal_final_s2_row_residual_re_term.
have -> :
    (fun x =>
      (ideal_final_s2_row_residual_value pre_bp avec row n x *
       creal (cpow (odd_root k) n)) ^ 2) =
    (fun x =>
      creal (cpow (odd_root k) n) ^ 2 *
      ideal_final_s2_row_residual_value pre_bp avec row n x ^ 2).
+ apply fun_ext => x.
  ring.
rewrite (expZ
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (creal (cpow (odd_root k) n) ^ 2)
  (fun x => ideal_final_s2_row_residual_value pre_bp avec row n x ^ 2)).
rewrite
  (ideal_final_s2_row_residual_value_exp_square
    pre_bp avec row n hrow hn256).
rewrite /ideal_final_s2_row_residual_re_profile.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
qed.

lemma ideal_final_s2_row_residual_im_prefix_sqE
    pre_bp avec row k n :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= n <= 256 =>
  E
    (ideal_final_s2_row_source_distribution n)
    (fun xs => ideal_final_s2_row_residual_im_prefix pre_bp avec row k n xs ^ 2) =
  ideal_final_s2_row_residual_im_profile pre_bp avec row k n.
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
           /ideal_final_s2_row_residual_im_profile.
   rewrite hrange !BRA.big_nil.
   ring.
move=> hn.
have hnprev : 0 <= n <= 256 by smt().
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
have hfin_map :
    is_finite
      (support
        (dmap
          (ideal_final_s2_row_source_distribution n `*`
           Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
             .ideal_eta_centered_trit_distribution)
          (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))).
+ apply finite_dmap.
   apply finite_dprod => //.
have hfin_prod :
    is_finite
      (support
        (ideal_final_s2_row_source_distribution n `*`
         Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
           .ideal_eta_centered_trit_distribution)).
+ apply finite_dprod => //.
rewrite /ideal_final_s2_row_source_distribution dlistSr 1:/#.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2)
    (fun xs =>
      ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 2)
    (hasE_finite _ _ hfin_map)).
rewrite
     (eq_exp
       (ideal_final_s2_row_source_distribution n `*`
        Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
          .ideal_eta_centered_trit_distribution)
       ((fun xs =>
          ideal_final_s2_row_residual_im_prefix pre_bp avec row k (n + 1) xs ^ 2) \o
        (fun x_xs : int list * int => rcons x_xs.`1 x_xs.`2))
       (fun (x_xs : int list * int) =>
         (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1) ^ 2 +
         2%r *
           ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 *
           ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2 +
         (ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2) ^ 2)).
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
  ring.
rewrite
  (expD
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1) ^ 2 +
      2%r *
        ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 *
        ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2)
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2) ^ 2)
    (hasE_finite _ _ hfin_prod)
    (hasE_finite _ _ hfin_prod)).
rewrite
  (expD
    (ideal_final_s2_row_source_distribution n `*`
     Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
       .ideal_eta_centered_trit_distribution)
    (fun (x_xs : int list * int) =>
      (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1) ^ 2)
    (fun (x_xs : int list * int) =>
      2%r *
        ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 *
        ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2)
    (hasE_finite _ _ hfin_prod)
    (hasE_finite _ _ hfin_prod)).
rewrite (exp_dprod_left_finite
  (ideal_final_s2_row_source_distribution n)
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (fun xs => ideal_final_s2_row_residual_im_prefix pre_bp avec row k n xs ^ 2))
  1:hfin_n 1:hfin_trit.
rewrite ih 1:/#.
have htritll :=
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
rewrite /is_lossless in htritll.
rewrite htritll.
have -> :
    (fun (x_xs : int list * int) =>
      2%r *
        ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 *
        ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2) =
    (fun (x_xs : int list * int) =>
      2%r *
        (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 *
         ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2)).
+ apply fun_ext => x_xs.
  ring.
rewrite (expZ
  (ideal_final_s2_row_source_distribution n `*`
   Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
     .ideal_eta_centered_trit_distribution)
  2%r
  (fun (x_xs : int list * int) =>
    ideal_final_s2_row_residual_im_prefix pre_bp avec row k n x_xs.`1 *
    ideal_final_s2_row_residual_im_term pre_bp avec row k n x_xs.`2)).
rewrite (exp_dprod_mul_factor
  (ideal_final_s2_row_source_distribution n)
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (ideal_final_s2_row_residual_im_prefix pre_bp avec row k n)
  (ideal_final_s2_row_residual_im_term pre_bp avec row k n))
  1:hfin_n 1:hfin_trit.
rewrite
  (ideal_final_s2_row_residual_im_prefix_exp_zero
    pre_bp avec row k n hrow hnprev).
rewrite (exp_dprod_right_finite
  (ideal_final_s2_row_source_distribution n)
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (fun x => ideal_final_s2_row_residual_im_term pre_bp avec row k n x ^ 2))
  1:hfin_n 1:hfin_trit.
rewrite ideal_final_s2_row_source_distribution_lossless.
have hn256 : 0 <= n < KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; smt().
rewrite /ideal_final_s2_row_residual_im_term.
have -> :
    (fun x =>
      (ideal_final_s2_row_residual_value pre_bp avec row n x *
       cimag (cpow (odd_root k) n)) ^ 2) =
    (fun x =>
      cimag (cpow (odd_root k) n) ^ 2 *
      ideal_final_s2_row_residual_value pre_bp avec row n x ^ 2).
+ apply fun_ext => x.
  ring.
rewrite (expZ
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (cimag (cpow (odd_root k) n) ^ 2)
  (fun x => ideal_final_s2_row_residual_value pre_bp avec row n x ^ 2)).
rewrite
  (ideal_final_s2_row_residual_value_exp_square
    pre_bp avec row n hrow hn256).
rewrite /ideal_final_s2_row_residual_im_profile.
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
rewrite ifT //.
qed.

lemma ideal_final_s2_row_residual_odd_dft256_sample_creal
    pre_bp avec row xs k :
  creal (ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k) =
  ideal_final_s2_row_residual_re_prefix pre_bp avec row k 256 xs.
proof.
rewrite /ideal_final_s2_row_residual_odd_dft256_sample
        /ideal_final_s2_row_residual_re_prefix
        /ideal_final_s2_row_residual_slice
        /odd_dft256 creal_csum256.
apply BRA.eq_bigr => j _.
simplify.
rewrite creal_mul creal_of_real cimag_of_real
        /ideal_final_s2_row_residual_re_term.
ring.
qed.

lemma ideal_final_s2_row_residual_odd_dft256_sample_cimag
    pre_bp avec row xs k :
  cimag (ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k) =
  ideal_final_s2_row_residual_im_prefix pre_bp avec row k 256 xs.
proof.
rewrite /ideal_final_s2_row_residual_odd_dft256_sample
        /ideal_final_s2_row_residual_im_prefix
        /ideal_final_s2_row_residual_slice
        /odd_dft256 cimag_csum256.
apply BRA.eq_bigr => j _.
simplify.
rewrite cimag_mul creal_of_real cimag_of_real
        /ideal_final_s2_row_residual_im_term.
ring.
qed.

lemma odd_root_power_norm1 k j :
  0 <= k =>
  0 <= j =>
  cnorm2 (cpow (odd_root k) j) = 1%r.
proof.
move=> hk hj.
rewrite /odd_root ideal_root_power.
apply ideal_root_norm1.
apply IntOrder.mulr_ge0.
+ smt().
exact hj.
qed.

lemma ideal_final_s2_row_residual_fft_real_mean_zero
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)
    creal = 0%r.
proof.
move=> hrow.
have hfin :
    is_finite
      (support (ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)).
+ rewrite /ideal_final_s2_row_residual_odd_dft256_distribution.
   apply finite_dmap.
   exact (ideal_final_s2_row_source_distribution_finite 256 _).
   rewrite /KeygenM23SingularSpec.singular_words_i.
   trivial.
rewrite /ideal_final_s2_row_residual_odd_dft256_distribution.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution 256)
    (fun xs => ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k)
    creal
    (hasE_finite _ _ hfin)).
rewrite
     (eq_exp
       (ideal_final_s2_row_source_distribution 256)
       (creal \o
         (fun xs => ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k))
       (ideal_final_s2_row_residual_re_prefix pre_bp avec row k 256)).
+ move=> xs hxs /=.
  rewrite /(\o).
  exact
    (ideal_final_s2_row_residual_odd_dft256_sample_creal
      pre_bp avec row xs k).
have h256 : 0 <= 256 <= 256 by smt().
exact
  (ideal_final_s2_row_residual_re_prefix_exp_zero
    pre_bp avec row k 256 hrow h256).
qed.

lemma ideal_final_s2_row_residual_fft_imag_mean_zero
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)
    cimag = 0%r.
proof.
move=> hrow.
have hfin :
    is_finite
      (support (ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)).
+ rewrite /ideal_final_s2_row_residual_odd_dft256_distribution.
   apply finite_dmap.
   exact (ideal_final_s2_row_source_distribution_finite 256 _).
   rewrite /KeygenM23SingularSpec.singular_words_i.
   trivial.
rewrite /ideal_final_s2_row_residual_odd_dft256_distribution.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution 256)
    (fun xs => ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k)
    cimag
    (hasE_finite _ _ hfin)).
rewrite
     (eq_exp
       (ideal_final_s2_row_source_distribution 256)
       (cimag \o
         (fun xs => ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k))
       (ideal_final_s2_row_residual_im_prefix pre_bp avec row k 256)).
+ move=> xs hxs /=.
  rewrite /(\o).
  exact
    (ideal_final_s2_row_residual_odd_dft256_sample_cimag
      pre_bp avec row xs k).
have h256 : 0 <= 256 <= 256 by smt().
exact
  (ideal_final_s2_row_residual_im_prefix_exp_zero
    pre_bp avec row k 256 hrow h256).
qed.

lemma ideal_final_s2_row_residual_fft_cnorm2E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)
    cnorm2 =
  ideal_final_s2_row_residual_re_profile pre_bp avec row k 256 +
  ideal_final_s2_row_residual_im_profile pre_bp avec row k 256.
proof.
move=> hrow.
have hfin :
    is_finite
      (support (ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)).
+ rewrite /ideal_final_s2_row_residual_odd_dft256_distribution.
   apply finite_dmap.
   exact (ideal_final_s2_row_source_distribution_finite 256 _).
   rewrite /KeygenM23SingularSpec.singular_words_i.
   trivial.
have hfinsrc :
    is_finite (support (ideal_final_s2_row_source_distribution 256)).
+ exact (ideal_final_s2_row_source_distribution_finite 256 _).
  rewrite /KeygenM23SingularSpec.singular_words_i.
  trivial.
rewrite /ideal_final_s2_row_residual_odd_dft256_distribution.
rewrite
  (exp_dmap
    (ideal_final_s2_row_source_distribution 256)
    (fun xs => ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k)
    cnorm2
    (hasE_finite _ _ hfin)).
rewrite
     (eq_exp
       (ideal_final_s2_row_source_distribution 256)
       (cnorm2 \o
         (fun xs => ideal_final_s2_row_residual_odd_dft256_sample pre_bp avec row xs k))
       (fun xs =>
         ideal_final_s2_row_residual_re_prefix pre_bp avec row k 256 xs ^ 2 +
         ideal_final_s2_row_residual_im_prefix pre_bp avec row k 256 xs ^ 2)).
+ move=> xs hxs /=.
  rewrite /(\o) /cnorm2.
  rewrite
    (ideal_final_s2_row_residual_odd_dft256_sample_creal
      pre_bp avec row xs k)
    (ideal_final_s2_row_residual_odd_dft256_sample_cimag
      pre_bp avec row xs k).
  ring.
rewrite
  (expD
    (ideal_final_s2_row_source_distribution 256)
    (fun xs => ideal_final_s2_row_residual_re_prefix pre_bp avec row k 256 xs ^ 2)
    (fun xs => ideal_final_s2_row_residual_im_prefix pre_bp avec row k 256 xs ^ 2)
    (hasE_finite _ _ hfinsrc)
    (hasE_finite _ _ hfinsrc)).
have h256 : 0 <= 256 <= 256 by smt().
rewrite
  (ideal_final_s2_row_residual_re_prefix_sqE
    pre_bp avec row k 256 hrow h256).
rewrite
  (ideal_final_s2_row_residual_im_prefix_sqE
    pre_bp avec row k 256 hrow h256).
trivial.
qed.

lemma ideal_final_s2_row_residual_fft_cnorm2_le
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  E
    (ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k)
    cnorm2 <=
  2048%r / 3%r.
proof.
move=> hctx hrow hk.
rewrite (ideal_final_s2_row_residual_fft_cnorm2E pre_bp avec row k hrow).
apply (ler_trans
  (BRA.bigi predT
    (fun j =>
      cnorm2 (cpow (odd_root k) j) *
      Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_residual_moment2_at
          pre_bp avec (ideal_final_s2_row_index row j))
    0 256)).
+ rewrite /ideal_final_s2_row_residual_re_profile
           /ideal_final_s2_row_residual_im_profile.
   rewrite -BRA.big_split.
   apply ler_sum_seq => j hj _.
   rewrite mem_range in hj.
   rewrite /cnorm2.
   apply lerr_eq.
   simplify.
   ring.
apply (ler_trans
  (BRA.bigi predT (fun _ => 8%r / 3%r) 0 256)).
+ apply ler_sum_seq => j hj _.
   rewrite mem_range in hj.
   have hj256 : 0 <= j < KeygenM23SingularSpec.singular_words_i by
     rewrite /KeygenM23SingularSpec.singular_words_i in hj; exact hj.
   have hidx :=
     ideal_final_s2_row_index_range row j hrow hj256.
   have hmoment :=
     Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
       .ideal_final_s2_residual_moment_bounds_at
         pre_bp avec (ideal_final_s2_row_index row j) hctx hidx.
   move: hmoment => [hmoment _].
   have hk0 : 0 <= k by smt().
   have hj0 : 0 <= j by smt().
   have hnorm : cnorm2 (cpow (odd_root k) j) = 1%r.
   + exact (odd_root_power_norm1 k j hk0 hj0).
   simplify.
   rewrite hnorm.
   exact hmoment.
rewrite Bigreal.sumr_const count_predT size_range /=.
apply lerr_eq.
field.
smt().
smt().
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.
