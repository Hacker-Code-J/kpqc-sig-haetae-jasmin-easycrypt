require import AllCore IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze.

import RealOrder Bigreal Bigreal.BRM.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.

(* This file only provides a center-radius interval kernel over reals, with
   soundness for absolute upper, point/add/mul/fixed-power/range-sum
   constructions. It does not define any FFT root certificates or moment
   evaluators. *)

type rinterval = real * real.

op interval_center (q : rinterval) : real = q.`1.
op interval_radius (q : rinterval) : real = q.`2.
op interval_lo (q : rinterval) : real = interval_center q - interval_radius q.
op interval_hi (q : rinterval) : real = interval_center q + interval_radius q.
op interval_abs_upper (q : rinterval) : real =
  `|interval_center q| + interval_radius q.

op interval_valid (q : rinterval) : bool =
  0%r <= interval_radius q.

op interval_holds (q : rinterval) (x : real) : bool =
  `|x - interval_center q| <= interval_radius q.

op interval_point (x : real) : rinterval = (x, 0%r).

op interval_add (qa qb : rinterval) : rinterval =
  (interval_center qa + interval_center qb,
   interval_radius qa + interval_radius qb).

op interval_mul (qa qb : rinterval) : rinterval =
  (interval_center qa * interval_center qb,
   `|interval_center qa| * interval_radius qb +
   `|interval_center qb| * interval_radius qa +
   interval_radius qa * interval_radius qb).

op interval_pow2 (q : rinterval) : rinterval = interval_mul q q.
op interval_pow3 (q : rinterval) : rinterval = interval_mul (interval_pow2 q) q.
op interval_pow4 (q : rinterval) : rinterval =
  interval_mul (interval_pow2 q) (interval_pow2 q).
op interval_pow5 (q : rinterval) : rinterval = interval_mul (interval_pow4 q) q.
op interval_pow6 (q : rinterval) : rinterval =
  interval_mul (interval_pow3 q) (interval_pow3 q).
op interval_pow8 (q : rinterval) : rinterval =
  interval_mul (interval_pow4 q) (interval_pow4 q).

op interval_bigi (f : int -> rinterval) (n : int) : rinterval =
  (BRA.bigi predT (fun i => interval_center (f i)) 0 n,
   BRA.bigi predT (fun i => interval_radius (f i)) 0 n).

lemma interval_point_valid x :
  interval_valid (interval_point x).
proof.
rewrite /interval_valid /interval_point.
trivial.
qed.

lemma interval_point_holds x :
  interval_holds (interval_point x) x.
proof.
rewrite /interval_holds /interval_point /interval_center.
trivial.
qed.

lemma interval_abs_upper_ge0 q :
  interval_valid q =>
  0%r <= interval_abs_upper q.
proof.
rewrite /interval_valid /interval_abs_upper.
move=> hv.
exact (addr_ge0 _ _ (normr_ge0 _) hv).
qed.

lemma interval_holds_abs_le q x :
  interval_holds q x =>
  `|x| <= interval_abs_upper q.
proof.
move=> hx.
rewrite /interval_abs_upper.
have -> : x = interval_center q + (x - interval_center q) by ring.
have hc : `|interval_center q| <= `|interval_center q| by trivial.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
    .profile_abs_add_bound
      (interval_center q)
      (x - interval_center q)
      `|interval_center q|
      (interval_radius q)
      hc hx).
qed.

lemma interval_add_valid qa qb :
  interval_valid qa =>
  interval_valid qb =>
  interval_valid (interval_add qa qb).
proof.
rewrite /interval_valid /interval_add /=.
smt().
qed.

lemma interval_add_holds qa qb x y :
  interval_holds qa x =>
  interval_holds qb y =>
  interval_holds (interval_add qa qb) (x + y).
proof.
move=> hqa hqb.
rewrite /interval_holds /interval_add /=.
have -> :
    x + y - (interval_center qa + interval_center qb) =
    (x - interval_center qa) + (y - interval_center qb) by ring.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
    .profile_abs_add_bound
      (x - interval_center qa)
      (y - interval_center qb)
      (interval_radius qa)
      (interval_radius qb)
      hqa hqb).
qed.

lemma interval_mul_valid qa qb :
  interval_valid qa =>
  interval_valid qb =>
  interval_valid (interval_mul qa qb).
proof.
rewrite /interval_valid /interval_mul /=.
move=> hva hvb.
have hna : 0%r <= interval_radius qa by exact hva.
have hnb : 0%r <= interval_radius qb by exact hvb.
have hca : 0%r <= `|interval_center qa| by exact (normr_ge0 _).
have hcb : 0%r <= `|interval_center qb| by exact (normr_ge0 _).
have h1 : 0%r <= `|interval_center qa| * interval_radius qb by
  exact (mulr_ge0 _ _ hca hnb).
have h2 : 0%r <= `|interval_center qb| * interval_radius qa by
  exact (mulr_ge0 _ _ hcb hna).
have h3 : 0%r <= interval_radius qa * interval_radius qb by
  exact (mulr_ge0 _ _ hna hnb).
smt().
qed.

lemma interval_mul_holds qa qb x y :
  interval_valid qa =>
  interval_valid qb =>
  interval_holds qa x =>
  interval_holds qb y =>
  interval_holds (interval_mul qa qb) (x * y).
proof.
move=> hva hvb hqa hqb.
have hna : 0%r <= interval_radius qa by exact hva.
have hnb : 0%r <= interval_radius qb by exact hvb.
rewrite /interval_holds /interval_mul /=.
have -> :
    x * y - interval_center qa * interval_center qb =
    interval_center qa * (y - interval_center qb) +
    interval_center qb * (x - interval_center qa) +
    (x - interval_center qa) * (y - interval_center qb) by ring.
have h1 :
    `|interval_center qa * (y - interval_center qb)| <=
    `|interval_center qa| * interval_radius qb.
+ have hcaabs : `|interval_center qa| <= `|interval_center qa| by smt().
  exact
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
      .profile_abs_mul_bound
        (interval_center qa)
        (y - interval_center qb)
        `|interval_center qa|
        (interval_radius qb)
        (normr_ge0 _)
        hnb
        hcaabs
        hqb).
have h2 :
    `|interval_center qb * (x - interval_center qa)| <=
    `|interval_center qb| * interval_radius qa.
+ have hcbabs : `|interval_center qb| <= `|interval_center qb| by smt().
  exact
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
      .profile_abs_mul_bound
        (interval_center qb)
        (x - interval_center qa)
        `|interval_center qb|
        (interval_radius qa)
        (normr_ge0 _)
        hna
        hcbabs
        hqa).
have h3 :
    `|(x - interval_center qa) * (y - interval_center qb)| <=
    interval_radius qa * interval_radius qb.
+ exact
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
      .profile_abs_mul_bound
        (x - interval_center qa)
        (y - interval_center qb)
        (interval_radius qa)
        (interval_radius qb)
        hna hnb hqa hqb).
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentProfileBoundPostFreeze
    .profile_abs_add3_bound
      (interval_center qa * (y - interval_center qb))
      (interval_center qb * (x - interval_center qa))
      ((x - interval_center qa) * (y - interval_center qb))
      (`|interval_center qa| * interval_radius qb)
      (`|interval_center qb| * interval_radius qa)
      (interval_radius qa * interval_radius qb)
      h1 h2 h3).
qed.

lemma interval_pow2_valid q :
  interval_valid q =>
  interval_valid (interval_pow2 q).
proof.
move=> hv.
exact (interval_mul_valid q q hv hv).
qed.

lemma interval_pow2_holds q x :
  interval_valid q =>
  interval_holds q x =>
  interval_holds (interval_pow2 q) (x ^ 2).
proof.
move=> hv hx.
rewrite /interval_pow2 RField.expr2.
exact (interval_mul_holds q q x x hv hv hx hx).
qed.

lemma interval_pow3_valid q :
  interval_valid q =>
  interval_valid (interval_pow3 q).
proof.
move=> hv.
rewrite /interval_pow3.
exact (interval_mul_valid (interval_pow2 q) q (interval_pow2_valid q hv) hv).
qed.

lemma interval_pow3_holds q x :
  interval_valid q =>
  interval_holds q x =>
  interval_holds (interval_pow3 q) (x ^ 3).
proof.
move=> hv hx.
rewrite /interval_pow3.
have h2 := interval_pow2_holds q x hv hx.
have hv2 := interval_pow2_valid q hv.
have -> : x ^ 3 = x ^ 2 * x by ring.
exact (interval_mul_holds (interval_pow2 q) q (x ^ 2) x hv2 hv h2 hx).
qed.

lemma interval_pow4_valid q :
  interval_valid q =>
  interval_valid (interval_pow4 q).
proof.
move=> hv.
rewrite /interval_pow4.
have hv2 := interval_pow2_valid q hv.
exact (interval_mul_valid (interval_pow2 q) (interval_pow2 q) hv2 hv2).
qed.

lemma interval_pow4_holds q x :
  interval_valid q =>
  interval_holds q x =>
  interval_holds (interval_pow4 q) (x ^ 4).
proof.
move=> hv hx.
rewrite /interval_pow4.
have h2 := interval_pow2_holds q x hv hx.
have hv2 := interval_pow2_valid q hv.
have -> : x ^ 4 = x ^ 2 * x ^ 2 by ring.
exact
  (interval_mul_holds
    (interval_pow2 q) (interval_pow2 q) (x ^ 2) (x ^ 2) hv2 hv2 h2 h2).
qed.

lemma interval_pow5_valid q :
  interval_valid q =>
  interval_valid (interval_pow5 q).
proof.
move=> hv.
rewrite /interval_pow5.
exact (interval_mul_valid (interval_pow4 q) q (interval_pow4_valid q hv) hv).
qed.

lemma interval_pow5_holds q x :
  interval_valid q =>
  interval_holds q x =>
  interval_holds (interval_pow5 q) (x ^ 5).
proof.
move=> hv hx.
rewrite /interval_pow5.
have h4 := interval_pow4_holds q x hv hx.
have hv4 := interval_pow4_valid q hv.
have -> : x ^ 5 = x ^ 4 * x by ring.
exact (interval_mul_holds (interval_pow4 q) q (x ^ 4) x hv4 hv h4 hx).
qed.

lemma interval_pow6_valid q :
  interval_valid q =>
  interval_valid (interval_pow6 q).
proof.
move=> hv.
rewrite /interval_pow6.
have hv3 := interval_pow3_valid q hv.
exact (interval_mul_valid (interval_pow3 q) (interval_pow3 q) hv3 hv3).
qed.

lemma interval_pow6_holds q x :
  interval_valid q =>
  interval_holds q x =>
  interval_holds (interval_pow6 q) (x ^ 6).
proof.
move=> hv hx.
rewrite /interval_pow6.
have h3 := interval_pow3_holds q x hv hx.
have hv3 := interval_pow3_valid q hv.
have -> : x ^ 6 = x ^ 3 * x ^ 3 by ring.
exact
  (interval_mul_holds
    (interval_pow3 q) (interval_pow3 q) (x ^ 3) (x ^ 3) hv3 hv3 h3 h3).
qed.

lemma interval_pow8_valid q :
  interval_valid q =>
  interval_valid (interval_pow8 q).
proof.
move=> hv.
rewrite /interval_pow8.
have hv4 := interval_pow4_valid q hv.
exact (interval_mul_valid (interval_pow4 q) (interval_pow4 q) hv4 hv4).
qed.

lemma interval_pow8_holds q x :
  interval_valid q =>
  interval_holds q x =>
  interval_holds (interval_pow8 q) (x ^ 8).
proof.
move=> hv hx.
rewrite /interval_pow8.
have h4 := interval_pow4_holds q x hv hx.
have hv4 := interval_pow4_valid q hv.
have -> : x ^ 8 = x ^ 4 * x ^ 4 by ring.
exact
  (interval_mul_holds
    (interval_pow4 q) (interval_pow4 q) (x ^ 4) (x ^ 4) hv4 hv4 h4 h4).
qed.

lemma interval_bigi_valid f n :
  (forall i, 0 <= i < n => interval_valid (f i)) =>
  interval_valid (interval_bigi f n).
proof.
rewrite /interval_valid /interval_bigi /=.
move=> hf.
change
  (0%r <=
    BRA.big predT (fun i => interval_radius (f i)) (range 0 n)).
apply Bigreal.sumr_ge0_seq => i hi _.
rewrite mem_range in hi.
exact (hf i hi).
qed.

lemma interval_bigiE f n :
  0 <= n =>
  interval_bigi f (n + 1) = interval_add (interval_bigi f n) (f n).
proof.
move=> hn.
rewrite /interval_bigi /interval_add.
rewrite !(rangeSr 0 n) 1:/# !BRA.big_rcons /= /predT ifT //.
qed.

lemma interval_bigi_holds f x n :
  (forall i, 0 <= i < n => interval_valid (f i)) =>
  (forall i, 0 <= i < n => interval_holds (f i) (x i)) =>
  interval_holds (interval_bigi f n) (BRA.bigi predT x 0 n).
proof.
move=> _ hfh.
rewrite /interval_holds /interval_bigi /=.
change
  (`|BRA.big predT x (range 0 n) -
      BRA.big predT (fun i => interval_center (f i)) (range 0 n)| <=
    BRA.big predT (fun i => interval_radius (f i)) (range 0 n)).
rewrite Bigreal.BRA.sumrB.
apply
  (ler_trans
    (BRA.big predT
      (fun i => `|x i - interval_center (f i)|)
      (range 0 n))).
+ exact
    (big_normr predT
      (fun i => x i - interval_center (f i))
      (range 0 n)).
apply ler_sum_seq => i hi _.
rewrite mem_range in hi.
exact (hfh i hi).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.
