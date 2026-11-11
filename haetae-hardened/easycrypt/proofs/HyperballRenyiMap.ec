require import AllCore Real RealExp RealSeries Distr Finite StdRing StdOrder.
require import GaussianRenyiSpec GaussianRenyiMoment GaussianRenyiConditioning
  FiniteExpectationError HyperballRenyiProduct.
import RField RealOrder.

(* A tangent inequality on the nonnegative half-line is sufficient for
   likelihood ratios, including odd integer orders. *)
lemma hrm_power_tangent (order : int) (x mean : real) :
  2<=order => 0%r<=x => 0%r<=mean =>
  mean^order+order%r*mean^(order-1)*(x-mean)<=x^order.
proof.
  move=> ho hx hm; case (mean=0%r) => [->|hne].
  + have h0 : (0%r)^order=0%r by rewrite expr0z; smt().
    have h1 : (0%r)^(order-1)=0%r by rewrite expr0z; smt().
    rewrite h0 h1 /=; exact (expr_ge0 order x hx).
  have hpos : 0%r<mean by smt().
  have hratio : 0%r<=x/mean by apply divr_ge0; smt().
  have hb := grn_bernoulli order (x/mean-1%r) _ _; first 2 smt().
  have hbase : 1%r+(x/mean-1%r)=x/mean by ring.
  move: hb; rewrite hbase => hb.
  have hp := expr_ge0 order mean hm.
  have hscaled := ler_wpmul2l (mean^order) hp _ _ hb.
  have hpow : mean^order=mean*mean^(order-1).
  + have he : order=(order-1)+1 by ring.
    by rewrite {1}he exprS 1:/#.
  have hleft : mean^order*(1%r+order%r*(x/mean-1%r)) =
    mean^order+order%r*mean^(order-1)*(x-mean).
  + rewrite hpow; field; smt().
  have hright : mean^order*(x/mean)^order=x^order.
  + rewrite -exprMn 1:/#; congr; field; smt().
  by move: hscaled; rewrite hleft hright.
qed.

lemma hrm_finite_jensen ['a] (order : int) (d : 'a distr) (f : 'a -> real) :
  is_finite (Distr.support d) => is_lossless d =>
  (forall x, x \in d => 0%r<=f x) => 2<=order =>
  (E d f)^order<=E d (fun x => (f x)^order).
proof.
  move=> hf hd hnonneg ho.
  pose mean := E d f.
  have hm : 0%r<=mean by apply exp_ge0; exact hnonneg.
  have h := finite_expectation_le d
    (fun x => mean^order+order%r*mean^(order-1)*(f x-mean))
    (fun x => (f x)^order) hf _.
  + move=> x hx; exact (hrm_power_tangent order (f x) mean ho (hnonneg x hx) hm).
  have he : E d (fun x => mean^order+order%r*mean^(order-1)*(f x-mean))=mean^order.
  + rewrite expD 1:hasEC 1:(hasE_finite d _ hf) expC hd expZ
      expB 1:(hasE_finite d f hf) 1:hasEC expC hd /= /mean.
    ring.
  move: h; rewrite he; trivial.
qed.

lemma hrm_zero_mass ['a] (p q : 'a distr) x :
  (forall z, z \in p => z \in q) => mu1 q x=0%r => mu1 p x=0%r.
proof.
  move=> hs hzero; have h := hs x.
  move: h; rewrite !supportP hzero; smt().
qed.

lemma hrm_likelihood_nonnegative ['a] (p q : 'a distr) x :
  0%r<=grn_likelihood p q x.
proof. rewrite /grn_likelihood; apply divr_ge0; apply ge0_mu1. qed.

lemma hrm_likelihood_event ['a] (p q : 'a distr) (event : 'a -> bool) :
  (forall x, x \in p => x \in q) =>
  E q (fun x => if event x then grn_likelihood p q x else 0%r)=mu p event.
proof.
  move=> hs; rewrite /E (muE p event); apply RealSeries.eq_sum => x /=.
  case (event x) => he /=; last trivial.
  case (mu1 q x=0%r) => hq.
  + have hp := hrm_zero_mass p q x hs hq.
    by rewrite /grn_likelihood hq hp /=.
  rewrite /grn_likelihood; field; trivial.
qed.

lemma hrm_fiber_mean ['a 'b] (p q : 'a distr) (f : 'a -> 'b) y :
  (forall x, x \in p => x \in q) =>
  E (dcond q (fun x => f x=y)) (grn_likelihood p q) =
    grn_likelihood (dmap p f) (dmap q f) y.
proof.
  move=> hs; rewrite exp_dcond /Ec (hrm_likelihood_event p q (fun x => f x=y) hs).
  by rewrite /grn_likelihood !dmap1E /pred1 /(\o).
qed.

lemma hrm_fiber_jensen ['a 'b] (order : int) (p q : 'a distr) (f : 'a -> 'b) y :
  is_finite (Distr.support q) => (forall x, x \in p => x \in q) =>
  2<=order => y \in dmap q f =>
  (grn_likelihood (dmap p f) (dmap q f) y)^order <=
    E (dcond q (fun x => f x=y)) (fun x => (grn_likelihood p q x)^order).
proof.
  move=> hf hs ho hy.
  have hmass : 0%r<mu1 (dmap q f) y by
    have h0 := ge0_mu1 (dmap q f) y; move: hy; rewrite supportP; smt().
  rewrite dmap1E /pred1 /(\o) in hmass.
  have hfin := finite_dcond q (fun x => f x=y) hf.
  have hll := dcond_ll q (fun x => f x=y) hmass.
  have hpos : forall x, x \in dcond q (fun x => f x=y) => 0%r<=grn_likelihood p q x by
    move=> x _; exact (hrm_likelihood_nonnegative p q x).
  have h := hrm_finite_jensen order (dcond q (fun x => f x=y))
    (grn_likelihood p q) hfin hll hpos ho.
  by move: h; rewrite (hrm_fiber_mean p q f y hs).
qed.

lemma hrm_map_support ['a 'b] (p q : 'a distr) (f : 'a -> 'b) :
  (forall x, x \in p => x \in q) =>
  forall y, y \in dmap p f => y \in dmap q f.
proof.
  move=> hs y; rewrite !supp_dmap.
  move=> [x [hx he]]; exists x; split; [exact (hs x hx)|exact he].
qed.

lemma hrm_moment_map ['a 'b] (order : int) (p q : 'a distr) (f : 'a -> 'b) :
  is_lossless p => is_lossless q =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  (forall x, x \in p => x \in q) => 2<=order =>
  grn_moment order (dmap p f) (dmap q f)<=grn_moment order p q.
proof.
  move=> hp hq hfp hfq hs ho.
  have hfin := grk_finite_map q f hfq.
  have hbound := finite_expectation_le (dmap q f)
    (fun y => (grn_likelihood (dmap p f) (dmap q f) y)^order)
    (fun y => E (dcond q (fun x => f x=y)) (fun x => (grn_likelihood p q x)^order)) hfin _.
  + move=> y hy; exact (hrm_fiber_jensen order p q f y hfq hs ho hy).
  have hE : hasE (dlet (dmap q f) (fun y => dcond q (fun x => f x=y)))
    (fun x => (grn_likelihood p q x)^order).
  + rewrite -(marginal_sampling q f); exact (hasE_finite q _ hfq).
  have htower := exp_dlet (dmap q f) (fun y => dcond q (fun x => f x=y))
    (fun x => (grn_likelihood p q x)^order) hE.
  rewrite -(marginal_sampling q f) in htower.
  move: hbound; rewrite -htower /grn_moment; trivial.
qed.

lemma hrm_moment_nonnegative ['a] (order : int) (p q : 'a distr) :
  0%r<=grn_moment order p q.
proof.
  rewrite /grn_moment; apply exp_ge0 => x hx.
  exact (expr_ge0 order (grn_likelihood p q x) (hrm_likelihood_nonnegative p q x)).
qed.

lemma hrm_renyi_map ['a 'b] (order : int) (p q : 'a distr) (f : 'a -> 'b) :
  is_lossless p => is_lossless q =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  (forall x, x \in p => x \in q) => 2<=order =>
  grn_renyi order (dmap p f) (dmap q f)<=grn_renyi order p q.
proof.
  move=> hp hq hfp hfq hs ho; rewrite /grn_renyi.
  have hm := hrm_moment_map order p q f hp hq hfp hfq hs ho.
  have h0 := hrm_moment_nonnegative order (dmap p f) (dmap q f).
  apply RealExp.rpow_hmono; last smt().
  apply divr_ge0; smt().
qed.

(* Common independent noise may include all sign bits. The map may retain
   both the full candidate output and its acceptance bit. *)
lemma hrm_shared_noise_map ['a 'b 'c] (order : int) (p q : 'a distr)
    (noise : 'b distr) (f : 'a * 'b -> 'c) :
  is_lossless p => is_lossless q => is_lossless noise =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  is_finite (Distr.support noise) =>
  (forall x, x \in p => x \in q) => 2<=order =>
  grn_renyi order (dmap (p `*` noise) f) (dmap (q `*` noise) f)<=grn_renyi order p q.
proof.
  move=> hp hq hn hfp hfq hfn hs ho.
  have hsub := hrt_support_product p q noise noise hs _; first trivial.
  have h := hrm_renyi_map order (p `*` noise) (q `*` noise) f
    (dprod_ll_auto p noise hp hn) (dprod_ll_auto q noise hq hn)
    (finite_dprod p noise hfp hfn) (finite_dprod q noise hfq hfn) hsub ho.
  by move: h; rewrite (hrt_shared_noise order p q noise hp hq hn hfp hfq hfn hs ho).
qed.
