require import AllCore List Real RealExp RealSeries Distr DList Finite StdRing StdOrder.
require import GaussianRenyiSpec GaussianRenyiMoment FiniteExpectationError IidExponentialTail.
import RField RealOrder.

lemma hrt_finite_dlist ['a] (d : 'a distr) (n : int) :
  is_finite (Distr.support d) => 0 <= n => is_finite (Distr.support (dlist d n)).
proof. exact (iet_finite_dlist d n). qed.

lemma hrt_support_product ['a 'b] (p1 q1 : 'a distr) (p2 q2 : 'b distr) :
  (forall x, x \in p1 => x \in q1) => (forall y, y \in p2 => y \in q2) =>
  forall xy, xy \in p1 `*` p2 => xy \in q1 `*` q2.
proof.
  move=> hs1 hs2 [x y]; rewrite !supp_dprod; smt().
qed.

lemma hrt_support_dlist ['a] (p q : 'a distr) (n : int) : 0 <= n =>
  (forall x, x \in p => x \in q) => forall xs, xs \in dlist p n => xs \in dlist q n.
proof.
  move=> hn hs xs; rewrite !supp_dlist 1..2:hn => -[hlen hall].
  split; first exact hlen.
  apply List.allP => x hx.
  move/List.allP: hall => hall; exact (hs x (hall x hx)).
qed.

lemma hrt_likelihood_mean ['a] (p q : 'a distr) : is_lossless p =>
  (forall x, x \in p => x \in q) => E q (grn_likelihood p q) = 1%r.
proof.
  move=> hp hs.
  have he : E q (grn_likelihood p q) = RealSeries.sum (mu1 p).
  + rewrite /E; apply RealSeries.eq_sum => x /=.
    case (mu1 q x=0%r) => hx.
    - have hp0 : mu1 p x=0%r by
        have h := hs x; move: h; rewrite !supportP hx; smt().
      by rewrite /grn_likelihood hx hp0 /=.
    rewrite /grn_likelihood; field; trivial.
  by rewrite he -weightE hp.
qed.

lemma hrt_affine_mean ['a] (p q : 'a distr) (c d : real) :
  is_lossless p => is_lossless q => is_finite (Distr.support q) =>
  (forall x, x \in p => x \in q) =>
  E q (fun x => c+d*(grn_likelihood p q x-1%r)) = c.
proof.
  move=> hp hq hf hs.
  rewrite expD 1:hasEC 1:(hasE_finite q _ hf) expC hq expZ
    expB 1:(hasE_finite q _ hf) 1:hasEC (hrt_likelihood_mean p q hp hs) expC hq /=.
  trivial.
qed.

lemma hrt_moment_ge1 ['a] (order : int) (p q : 'a distr) :
  is_lossless p => is_lossless q => is_finite (Distr.support q) =>
  (forall x, x \in p => x \in q) => 0 <= order => 1%r <= grn_moment order p q.
proof.
  move=> hp hq hf hs ho.
  have hl := finite_expectation_le q
    (fun x => 1%r+order%r*(grn_likelihood p q x-1%r))
    (fun x => (grn_likelihood p q x)^order) hf _.
  + move=> x hx /=.
    have hr : 0%r <= grn_likelihood p q x by
      rewrite /grn_likelihood; apply divr_ge0; exact ge0_mu1.
    have hc : 1%r+(grn_likelihood p q x-1%r)=grn_likelihood p q x by ring.
    have h := grn_bernoulli order (grn_likelihood p q x-1%r) ho _; first smt().
    by rewrite hc in h.
  rewrite (hrt_affine_mean p q 1%r order%r hp hq hf hs) in hl.
  exact hl.
qed.

lemma hrt_likelihood_product ['a 'b] (p1 q1 : 'a distr) (p2 q2 : 'b distr) x y :
  grn_likelihood (p1 `*` p2) (q1 `*` q2) (x,y) =
    grn_likelihood p1 q1 x * grn_likelihood p2 q2 y.
proof.
  rewrite /grn_likelihood !dprod1E.
  case (mu1 q1 x=0%r) => h1; first by rewrite h1 /=.
  case (mu1 q2 y=0%r) => h2; first by rewrite h2 /=.
  field; smt().
qed.

(* Integrable independent likelihood powers factor exactly. *)
lemma hrt_moment_product ['a 'b] (order : int) (p1 q1 : 'a distr) (p2 q2 : 'b distr) :
  is_finite (Distr.support q1) => is_finite (Distr.support q2) => 0 <= order =>
  grn_moment order (p1 `*` p2) (q1 `*` q2) =
    grn_moment order p1 q1 * grn_moment order p2 q2.
proof.
  move=> hq1 hq2 ho.
  have he1 := hasE_finite q1 (fun x => (grn_likelihood p1 q1 x)^order) hq1.
  have he2 := hasE_finite q2 (fun y => (grn_likelihood p2 q2 y)^order) hq2.
  rewrite /grn_moment -(iet_expectation_product q1 q2 _ _ he1 he2).
  apply eq_exp; case=> x y hxy /=.
  by rewrite hrt_likelihood_product exprMn 1:ho.
qed.

lemma hrt_renyi_product ['a 'b] (order : int) (p1 q1 : 'a distr) (p2 q2 : 'b distr) :
  is_lossless p1 => is_lossless q1 => is_lossless p2 => is_lossless q2 =>
  is_finite (Distr.support p1) => is_finite (Distr.support q1) =>
  is_finite (Distr.support p2) => is_finite (Distr.support q2) =>
  (forall x, x \in p1 => x \in q1) => (forall y, y \in p2 => y \in q2) => 2 <= order =>
  grn_renyi order (p1 `*` p2) (q1 `*` q2) =
    grn_renyi order p1 q1 * grn_renyi order p2 q2.
proof.
  move=> hp1 hq1 hp2 hq2 hfp1 hfq1 hfp2 hfq2 hs1 hs2 ho.
  have hn : 0 <= order by smt().
  have h1 := hrt_moment_ge1 order p1 q1 hp1 hq1 hfq1 hs1 hn.
  have h2 := hrt_moment_ge1 order p2 q2 hp2 hq2 hfq2 hs2 hn.
  rewrite /grn_renyi (hrt_moment_product order p1 q1 p2 q2 hfq1 hfq2 hn).
  apply RealExp.rpowMr; smt().
qed.

lemma hrt_moment_self ['a] (order : int) (d : 'a distr) : is_lossless d =>
  grn_moment order d d = 1%r.
proof.
  move=> hd; rewrite /grn_moment.
  have he : E d (fun x => (grn_likelihood d d x)^order) = E d (fun _ => 1%r).
  + apply eq_exp => x hx /=.
    have hn : mu1 d x <> 0%r by rewrite -supportP.
    have heq : grn_likelihood d d x = 1%r by
      rewrite /grn_likelihood; field; trivial.
    by rewrite heq ?expr1z.
  by rewrite he expC hd /=.
qed.

lemma hrt_renyi_self ['a] (order : int) (d : 'a distr) : is_lossless d =>
  grn_renyi order d d = 1%r.
proof. by move=> hd; rewrite /grn_renyi (hrt_moment_self order d hd) RealExp.rpow1r. qed.

lemma hrt_shared_noise ['a 'b] (order : int) (p q : 'a distr) (s : 'b distr) :
  is_lossless p => is_lossless q => is_lossless s =>
  is_finite (Distr.support p) => is_finite (Distr.support q) => is_finite (Distr.support s) =>
  (forall x, x \in p => x \in q) => 2 <= order =>
  grn_renyi order (p `*` s) (q `*` s) = grn_renyi order p q.
proof.
  move=> hp hq hs hfp hfq hfs hsub ho.
  rewrite (hrt_renyi_product order p q s s hp hq hs hs hfp hfq hfs hfs hsub _) 1:// 1:ho
    (hrt_renyi_self order s hs) /=.
  trivial.
qed.

lemma hrt_dmap_mass ['a 'b] (d : 'a distr) (f : 'a -> 'b) x : injective f =>
  mu1 (dmap d f) (f x) = mu1 d x.
proof.
  move=> hf; rewrite dmap1E; apply mu_eq => y.
  rewrite /(\o) /pred1 /=; smt().
qed.

lemma hrt_moment_injective ['a 'b] (order : int) (p q : 'a distr) (f : 'a -> 'b) :
  is_finite (Distr.support q) => injective f =>
  grn_moment order (dmap p f) (dmap q f) = grn_moment order p q.
proof.
  move=> hq hf.
  have hmap := iet_finite_dmap q f hq.
  have hE := hasE_finite (dmap q f)
    (fun x => (grn_likelihood (dmap p f) (dmap q f) x)^order) hmap.
  rewrite /grn_moment (exp_dmap q f _ hE).
  apply eq_exp => x hx; rewrite /(\o) /grn_likelihood /= !hrt_dmap_mass 1..2:hf.
  trivial.
qed.

lemma hrt_cons_injective ['a] : injective (fun (xy : 'a*'a list) => xy.`1::xy.`2).
proof. move=> [x xs] [y ys] /=; smt(). qed.

lemma hrt_moment_dlist ['a] (order : int) (p q : 'a distr) (n : int) :
  is_finite (Distr.support q) => 0 <= order => 0 <= n =>
  grn_moment order (dlist p n) (dlist q n) = (grn_moment order p q)^n.
proof.
  move=> hq ho; elim: n => [|n hn ih].
  + by rewrite !dlist0 1..2:// (hrt_moment_self order (dunit []) (dunit_ll [])) expr0.
  have hqn := hrt_finite_dlist q n hq hn.
  have hpair := finite_dprod q (dlist q n) hq hqn.
  rewrite !dlistS 1..2:hn !dapply_dmap
    (hrt_moment_injective order (p `*` dlist p n) (q `*` dlist q n)
      (fun (xy : 'a*'a list) => xy.`1::xy.`2) hpair hrt_cons_injective)
    (hrt_moment_product order p q (dlist p n) (dlist q n) hq hqn ho) ih exprS 1:hn.
  trivial.
qed.

lemma hrt_root_nat_power (value power : real) (n : int) : 0%r < value => 0 <= n =>
  (value^n)^power = (value^power)^n.
proof.
  move=> hv hn.
  have hp := RealExp.rpow_gt0 value power hv.
  rewrite -(RealExp.rpow_int value n) 1:/#
    -(RealExp.rpow_int (value^power) n) 1:/# -!RealExp.rpowM 1..2:hv.
  congr; ring.
qed.

lemma hrt_renyi_dlist ['a] (order : int) (p q : 'a distr) (n : int) :
  is_lossless p => is_lossless q =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  (forall x, x \in p => x \in q) => 2 <= order => 0 <= n =>
  grn_renyi order (dlist p n) (dlist q n) = (grn_renyi order p q)^n.
proof.
  move=> hp hq hfp hfq hs ho hn.
  have horder : 0 <= order by smt().
  have hm := hrt_moment_ge1 order p q hp hq hfq hs horder.
  rewrite /grn_renyi (hrt_moment_dlist order p q n hfq horder hn).
  apply hrt_root_nat_power; smt().
qed.

lemma hrt_power_mono (x y : real) (n : int) : 0 <= n => 0%r <= x <= y => x^n <= y^n.
proof.
  move=> hn hxy.
  have h := RealExp.rpow_hmono x y n%r _ hxy; first smt().
  by move: h; rewrite !RealExp.rpow_int 1..2:/#.
qed.

lemma hrt_dlist_bound ['a] (order : int) (p q : 'a distr) (n : int) :
  is_lossless p => is_lossless q =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  grn_mass_bounds p q => 2 <= order <= 1024 => 0 <= n =>
  grn_renyi order (dlist p n) (dlist q n) <= (1%r+grn_epsilon)^n.
proof.
  move=> hp hq hfp hfq hb ho hn.
  have hs := grn_support_inclusion p q hb.
  have horder : 2 <= order by smt().
  rewrite (hrt_renyi_dlist order p q n hp hq hfp hfq hs horder hn).
  have hu := grn_finite_bound order p q hp hq hfp hfq hb ho.
  have hm := grn_moment_bounds order p q hp hq hfq hb _; first smt().
  have hpos : 0%r <= grn_renyi order p q by
    rewrite /grn_renyi; apply RealExp.rpow_ge0; smt().
  apply hrt_power_mono; smt().
qed.

lemma hrt_small_power (n : int) : 0 <= n => n <= 2818 =>
  (1%r+grn_epsilon)^n <= 1%r+(4%r/3%r)*n%r*grn_epsilon.
proof.
  elim: n => [|n hn ih] hcap.
  + by rewrite expr0 /=.
  have he := grn_constants.
  have hbase : 0%r <= 1%r+grn_epsilon by smt().
  have hprev := ih _; first smt().
  have hm := ler_wpmul2l (1%r+grn_epsilon) hbase _ _ hprev.
  have hs : (1%r+grn_epsilon)*(1%r+(4%r/3%r)*n%r*grn_epsilon) <=
      1%r+(4%r/3%r)*(n+1)%r*grn_epsilon.
  + rewrite /grn_epsilon fromintD /=; smt().
  rewrite exprS 1:hn; exact (ler_trans _ _ _ hm hs).
qed.

lemma hrt_common_bound (n : int) : 0 <= n <= 2818 =>
  (1%r+grn_epsilon)^n < 1%r+1%r/72057594037927936%r.
proof.
  move=> hn; have h := hrt_small_power n _ _; first 2 smt().
  have hs : 1%r+(4%r/3%r)*n%r*grn_epsilon < 1%r+1%r/72057594037927936%r by
    rewrite /grn_epsilon; smt().
  exact (ler_lt_trans _ _ _ h hs).
qed.

lemma hrt_dlist_common_bound ['a] (order : int) (p q : 'a distr) (n : int) :
  is_lossless p => is_lossless q =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  grn_mass_bounds p q => 2 <= order <= 1024 => 0 <= n <= 2818 =>
  grn_renyi order (dlist p n) (dlist q n) < 1%r+1%r/72057594037927936%r.
proof.
  move=> hp hq hfp hfq hb ho hn.
  have h := hrt_dlist_bound order p q n hp hq hfp hfq hb ho _; first smt().
  exact (ler_lt_trans _ _ _ h (hrt_common_bound n hn)).
qed.
