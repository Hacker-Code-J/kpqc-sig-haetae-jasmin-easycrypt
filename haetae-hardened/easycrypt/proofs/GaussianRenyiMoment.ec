require import AllCore Real RealExp RealSeries Distr Finite StdRing StdOrder.
require import GaussianRenyiSpec FiniteExpectationError.
import RField RealOrder.

lemma grn_constants :
  0%r < grn_delta < 1%r /\ 0%r < grn_epsilon /\
  1024%r*grn_delta < 1%r /\ 1024%r*grn_delta^2 = grn_epsilon.
proof. rewrite /grn_delta /grn_epsilon expr2; smt(). qed.

lemma grn_remainder_step (n z : real) :
  0%r <= n <= 1023%r => `|z| <= grn_delta =>
  (1%r+z)*(1%r+n*z+n*(n-1%r)*grn_delta^2) <=
    1%r+(n+1%r)*z+(n+1%r)*n*grn_delta^2.
proof.
  move=> hn hz; rewrite ler_norml in hz.
  have hd := grn_constants.
  have hs : 0%r <= grn_delta^2-z*z.
  + have h := mulr_ge0 (grn_delta-z) (grn_delta+z) _ _; first 2 smt().
    rewrite expr2; smt().
  have ht : 0%r <= 1%r-(n-1%r)*z.
  + move: hz; rewrite /grn_delta; smt().
  have hh : 0%r <= n*((grn_delta^2-z*z)+grn_delta^2*(1%r-(n-1%r)*z)).
  + apply mulr_ge0; first smt().
    apply addr_ge0; first exact hs.
    apply mulr_ge0; first by rewrite expr2; smt().
    exact ht.
  have he : (1%r+(n+1%r)*z+(n+1%r)*n*grn_delta^2) -
      (1%r+z)*(1%r+n*z+n*(n-1%r)*grn_delta^2) =
      n*((grn_delta^2-z*z)+grn_delta^2*(1%r-(n-1%r)*z)) by ring.
  smt().
qed.

lemma grn_power_upper (order : int) (z : real) :
  0 <= order => order <= 1024 => `|z| <= grn_delta =>
  (1%r+z)^order <= 1%r+order%r*z+order%r*(order-1)%r*grn_delta^2.
proof.
  elim: order => [|n hn ih] hcap hz.
  + by rewrite expr0 /=.
  have hprev := ih _ hz; first smt().
  have hbase : 0%r <= 1%r+z by
    have hd := grn_constants; move: hz; rewrite ler_norml; smt().
  have hm := ler_wpmul2l (1%r+z) hbase _ _ hprev.
  have hstep := grn_remainder_step n%r z _ hz; first smt().
  rewrite exprS 1:hn fromintD fromintB /=.
  move: hm; rewrite fromintB /=.
  smt().
qed.

lemma grn_bernoulli (n : int) (z : real) :
  0 <= n => -1%r <= z => 1%r+n%r*z <= (1%r+z)^n.
proof.
  elim: n => [|n hn ih] hz.
  + by rewrite expr0 /=.
  have hbase : 0%r <= 1%r+z by smt().
  have hm := ler_wpmul2l (1%r+z) hbase _ _ (ih hz).
  have hsq : 0%r <= n%r*z*z by
    have hh := mulr_ge0 n%r (z*z) _ _; smt().
  rewrite exprS 1:hn fromintD /=; smt().
qed.

lemma grn_zero_mass ['a] (p q : 'a distr) x : grn_mass_bounds p q =>
  mu1 q x = 0%r => mu1 p x = 0%r.
proof.
  move=> hb hq; have h := hb x; have hp := ge0_mu1 p x.
  rewrite hq /= in h; smt().
qed.

lemma grn_support_inclusion ['a] (p q : 'a distr) : grn_mass_bounds p q =>
  forall x, x \in p => x \in q.
proof.
  move=> hb x hp; case (x \in q) => hq //.
  have hzero : mu1 q x = 0%r by rewrite -supportPn.
  have hpzero := grn_zero_mass p q x hb hzero.
  move: hp; rewrite supportP hpzero; trivial.
qed.

lemma grn_likelihood_bounds ['a] (p q : 'a distr) x :
  grn_mass_bounds p q => x \in q =>
  1%r-grn_delta <= grn_likelihood p q x <= 1%r+grn_delta.
proof.
  move=> hb hx; have h := hb x.
  have hq : 0%r < mu1 q x by move: hx; rewrite supportP; have := ge0_mu1 q x; smt().
  rewrite /grn_likelihood.
  rewrite (ler_pdivl_mulr _ _ _ hq) (ler_pdivr_mulr _ _ _ hq).
  exact h.
qed.

lemma grn_likelihood_hasE ['a] (p q : 'a distr) :
  is_finite (Distr.support q) => hasE q (grn_likelihood p q).
proof. exact (hasE_finite q (grn_likelihood p q)). qed.

lemma grn_moment_hasE ['a] (order : int) (p q : 'a distr) :
  is_finite (Distr.support q) => hasE q (fun x => (grn_likelihood p q x)^order).
proof. exact (hasE_finite q _). qed.

lemma grn_likelihood_mean ['a] (p q : 'a distr) :
  is_lossless p => grn_mass_bounds p q => E q (grn_likelihood p q) = 1%r.
proof.
  move=> hp hb.
  have he : E q (grn_likelihood p q) = RealSeries.sum (mu1 p).
  + rewrite /E; apply RealSeries.eq_sum => x /=.
    case (mu1 q x = 0%r) => hx.
    - have hp0 := grn_zero_mass p q x hb hx.
      by rewrite /grn_likelihood hx hp0 /=.
    rewrite /grn_likelihood; field; trivial.
  by rewrite he -weightE hp.
qed.

lemma grn_centered_mean ['a] (p q : 'a distr) :
  is_lossless p => is_lossless q => is_finite (Distr.support q) => grn_mass_bounds p q =>
  E q (fun x => grn_likelihood p q x-1%r) = 0%r.
proof.
  move=> hp hq hfin hb.
  rewrite expB 1:(grn_likelihood_hasE p q hfin) 1:hasEC
    (grn_likelihood_mean p q hp hb) expC hq /=.
  trivial.
qed.

lemma grn_affine_mean ['a] (p q : 'a distr) (c d : real) :
  is_lossless p => is_lossless q => is_finite (Distr.support q) => grn_mass_bounds p q =>
  E q (fun x => c+d*(grn_likelihood p q x-1%r)) = c.
proof.
  move=> hp hq hfin hb.
  rewrite expD 1:hasEC 1:(hasE_finite q _ hfin) expC hq expZ
    (grn_centered_mean p q hp hq hfin hb) /=.
  trivial.
qed.

lemma grn_moment_bounds ['a] (order : int) (p q : 'a distr) :
  is_lossless p => is_lossless q => is_finite (Distr.support q) =>
  grn_mass_bounds p q => 0 <= order <= 1024 =>
  1%r <= grn_moment order p q <=
    1%r+order%r*(order-1)%r*grn_delta^2.
proof.
  move=> hp hq hfin hb ho.
  have hl := finite_expectation_le q
    (fun x => 1%r+order%r*(grn_likelihood p q x-1%r))
    (fun x => (grn_likelihood p q x)^order) hfin _.
  + move=> x hx /=.
    have hr := grn_likelihood_bounds p q x hb hx.
    have hd := grn_constants.
    have hc : 1%r+(grn_likelihood p q x-1%r)=grn_likelihood p q x by ring.
    have h := grn_bernoulli order (grn_likelihood p q x-1%r) _ _; first 2 smt().
    by rewrite hc in h.
  have hu := finite_expectation_le q
    (fun x => (grn_likelihood p q x)^order)
    (fun x => (1%r+order%r*(order-1)%r*grn_delta^2)+
      order%r*(grn_likelihood p q x-1%r)) hfin _.
  + move=> x hx /=.
    have hr := grn_likelihood_bounds p q x hb hx.
    have hz : `|grn_likelihood p q x-1%r| <= grn_delta by rewrite ler_norml; smt().
    have hc : 1%r+(grn_likelihood p q x-1%r)=grn_likelihood p q x by ring.
    have h := grn_power_upper order (grn_likelihood p q x-1%r) _ _ hz; first 2 smt().
    rewrite hc in h; smt().
  rewrite (grn_affine_mean p q 1%r order%r hp hq hfin hb) in hl.
  rewrite (grn_affine_mean p q (1%r+order%r*(order-1)%r*grn_delta^2)
    order%r hp hq hfin hb) in hu.
  rewrite /grn_moment; smt().
qed.

lemma grn_root_bound (order : int) (moment : real) : 2 <= order <= 1024 =>
  1%r <= moment <= 1%r+order%r*(order-1)%r*grn_delta^2 =>
  moment ^ (1%r/(order-1)%r) <= 1%r+grn_epsilon.
proof.
  move=> ho hm.
  have hd := grn_constants.
  have he : order%r*grn_delta^2 <= grn_epsilon by
    rewrite /grn_delta /grn_epsilon expr2; smt().
  have hb := grn_bernoulli (order-1) grn_epsilon _ _; first 2 smt().
  have hup : moment <= (1%r+grn_epsilon)^(order-1) by smt().
  have hr := RealExp.rpow_hmono moment ((1%r+grn_epsilon)^(order-1))
    (1%r/(order-1)%r) _ _; first 2 smt().
  have hbase : 0%r < 1%r+grn_epsilon by smt().
  have hroot : ((1%r+grn_epsilon)^(order-1)) ^
      (1%r/(order-1)%r) = 1%r+grn_epsilon.
  + rewrite -(RealExp.rpow_int (1%r+grn_epsilon) (order-1)) 1:/#
      -RealExp.rpowM 1:hbase.
    have -> : (order-1)%r*(1%r/(order-1)%r) = 1%r by field; smt().
    exact (RealExp.rpow1 (1%r+grn_epsilon) hbase).
  by move: hr; rewrite hroot.
qed.

lemma grn_finite_bound ['a] (order : int) (p q : 'a distr) :
  is_lossless p => is_lossless q =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  grn_mass_bounds p q => 2 <= order <= 1024 =>
  grn_renyi order p q <= 1%r+grn_epsilon.
proof.
  move=> hp hq hfp hfq hb ho; rewrite /grn_renyi.
  apply (grn_root_bound order (grn_moment order p q) ho).
  apply (grn_moment_bounds order p q hp hq hfq hb); smt().
qed.

lemma grn_power_weight (order : int) (u v : real) : 2 <= order => 0%r < v =>
  (u/v)^order*v = u^order/v^(order-1).
proof.
  move=> ho hv.
  have he : v^order = v*v^(order-1).
  + have hn : order=(order-1)+1 by ring.
    by rewrite {1}hn exprS 1:/#.
  have hp := expr_gt0 (order-1) v hv.
  rewrite exprMn 1:/# exprVn 1:/# he.
  field; smt().
qed.

(* Exact correspondence with the published power-sum form. Zero-mass
   points contribute zero, and support inclusion excludes singular terms. *)
lemma grn_moment_rossi ['a] (order : int) (p q : 'a distr) :
  2 <= order => is_lossless p => is_lossless q =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  (forall x, x \in p => x \in q) =>
  grn_moment order p q = RealSeries.sum (fun x => (mu1 p x)^order/(mu1 q x)^(order-1)).
proof.
  move=> ho hp hq hfp hfq hs.
  rewrite /grn_moment /E; apply RealSeries.eq_sum => x /=.
  case (mu1 q x=0%r) => hx.
  + have hp0 : mu1 p x=0%r by
      have h := hs x; move: h; rewrite !supportP hx; smt().
    rewrite /grn_likelihood hx hp0 /= !expr0z.
    have -> : !(order=0) by smt().
    trivial.
  have hv : 0%r < mu1 q x by have := ge0_mu1 q x; smt().
  rewrite /grn_likelihood; exact (grn_power_weight order (mu1 p x) (mu1 q x) ho hv).
qed.

lemma grn_renyi_rossi ['a] (order : int) (p q : 'a distr) :
  2 <= order => is_lossless p => is_lossless q =>
  is_finite (Distr.support p) => is_finite (Distr.support q) =>
  (forall x, x \in p => x \in q) =>
  grn_renyi order p q =
    (RealSeries.sum (fun x => (mu1 p x)^order/(mu1 q x)^(order-1))) ^ (1%r/(order-1)%r).
proof.
  move=> ho hp hq hfp hfq hs.
  by rewrite /grn_renyi (grn_moment_rossi order p q ho hp hq hfp hfq hs).
qed.
