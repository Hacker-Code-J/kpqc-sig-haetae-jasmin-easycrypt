require import AllCore StdRing StdOrder RealSeries Distr DBool SDist.
import RField RealOrder.

(* A bound on the support suffices for integrability, even when that
   support is infinite. No finite enumeration is used. *)
lemma distribution_hasE_unit_interval ['a] (d : 'a distr) (f : 'a -> real) :
  (forall x, x \in d => 0%r <= f x <= 1%r) => hasE d f.
proof.
  move=> hbound; rewrite /hasE.
  apply (RealSeries.summable_le (mu1 d) _ (summable_mu1 d)) => x /=.
  case (x \in d) => hx.
  + have hf := hbound x hx; have hm := ge0_mu1 d x.
    rewrite normrM !ger0_norm 1..3:/#; smt().
  have hz : mu1 d x = 0%r by rewrite -supportPn.
  by rewrite hz /=.
qed.

(* Sampling a biased bit is a proof device: its true-event probability
   equals the expectation of f. Values outside the support have no mass. *)
lemma distribution_expectation_biased ['a] (d : 'a distr) (f : 'a -> real) :
  (forall x, x \in d => 0%r <= f x <= 1%r) =>
  E d f = mu1 (dlet d (fun x => Biased.dbiased (f x))) true.
proof.
  move=> hbound; rewrite /E dlet1E.
  apply RealSeries.eq_sum => x /=.
  case (x \in d) => hx.
  + rewrite Biased.dbiased1E /= (Biased.clamp_id _ (hbound x hx)); smt().
  have hz : mu1 d x = 0%r by rewrite -supportPn.
  by rewrite hz /=.
qed.

(* SDist is the supremum of event-probability differences. Its installed
   data-processing theorem applies to subdistributions as well, so no
   losslessness or finite-support hypothesis is required here. *)
lemma distribution_expectation_distance ['a]
    (d1 d2 : 'a distr) (f : 'a -> real) :
  (forall x, x \in d1 \/ x \in d2 => 0%r <= f x <= 1%r) =>
  `|E d1 f - E d2 f| <= SDist.sdist d1 d2.
proof.
  move=> hbound.
  have h1 : forall x, x \in d1 => 0%r <= f x <= 1%r by smt().
  have h2 : forall x, x \in d2 => 0%r <= f x <= 1%r by smt().
  rewrite (distribution_expectation_biased d1 f h1)
    (distribution_expectation_biased d2 f h2).
  have hmu := SDist.sdist_upper_bound
    (dlet d1 (fun x => Biased.dbiased (f x)))
    (dlet d2 (fun x => Biased.dbiased (f x))) (pred1 true).
  have hcontract := SDist.sdist_dlet d1 d2 (fun x => Biased.dbiased (f x)).
  exact (ler_trans _ _ _ hmu hcontract).
qed.

lemma distribution_expectation_distance_global ['a]
    (d1 d2 : 'a distr) (f : 'a -> real) :
  (forall x, 0%r <= f x <= 1%r) =>
  `|E d1 f - E d2 f| <= SDist.sdist d1 d2.
proof.
  move=> hbound; apply distribution_expectation_distance => x hx.
  exact (hbound x).
qed.
