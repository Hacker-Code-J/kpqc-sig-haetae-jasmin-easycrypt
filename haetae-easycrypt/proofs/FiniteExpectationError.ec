require import AllCore StdRing StdOrder Finite Distr.
import RField RealOrder.

lemma finite_expectation_le ['a] (d : 'a distr) (f g : 'a -> real) :
  is_finite (Distr.support d) =>
  (forall x, x \in d => f x <= g x) => E d f <= E d g.
proof.
  move=> hfin hpoint.
  have hf := hasE_finite d f hfin.
  have hg := hasE_finite d g hfin.
  have hnonneg : 0%r <= E d (fun x => g x - f x).
  + apply exp_ge0 => x hx; have h := hpoint x hx; smt().
  rewrite expB 1:hg 1:hf in hnonneg; smt().
qed.

(* A pointwise error has a uniform part and an additional cost on one
   event. Its average additional cost is weighted by that event's mass. *)
lemma finite_expectation_error ['a]
    (d : 'a distr) (f g : 'a -> real) (event : 'a -> bool)
    (epsilon c : real) :
  is_finite (Distr.support d) => is_lossless d =>
  0%r <= epsilon => 0%r <= c =>
  (forall x, x \in d => `|f x - g x| <= epsilon + c * b2r (event x)) =>
  `|E d f - E d g| <= epsilon + c * mu d event.
proof.
  move=> hfin hll hepsilon hc hpoint.
  have hf := hasE_finite d f hfin.
  have hg := hasE_finite d g hfin.
  have hdiff := hasE_finite d (fun x => f x - g x) hfin.
  have hnorm := exp_norm d (fun x => f x - g x) hdiff.
  rewrite expB 1:hf 1:hg in hnorm.
  have hdom : forall x, x \in d =>
      `|f x - g x| <= epsilon + (if event x then c else 0%r).
  + move=> x hx; have h := hpoint x hx.
    by move: h; rewrite /b2r; case (event x) => he /=.
  have hmean := finite_expectation_le d (fun x => `|f x - g x|)
    (fun x => epsilon + (if event x then c else 0%r)) hfin hdom.
  have hconstant := hasE_finite d (fun _ => epsilon) hfin.
  have hevent := hasE_finite d (fun x => if event x then c else 0%r) hfin.
  have hsum := expD d (fun _ => epsilon)
    (fun x => if event x then c else 0%r) hconstant hevent.
  rewrite expC expC_cond hll /= in hsum.
  have hmean' := hmean.
  rewrite hsum in hmean'.
  exact (ler_trans _ _ _ hnorm hmean').
qed.
