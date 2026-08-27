require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.

theory Mode2FaithfulSecurityBoundedKeygenExhaustionBoundPostFreeze.

import RealOrder.
import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.

(* This file derives a finite geometric exhaustion bound from an explicit
   contraction certificate on the actual sampled bounded-keygen exhaustion
   masses.  The certificate does not assert independence between retries.
   This layer does not derive a numeric contraction factor, an XOF
   pseudorandomness statement, unbounded termination, packing, full key
   generation, or equality with [HAETAE.kg]. *)

op finite_geometric_recurrence_certificate
    (mass : int -> real) fuel0 rho p0 : bool =
  0 <= fuel0 /\
  0%r <= rho <= 1%r /\
  0%r <= p0 <= 1%r /\
  mass 0 <= p0 /\
  (forall i,
     0 <= i < fuel0 =>
     mass (i + 1) <= rho * mass i).

lemma finite_geometric_recurrence_bound
    (mass : int -> real) fuel0 rho p0 :
  finite_geometric_recurrence_certificate mass fuel0 rho p0 =>
  mass fuel0 <= p0 * rho ^ fuel0.
proof.
rewrite /finite_geometric_recurrence_certificate.
move=> [hfuel [[hrho0 hrho1] [hp0 [hbase hstep]]]].
elim/intind: fuel0 hfuel hstep => [|fuel hfuel ih] hstep.
+ rewrite RField.expr0.
  smt().
rewrite RField.exprS //.
have hprev : mass fuel <= p0 * rho ^ fuel.
+ apply ih.
  move=> i hi.
  apply hstep.
  smt().
have hnext : mass (fuel + 1) <= rho * mass fuel.
+ apply hstep.
  smt().
have hscaled :
    rho * mass fuel <= rho * (p0 * rho ^ fuel).
+ exact (ler_wpmul2l rho hrho0 (mass fuel) (p0 * rho ^ fuel) hprev).
apply (ler_trans (rho * mass fuel)); first exact hnext.
rewrite
  (_ : rho * (p0 * rho ^ fuel) =
       p0 * (rho * rho ^ fuel)) in hscaled.
+ ring.
exact hscaled.
qed.

lemma sampled_bounded_keygen_exhaustion_geometric_bound
    fuel0 rho p0 &m :
  finite_geometric_recurrence_certificate
    (fun i =>
      Pr[SampledBoundedKeygenDecision.main(i) @ &m :
           sampled_bounded_keygen_rejected_tail_exhausted
             SampledBoundedKeygenDecision.raw_current i res])
    fuel0 rho p0 =>
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledBoundedKeygenDecision.raw_current fuel0 res] <=
  p0 * rho ^ fuel0.
proof.
exact
  (finite_geometric_recurrence_bound
    (fun i =>
      Pr[SampledBoundedKeygenDecision.main(i) @ &m :
           sampled_bounded_keygen_rejected_tail_exhausted
             SampledBoundedKeygenDecision.raw_current i res])
    fuel0 rho p0).
qed.

lemma sampled_bounded_keygen_accepted_mass_geometric_bound
    fuel0 rho p0 &m :
  finite_geometric_recurrence_certificate
    (fun i =>
      Pr[SampledBoundedKeygenDecision.main(i) @ &m :
           sampled_bounded_keygen_rejected_tail_exhausted
             SampledBoundedKeygenDecision.raw_current i res])
    fuel0 rho p0 =>
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_first_accept
         SampledBoundedKeygenDecision.raw_current fuel0 res] +
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_accept
         SampledBoundedKeygenDecision.raw_current fuel0 res] >=
  (1%r - delta_bounded_keygen_progress fuel0 - p0 * rho ^ fuel0).
proof.
move=> hcontraction.
have hfuel : 0 <= fuel0.
+ move: hcontraction.
  rewrite /finite_geometric_recurrence_certificate.
  smt().
have hexhaust :=
  sampled_bounded_keygen_exhaustion_geometric_bound
    fuel0 rho p0 &m hcontraction.
have hadditive :=
  sampled_bounded_keygen_additive_outcome_mass_bound fuel0 &m hfuel.
smt().
qed.

end Mode2FaithfulSecurityBoundedKeygenExhaustionBoundPostFreeze.
