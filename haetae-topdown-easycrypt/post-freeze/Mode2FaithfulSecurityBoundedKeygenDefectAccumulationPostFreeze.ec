require import AllCore Distr Real StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
               Mode2FaithfulSecuritySampledBoundedKeygenExhaustionMonotonicityPostFreeze.

theory Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze.

import RealOrder.
import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.
import Mode2FaithfulSecuritySampledBoundedKeygenExhaustionMonotonicityPostFreeze.

module SampledDecision =
  Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
    .SampledBoundedKeygenDecision.

(* This layer iterates the certified one-step sampled exhaustion inequality
   across a finite retry budget.  It exposes the exact accumulated progress
   defect and does not claim that the defect is zero or numeric, that the
   exhaustion mass contracts strictly, or that the unbounded keygen loop
   terminates. *)

op finite_additive_defect_prefix
    (defect : int -> real) fuel0 : real =
  Bigreal.BRA.bigi predT defect 1 (fuel0 + 1).

op finite_additive_defect_recurrence_certificate
    (mass defect : int -> real) fuel0 : bool =
  0 <= fuel0 /\
  forall i,
    0 <= i < fuel0 =>
    mass (i + 1) <= mass i + defect (i + 1).

lemma finite_additive_defect_recurrence_bound
    (mass defect : int -> real) fuel0 :
  finite_additive_defect_recurrence_certificate
    mass defect fuel0 =>
  mass fuel0 <=
    mass 0 + finite_additive_defect_prefix defect fuel0.
proof.
rewrite /finite_additive_defect_recurrence_certificate.
move=> [hfuel hstep].
elim/intind: fuel0 hfuel hstep => [|fuel hfuel ih] hstep.
+ rewrite /finite_additive_defect_prefix.
  rewrite Bigreal.BRA.big_geq 1:/#.
  smt().
have hprev :
  mass fuel <= mass 0 + finite_additive_defect_prefix defect fuel.
+ apply ih.
  move=> i hi.
  apply hstep.
  smt().
have hnext :
  mass (fuel + 1) <= mass fuel + defect (fuel + 1).
+ apply hstep.
  smt().
rewrite /finite_additive_defect_prefix.
rewrite
  (Bigreal.BRA.big_int_recr (fuel + 1) 1 defect) 1:/#.
smt().
qed.

lemma sampled_bounded_keygen_exhaustion_additive_defect_certificate
    fuel0 &m :
  0 <= fuel0 =>
  finite_additive_defect_recurrence_certificate
    (fun i =>
      Pr[SampledDecision.main(i) @ &m :
           sampled_bounded_keygen_rejected_tail_exhausted
             SampledDecision.raw_current i res])
    delta_bounded_keygen_progress
    fuel0.
proof.
move=> hfuel.
rewrite /finite_additive_defect_recurrence_certificate.
split; first exact hfuel.
move=> i hi.
have hi0 : 0 <= i by smt().
exact
  (sampled_bounded_keygen_rejected_tail_exhaustion_mass_prefix
    i &m hi0).
qed.

lemma sampled_bounded_keygen_exhaustion_additive_defect_bound
    fuel0 &m :
  0 <= fuel0 =>
  Pr[SampledDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledDecision.raw_current fuel0 res] <=
  Pr[SampledDecision.main(0) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledDecision.raw_current 0 res] +
  finite_additive_defect_prefix
    delta_bounded_keygen_progress fuel0.
proof.
move=> hfuel.
apply
  (finite_additive_defect_recurrence_bound
    (fun i =>
      Pr[SampledDecision.main(i) @ &m :
           sampled_bounded_keygen_rejected_tail_exhausted
             SampledDecision.raw_current i res])
    delta_bounded_keygen_progress
    fuel0).
exact
  (sampled_bounded_keygen_exhaustion_additive_defect_certificate
    fuel0 &m hfuel).
qed.

end Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze.
