require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32.
require import TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
               Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
               Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze
               Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze
               Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze.

theory Mode2FaithfulSecuritySampledFirstAttemptRejectCertificatePostFreeze.

import RealOrder.
import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze.
import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze.

module SampledFirst =
  Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze
    .SampledFirstAttemptDecision.

module SampledBounded =
  Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
    .SampledBoundedKeygenDecision.

(* This layer only re-expresses the sampled first-attempt rejection event as
   the exact singular-score tail event and threads an abstract epsilon
   certificate into the existing bounded-keygen lower bound.  It does not add
   a numeric tail estimate, a new sampler-progress premise, retry semantics,
   unbounded termination, packing, or any HAETAE.kg equality. *)

op sampled_first_attempt_score_tail
    (trace : first_attempt_trace) : bool =
  611098 < W64.to_uint (first_attempt_trace_score trace).

lemma checked_first_attempt_snapshot_reject_score_tailE
    (raw_seed0 : BArray32.t) (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0 trace =>
  (! first_attempt_trace_accepted trace <=>
   sampled_first_attempt_score_tail trace).
proof.
move=> hsnapshot.
have haccept :=
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_accepted_iff_score_le
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0 trace hsnapshot.
rewrite /sampled_first_attempt_score_tail.
split.
+ move=> hreject.
   move: haccept hreject.
   smt().
+ move=> htail.
   move: haccept htail.
   smt().
qed.

lemma sampled_first_attempt_reject_score_tail_equiv :
  equiv [SampledFirst.main ~ SampledFirst.main :
    true ==>
    SampledFirst.raw_current{1} = SampledFirst.raw_current{2} /\
    res{1} = res{2} /\
    (! first_attempt_trace_accepted res{1} <=>
     sampled_first_attempt_score_tail res{2})].
proof.
proc.
seq 1 1 :
  (SampledFirst.raw_current{1} = SampledFirst.raw_current{2}).
+ rnd.
   auto.
exlim SampledFirst.raw_current{2} => raw0.
call
  (checked_mode2_first_attempt_decision_self_snapshot raw0).
auto => />.
move=> result hsnapshot.
have hevent :=
  checked_first_attempt_snapshot_reject_score_tailE
    raw0 result hsnapshot.
split.
+ move=> hreject.
  apply hevent.
  exact hreject.
+ move=> htail.
  apply hevent.
  exact htail.
qed.

lemma sampled_first_attempt_reject_score_tail_massE &m :
  Pr[SampledFirst.main() @ &m :
       ! first_attempt_trace_accepted res] =
  Pr[SampledFirst.main() @ &m :
       sampled_first_attempt_score_tail res].
proof.
byequiv sampled_first_attempt_reject_score_tail_equiv => //=.
qed.

op sampled_first_attempt_reject_probability_certificate
    (epsilon reject_mass : real) : bool =
  0%r <= epsilon <= 1%r /\ reject_mass <= epsilon.

lemma sampled_first_attempt_reject_probability_certificate_score_tailE
    epsilon &m :
  sampled_first_attempt_reject_probability_certificate
    epsilon
    Pr[SampledFirst.main() @ &m :
         ! first_attempt_trace_accepted res] <=>
  sampled_first_attempt_reject_probability_certificate
    epsilon
    Pr[SampledFirst.main() @ &m :
         sampled_first_attempt_score_tail res].
proof.
rewrite /sampled_first_attempt_reject_probability_certificate.
rewrite sampled_first_attempt_reject_score_tail_massE.
done.
qed.

lemma sampled_bounded_keygen_success_lower_bound_from_score_tail_certificate
    fuel0 epsilon &m :
  0 <= fuel0 =>
  sampled_first_attempt_reject_probability_certificate
    epsilon
    Pr[SampledFirst.main() @ &m :
         sampled_first_attempt_score_tail res] =>
  Pr[SampledBounded.main(fuel0) @ &m :
       sampled_bounded_keygen_first_accept
         SampledBounded.raw_current fuel0 res] +
  Pr[SampledBounded.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_accept
         SampledBounded.raw_current fuel0 res] >=
  1%r -
  delta_bounded_keygen_progress fuel0 -
  epsilon -
  finite_additive_defect_prefix
    delta_bounded_keygen_progress fuel0.
proof.
move=> hfuel hcert.
move: hcert.
rewrite -sampled_first_attempt_reject_probability_certificate_score_tailE.
move=> [[heps0 heps1] hreject].
have hbound :=
  sampled_bounded_keygen_accepted_mass_first_reject_defect_bound
    fuel0 &m hfuel.
have hstep :
    1%r - delta_bounded_keygen_progress fuel0 - epsilon -
      finite_additive_defect_prefix
        delta_bounded_keygen_progress fuel0 <=
    1%r - delta_bounded_keygen_progress fuel0 -
      Pr[SampledFirst.main() @ &m :
           ! first_attempt_trace_accepted res] -
      finite_additive_defect_prefix
        delta_bounded_keygen_progress fuel0.
+ smt().
exact (ler_trans _ _ _ hstep hbound).
qed.

end Mode2FaithfulSecuritySampledFirstAttemptRejectCertificatePostFreeze.
