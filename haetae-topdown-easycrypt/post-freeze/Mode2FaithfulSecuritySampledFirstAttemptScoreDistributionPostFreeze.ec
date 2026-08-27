require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecuritySampledFirstAttemptRejectCertificatePostFreeze
               Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze.

theory Mode2FaithfulSecuritySampledFirstAttemptScoreDistributionPostFreeze.

import RealOrder.
import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecuritySampledFirstAttemptRejectCertificatePostFreeze.
import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze.

module SampledFirst =
  Mode2FaithfulSecuritySampledFirstAttemptRejectCertificatePostFreeze.SampledFirst.

module SampledBounded =
  Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
    .SampledBoundedKeygenDecision.

(* This bridge is intentionally thin.  It does not manufacture a numeric
   estimate for the first-attempt score tail; instead, it packages the exact
   place where an external ideal-vs-actual comparison would enter and then
   threads that comparison into the existing reject certificate. *)

op sampled_first_attempt_score_distribution_bridge_certificate
    (actual_tail ideal_tail delta_xof : real) : bool =
  0%r <= delta_xof <= 1%r /\
  0%r <= ideal_tail <= 1%r /\
  actual_tail <= ideal_tail + delta_xof.

lemma sampled_first_attempt_score_distribution_bridge_certificateE
    actual_tail ideal_tail delta_xof :
  sampled_first_attempt_score_distribution_bridge_certificate
    actual_tail ideal_tail delta_xof =>
  actual_tail <= ideal_tail + delta_xof.
proof.
rewrite /sampled_first_attempt_score_distribution_bridge_certificate.
smt().
qed.

lemma sampled_first_attempt_score_distribution_certificate_to_reject_probability
    actual_tail ideal_tail delta_xof epsilon_singular :
  sampled_first_attempt_score_distribution_bridge_certificate
    actual_tail ideal_tail delta_xof =>
  ideal_tail <= epsilon_singular =>
  0%r <= epsilon_singular <= 1%r =>
  epsilon_singular + delta_xof <= 1%r =>
  sampled_first_attempt_reject_probability_certificate
    (epsilon_singular + delta_xof)
    actual_tail.
proof.
move=> hbridge hideal heps hepsum.
rewrite /sampled_first_attempt_reject_probability_certificate.
have htail :=
  sampled_first_attempt_score_distribution_bridge_certificateE
    actual_tail ideal_tail delta_xof hbridge.
smt().
qed.

lemma sampled_bounded_keygen_success_lower_bound_from_score_distribution_certificate
    fuel0 epsilon_singular delta_xof ideal_tail &m :
  0 <= fuel0 =>
  sampled_first_attempt_score_distribution_bridge_certificate
    (Pr[SampledFirst.main() @ &m :
         sampled_first_attempt_score_tail res])
    ideal_tail delta_xof =>
  ideal_tail <= epsilon_singular =>
  0%r <= epsilon_singular <= 1%r =>
  epsilon_singular + delta_xof <= 1%r =>
  Pr[SampledBounded.main(fuel0) @ &m :
       sampled_bounded_keygen_first_accept
         SampledBounded.raw_current fuel0 res] +
  Pr[SampledBounded.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_accept
         SampledBounded.raw_current fuel0 res] >=
  1%r -
  delta_bounded_keygen_progress fuel0 -
  epsilon_singular -
  delta_xof -
  Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze
    .finite_additive_defect_prefix
    delta_bounded_keygen_progress fuel0.
proof.
move=> hfuel hbridge hideal heps hepsum.
have hcert :
  sampled_first_attempt_reject_probability_certificate
    (epsilon_singular + delta_xof)
    (Pr[SampledFirst.main() @ &m :
         sampled_first_attempt_score_tail res]).
+ exact
    (sampled_first_attempt_score_distribution_certificate_to_reject_probability
      (Pr[SampledFirst.main() @ &m :
         sampled_first_attempt_score_tail res])
      ideal_tail delta_xof epsilon_singular hbridge hideal heps hepsum).
have hbound :=
  sampled_bounded_keygen_success_lower_bound_from_score_tail_certificate
    fuel0 (epsilon_singular + delta_xof) &m hfuel hcert.
smt().
qed.

end Mode2FaithfulSecuritySampledFirstAttemptScoreDistributionPostFreeze.
