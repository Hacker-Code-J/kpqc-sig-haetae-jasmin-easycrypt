require import AllCore Distr List Real StdOrder.

from Jasmin require import JModel_x86.

require import
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
  Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze
  Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze.

import RealOrder.
import Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze.
import Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze.

theory Mode2FaithfulSecuritySampledFirstAttemptAcceptedClassTraceP8PostFreeze.

(* This layer only packages accepted-and-trace events for the sampled
   first-attempt program and the existing joint carrier.  Callers must still
   supply the ideal mass certificate and the one-shot actual-to-ideal gap; no
   fixed trace, independence, conditioning, or numeric P8 estimate is added
   here. *)

module SampledDSeed = Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze.SampledDSeed.

module SampledDSeedFirstAttemptClassTrace =
  Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze
    .SampledDSeedFirstAttemptClassTrace.

op accepted_class_trace_p8_bad
    (p8_bad : int list list -> bool)
    (observation : first_attempt_class_trace_observation) : bool =
  observation.`1 /\ p8_bad observation.`3.

op ideal_mode2_joint_accepted_class_trace_p8_bad
    (p8_bad : int list list -> bool)
    (joint : ideal_mode2_accumulator_joint_sample) : bool =
  accepted_class_trace_p8_bad p8_bad
    (ideal_mode2_joint_class_trace_observation joint).

op ideal_mode2_joint_accepted_class_trace_p8_mass
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    (p8_bad : int list list -> bool) : real =
  mu (ideal_mode2_joint_class_trace_distribution djoint)
     (accepted_class_trace_p8_bad p8_bad).

op ideal_mode2_joint_accepted_class_trace_p8_probability_certificate
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    (p8_bad : int list list -> bool)
    (epsilon_p8 : real) : bool =
  0%r <= epsilon_p8 <= 1%r /\
  ideal_mode2_joint_accepted_class_trace_p8_mass djoint p8_bad <= epsilon_p8.

lemma ideal_mode2_joint_accepted_class_trace_p8_massE
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    (p8_bad : int list list -> bool) :
  ideal_mode2_joint_accepted_class_trace_p8_mass djoint p8_bad =
  mu djoint (ideal_mode2_joint_accepted_class_trace_p8_bad p8_bad).
proof.
rewrite /ideal_mode2_joint_accepted_class_trace_p8_mass
        /ideal_mode2_joint_accepted_class_trace_p8_bad
        /ideal_mode2_joint_class_trace_distribution.
by rewrite dmapE /(\o).
qed.

lemma ideal_mode2_joint_accepted_class_trace_p8_probability_certificateE
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    (p8_bad : int list list -> bool)
    epsilon_p8 :
  ideal_mode2_joint_accepted_class_trace_p8_probability_certificate
    djoint p8_bad epsilon_p8 =>
  ideal_mode2_joint_accepted_class_trace_p8_mass djoint p8_bad <= epsilon_p8.
proof.
rewrite
  /ideal_mode2_joint_accepted_class_trace_p8_probability_certificate.
smt().
qed.

lemma checked_first_attempt_snapshot_accepted_class_trace_p8_badE
    raw0 trace (p8_bad : int list list -> bool) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw0 trace =>
  accepted_class_trace_p8_bad p8_bad
    (first_attempt_class_trace_observation trace) =
  ideal_mode2_joint_accepted_class_trace_p8_bad p8_bad
    (trace_local_joint_sample trace).
proof.
move=> hsnapshot.
have hobs :=
  checked_first_attempt_snapshot_joint_observationE
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    raw0 trace hsnapshot.
rewrite /ideal_mode2_joint_accepted_class_trace_p8_bad.
rewrite /first_attempt_joint_class_trace_observation in hobs.
rewrite -hobs.
done.
qed.

lemma sampled_dseed_first_attempt_accepted_class_trace_p8_joint_equiv
    (p8_bad : int list list -> bool) :
  equiv [SampledDSeed.main ~ SampledDSeed.main :
    true ==>
    (accepted_class_trace_p8_bad p8_bad
       (first_attempt_class_trace_observation res{1}) =
     ideal_mode2_joint_accepted_class_trace_p8_bad p8_bad
       (trace_local_joint_sample res{2}))].
proof.
proc.
seq 2 2 :
  (SampledDSeed.raw_current{1} = SampledDSeed.raw_current{2}).
+ wp.
   rnd.
   auto.
exlim SampledDSeed.raw_current{2} => raw0.
call
  (Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze
    .checked_mode2_first_attempt_decision_self_snapshot raw0).
auto => />.
move=> result hsnapshot.
exact
  (checked_first_attempt_snapshot_accepted_class_trace_p8_badE
    raw0 result p8_bad hsnapshot).
qed.

lemma sampled_dseed_first_attempt_accepted_class_trace_p8_joint_massE
    (p8_bad : int list list -> bool) &m :
  Pr[SampledDSeed.main() @ &m :
       accepted_class_trace_p8_bad p8_bad
         (first_attempt_class_trace_observation res)] =
  Pr[SampledDSeed.main() @ &m :
       ideal_mode2_joint_accepted_class_trace_p8_bad p8_bad
         (trace_local_joint_sample res)].
proof.
byequiv
  (sampled_dseed_first_attempt_accepted_class_trace_p8_joint_equiv p8_bad).
+ done.
move=> &1 &2 /= heq.
move: heq.
smt().
qed.

lemma sampled_dseed_first_attempt_accepted_class_trace_p8_joint_prE
    (p8_bad : int list list -> bool) &m :
  Pr[SampledDSeedFirstAttemptClassTrace.main() @ &m :
       accepted_class_trace_p8_bad p8_bad res] =
  Pr[SampledDSeed.main() @ &m :
       ideal_mode2_joint_accepted_class_trace_p8_bad p8_bad
         (trace_local_joint_sample res)].
proof.
rewrite
  (sampled_dseed_first_attempt_class_trace_prE
    (accepted_class_trace_p8_bad p8_bad) &m).
exact
  (sampled_dseed_first_attempt_accepted_class_trace_p8_joint_massE
    p8_bad &m).
qed.

lemma sampled_dseed_first_attempt_accepted_class_trace_p8_pr_le_certificate
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    (p8_bad : int list list -> bool)
    delta_xof epsilon_p8 &m :
  0%r <= delta_xof <= 1%r =>
  ideal_mode2_joint_accepted_class_trace_p8_probability_certificate
    djoint p8_bad epsilon_p8 =>
  (forall (E : ideal_mode2_accumulator_joint_sample -> bool),
    Pr[SampledDSeed.main() @ &m :
         E (trace_local_joint_sample res)] <=
    mu djoint E + delta_xof) =>
  Pr[SampledDSeedFirstAttemptClassTrace.main() @ &m :
       accepted_class_trace_p8_bad p8_bad res] <=
  epsilon_p8 + delta_xof.
proof.
move=> hdelta hcert hgap.
have hactual :=
  hgap (ideal_mode2_joint_accepted_class_trace_p8_bad p8_bad).
rewrite -sampled_dseed_first_attempt_accepted_class_trace_p8_joint_prE
        -ideal_mode2_joint_accepted_class_trace_p8_massE in hactual.
have hideal :=
  ideal_mode2_joint_accepted_class_trace_p8_probability_certificateE
    djoint p8_bad epsilon_p8 hcert.
smt().
qed.

end Mode2FaithfulSecuritySampledFirstAttemptAcceptedClassTraceP8PostFreeze.
