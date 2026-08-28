require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32.
require import
  KeygenM23SingularFFTAccumulatorProbability
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23FirstAttemptAccumulator
  TargetKeygenM23FirstAttemptAccumulatorProbability
  TargetKeygenM23SingularFFTInputBounds
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
  Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptDSeedScoreTailPostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
  Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
  Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze.

import RealOrder.
import KeygenM23SingularFFTAccumulatorProbability.
import TargetKeygenM23FullFirstAttempt.
import TargetKeygenM23FirstAttemptAccumulator.
import TargetKeygenM23FirstAttemptAccumulatorProbability.
import Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze.

theory Mode2FaithfulSecuritySampledDSeedJointGapPostFreeze.

(* This file only lifts the existing sampled-dseed first-attempt program to the
   trace-local joint carrier used by the accumulator coupling layer.  The
   current HAETAE_ROM model still has no keygen eta-XOF query, so [delta_xof]
   remains an abstract assumption here.  Accordingly this file does not prove
   any SHAKE idealization, any equality with [HAETAE.kg], any numeric tail, any
   context/secret independence, or any point-mass/uniformity transfer through
   finalization. *)

module SampledDSeed =
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze
    .SampledDSeed.

lemma sampled_dseed_first_attempt_snapshot_correct :
  hoare [SampledDSeed.main : true ==>
    Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_first_attempt_snapshot_facts
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        SampledDSeed.raw_current res].
proof.
proc.
seq 2 :
  true.
+ auto.
wp.
exlim SampledDSeed.raw_current => raw0.
call
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_snapshot_correct
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw0).
auto => />.
qed.

op trace_local_joint_headroom_bad
    (trace : first_attempt_trace) : bool =
  mode2_accumulator_trace_headroom_bad
    (ideal_mode2_joint_to_accumulator (trace_local_joint_sample trace)).

lemma checked_first_attempt_snapshot_headroom_trace_local_jointE
    (raw0 : BArray32.t) (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw0 trace =>
  first_attempt_trace_accumulator_headroom_bad trace =
  trace_local_joint_headroom_bad trace.
proof.
move=> hsnapshot.
rewrite first_attempt_trace_accumulator_headroom_badE
        /trace_local_joint_headroom_bad.
rewrite
  (Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
    .checked_first_attempt_snapshot_accumulator_sample_eq_trace_local
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw0 trace hsnapshot).
rewrite
  /Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
    .trace_local_ideal_accumulator_sample
  /ideal_mode2_joint_to_accumulator
  /trace_local_joint_sample.
done.
qed.

lemma sampled_dseed_headroom_trace_local_joint_event_equiv :
  equiv [SampledDSeed.main ~ SampledDSeed.main :
    true ==>
    (first_attempt_trace_accumulator_headroom_bad res{1} =
     trace_local_joint_headroom_bad res{2})].
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
  (checked_first_attempt_snapshot_headroom_trace_local_jointE
    raw0 result hsnapshot).
qed.

lemma sampled_dseed_headroom_trace_local_joint_prE &m :
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res] =
  Pr[SampledDSeed.main() @ &m :
       trace_local_joint_headroom_bad res].
proof.
byequiv sampled_dseed_headroom_trace_local_joint_event_equiv.
+ done.
move=> &1 &2 /= heq.
move: heq.
smt().
qed.

lemma sampled_dseed_joint_gap_headroom_certificate
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    delta_xof &m :
  0%r <= delta_xof <= 1%r =>
  (forall (E : ideal_mode2_accumulator_joint_sample -> bool),
    Pr[SampledDSeed.main() @ &m :
         E (trace_local_joint_sample res)] <=
    mu djoint E + delta_xof) =>
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
    .sampled_dseed_accumulator_headroom_distribution_bridge_certificate
      (Pr[SampledDSeed.main() @ &m :
           first_attempt_trace_accumulator_headroom_bad res])
      (mu (ideal_mode2_accumulator_joint_distribution djoint)
           mode2_accumulator_trace_headroom_bad)
      delta_xof.
proof.
move=> hdelta hgap.
rewrite
  /Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
    .sampled_dseed_accumulator_headroom_distribution_bridge_certificate.
split; first exact hdelta.
split.
+ exact (mu_bounded _ mode2_accumulator_trace_headroom_bad).
have htrace :=
  hgap
    (fun joint =>
      mode2_accumulator_trace_headroom_bad
        (ideal_mode2_joint_to_accumulator joint)).
rewrite -sampled_dseed_headroom_trace_local_joint_prE in htrace.
rewrite /ideal_mode2_accumulator_joint_distribution dmapE /(\o).
exact htrace.
qed.

lemma sampled_dseed_joint_gap_headroom_certificate_with_contract
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    delta_xof &m :
  ideal_mode2_accumulator_joint_contract djoint =>
  0%r <= delta_xof <= 1%r =>
  (forall (E : ideal_mode2_accumulator_joint_sample -> bool),
    Pr[SampledDSeed.main() @ &m :
         E (trace_local_joint_sample res)] <=
    mu djoint E + delta_xof) =>
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
    .sampled_dseed_accumulator_headroom_distribution_bridge_certificate
      (Pr[SampledDSeed.main() @ &m :
           first_attempt_trace_accumulator_headroom_bad res])
      (mu (ideal_mode2_accumulator_joint_distribution djoint)
           mode2_accumulator_trace_headroom_bad)
      delta_xof /\
  is_lossless (ideal_mode2_accumulator_joint_distribution djoint) /\
  (forall sample,
    sample \in ideal_mode2_accumulator_joint_distribution djoint =>
    TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
      sample.`1 sample.`2).
proof.
move=> hcontract hdelta hgap.
split.
+ exact
    (sampled_dseed_joint_gap_headroom_certificate
      djoint delta_xof &m hdelta hgap).
split.
+ exact
    (ideal_mode2_accumulator_joint_distribution_lossless
      djoint hcontract).
move=> sample hsample.
exact (ideal_mode2_accumulator_joint_bound2 djoint sample hcontract hsample).
qed.

end Mode2FaithfulSecuritySampledDSeedJointGapPostFreeze.
