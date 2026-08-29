require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32 BArray8192 BArray32768.
require import
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorProbability
  KeygenM23SingularFFTSpec
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23FirstAttemptAccumulatorProbability
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
  Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze
  Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze.

import RealOrder.
import KeygenM23SingularFFTAccumulatorBridge.
import KeygenM23SingularFFTAccumulatorProbability.
import TargetKeygenM23FullFirstAttempt.
import TargetKeygenM23FirstAttemptAccumulatorProbability.
import Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.
import Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.
import Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze.

theory Mode2FaithfulSecurityActualAccumulatorUpperPrefixTransportPostFreeze.

(* This file exposes the exact remaining transport boundary between an actual
   trace-local SHAKE execution and the fixed-context iid-eta accumulator law.
   It does not assert that boundary for free: callers must supply one joint
   all-event gap.  In particular, the repository's raw-seed-zero accepted
   trace comes from attempt index 2, not the first attempt, so this theory does
   not instantiate that artifact as a first-attempt program theorem. *)

op ideal_mode2_fixed_context_joint_distribution
    (pre_bp avec : BArray8192.t) :
    ideal_mode2_accumulator_joint_sample distr =
  dmap
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_packed_secret_pair_distribution
    (fun pair => ((pre_bp, avec), pair)).

lemma ideal_mode2_fixed_context_joint_distribution_lossless
    pre_bp avec :
  is_lossless (ideal_mode2_fixed_context_joint_distribution pre_bp avec).
proof.
rewrite /ideal_mode2_fixed_context_joint_distribution.
apply dmap_ll.
exact
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_packed_secret_pair_lossless.
qed.

lemma ideal_mode2_fixed_context_joint_contract pre_bp avec :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  ideal_mode2_accumulator_joint_contract
    (ideal_mode2_fixed_context_joint_distribution pre_bp avec).
proof.
move=> hctx.
rewrite /ideal_mode2_accumulator_joint_contract.
split.
+ exact (ideal_mode2_fixed_context_joint_distribution_lossless pre_bp avec).
split.
+ move=> joint hjoint.
  rewrite /ideal_mode2_fixed_context_joint_distribution supp_dmap in hjoint.
  move: hjoint => [pair [hpair ->]].
  rewrite /ideal_mode2_joint_context_valid
          /ideal_mode2_joint_context
          /ideal_mode2_context_pre_bp
          /ideal_mode2_context_avec /=.
  exact hctx.
rewrite /ideal_mode2_joint_secret_marginal
        /ideal_mode2_fixed_context_joint_distribution dmap_comp.
have -> :
    (ideal_mode2_joint_secret_pair \o
      (fun pair => ((pre_bp, avec), pair))) = idfun.
+ apply fun_ext => pair.
  rewrite /(\o) /ideal_mode2_joint_secret_pair /=.
  trivial.
rewrite dmap_id.
trivial.
qed.

lemma ideal_mode2_fixed_context_joint_accumulatorE pre_bp avec :
  ideal_mode2_accumulator_joint_distribution
    (ideal_mode2_fixed_context_joint_distribution pre_bp avec) =
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_distribution pre_bp avec.
proof.
rewrite /ideal_mode2_accumulator_joint_distribution
        /ideal_mode2_fixed_context_joint_distribution dmap_comp.
rewrite
  /Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_distribution.
congr.
apply fun_ext => pair.
rewrite /(\o)
        /ideal_mode2_joint_to_accumulator
        /ideal_mode2_joint_context
        /ideal_mode2_joint_secret_pair
        /ideal_mode2_context_pre_bp
        /ideal_mode2_context_avec /=.
trivial.
qed.

lemma checked_snapshot_accumulator_unsafe_mu_lt_one_half_plus_gap
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (dtrace : first_attempt_trace distr)
    (pre_bp avec : BArray8192.t)
    delta_xof :
  (forall trace,
    trace \in dtrace =>
    checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace) =>
  ideal_mode2_accumulator_joint_event_gap
    (trace_local_joint_distribution dtrace)
    (ideal_mode2_fixed_context_joint_distribution pre_bp avec)
    delta_xof =>
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (first_attempt_trace_accumulator_sample_distribution dtrace)
    (fun (sample : mode2_accumulator_sample) =>
      ! actual_mode2_accumulate_safe_trace
          sample.`1 sample.`2
          KeygenM23SingularFFTSpec.mode2_slice_count_i) <
  1%r / 2%r + delta_xof.
proof.
move=> hsnapshot hgap hnumeric hctx htrace.
have hactual :=
  Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
    .checked_first_attempt_snapshot_accumulator_distribution_eq_trace_local
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 dtrace hsnapshot.
have hfactor :=
  trace_local_ideal_accumulator_distribution_factor dtrace.
have hgap_acc :=
  ideal_mode2_accumulator_joint_event_gap_data_processing
    (trace_local_joint_distribution dtrace)
    (ideal_mode2_fixed_context_joint_distribution pre_bp avec)
    delta_xof hgap
    (fun (sample : mode2_accumulator_sample) =>
      ! actual_mode2_accumulate_safe_trace
          sample.`1 sample.`2
          KeygenM23SingularFFTSpec.mode2_slice_count_i).
rewrite -hfactor -hactual
        ideal_mode2_fixed_context_joint_accumulatorE in hgap_acc.
have hideal := ideal_mode2_accumulator_unsafe_mu_lt_one_half_closed
  pre_bp avec hnumeric hctx htrace.
smt().
qed.

end Mode2FaithfulSecurityActualAccumulatorUpperPrefixTransportPostFreeze.
