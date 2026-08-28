require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23SingularFFTAccumulatorProbability
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23SingularFFTInputBounds
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze.

import RealOrder.
import KeygenM23SingularFFTAccumulatorProbability.
import TargetKeygenM23FullFirstAttempt.

theory Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze.

(* This layer uses a single joint carrier for a per-sample finalize context and
   a pre-final secret pair.  It intentionally does not assume context/secret
   independence, does not idealize deterministic SHAKE behavior, does not
   assert any program-level [Pr] equality, does not provide numeric tails, and
   does not transfer post-final point-mass or uniformity claims through the
   finalizer pushforward. *)

type ideal_eta_packed_secret_pair =
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_eta_packed_secret_pair.

type ideal_mode2_finalize_context = BArray8192.t * BArray8192.t.
type ideal_mode2_accumulator_joint_sample =
  ideal_mode2_finalize_context * ideal_eta_packed_secret_pair.

op ideal_mode2_context_pre_bp
    (ctx : ideal_mode2_finalize_context) : BArray8192.t = ctx.`1.

op ideal_mode2_context_avec
    (ctx : ideal_mode2_finalize_context) : BArray8192.t = ctx.`2.

op ideal_mode2_joint_context
    (joint : ideal_mode2_accumulator_joint_sample) :
    ideal_mode2_finalize_context = joint.`1.

op ideal_mode2_joint_secret_pair
    (joint : ideal_mode2_accumulator_joint_sample) :
    ideal_eta_packed_secret_pair = joint.`2.

op ideal_mode2_joint_context_valid
    (joint : ideal_mode2_accumulator_joint_sample) : bool =
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid
      (ideal_mode2_context_pre_bp (ideal_mode2_joint_context joint))
      (ideal_mode2_context_avec (ideal_mode2_joint_context joint)).

op ideal_mode2_joint_to_accumulator
    (joint : ideal_mode2_accumulator_joint_sample) :
    mode2_accumulator_sample =
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_sample
      (ideal_mode2_context_pre_bp (ideal_mode2_joint_context joint))
      (ideal_mode2_context_avec (ideal_mode2_joint_context joint))
      (ideal_mode2_joint_secret_pair joint).

op ideal_mode2_joint_secret_marginal
    (djoint : ideal_mode2_accumulator_joint_sample distr) :
    ideal_eta_packed_secret_pair distr =
  dmap djoint ideal_mode2_joint_secret_pair.

op ideal_mode2_accumulator_joint_distribution
    (djoint : ideal_mode2_accumulator_joint_sample distr) :
    mode2_accumulator_sample distr =
  dmap djoint ideal_mode2_joint_to_accumulator.

op ideal_mode2_accumulator_joint_distribution_valid
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    (sample : mode2_accumulator_sample) : bool =
  exists joint,
    joint \in djoint /\
    sample = ideal_mode2_joint_to_accumulator joint.

op ideal_mode2_accumulator_joint_contract
    (djoint : ideal_mode2_accumulator_joint_sample distr) : bool =
  is_lossless djoint /\
  (forall joint, joint \in djoint => ideal_mode2_joint_context_valid joint) /\
  ideal_mode2_joint_secret_marginal djoint =
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_packed_secret_pair_distribution.

lemma ideal_mode2_accumulator_joint_distribution_support
    djoint sample :
  sample \in ideal_mode2_accumulator_joint_distribution djoint <=>
  ideal_mode2_accumulator_joint_distribution_valid djoint sample.
proof.
rewrite
  /ideal_mode2_accumulator_joint_distribution
  /ideal_mode2_accumulator_joint_distribution_valid
  supp_dmap.
trivial.
qed.

lemma ideal_mode2_accumulator_joint_distribution_lossless djoint :
  ideal_mode2_accumulator_joint_contract djoint =>
  is_lossless (ideal_mode2_accumulator_joint_distribution djoint).
proof.
move=> [hll [_ _]].
rewrite /ideal_mode2_accumulator_joint_distribution.
by apply dmap_ll.
qed.

lemma ideal_mode2_joint_secret_pair_in_ideal_support
    djoint joint :
  ideal_mode2_accumulator_joint_contract djoint =>
  joint \in djoint =>
  ideal_mode2_joint_secret_pair joint \in
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_packed_secret_pair_distribution.
proof.
move=> [_ [_ hmarg]] hjoint.
have hproj :
    ideal_mode2_joint_secret_pair joint \in
      ideal_mode2_joint_secret_marginal djoint.
+ rewrite /ideal_mode2_joint_secret_marginal supp_dmap.
   by exists joint.
by rewrite hmarg in hproj.
qed.

lemma ideal_mode2_accumulator_joint_bound2
    djoint sample :
  ideal_mode2_accumulator_joint_contract djoint =>
  sample \in ideal_mode2_accumulator_joint_distribution djoint =>
  TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
    sample.`1 sample.`2.
proof.
move=> [hll [hctx hmarg]].
rewrite ideal_mode2_accumulator_joint_distribution_support.
move=> [joint [hjoint ->]].
have hcontract : ideal_mode2_accumulator_joint_contract djoint by
  split; [exact hll | split; [exact hctx | exact hmarg]].
case: joint hjoint => [[pre_bp avec] pair] /= hjoint.
have hpair :=
  ideal_mode2_joint_secret_pair_in_ideal_support
    djoint ((pre_bp, avec), pair) hcontract hjoint.
have hcontext := hctx ((pre_bp, avec), pair) hjoint.
have hreach :=
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_reachable_inputs_of_context
      pre_bp avec pair hcontext hpair.
exact
  (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_sample_bound2
      pre_bp avec pair hpair hreach).
qed.

op trace_local_joint_sample
    (trace : first_attempt_trace) :
    ideal_mode2_accumulator_joint_sample =
  ((Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
      .trace_local_pre_bp trace,
    Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
      .trace_local_avec trace),
   Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
     .trace_local_pre_final_pair trace).

op trace_local_joint_distribution
    (dtrace : first_attempt_trace distr) :
    ideal_mode2_accumulator_joint_sample distr =
  dmap dtrace trace_local_joint_sample.

lemma trace_local_ideal_accumulator_distribution_factor
    (dtrace : first_attempt_trace distr) :
  Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
    .trace_local_ideal_accumulator_distribution dtrace =
  ideal_mode2_accumulator_joint_distribution
    (trace_local_joint_distribution dtrace).
proof.
rewrite
  /Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
    .trace_local_ideal_accumulator_distribution
  /ideal_mode2_accumulator_joint_distribution
  /trace_local_joint_distribution.
have hfun :
  Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
    .trace_local_ideal_accumulator_sample =
  (ideal_mode2_joint_to_accumulator \o trace_local_joint_sample).
+ apply fun_ext => trace.
   rewrite /(\o) /trace_local_joint_sample
           /ideal_mode2_joint_to_accumulator.
   trivial.
rewrite hfun -dmap_comp.
trivial.
qed.

op ideal_mode2_accumulator_joint_event_gap
    (dactual dideal : ideal_mode2_accumulator_joint_sample distr)
    (delta_xof : real) : bool =
  0%r <= delta_xof <= 1%r /\
  forall (E : ideal_mode2_accumulator_joint_sample -> bool),
    mu dactual E <= mu dideal E + delta_xof.

lemma ideal_mode2_accumulator_joint_event_gap_data_processing
    (dactual dideal : ideal_mode2_accumulator_joint_sample distr)
    delta_xof :
  ideal_mode2_accumulator_joint_event_gap
    dactual dideal delta_xof =>
  forall (E : mode2_accumulator_sample -> bool),
    mu (ideal_mode2_accumulator_joint_distribution dactual) E <=
    mu (ideal_mode2_accumulator_joint_distribution dideal) E + delta_xof.
proof.
move=> [_ hgap] E.
have :=
  hgap (E \o ideal_mode2_joint_to_accumulator).
rewrite /ideal_mode2_accumulator_joint_distribution !dmapE /(\o).
trivial.
qed.

lemma ideal_mode2_accumulator_joint_event_gap_headroom_certificate
    (dactual dideal : ideal_mode2_accumulator_joint_sample distr)
    delta_xof :
  ideal_mode2_accumulator_joint_event_gap
    dactual dideal delta_xof =>
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
    .sampled_dseed_accumulator_headroom_distribution_bridge_certificate
      (mu (ideal_mode2_accumulator_joint_distribution dactual)
          mode2_accumulator_trace_headroom_bad)
      (mu (ideal_mode2_accumulator_joint_distribution dideal)
          mode2_accumulator_trace_headroom_bad)
      delta_xof.
proof.
move=> [hdelta hgap].
have hgapfull : ideal_mode2_accumulator_joint_event_gap
    dactual dideal delta_xof by
  split; [exact hdelta | exact hgap].
rewrite
  /Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
    .sampled_dseed_accumulator_headroom_distribution_bridge_certificate.
split; first exact hdelta.
split.
+ exact (mu_bounded _ mode2_accumulator_trace_headroom_bad).
exact
  (ideal_mode2_accumulator_joint_event_gap_data_processing
    dactual dideal delta_xof
    hgapfull
    mode2_accumulator_trace_headroom_bad).
qed.

lemma trace_local_vs_ideal_joint_event_gap_headroom_certificate
    (dtrace : first_attempt_trace distr)
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    delta_xof :
  ideal_mode2_accumulator_joint_contract djoint =>
  ideal_mode2_accumulator_joint_event_gap
    (trace_local_joint_distribution dtrace)
    djoint
    delta_xof =>
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
    .sampled_dseed_accumulator_headroom_distribution_bridge_certificate
      (mu
        (Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
          .trace_local_ideal_accumulator_distribution dtrace)
        mode2_accumulator_trace_headroom_bad)
      (mu
        (ideal_mode2_accumulator_joint_distribution djoint)
        mode2_accumulator_trace_headroom_bad)
      delta_xof.
proof.
move=> _ hgap.
rewrite
  (trace_local_ideal_accumulator_distribution_factor dtrace).
exact
  (ideal_mode2_accumulator_joint_event_gap_headroom_certificate
    (trace_local_joint_distribution dtrace)
    djoint
    delta_xof hgap).
qed.

end Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze.
