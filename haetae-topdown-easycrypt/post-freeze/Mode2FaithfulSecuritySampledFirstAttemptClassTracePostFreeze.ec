require import AllCore Distr List Real StdOrder.

from Jasmin require import JModel_x86.

require import
  KeygenMode2ParentTarget
  KeygenM23SingularFFTSpec
  TargetKeygenM23FullFirstAttempt
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze
  Mode2FaithfulSecuritySampledDSeedJointGapPostFreeze
  Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.

import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.

theory Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze.

(* This file exposes the joint observed carrier needed by a future
   distribution-weighted accepted-context analysis.  The ordered class trace
   is retained in full.  No fixed seed, class histogram reduction,
   context/secret independence, conditional law, XOF idealization, numeric
   P8 bound, or unbounded retry claim is introduced here. *)

module SampledDSeed =
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze
    .SampledDSeed.

op mode2_class_trace_rows : int = 2.
op mode2_class_trace_words : int = 256.

op first_attempt_row_class_trace
    (trace : first_attempt_trace) (row : int) : int list =
  mkseq
    (fun j =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
        .ideal_final_s2_row_class_trace
          (Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
            .trace_local_pre_bp trace)
          (Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
            .trace_local_avec trace)
          row j)
    mode2_class_trace_words.

op first_attempt_ordered_class_trace
    (trace : first_attempt_trace) : int list list =
  mkseq (first_attempt_row_class_trace trace) mode2_class_trace_rows.

type first_attempt_class_trace_observation =
  bool * W64.t * int list list.

type ideal_mode2_accumulator_joint_sample =
  Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
    .ideal_mode2_accumulator_joint_sample.

op ideal_mode2_joint_score
    (joint : ideal_mode2_accumulator_joint_sample) : W64.t =
  KeygenM23SingularFFTSpec.mode2_singular_word
    (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
      .ideal_mode2_joint_secret_pair joint).`1
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_s2
        (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
          .ideal_mode2_context_pre_bp
            (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
              .ideal_mode2_joint_context joint))
        (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
          .ideal_mode2_joint_secret_pair joint).`2
        (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
          .ideal_mode2_context_avec
            (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
              .ideal_mode2_joint_context joint)))
    KeygenMode2ParentTarget.jfft_roots
    KeygenMode2ParentTarget.jfft_brv8.

op ideal_mode2_joint_row_class_trace
    (joint : ideal_mode2_accumulator_joint_sample)
    (row : int) : int list =
  mkseq
    (fun j =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
        .ideal_final_s2_row_class_trace
          (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
            .ideal_mode2_context_pre_bp
              (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
                .ideal_mode2_joint_context joint))
          (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
            .ideal_mode2_context_avec
              (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
                .ideal_mode2_joint_context joint))
          row j)
    mode2_class_trace_words.

op ideal_mode2_joint_ordered_class_trace
    (joint : ideal_mode2_accumulator_joint_sample) : int list list =
  mkseq (ideal_mode2_joint_row_class_trace joint) mode2_class_trace_rows.

op ideal_mode2_joint_class_trace_observation
    (joint : ideal_mode2_accumulator_joint_sample) :
    first_attempt_class_trace_observation =
  (W64.to_uint (ideal_mode2_joint_score joint) <= 611098,
   ideal_mode2_joint_score joint,
   ideal_mode2_joint_ordered_class_trace joint).

op first_attempt_class_trace_observation
    (trace : first_attempt_trace) : first_attempt_class_trace_observation =
  (first_attempt_trace_accepted trace,
   first_attempt_trace_score trace,
   first_attempt_ordered_class_trace trace).

op first_attempt_joint_class_trace_observation
    (trace : first_attempt_trace) : first_attempt_class_trace_observation =
  ideal_mode2_joint_class_trace_observation
    (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
      .trace_local_joint_sample trace).

op ordered_class_trace_wf (rows : int list list) : bool =
  size rows = mode2_class_trace_rows /\
  forall row,
    0 <= row < mode2_class_trace_rows =>
    size (nth [] rows row) = mode2_class_trace_words /\
    forall j,
      0 <= j < mode2_class_trace_words =>
      0 <= nth 0 (nth [] rows row) j <= 5.

op first_attempt_class_trace_joint_distribution
    (dtrace : first_attempt_trace distr) :
    first_attempt_class_trace_observation distr =
  dmap dtrace first_attempt_class_trace_observation.

op first_attempt_joint_class_trace_distribution
    (dtrace : first_attempt_trace distr) :
    first_attempt_class_trace_observation distr =
  dmap dtrace first_attempt_joint_class_trace_observation.

op ideal_mode2_joint_class_trace_distribution
    (djoint : ideal_mode2_accumulator_joint_sample distr) :
    first_attempt_class_trace_observation distr =
  dmap djoint ideal_mode2_joint_class_trace_observation.

lemma first_attempt_row_class_trace_size trace row :
  size (first_attempt_row_class_trace trace row) =
    mode2_class_trace_words.
proof.
by rewrite /first_attempt_row_class_trace size_mkseq.
qed.

lemma ideal_mode2_joint_row_class_trace_size joint row :
  size (ideal_mode2_joint_row_class_trace joint row) =
    mode2_class_trace_words.
proof.
by rewrite /ideal_mode2_joint_row_class_trace size_mkseq.
qed.

lemma ideal_mode2_joint_row_class_trace_nth_range joint row j :
  0 <= j < mode2_class_trace_words =>
  0 <= nth 0 (ideal_mode2_joint_row_class_trace joint row) j <= 5.
proof.
move=> hj.
rewrite /ideal_mode2_joint_row_class_trace nth_mkseq 1:hj.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
    .ideal_final_s2_row_class_trace_range
      (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
        .ideal_mode2_context_pre_bp
          (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
            .ideal_mode2_joint_context joint))
      (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
        .ideal_mode2_context_avec
          (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
            .ideal_mode2_joint_context joint))
      row j).
qed.

lemma ideal_mode2_joint_ordered_class_trace_wf joint :
  ordered_class_trace_wf
    (ideal_mode2_joint_ordered_class_trace joint).
proof.
rewrite /ordered_class_trace_wf /ideal_mode2_joint_ordered_class_trace.
rewrite size_mkseq.
split; first trivial.
move=> row hrow.
rewrite nth_mkseq 1:hrow ideal_mode2_joint_row_class_trace_size.
split; first trivial.
move=> j hj.
exact (ideal_mode2_joint_row_class_trace_nth_range joint row j hj).
qed.

lemma ideal_mode2_joint_class_trace_observation_wf joint :
  ordered_class_trace_wf
    (ideal_mode2_joint_class_trace_observation joint).`3.
proof.
rewrite /ideal_mode2_joint_class_trace_observation /=.
exact (ideal_mode2_joint_ordered_class_trace_wf joint).
qed.

lemma first_attempt_row_class_trace_nth_range trace row j :
  0 <= j < mode2_class_trace_words =>
  0 <= nth 0 (first_attempt_row_class_trace trace row) j <= 5.
proof.
move=> hj.
rewrite /first_attempt_row_class_trace nth_mkseq 1:hj.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
    .ideal_final_s2_row_class_trace_range
      (Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
        .trace_local_pre_bp trace)
      (Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
        .trace_local_avec trace)
      row j).
qed.

lemma first_attempt_ordered_class_trace_wf trace :
  ordered_class_trace_wf (first_attempt_ordered_class_trace trace).
proof.
rewrite /ordered_class_trace_wf /first_attempt_ordered_class_trace.
rewrite size_mkseq.
split; first trivial.
move=> row hrow.
rewrite nth_mkseq 1:hrow first_attempt_row_class_trace_size.
split; first trivial.
move=> j hj.
exact (first_attempt_row_class_trace_nth_range trace row j hj).
qed.

lemma first_attempt_class_trace_observation_wf trace :
  ordered_class_trace_wf
    (first_attempt_class_trace_observation trace).`3.
proof.
rewrite /first_attempt_class_trace_observation /=.
exact (first_attempt_ordered_class_trace_wf trace).
qed.

lemma first_attempt_class_trace_observation_guard
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
  ((first_attempt_class_trace_observation trace).`1 <=>
   W64.to_uint (first_attempt_class_trace_observation trace).`2 <= 611098).
proof.
move=> hsnapshot.
rewrite /first_attempt_class_trace_observation /=.
exact
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_accepted_iff_score_le
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw0 trace hsnapshot).
qed.

lemma first_attempt_joint_row_class_traceE trace row :
  ideal_mode2_joint_row_class_trace
    (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
      .trace_local_joint_sample trace) row =
  first_attempt_row_class_trace trace row.
proof.
rewrite /ideal_mode2_joint_row_class_trace
        /first_attempt_row_class_trace
        /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
          .trace_local_joint_sample
        /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
          .ideal_mode2_joint_context
        /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
          .ideal_mode2_context_pre_bp
        /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
          .ideal_mode2_context_avec.
trivial.
qed.

lemma first_attempt_joint_ordered_class_traceE trace :
  ideal_mode2_joint_ordered_class_trace
    (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
      .trace_local_joint_sample trace) =
  first_attempt_ordered_class_trace trace.
proof.
rewrite /ideal_mode2_joint_ordered_class_trace
        /first_attempt_ordered_class_trace.
apply eq_in_mkseq => row hrow.
exact (first_attempt_joint_row_class_traceE trace row).
qed.

lemma checked_first_attempt_snapshot_joint_scoreE
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw0 : BArray32.t) (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw0 trace =>
  ideal_mode2_joint_score
    (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
      .trace_local_joint_sample trace) =
  first_attempt_trace_score trace.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite
  /checked_first_attempt_snapshot_facts
  /ideal_mode2_joint_score
  /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
    .trace_local_joint_sample
  /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
    .ideal_mode2_joint_context
  /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
    .ideal_mode2_joint_secret_pair
  /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
    .ideal_mode2_context_pre_bp
  /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
    .ideal_mode2_context_avec
  /first_attempt_trace_score /=.
move=> [hsampler [hm23 [hfinal [harray [hhaetae
  [hscore [hcounter [hbound [hreject haccept]]]]]]]]].
have [_ hs2] :=
  Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze
    .finalize_output_eq_pure_final
      pre_bp sampled_s2 avec final_bp final_s2 hfinal.
by rewrite hscore hs2.
qed.

lemma checked_first_attempt_snapshot_joint_observationE
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw0 : BArray32.t) (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw0 trace =>
  first_attempt_joint_class_trace_observation trace =
  first_attempt_class_trace_observation trace.
proof.
move=> hsnapshot.
have hscore :=
  checked_first_attempt_snapshot_joint_scoreE
    mat0 avec0 s10 s20 bp0 s1hat0 raw0 trace hsnapshot.
have hguard :=
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_accepted_iff_score_le
      mat0 avec0 s10 s20 bp0 s1hat0 raw0 trace hsnapshot.
have htrace := first_attempt_joint_ordered_class_traceE trace.
rewrite /first_attempt_joint_class_trace_observation
        /ideal_mode2_joint_class_trace_observation
        /first_attempt_class_trace_observation hscore htrace /=.
smt().
qed.

lemma first_attempt_class_trace_joint_distribution_lossless dtrace :
  is_lossless dtrace =>
  is_lossless (first_attempt_class_trace_joint_distribution dtrace).
proof.
rewrite /first_attempt_class_trace_joint_distribution.
apply dmap_ll.
qed.

lemma first_attempt_joint_class_trace_distribution_factor dtrace :
  first_attempt_joint_class_trace_distribution dtrace =
  ideal_mode2_joint_class_trace_distribution
    (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
      .trace_local_joint_distribution dtrace).
proof.
rewrite /first_attempt_joint_class_trace_distribution
        /ideal_mode2_joint_class_trace_distribution
        /Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
          .trace_local_joint_distribution.
have hfun :
  first_attempt_joint_class_trace_observation =
  (ideal_mode2_joint_class_trace_observation \o
   Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
     .trace_local_joint_sample).
+ apply fun_ext => trace.
  rewrite /first_attempt_joint_class_trace_observation /(\o).
  trivial.
rewrite hfun -dmap_comp.
trivial.
qed.

lemma checked_first_attempt_class_trace_joint_distribution_factor
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (dtrace : first_attempt_trace distr) :
  (forall trace,
    trace \in dtrace =>
    exists raw0,
      Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
        .checked_first_attempt_snapshot_facts
          mat0 avec0 s10 s20 bp0 s1hat0 raw0 trace) =>
  first_attempt_class_trace_joint_distribution dtrace =
  ideal_mode2_joint_class_trace_distribution
    (Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
      .trace_local_joint_distribution dtrace).
proof.
move=> hsnapshot.
rewrite -first_attempt_joint_class_trace_distribution_factor.
rewrite /first_attempt_class_trace_joint_distribution
        /first_attempt_joint_class_trace_distribution.
apply eq_dmap_in => trace htrace.
move: (hsnapshot trace htrace) => [raw0 hsnapshot_trace].
apply eq_sym.
exact
  (checked_first_attempt_snapshot_joint_observationE
    mat0 avec0 s10 s20 bp0 s1hat0 raw0 trace hsnapshot_trace).
qed.

lemma ideal_mode2_joint_event_gap_class_trace_data_processing
    (dactual dideal : ideal_mode2_accumulator_joint_sample distr)
    delta_xof :
  Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
    .ideal_mode2_accumulator_joint_event_gap
      dactual dideal delta_xof =>
  forall (E : first_attempt_class_trace_observation -> bool),
    mu (ideal_mode2_joint_class_trace_distribution dactual) E <=
    mu (ideal_mode2_joint_class_trace_distribution dideal) E + delta_xof.
proof.
move=> [_ hgap] E.
have := hgap (E \o ideal_mode2_joint_class_trace_observation).
rewrite /ideal_mode2_joint_class_trace_distribution !dmapE /(\o).
trivial.
qed.

lemma first_attempt_class_trace_joint_distribution_muE dtrace P :
  mu (first_attempt_class_trace_joint_distribution dtrace) P =
  mu dtrace (fun trace => P (first_attempt_class_trace_observation trace)).
proof.
by rewrite /first_attempt_class_trace_joint_distribution dmapE /(\o).
qed.

lemma first_attempt_class_trace_joint_distribution_support_wf
    dtrace observation :
  observation \in first_attempt_class_trace_joint_distribution dtrace =>
  ordered_class_trace_wf observation.`3.
proof.
rewrite /first_attempt_class_trace_joint_distribution supp_dmap.
move=> [trace [htrace ->]].
exact (first_attempt_class_trace_observation_wf trace).
qed.

module SampledDSeedFirstAttemptClassTrace = {
  proc main() : first_attempt_class_trace_observation = {
    var trace : first_attempt_trace;

    trace <@ SampledDSeed.main();
    return first_attempt_class_trace_observation trace;
  }
}.

lemma sampled_dseed_first_attempt_class_trace_equiv :
  equiv [SampledDSeedFirstAttemptClassTrace.main ~ SampledDSeed.main :
    true ==>
    res{1} = first_attempt_class_trace_observation res{2}].
proof.
proc.
inline SampledDSeed.main.
sim.
qed.

lemma sampled_dseed_first_attempt_class_trace_prE
    (P : first_attempt_class_trace_observation -> bool) &m :
  Pr[SampledDSeedFirstAttemptClassTrace.main() @ &m : P res] =
  Pr[SampledDSeed.main() @ &m :
       P (first_attempt_class_trace_observation res)].
proof.
byequiv sampled_dseed_first_attempt_class_trace_equiv => //=.
qed.

lemma sampled_dseed_first_attempt_accepted_class_trace_prE
    (P : int list list -> bool) &m :
  Pr[SampledDSeedFirstAttemptClassTrace.main() @ &m :
       res.`1 /\ P res.`3] =
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accepted res /\
       P (first_attempt_ordered_class_trace res)].
proof.
rewrite
  (sampled_dseed_first_attempt_class_trace_prE
    (fun (observation : first_attempt_class_trace_observation) =>
      observation.`1 /\ P observation.`3) &m).
done.
qed.

end Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze.
