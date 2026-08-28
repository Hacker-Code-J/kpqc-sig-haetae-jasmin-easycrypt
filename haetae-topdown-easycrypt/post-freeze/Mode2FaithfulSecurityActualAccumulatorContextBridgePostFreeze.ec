require import AllCore Distr IntDiv.

from Jasmin require import JModel_x86.

require import
  BArray32 BArray128 BArray8192 BArray32768
  KeygenM23MatrixSpec
  KeygenM23FinalizeSpec
  KeygenM23SingularFFTAccumulatorProbability
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23FirstAttemptAccumulatorProbability
  TargetKeygenM23FinalizeComposition
  TargetKeygenM23FinalizeSemanticComposition
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze.

import KeygenM23SingularFFTAccumulatorProbability.
import TargetKeygenM23FullFirstAttempt.
import TargetKeygenM23FirstAttemptAccumulatorProbability.
import Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.
import Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze.

theory Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze.

(* This bridge is pointwise and trace-local.  The [pre_bp] and [avec]
   parameters vary with each trace and remain correlated with the same trace's
   [s1] and [sampled_s2].  Consequently this file does not identify the actual
   accumulator law with one fixed
   [ideal_mode2_accumulator_distribution pre_bp avec], does not idealize the
   deterministic SHAKE streams, does not show the actual pre-final pair lies in
   the ideal eta support, and provides no numeric tail bound. *)

lemma finalize_output_functional
    (pre_bp sampled_s2 avec : BArray8192.t)
    (bp1 s21 bp2 s22 : BArray8192.t) :
  KeygenM23FinalizeSpec.finalize_output pre_bp sampled_s2 avec bp1 s21 =>
  KeygenM23FinalizeSpec.finalize_output pre_bp sampled_s2 avec bp2 s22 =>
  bp1 = bp2 /\ s21 = s22.
proof.
rewrite /KeygenM23FinalizeSpec.finalize_output
        /KeygenM23FinalizeSpec.finalize_prefix.
move=> [hcount1 [hbp1 [hs21 [hbp1tail hs21tail]]]]
        [hcount2 [hbp2 [hs22 [hbp2tail hs22tail]]]].
split.
+ apply BArray8192.ext_eq32 => i hi.
   have hiw : 0 <= i < KeygenM23MatrixSpec.array_words_i.
   + move: hi.
     rewrite /KeygenM23MatrixSpec.array_words_i /BArray8192.size.
     smt().
   case (i < KeygenM23MatrixSpec.mode2_b_words_i) => hactive.
   + have hiactive : 0 <= i < KeygenM23MatrixSpec.mode2_b_words_i by smt().
     by rewrite (hbp1 i hiactive) (hbp2 i hiactive).
   have hitail :
       KeygenM23MatrixSpec.mode2_b_words_i <= i <
       KeygenM23MatrixSpec.array_words_i by smt().
   by rewrite (hbp1tail i hitail) (hbp2tail i hitail).
+ apply BArray8192.ext_eq32 => i hi.
   have hiw : 0 <= i < KeygenM23MatrixSpec.array_words_i.
   + move: hi.
     rewrite /KeygenM23MatrixSpec.array_words_i /BArray8192.size.
     smt().
   case (i < KeygenM23MatrixSpec.mode2_b_words_i) => hactive.
   + have hiactive : 0 <= i < KeygenM23MatrixSpec.mode2_b_words_i by smt().
     by rewrite (hs21 i hiactive) (hs22 i hiactive).
   have hitail :
       KeygenM23MatrixSpec.mode2_b_words_i <= i <
       KeygenM23MatrixSpec.array_words_i by smt().
   by rewrite (hs21tail i hitail) (hs22tail i hitail).
qed.

lemma finalize_output_eq_pure_final
    (pre_bp sampled_s2 avec final_bp final_s2 : BArray8192.t) :
  KeygenM23FinalizeSpec.finalize_output
    pre_bp sampled_s2 avec final_bp final_s2 =>
  final_bp =
    Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_bp pre_bp sampled_s2 avec /\
  final_s2 =
    Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_s2 pre_bp sampled_s2 avec.
proof.
move=> hfinal.
have hpure :=
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .pure_finalize_output pre_bp sampled_s2 avec.
have [hbp hs2] :=
  finalize_output_functional
    pre_bp sampled_s2 avec
    final_bp final_s2
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_bp pre_bp sampled_s2 avec)
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_s2 pre_bp sampled_s2 avec)
    hfinal hpure.
split; [exact hbp | exact hs2].
qed.

op trace_local_pre_bp (trace : first_attempt_trace) : BArray8192.t =
  with trace =
    FirstAttemptTrace _ _ _ _ _ _ pre_bp _ _ _ _ _ _ _ =>
    pre_bp.

op trace_local_avec (trace : first_attempt_trace) : BArray8192.t =
  with trace =
    FirstAttemptTrace _ _ _ avec _ _ _ _ _ _ _ _ _ _ =>
    avec.

op trace_local_pre_final_pair
    (trace : first_attempt_trace) :
    Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_eta_packed_secret_pair =
  with trace =
    FirstAttemptTrace _ _ _ _ s1 sampled_s2 _ _ _ _ _ _ _ _ =>
    (s1, sampled_s2).

op trace_local_ideal_accumulator_sample
    (trace : first_attempt_trace) : mode2_accumulator_sample =
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_sample
      (trace_local_pre_bp trace)
      (trace_local_avec trace)
      (trace_local_pre_final_pair trace).

op trace_local_ideal_accumulator_distribution
    (d : first_attempt_trace distr) : mode2_accumulator_sample distr =
  dmap d trace_local_ideal_accumulator_sample.

lemma checked_first_attempt_snapshot_trace_local_context_valid
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid
      (trace_local_pre_bp trace)
      (trace_local_avec trace).
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /checked_first_attempt_snapshot_facts
        /trace_local_pre_bp
        /trace_local_avec
        /ideal_mode2_finalize_context_valid /=.
move=> [hsampler [hm23 [hfinal [harray [hhaetae
  [hscore [hcounter [hbound [hreject haccept]]]]]]]]].
split.
+ move=> i hi.
   exact
     (TargetKeygenM23FinalizeSemanticComposition.mode2_m23_facts_word_bound16
       mat s1 pre_bp s1hat bp0 s1hat0 i hm23 hi).
move=> i hi.
exact
  (TargetKeygenM23FinalizeSemanticComposition.mode2_sampler_facts_avec_bounded
    seedbuf mat avec s1 sampled_s2 counter
    mat0 avec0 s10 s20 raw_seed0 i hsampler hi).
qed.

lemma checked_first_attempt_snapshot_accumulator_sample_eq_trace_local
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace =>
  TargetKeygenM23FirstAttemptAccumulatorProbability
    .first_attempt_trace_accumulator_sample trace =
  trace_local_ideal_accumulator_sample trace.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /checked_first_attempt_snapshot_facts
        /first_attempt_trace_accumulator_sample
        /trace_local_ideal_accumulator_sample
        /trace_local_pre_bp
        /trace_local_avec
        /trace_local_pre_final_pair
        /ideal_mode2_accumulator_sample /=.
move=> [hsampler [hm23 [hfinal [harray [hhaetae
  [hscore [hcounter [hbound [hreject haccept]]]]]]]]].
have [_ hs2] := finalize_output_eq_pure_final
  pre_bp sampled_s2 avec final_bp final_s2 hfinal.
by rewrite hs2.
qed.

lemma checked_first_attempt_snapshot_accumulator_distribution_eq_trace_local
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (d : first_attempt_trace distr) :
  (forall trace,
    trace \in d =>
    Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_first_attempt_snapshot_facts
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace) =>
  TargetKeygenM23FirstAttemptAccumulatorProbability
    .first_attempt_trace_accumulator_sample_distribution d =
  trace_local_ideal_accumulator_distribution d.
proof.
move=> hsnapshot.
rewrite
  /first_attempt_trace_accumulator_sample_distribution
  /trace_local_ideal_accumulator_distribution.
apply eq_dmap_in => trace htrace.
exact
  (checked_first_attempt_snapshot_accumulator_sample_eq_trace_local
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace
    (hsnapshot trace htrace)).
qed.

lemma trace_local_ideal_accumulator_distribution_lossless
    (d : first_attempt_trace distr) :
  is_lossless d =>
  is_lossless (trace_local_ideal_accumulator_distribution d).
proof.
rewrite /trace_local_ideal_accumulator_distribution.
apply dmap_ll.
qed.

end Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze.
