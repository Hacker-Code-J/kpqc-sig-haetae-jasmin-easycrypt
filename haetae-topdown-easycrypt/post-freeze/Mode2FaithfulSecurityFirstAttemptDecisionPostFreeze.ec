require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray32 BArray128 BArray8192 BArray32768.
require import KeygenMode2ParentSpec
               KeygenMode2ParentTarget
               KeygenM23FinalizeSpec
               KeygenM23FinalizeArraySemantics
               KeygenM23FinalizeHAETAEBridge
               KeygenM23SingularFFTSpec
               TargetKeygenM23FinalizeComposition
               TargetKeygenM23FinalizeSemanticComposition
               TargetKeygenM23Singular
               TargetKeygenM23SingularTotality
               TargetKeygenM23FullFirstAttempt.

theory Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.

import TargetKeygenM23FullFirstAttempt.

module Parent = KeygenMode2ParentTarget.M.

(* This observer stops immediately after the checked first-attempt parent state
   and the actual singular-value guard decision.  It does not model retry
   control, packing, acceptance probability, or full key generation. *)
module CheckedMode2FirstAttemptDecision = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       raw_seed : BArray32.t) : first_attempt_trace = {
    var counter : W64.t;
    var sampled_s2 : BArray8192.t;
    var pre_bp : BArray8192.t;
    var sv : W64.t;
    var bound : W64.t;
    var reject : W64.t;
    var ms : W64.t;

    (seedbuf, mat, avec, s1, sampled_s2, counter,
     pre_bp, s1hatp, bp, s2) <@
      TargetKeygenM23FinalizeComposition.CheckedMode2ParentM23Finalize.run
        (seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed);

    sv <@ Parent._singular_full (s1, s2, 3, 2, 5, 58, 24);
    bound <- W64.of_int 611098;
    ms <- init_msf;
    sv <- protect_64 sv ms;
    bound <- protect_64 bound ms;
    reject <- W64.zero;
    if (bound \ult sv) {
      reject <- W64.one;
    } else {
    }

    return
      FirstAttemptTrace
        (reject = W64.zero)
        seedbuf mat avec s1 sampled_s2
        pre_bp s1hatp bp s2
        counter sv bound reject;
  }
}.

op checked_first_attempt_snapshot_facts
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace
      accepted seedbuf mat
      avec s1 sampled_s2 pre_bp s1hat final_bp final_s2
      counter sv bound reject =>
    TargetKeygenM23FinalizeComposition.mode2_sampler_facts
      seedbuf mat avec s1 sampled_s2 counter
      mat0 avec0 s10 s20 raw_seed0 /\
    TargetKeygenM23FinalizeComposition.mode2_m23_facts
      mat s1 pre_bp s1hat bp0 s1hat0 /\
    KeygenM23FinalizeSpec.finalize_output
      pre_bp sampled_s2 avec final_bp final_s2 /\
    KeygenM23FinalizeArraySemantics.finalize_semantic_output
      pre_bp sampled_s2 avec final_bp final_s2 /\
    KeygenM23FinalizeHAETAEBridge.finalize_haetae_semantic_output
      pre_bp sampled_s2 avec final_bp final_s2 /\
    sv =
      KeygenM23SingularFFTSpec.mode2_singular_word
        s1 final_s2
        KeygenMode2ParentTarget.jfft_roots
        KeygenMode2ParentTarget.jfft_brv8 /\
    counter = W64.of_int 5 /\
    bound = W64.of_int 611098 /\
    reject = (if bound \ult sv then W64.one else W64.zero) /\
    accepted = (reject = W64.zero).

lemma checked_first_attempt_snapshot_score_guardE
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (trace : first_attempt_trace) :
  checked_first_attempt_snapshot_facts
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace =>
  (first_attempt_trace_accepted trace <=>
   first_attempt_trace_score_within_bound trace).
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /checked_first_attempt_snapshot_facts
        /first_attempt_trace_accepted
        /first_attempt_trace_score_within_bound
        /first_attempt_trace_score /=.
move=> [hsampler [hm23 [hfinal [harray [hhaetae
  [hscore [hcounter [hbound [hreject haccept]]]]]]]]].
rewrite haccept hreject hbound.
exact (mode2_singular_reject_zeroE sv).
qed.

lemma checked_first_attempt_snapshot_trace_guardE
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (trace : first_attempt_trace) :
  checked_first_attempt_snapshot_facts
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace =>
  (first_attempt_trace_guard trace <=>
   first_attempt_trace_score_within_bound trace).
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /checked_first_attempt_snapshot_facts
        /first_attempt_trace_guard
        /first_attempt_trace_score_within_bound
        /first_attempt_trace_score /=.
move=> [hsampler [hm23 [hfinal [harray [hhaetae
  [hscore [hcounter [hbound [hreject haccept]]]]]]]]].
rewrite hbound.
exact (TargetKeygenM23Singular.mode2_singular_guardE sv).
qed.

lemma checked_mode2_first_attempt_decision_snapshot_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [
    CheckedMode2FirstAttemptDecision.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0
    ==>
    checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res].
proof.
proc.
seq 1 :
  (TargetKeygenM23FinalizeComposition.mode2_sampler_facts
     seedbuf mat avec s1 sampled_s2 counter
     mat0 avec0 s10 s20 raw_seed0 /\
   TargetKeygenM23FinalizeComposition.mode2_m23_facts
     mat s1 pre_bp s1hatp bp0 s1hat0 /\
   KeygenM23FinalizeSpec.finalize_output
     pre_bp sampled_s2 avec bp s2 /\
   KeygenM23FinalizeArraySemantics.finalize_semantic_output
     pre_bp sampled_s2 avec bp s2 /\
   KeygenM23FinalizeHAETAEBridge.finalize_haetae_semantic_output
     pre_bp sampled_s2 avec bp s2).
+ call
    (TargetKeygenM23FinalizeSemanticComposition
      .checked_mode2_parent_m23_finalize_haetae_correct
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
  auto => />.
wp.
ecall
  (TargetKeygenM23Singular.singular_full_mode2_word_exact
     s1 s2).
auto => />.
qed.

lemma checked_mode2_first_attempt_decision_score_guard_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [
    CheckedMode2FirstAttemptDecision.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0
    ==>
    checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res /\
    (first_attempt_trace_accepted res <=>
     first_attempt_trace_score_within_bound res)].
proof.
conseq
  (checked_mode2_first_attempt_decision_snapshot_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr hpre result hsnapshot.
split; first exact hsnapshot.
exact
  (checked_first_attempt_snapshot_score_guardE
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 result hsnapshot).
qed.

lemma checked_mode2_first_attempt_decision_accepted_iff_score_le
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (trace : first_attempt_trace) :
  checked_first_attempt_snapshot_facts
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace =>
  (first_attempt_trace_accepted trace <=>
   W64.to_uint (first_attempt_trace_score trace) <= 611098).
proof.
exact
  (checked_first_attempt_snapshot_score_guardE
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace).
qed.

lemma checked_mode2_first_attempt_decision_accepted_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [
    CheckedMode2FirstAttemptDecision.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0
    ==>
    first_attempt_trace_accepted res =>
      checked_first_attempt_snapshot_facts
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res /\
      first_attempt_trace_guard res].
proof.
conseq
  (checked_mode2_first_attempt_decision_score_guard_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr hpre result [hsnapshot haccept_score] haccept.
split; first exact hsnapshot.
have hguard_score :
    first_attempt_trace_guard result <=>
    first_attempt_trace_score_within_bound result.
+ exact
    (checked_first_attempt_snapshot_trace_guardE
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 result hsnapshot).
smt().
qed.

lemma checked_mode2_first_attempt_decision_progress_ll
    (seedbuf0 : BArray128.t) (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  phoare [CheckedMode2FirstAttemptDecision.run :
    seedbuf = seedbuf0 /\ raw_seed = raw_seed0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit
    ==> true] = 1%r.
proof.
proc.
wp.
call TargetKeygenM23SingularTotality.m23sing_total_singular_full_mode2_ll.
wp.
call
  (TargetKeygenM23FinalizeComposition
    .checked_mode2_parent_m23_finalize_progress_ll
    seedbuf0 raw_seed0 mat_limit vec_limit eta_limit).
auto => />.
qed.

end Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.
