require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import KeygenSamplerCallersSpec
               KeygenM23ArithmeticSpec
               Mode2KeygenCoreEquation
               TargetKeygenM23FinalizeComposition
               TargetKeygenM23FullFirstAttempt
               TargetKeygenM23ParentComposition
               TargetKeygenM23FinalizeSemanticComposition.
require import Mode2FaithfulSecurityRetryEtaProgressPostFreeze
               Mode2FaithfulSecurityRetryTailInvariantPostFreeze
               Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.

theory Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze.

import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.
import Mode2FaithfulSecurityRetryTailInvariantPostFreeze.

(* This bridge only enters the peeled retry tail after a rejected checked
   first attempt.  It does not claim retry-step reachability beyond this
   entry point, acceptance probability, whole-loop termination, packing,
   or full [HAETAE.kg] correctness. *)

op first_attempt_rejected_retry1_tail_state
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat final_bp final_s2
      counter sv bound reject =>
    checked_mode2_retry_tail_state
      seedbuf mat avec s1 final_s2 final_bp s1hat 1 counter reject.

lemma first_attempt_sampler_facts_matrix_active
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2 counter mat0 avec0 s10 s20 raw_seed0 =>
  KeygenM23ArithmeticSpec.matrix_active_bound16 mat.
proof.
move=> hsampler.
have hrange :
    KeygenSamplerCallersSpec.uniform_matrix_range32768
      mat KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i.
+ move: hsampler.
   rewrite /TargetKeygenM23FinalizeComposition.mode2_sampler_facts.
   smt().
exact
  (TargetKeygenM23ParentComposition.sampler_matrix_range_mode2_bound16
    mat hrange).
qed.

lemma first_attempt_sampler_facts_canonical_a_active
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2 counter mat0 avec0 s10 s20 raw_seed0 =>
  Mode2KeygenCoreEquation.canonical_a_active avec.
proof.
move=> hsampler.
rewrite /Mode2KeygenCoreEquation.canonical_a_active.
move=> flat hflat.
exact
  (TargetKeygenM23FinalizeSemanticComposition.mode2_sampler_facts_avec_bounded
    seedbuf mat avec s1 s2 counter mat0 avec0 s10 s20 raw_seed0 flat
    hsampler hflat).
qed.

lemma retry1_tail_nowrap :
  Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_retry_eta_nowrap 1.
proof.
rewrite /Mode2FaithfulSecurityRetryEtaProgressPostFreeze
          .mode2_retry_eta_nowrap
        /KeygenSamplerCallersSpec.mode2_eta_nonce_i
        /KeygenSamplerCallersSpec.mode2_retry_counter_i
        /KeygenSamplerCallersSpec.mode2_retry_span_i
        /KeygenSamplerCallersSpec.mode2_k_i
        /KeygenSamplerCallersSpec.mode2_m_i.
smt().
qed.

lemma rejected_first_attempt_enters_retry_tail_state
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (trace : first_attempt_trace) :
  checked_first_attempt_snapshot_facts
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace =>
  ! first_attempt_trace_accepted trace =>
  first_attempt_rejected_retry1_tail_state trace.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject /=.
rewrite /checked_first_attempt_snapshot_facts
        /first_attempt_trace_accepted
        /first_attempt_rejected_retry1_tail_state /=.
move=> [hsampler [hm23 [hfinal [harray [hhaetae
  [hscore [hcounter [hbound [hreject haccept]]]]]]]]] hnotacc.
have hreject1 : reject = W64.one by smt().
have hmat :
    KeygenM23ArithmeticSpec.matrix_active_bound16 mat.
+ exact
    (first_attempt_sampler_facts_matrix_active
      seedbuf mat avec s1 sampled_s2 counter
      mat0 avec0 s10 s20 raw_seed0 hsampler).
have hcanonical :
    Mode2KeygenCoreEquation.canonical_a_active avec.
+ exact
    (first_attempt_sampler_facts_canonical_a_active
      seedbuf mat avec s1 sampled_s2 counter
      mat0 avec0 s10 s20 raw_seed0 hsampler).
rewrite /checked_mode2_retry_tail_state.
split; first smt().
split; first exact hreject1.
split.
+ rewrite hcounter.
   rewrite /KeygenSamplerCallersSpec.mode2_retry_counter_i
           /KeygenSamplerCallersSpec.mode2_retry_span_i
           /KeygenSamplerCallersSpec.mode2_m_i
           /KeygenSamplerCallersSpec.mode2_k_i.
   congr.
   ring.
split; first exact retry1_tail_nowrap.
split; first exact hmat.
exact hcanonical.
qed.

lemma checked_mode2_first_attempt_decision_rejected_tail_entry
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
    ! first_attempt_trace_accepted res =>
      first_attempt_rejected_retry1_tail_state res].
proof.
conseq
  (checked_mode2_first_attempt_decision_snapshot_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr hpre result hsnapshot hreject.
exact
  (rejected_first_attempt_enters_retry_tail_state
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 result hsnapshot hreject).
qed.

end Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze.
