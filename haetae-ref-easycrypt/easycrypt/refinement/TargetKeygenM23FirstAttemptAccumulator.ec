require import AllCore.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety
  KeygenMode2ParentTarget
  TargetKeygenM23SingularFFTInputBounds
  TargetKeygenM23FullFirstAttempt.

import
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety
  TargetKeygenM23FullFirstAttempt.

theory TargetKeygenM23FirstAttemptAccumulator.

(* The first-attempt snapshot fixes the five FFT inputs, while this predicate
   keeps the signed-W32 safety condition for every evolving accumulator word
   explicit.  The sampler coefficient bound alone does not discharge it. *)
op first_attempt_trace_accumulator_safe
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace
      _ _ _ _ s1 _ _ _ _ final_s2 _ _ _ _ =>
    actual_mode2_accumulate_safe_trace
      s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i.

op first_attempt_trace_accumulator_headroom
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace
      _ _ _ _ s1 _ _ _ _ final_s2 _ _ _ _ =>
    mode2_accumulator_headroom_trace
      s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i.

op first_attempt_trace_accumulator_headroom_bad
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace
      _ _ _ _ s1 _ _ _ _ final_s2 _ _ _ _ =>
    mode2_accumulator_headroom_bad_event
      s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i.

op first_attempt_trace_accumulator_error_at
    (trace : first_attempt_trace) (j : int) : bool =
  with trace =
    FirstAttemptTrace
      _ _ _ _ s1 _ _ _ _ final_s2 _ _ _ _ =>
    `|accumulator_decode_at
         (KeygenM23SingularFFTSpec.mode2_accumulate
           s1 final_s2
           KeygenMode2ParentTarget.jfft_roots
           KeygenMode2ParentTarget.jfft_brv8) j -
       mode2_ideal_energy_prefix
         s1 final_s2
         KeygenM23SingularFFTSpec.mode2_slice_count_i j| <=
      mode2_energy_error_prefix
        s1 final_s2
        KeygenM23SingularFFTSpec.mode2_slice_count_i j.

lemma first_attempt_trace_accumulator_headroom_iff_no_bad
    (trace : first_attempt_trace) :
  first_attempt_trace_accumulator_headroom trace <=>
  !first_attempt_trace_accumulator_headroom_bad trace.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /first_attempt_trace_accumulator_headroom
        /first_attempt_trace_accumulator_headroom_bad /=.
apply mode2_accumulator_headroom_trace_iff_no_bad_event.
rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i.
smt().
qed.

lemma first_attempt_snapshot_accumulator_safe_outside_headroom_bad
    (seed0 : BArray32.t) (trace : first_attempt_trace) :
  first_attempt_snapshot_facts seed0 trace =>
  !first_attempt_trace_accumulator_headroom_bad trace =>
  first_attempt_trace_accumulator_safe trace.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
move=> hsnapshot hnotbad.
rewrite /first_attempt_trace_accumulator_headroom_bad /= in hnotbad.
rewrite /first_attempt_trace_accumulator_safe /=.
have hheadroom :
    mode2_accumulator_headroom_trace
      s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i.
+ have hiff :=
    mode2_accumulator_headroom_trace_iff_no_bad_event
      s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i _.
  + rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i.
    smt().
  exact (iffRL _ _ hiff hnotbad).
have hinputs0 :=
  first_attempt_snapshot_fft_inputs_bound2 seed0
    (FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2
      pre_bp s1hat final_bp final_s2
      counter sv bound reject) hsnapshot.
rewrite /first_attempt_trace_fft_inputs_bound2 /= in hinputs0.
have hinputs : mode2_accumulator_inputs_bound2 s1 final_s2.
+ move: hinputs0.
  rewrite
    /TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
    /mode2_accumulator_inputs_bound2.
  done.
apply
  (mode2_actual_accumulate_safe_from_headroom
    s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i).
+ rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i.
  smt().
+ done.
+ exact hinputs.
exact hheadroom.
qed.

lemma first_attempt_snapshot_accumulator_error
    (seed0 : BArray32.t) (trace : first_attempt_trace) (j : int) :
  first_attempt_snapshot_facts seed0 trace =>
  first_attempt_trace_accumulator_safe trace =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  first_attempt_trace_accumulator_error_at trace j.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
move=> hsnapshot hsafe hj.
rewrite /first_attempt_trace_accumulator_safe /= in hsafe.
rewrite /first_attempt_trace_accumulator_error_at /=.
have hinputs0 :=
  first_attempt_snapshot_fft_inputs_bound2 seed0
    (FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2
      pre_bp s1hat final_bp final_s2
      counter sv bound reject) hsnapshot.
rewrite /first_attempt_trace_fft_inputs_bound2 /= in hinputs0.
have hinputs : mode2_accumulator_inputs_bound2 s1 final_s2.
+ move: hinputs0.
  rewrite
    /TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
    /mode2_accumulator_inputs_bound2.
  done.
exact
  (mode2_actual_accumulate_full_error
    s1 final_s2 j hj hinputs hsafe).
qed.

lemma first_attempt_snapshot_accumulator_error_outside_headroom_bad
    (seed0 : BArray32.t) (trace : first_attempt_trace) (j : int) :
  first_attempt_snapshot_facts seed0 trace =>
  !first_attempt_trace_accumulator_headroom_bad trace =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  first_attempt_trace_accumulator_error_at trace j.
proof.
move=> hsnapshot hnotbad hj.
apply (first_attempt_snapshot_accumulator_error seed0 trace j).
+ exact hsnapshot.
+ exact
    (first_attempt_snapshot_accumulator_safe_outside_headroom_bad
      seed0 trace hsnapshot hnotbad).
exact hj.
qed.

end TargetKeygenM23FirstAttemptAccumulator.
