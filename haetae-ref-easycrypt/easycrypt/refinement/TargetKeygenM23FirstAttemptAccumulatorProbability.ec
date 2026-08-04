require import AllCore Distr.

from Jasmin require import JModel_x86.

require import BArray32 BArray8192.
require import
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorProbability
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23FirstAttemptAccumulator.

import
  KeygenM23SingularFFTAccumulatorProbability
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23FirstAttemptAccumulator.

theory TargetKeygenM23FirstAttemptAccumulatorProbability.

(* Project an arbitrary distribution on immutable first-attempt traces onto
   the two arrays consumed by the deterministic accumulator event. *)
op first_attempt_trace_accumulator_sample
    (trace : first_attempt_trace) : mode2_accumulator_sample =
  with trace =
    FirstAttemptTrace
      _ _ _ _ s1 _ _ _ _ final_s2 _ _ _ _ =>
    (s1, final_s2).

op first_attempt_trace_accumulator_sample_distribution
    (d : first_attempt_trace distr) : mode2_accumulator_sample distr =
  dmap d first_attempt_trace_accumulator_sample.

lemma first_attempt_trace_accumulator_headroom_badE
    (trace : first_attempt_trace) :
  first_attempt_trace_accumulator_headroom_bad trace =
  mode2_accumulator_trace_headroom_bad
    (first_attempt_trace_accumulator_sample trace).
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
by rewrite /first_attempt_trace_accumulator_headroom_bad
           /first_attempt_trace_accumulator_sample
           /mode2_accumulator_trace_headroom_bad /=.
qed.

lemma first_attempt_trace_accumulator_headroom_bad_muE
    (d : first_attempt_trace distr) :
  mu d first_attempt_trace_accumulator_headroom_bad =
  mu (first_attempt_trace_accumulator_sample_distribution d)
    mode2_accumulator_trace_headroom_bad.
proof.
rewrite /first_attempt_trace_accumulator_sample_distribution dmapE.
apply mu_eq => trace.
rewrite /(\o).
exact (first_attempt_trace_accumulator_headroom_badE trace).
qed.

lemma first_attempt_trace_accumulator_headroom_bad_mu_le_split
    (d : first_attempt_trace distr)
    (delta_lower delta_upper delta_real delta_imag : real) :
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu (first_attempt_trace_accumulator_sample_distribution d)
      (fun sample =>
        mode2_accumulator_prefix_lower_bad_at sample processed j) <=
      delta_lower) =>
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu (first_attempt_trace_accumulator_sample_distribution d)
      (fun sample =>
        mode2_accumulator_prefix_upper_bad_at sample processed j) <=
      delta_upper) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu (first_attempt_trace_accumulator_sample_distribution d)
      (fun sample =>
        mode2_accumulator_coordinate_real_bad_at sample slot j) <=
      delta_real) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu (first_attempt_trace_accumulator_sample_distribution d)
      (fun sample =>
        mode2_accumulator_coordinate_imag_bad_at sample slot j) <=
      delta_imag) =>
  mu d first_attempt_trace_accumulator_headroom_bad <=
    1536%r * (delta_lower + delta_upper) +
    1280%r * (delta_real + delta_imag).
proof.
move=> hlower hupper hreal himag.
rewrite first_attempt_trace_accumulator_headroom_bad_muE.
exact
  (mode2_accumulator_headroom_bad_event_mu_le_split
    (first_attempt_trace_accumulator_sample_distribution d)
    delta_lower delta_upper delta_real delta_imag
    hlower hupper hreal himag).
qed.

lemma first_attempt_snapshot_accumulator_unsafe_mu_le_headroom_bad
    (d : first_attempt_trace distr) (seed0 : BArray32.t) :
  mu d (fun trace =>
    first_attempt_snapshot_facts seed0 trace /\
    !first_attempt_trace_accumulator_safe trace) <=
  mu d first_attempt_trace_accumulator_headroom_bad.
proof.
apply mu_sub => trace.
move=> [hsnapshot hunsafe].
case (first_attempt_trace_accumulator_headroom_bad trace) => hbad.
+ trivial.
have hnotbad :
    !first_attempt_trace_accumulator_headroom_bad trace by
  rewrite hbad.
have hsafe :=
  first_attempt_snapshot_accumulator_safe_outside_headroom_bad
    seed0 trace hsnapshot hnotbad.
smt().
qed.

lemma first_attempt_snapshot_accumulator_error_failure_mu_le_headroom_bad
    (d : first_attempt_trace distr) (seed0 : BArray32.t) (j : int) :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  mu d (fun trace =>
    first_attempt_snapshot_facts seed0 trace /\
    !first_attempt_trace_accumulator_error_at trace j) <=
  mu d first_attempt_trace_accumulator_headroom_bad.
proof.
move=> hj.
apply mu_sub => trace.
move=> [hsnapshot herror].
case (first_attempt_trace_accumulator_headroom_bad trace) => hbad.
+ trivial.
have hnotbad :
    !first_attempt_trace_accumulator_headroom_bad trace by
  rewrite hbad.
have hbound :=
  first_attempt_snapshot_accumulator_error_outside_headroom_bad
    seed0 trace j hsnapshot hnotbad hj.
smt().
qed.

end TargetKeygenM23FirstAttemptAccumulatorProbability.
