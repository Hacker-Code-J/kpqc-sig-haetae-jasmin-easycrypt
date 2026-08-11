require import TargetKeygenM23FullFirstAttempt.

theory ExistingFirstAttemptAdapter.

(* Thin import-only adapter: it deliberately preserves every concrete mode-2
   precondition of the reused theorem and claims only returned packed-buffer
   equivalence with the peeled first-attempt observer. *)
lemma imported_mode2_full_first_attempt_equiv :
  equiv [
    TargetKeygenM23FullFirstAttempt.Parent._keypair_full_m23 ~
    TargetKeygenM23FullFirstAttempt.Mode2FullFirstAttempt.run :
    vkp{1} = vkp{2} /\ skp{1} = skp{2} /\ seedp{1} = seedp{2} /\
    k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
    best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
    singular_bound{1} = 611098
    ==>
    res{1} = res{2}.`1].
proof.
exact TargetKeygenM23FullFirstAttempt.mode2_full_first_attempt_equiv.
qed.

lemma imported_mode2_first_attempt_fft_inputs_bound2
    (seed0 : BArray32.t) :
  hoare [
    TargetKeygenM23FullFirstAttempt.Mode2FullFirstAttempt.run :
    seedp = seed0
    ==>
    TargetKeygenM23FullFirstAttempt.first_attempt_snapshot_facts
      seed0 res.`2 /\
    TargetKeygenM23FullFirstAttempt.first_attempt_trace_fft_inputs_bound2
      res.`2].
proof.
exact
  (TargetKeygenM23FullFirstAttempt.mode2_full_first_attempt_fft_inputs_bound2_correct
     seed0).
qed.

lemma imported_mode2_first_attempt_score_guard
    (seed0 : BArray32.t) :
  hoare [
    TargetKeygenM23FullFirstAttempt.Mode2FullFirstAttempt.run :
    seedp = seed0
    ==>
    TargetKeygenM23FullFirstAttempt.first_attempt_snapshot_facts
      seed0 res.`2 /\
    (TargetKeygenM23FullFirstAttempt.first_attempt_trace_accepted res.`2 <=>
     TargetKeygenM23FullFirstAttempt.first_attempt_trace_score_within_bound
       res.`2)].
proof.
exact
  (TargetKeygenM23FullFirstAttempt.mode2_full_first_attempt_score_guard_correct
     seed0).
qed.

lemma imported_mode2_first_attempt_accepted
    (seed0 : BArray32.t) :
  hoare [
    TargetKeygenM23FullFirstAttempt.Mode2FullFirstAttempt.run :
    seedp = seed0
    ==>
    TargetKeygenM23FullFirstAttempt.first_attempt_trace_accepted res.`2 =>
      TargetKeygenM23FullFirstAttempt.first_attempt_snapshot_facts
        seed0 res.`2 /\
      TargetKeygenM23FullFirstAttempt.first_attempt_trace_guard res.`2].
proof.
exact
  (TargetKeygenM23FullFirstAttempt.mode2_full_first_attempt_accepted_correct
     seed0).
qed.

end ExistingFirstAttemptAdapter.
