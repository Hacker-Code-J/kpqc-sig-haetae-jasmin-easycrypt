require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray128 BArray8192 BArray32768.
require import KeygenSamplerCallersSpec
               KeygenM23ArithmeticSpec
               Mode2KeygenCoreEquation
               Mode2FaithfulSecurityRetryEtaProgressPostFreeze
               Mode2FaithfulSecurityCheckedRetryStepPostFreeze
               Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze.

theory Mode2FaithfulSecurityRetryTailInvariantPostFreeze.

module RetryStep =
  Mode2FaithfulSecurityCheckedRetryStepPostFreeze.CheckedMode2RetryStep.

(* This glue layer covers one rejected tail transition only.  It does not
   derive next-retry progress or no-wrap, first-tail reachability, an
   acceptance probability, whole-loop termination, packing, full key
   generation, or equality with [HAETAE.kg].  State components without a
   structural premise are carried explicitly because the actual loop reuses
   them as the next call arguments. *)

op checked_mode2_retry_tail_state
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec : BArray8192.t)
    (s1 s2 bp s1hat : BArray8192.t)
    retry (counter reject : W64.t) : bool =
  1 <= retry /\
  reject = W64.one /\
  counter =
    W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i retry) /\
  Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_retry_eta_nowrap retry /\
  KeygenM23ArithmeticSpec.matrix_active_bound16 mat /\
  Mode2KeygenCoreEquation.canonical_a_active avec.

lemma checked_mode2_retry_snapshot_counterE
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry snapshot :
  Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
    .checked_mode2_retry_step_snapshot_facts
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry snapshot =>
  snapshot.`6 =
    W64.of_int
      (KeygenSamplerCallersSpec.mode2_retry_counter_i (retry + 1)).
proof.
rewrite /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
          .checked_mode2_retry_step_snapshot_facts
        /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
          .retry_step_eta_pair_facts.
smt().
qed.

lemma checked_mode2_retry_step_progress_snapshot_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry (eta_limit : int -> int) :
  phoare [RetryStep.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    checked_mode2_retry_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry counter W64.one /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_progress seedbuf0 retry eta_limit
    ==>
    Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
      .checked_mode2_retry_step_snapshot_facts
        seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry res] = 1%r.
proof.
conseq
  (Mode2FaithfulSecurityCheckedRetryStepPostFreeze
    .checked_mode2_retry_step_progress_ll
    seedbuf0 retry eta_limit)
  (Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
    .checked_mode2_retry_tail_snapshot_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry) => //=.
rewrite /checked_mode2_retry_tail_state.
smt().
move=> &hr _ result.
split.
+ move=> [hsnapshot _].
  split.
  + exact
      (checked_mode2_retry_snapshot_counterE
        seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry result hsnapshot).
  + exact hsnapshot.
+ move=> [_ hsnapshot].
  split; exact hsnapshot.
qed.

lemma rejected_retry_snapshot_preserves_tail_state
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry (counter0 : W64.t) snapshot :
  checked_mode2_retry_tail_state
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry
    counter0 W64.one =>
  Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
    .checked_mode2_retry_step_snapshot_facts
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry snapshot =>
  snapshot.`13 = W64.one =>
  Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_retry_eta_nowrap (retry + 1) =>
  checked_mode2_retry_tail_state
    snapshot.`1 snapshot.`2 snapshot.`3 snapshot.`4 snapshot.`10
    snapshot.`9 snapshot.`8 (retry + 1) snapshot.`6 snapshot.`13.
proof.
move=> htail hsnapshot hreject hnextnowrap.
move: htail => [hretry [_ [_ [_ [hmat _]]]]].
rewrite /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
          .checked_mode2_retry_step_snapshot_facts in hsnapshot.
move: hsnapshot => [hseedE [hmatE [havecE [hcanonical [heta _]]]]].
rewrite /checked_mode2_retry_tail_state.
move: heta.
rewrite /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
          .retry_step_eta_pair_facts.
move=> [_ [_ [_ [_ [_ [_ hcounter]]]]]].
split; first smt().
split; first exact hreject.
split; first exact hcounter.
split; first exact hnextnowrap.
split.
+ by rewrite hmatE.
+ exact hcanonical.
qed.

lemma checked_mode2_retry_tail_step_snapshot_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry (eta_limit : int -> int) :
  phoare [RetryStep.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    checked_mode2_retry_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry counter W64.one /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_progress seedbuf0 retry eta_limit
    ==>
    Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
      .checked_mode2_retry_step_snapshot_facts
        seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry res /\
    (res.`13 = W64.one =>
      Mode2FaithfulSecurityRetryEtaProgressPostFreeze
        .mode2_retry_eta_nowrap (retry + 1) =>
      checked_mode2_retry_tail_state
        res.`1 res.`2 res.`3 res.`4 res.`10
        res.`9 res.`8 (retry + 1) res.`6 res.`13)] = 1%r.
proof.
conseq
  (checked_mode2_retry_step_progress_snapshot_ll
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry eta_limit) => //=.
move=> &hr hpre result.
split.
+ move=> [hsnapshot _].
  exact hsnapshot.
+ move=> hsnapshot.
  split; first exact hsnapshot.
  move=> hreject hnextnowrap.
  move: hpre => [_ [_ [_ [_ [_ [_ [_ [htail _]]]]]]]].
  exact
    (rejected_retry_snapshot_preserves_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry counter{hr} result
      htail hsnapshot hreject hnextnowrap).
qed.

end Mode2FaithfulSecurityRetryTailInvariantPostFreeze.
