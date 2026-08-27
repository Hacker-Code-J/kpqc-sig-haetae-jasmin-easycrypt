require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray128 BArray8192 BArray32768.
require import KeygenSamplerCallersSpec
               Mode2FaithfulSecurityRetryEtaProgressPostFreeze
               Mode2FaithfulSecurityCheckedRetryStepPostFreeze
               Mode2FaithfulSecurityRetryTailInvariantPostFreeze
               Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze.

theory Mode2FaithfulSecurityBoundedRetryTailPostFreeze.

module RetryStep =
  Mode2FaithfulSecurityCheckedRetryStepPostFreeze.CheckedMode2RetryStep.

(* This proof-only driver executes at most [fuel] checked tail retries under
   an external progress/no-wrap window.  It proves bounded termination and
   final tail-state preservation, but not an unbounded loop, an acceptance
   probability, last-snapshot semantics, packing, full key generation, or
   equality with [HAETAE.kg]. *)

op checked_mode2_retry_window_progress
    (seedbuf0 : BArray128.t) retry0 fuel0
    (eta_limits : int -> int -> int) : bool =
  (forall offset,
     0 <= offset < fuel0 =>
     Mode2FaithfulSecurityRetryEtaProgressPostFreeze
       .mode2_retry_eta_progress
         seedbuf0 (retry0 + offset) (eta_limits offset)) /\
  (forall offset,
     0 <= offset <= fuel0 =>
     Mode2FaithfulSecurityRetryEtaProgressPostFreeze
       .mode2_retry_eta_nowrap (retry0 + offset)).

lemma checked_mode2_retry_window_progressE
    seedbuf0 retry0 fuel0 eta_limits offset :
  checked_mode2_retry_window_progress seedbuf0 retry0 fuel0 eta_limits =>
  0 <= offset < fuel0 =>
  Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_retry_eta_progress
      seedbuf0 (retry0 + offset) (eta_limits offset).
proof.
rewrite /checked_mode2_retry_window_progress.
by move=> [hprogress _] hoff; apply hprogress.
qed.

lemma checked_mode2_retry_window_nowrapE
    seedbuf0 retry0 fuel0 eta_limits offset :
  checked_mode2_retry_window_progress seedbuf0 retry0 fuel0 eta_limits =>
  0 <= offset <= fuel0 =>
  Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_retry_eta_nowrap (retry0 + offset).
proof.
rewrite /checked_mode2_retry_window_progress.
by move=> [_ hnowrap] hoff; apply hnowrap.
qed.

lemma checked_mode2_retry_window_step_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry :
  hoare [RetryStep.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    Mode2FaithfulSecurityRetryTailInvariantPostFreeze
      .checked_mode2_retry_tail_state
        seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry counter W64.one /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_nowrap (retry + 1)
    ==>
    res.`1 = seedbuf0 /\ res.`2 = mat0 /\ res.`3 = avec0 /\
    res.`6 =
      W64.of_int
        (KeygenSamplerCallersSpec.mode2_retry_counter_i (retry + 1)) /\
    (res.`13 = W64.zero \/ res.`13 = W64.one) /\
    (res.`13 = W64.one =>
      Mode2FaithfulSecurityRetryTailInvariantPostFreeze
        .checked_mode2_retry_tail_state
          res.`1 res.`2 res.`3 res.`4 res.`10 res.`9 res.`8
          (retry + 1) res.`6 res.`13)].
proof.
conseq
  (Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
    .checked_mode2_retry_tail_snapshot_correct
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry) => //=.
+ rewrite /Mode2FaithfulSecurityRetryTailInvariantPostFreeze
            .checked_mode2_retry_tail_state.
  smt().
move=> &hr hpre result hsnapshot.
have hseed : result.`1 = seedbuf0.
+ move: hsnapshot.
  rewrite /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
            .checked_mode2_retry_step_snapshot_facts.
  smt().
have hmat : result.`2 = mat0.
+ move: hsnapshot.
  rewrite /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
            .checked_mode2_retry_step_snapshot_facts.
  smt().
have havec : result.`3 = avec0.
+ move: hsnapshot.
  rewrite /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
            .checked_mode2_retry_step_snapshot_facts.
  smt().
have hcounter :=
  Mode2FaithfulSecurityRetryTailInvariantPostFreeze
    .checked_mode2_retry_snapshot_counterE
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry result hsnapshot.
have hbinary : result.`13 = W64.zero \/ result.`13 = W64.one.
+ move: hsnapshot.
  rewrite /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
            .checked_mode2_retry_step_snapshot_facts
          /Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
            .retry_step_decision_facts.
  smt().
split; first exact hseed.
split; first exact hmat.
split; first exact havec.
split; first exact hcounter.
split; first exact hbinary.
move=> hreject.
have htail :
    Mode2FaithfulSecurityRetryTailInvariantPostFreeze
      .checked_mode2_retry_tail_state
        seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry counter{hr} W64.one.
+ move: hpre; smt().
have hnextnowrap :
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_nowrap (retry + 1) by
  move: hpre; smt().
exact
  (Mode2FaithfulSecurityRetryTailInvariantPostFreeze
    .rejected_retry_snapshot_preserves_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry counter{hr} result
      htail hsnapshot hreject hnextnowrap).
qed.

lemma checked_mode2_retry_window_step_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry (eta_limit : int -> int) :
  phoare [RetryStep.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    Mode2FaithfulSecurityRetryTailInvariantPostFreeze
      .checked_mode2_retry_tail_state
        seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry counter W64.one /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_progress seedbuf0 retry eta_limit /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_nowrap (retry + 1)
    ==>
    res.`1 = seedbuf0 /\ res.`2 = mat0 /\ res.`3 = avec0 /\
    res.`6 =
      W64.of_int
        (KeygenSamplerCallersSpec.mode2_retry_counter_i (retry + 1)) /\
    (res.`13 = W64.zero \/ res.`13 = W64.one) /\
    (res.`13 = W64.one =>
      Mode2FaithfulSecurityRetryTailInvariantPostFreeze
        .checked_mode2_retry_tail_state
          res.`1 res.`2 res.`3 res.`4 res.`10 res.`9 res.`8
          (retry + 1) res.`6 res.`13)] = 1%r.
proof.
conseq
  (Mode2FaithfulSecurityCheckedRetryStepPostFreeze
    .checked_mode2_retry_step_progress_ll
      seedbuf0 retry eta_limit)
  (checked_mode2_retry_window_step_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry) => //=.
+ rewrite /Mode2FaithfulSecurityRetryTailInvariantPostFreeze
            .checked_mode2_retry_tail_state.
  smt().
qed.

type checked_mode2_bounded_retry_tail_result =
  BArray128.t * BArray32768.t * BArray8192.t *
  BArray8192.t * BArray8192.t * BArray8192.t * BArray8192.t *
  W64.t * W64.t * int * int.

op checked_mode2_bounded_retry_tail_post
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 : BArray8192.t)
    retry0 fuel0
    (result : checked_mode2_bounded_retry_tail_result) : bool =
  result.`1 = seedbuf0 /\
  result.`2 = mat0 /\
  result.`3 = avec0 /\
  0 <= result.`11 <= fuel0 /\
  result.`10 = retry0 + result.`11 /\
  (result.`9 = W64.zero \/ result.`9 = W64.one) /\
  (result.`9 = W64.one =>
    Mode2FaithfulSecurityRetryTailInvariantPostFreeze
      .checked_mode2_retry_tail_state
        result.`1 result.`2 result.`3 result.`4 result.`5
        result.`6 result.`7 result.`10 result.`8 result.`9) /\
  (result.`9 = W64.zero \/ result.`11 = fuel0).

module CheckedMode2BoundedRetryTail = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       counter : W64.t, retry fuel : int)
      : checked_mode2_bounded_retry_tail_result = {
    var reject : W64.t;
    var steps : int;
    var snapshot :
      Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
        .retry_step_snapshot;

    reject <- W64.one;
    steps <- 0;
    snapshot <- witness;
    while (0 < fuel /\ reject = W64.one) {
      snapshot <@ RetryStep.run(seedbuf, mat, avec, s1, s2, bp, s1hatp, counter);
      seedbuf <- snapshot.`1;
      mat <- snapshot.`2;
      avec <- snapshot.`3;
      s1 <- snapshot.`4;
      s2 <- snapshot.`10;
      bp <- snapshot.`9;
      s1hatp <- snapshot.`8;
      counter <- snapshot.`6;
      reject <- snapshot.`13;
      retry <- retry + 1;
      fuel <- fuel - 1;
      steps <- steps + 1;
    }
    return
      (seedbuf, mat, avec, s1, s2, bp, s1hatp,
       counter, reject, retry, steps);
  }
}.

lemma checked_mode2_bounded_retry_tail_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t)
    retry0 fuel0 eta_limits :
  phoare [CheckedMode2BoundedRetryTail.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    counter = counter0 /\ retry = retry0 /\ fuel = fuel0 /\
    0 <= fuel0 /\
    Mode2FaithfulSecurityRetryTailInvariantPostFreeze
      .checked_mode2_retry_tail_state
        seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry0 counter0 W64.one /\
    checked_mode2_retry_window_progress seedbuf0 retry0 fuel0 eta_limits
    ==>
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 fuel0 res] = 1%r.
proof.
proc.
while
  (seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
   0 <= steps /\ 0 <= fuel /\
   retry = retry0 + steps /\ fuel = fuel0 - steps /\
   (reject = W64.zero \/ reject = W64.one) /\
   (reject = W64.one =>
    Mode2FaithfulSecurityRetryTailInvariantPostFreeze
      .checked_mode2_retry_tail_state
        seedbuf0 mat0 avec0 s1 s2 bp s1hatp retry counter reject) /\
   checked_mode2_retry_window_progress seedbuf0 retry0 fuel0 eta_limits)
  fuel.
+ move=> z.
   wp.
   exlim s1 => s1_before.
   exlim s2 => s2_before.
   exlim bp => bp_before.
   exlim s1hatp => s1hat_before.
   exlim retry => retry_before.
   exlim steps => steps_before.
   call
     (checked_mode2_retry_window_step_ll
       seedbuf0 mat0 avec0
       s1_before s2_before bp_before s1hat_before
       retry_before (eta_limits steps_before)).
   auto => />.
   move=> &hr hsteps hfuel0 htail hprogress_all hnowrap_all hguard.
   split.
   + have hprogress := hprogress_all steps_before _.
     + smt().
     have hnextnowrap := hnowrap_all (steps_before + 1) _.
     + smt().
     move: htail hnextnowrap.
     rewrite /Mode2FaithfulSecurityRetryTailInvariantPostFreeze
               .checked_mode2_retry_tail_state
             /Mode2FaithfulSecurityRetryEtaProgressPostFreeze
               .mode2_retry_eta_nowrap.
     smt().
   + move=> _ _ _ _ _ _ _ _ _ result _ _ _ _ _ _.
     smt().
+ auto => />.
   smt().
qed.

end Mode2FaithfulSecurityBoundedRetryTailPostFreeze.
