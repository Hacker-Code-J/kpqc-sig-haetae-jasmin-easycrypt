require import AllCore Distr IntDiv.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import KeygenMode2ParentSpec
               TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
               Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze
               Mode2FaithfulSecurityRetryEtaProgressPostFreeze
               Mode2FaithfulSecurityRetryTailInvariantPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailPostFreeze.

theory Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze.

import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze.
import Mode2FaithfulSecurityRetryEtaProgressPostFreeze.
import Mode2FaithfulSecurityRetryTailInvariantPostFreeze.

module FirstDecision =
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .CheckedMode2FirstAttemptDecision.

module BoundedTail =
  Mode2FaithfulSecurityBoundedRetryTailPostFreeze
    .CheckedMode2BoundedRetryTail.

(* The first checked attempt is followed by at most [fuel] checked retries.
   The external progress window is deliberately explicit.  This proof-only
   driver does not claim unbounded-loop termination, an acceptance
   probability, packing, full key generation, or equality with [HAETAE.kg]. *)

type first_attempt_retry1_inputs =
  BArray128.t * BArray32768.t * BArray8192.t *
  BArray8192.t * BArray8192.t * BArray8192.t * BArray8192.t *
  W64.t.

op first_attempt_trace_retry1_inputs
    (trace : first_attempt_trace) : first_attempt_retry1_inputs =
  with trace =
    FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
      final_bp final_s2 counter sv bound reject =>
    (seedbuf, mat, avec, s1, final_s2, final_bp, s1hat, counter).

op checked_first_reject_window_ready
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 (eta_limits : int -> int -> int) : bool =
  forall trace,
    Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_first_attempt_snapshot_facts
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace =>
    ! first_attempt_trace_accepted trace =>
    Mode2FaithfulSecurityBoundedRetryTailPostFreeze
      .checked_mode2_retry_window_progress
        (first_attempt_trace_retry1_inputs trace).`1
        1 fuel0 eta_limits.

type checked_mode2_bounded_keygen_decision_result =
  first_attempt_trace * bool *
  Mode2FaithfulSecurityBoundedRetryTailPostFreeze
    .checked_mode2_bounded_retry_tail_result.

op checked_mode2_bounded_keygen_decision_post
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) fuel0
    (result : checked_mode2_bounded_keygen_decision_result) : bool =
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 result.`1 /\
  (if first_attempt_trace_accepted result.`1 then
     ! result.`2
   else
     result.`2 /\
     Mode2FaithfulSecurityBoundedRetryTailPostFreeze
       .checked_mode2_bounded_retry_tail_post
         (first_attempt_trace_retry1_inputs result.`1).`1
         (first_attempt_trace_retry1_inputs result.`1).`2
         (first_attempt_trace_retry1_inputs result.`1).`3
         1 fuel0 result.`3).

op checked_mode2_bounded_keygen_decision_entry_post
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) fuel0
    (result : checked_mode2_bounded_keygen_decision_result) : bool =
  checked_mode2_bounded_keygen_decision_post
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 result /\
  (! first_attempt_trace_accepted result.`1 =>
   first_attempt_rejected_retry1_tail_state result.`1).

module CheckedMode2BoundedKeygenDecision = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       raw_seed : BArray32.t, fuel : int)
      : checked_mode2_bounded_keygen_decision_result = {
    var trace : first_attempt_trace;
    var tail_ran : bool;
    var tail :
      Mode2FaithfulSecurityBoundedRetryTailPostFreeze
        .checked_mode2_bounded_retry_tail_result;

    trace <@ FirstDecision.run
      (seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed);
    if (! first_attempt_trace_accepted trace) {
      tail <@ BoundedTail.run
        ((first_attempt_trace_retry1_inputs trace).`1,
         (first_attempt_trace_retry1_inputs trace).`2,
         (first_attempt_trace_retry1_inputs trace).`3,
         (first_attempt_trace_retry1_inputs trace).`4,
         (first_attempt_trace_retry1_inputs trace).`5,
         (first_attempt_trace_retry1_inputs trace).`6,
         (first_attempt_trace_retry1_inputs trace).`7,
         (first_attempt_trace_retry1_inputs trace).`8,
         1, fuel);
      tail_ran <- true;
    } else {
      tail_ran <- false;
      tail <- witness;
    }
    return (trace, tail_ran, tail);
  }
}.

lemma rejected_first_attempt_retry1_inputs_tail_state
    (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze
    .first_attempt_rejected_retry1_tail_state trace =>
  Mode2FaithfulSecurityRetryTailInvariantPostFreeze
    .checked_mode2_retry_tail_state
      (first_attempt_trace_retry1_inputs trace).`1
      (first_attempt_trace_retry1_inputs trace).`2
      (first_attempt_trace_retry1_inputs trace).`3
      (first_attempt_trace_retry1_inputs trace).`4
      (first_attempt_trace_retry1_inputs trace).`5
      (first_attempt_trace_retry1_inputs trace).`6
      (first_attempt_trace_retry1_inputs trace).`7
      1 (first_attempt_trace_retry1_inputs trace).`8 W64.one.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /first_attempt_rejected_retry1_tail_state
        /first_attempt_trace_retry1_inputs /=.
rewrite /checked_mode2_retry_tail_state.
smt().
qed.

lemma checked_mode2_bounded_keygen_decision_post_rejected_entry
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) fuel0
    (result : checked_mode2_bounded_keygen_decision_result) :
  checked_mode2_bounded_keygen_decision_post
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 result =>
  ! first_attempt_trace_accepted result.`1 =>
  first_attempt_rejected_retry1_tail_state result.`1.
proof.
rewrite /checked_mode2_bounded_keygen_decision_post.
move=> [hsnapshot hdecision] hreject.
exact
  (rejected_first_attempt_enters_retry_tail_state
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 result.`1
    hsnapshot hreject).
qed.

lemma checked_mode2_first_attempt_decision_snapshot_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  phoare [FirstDecision.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit
    ==>
    Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_first_attempt_snapshot_facts
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res] = 1%r.
proof.
conseq
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_progress_ll
      seedbuf0 raw_seed0 mat_limit vec_limit eta_limit)
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_snapshot_correct
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0) => //=.
qed.

lemma checked_mode2_first_attempt_decision_snapshot_complement0
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  phoare [FirstDecision.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit
    ==>
    ! Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
        .checked_first_attempt_snapshot_facts
          mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res] = 0%r.
proof.
bypr=> &m hpre.
have hgood :
  Pr[FirstDecision.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}) @ &m :
     Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
       .checked_first_attempt_snapshot_facts
         mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res] = 1%r.
+ by byphoare
    (checked_mode2_first_attempt_decision_snapshot_ll
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      mat_limit vec_limit eta_limit) => //.
have htotal :
  Pr[FirstDecision.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}) @ &m : true] = 1%r.
+ byphoare
    (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_mode2_first_attempt_decision_progress_ll
        seedbuf0 raw_seed0 mat_limit vec_limit eta_limit).
  + move: hpre.
    smt().
  + trivial.
have hpartition :
  Pr[FirstDecision.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}) @ &m :
     Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
       .checked_first_attempt_snapshot_facts
         mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res] +
  Pr[FirstDecision.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}) @ &m :
     ! Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
         .checked_first_attempt_snapshot_facts
           mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res] =
  Pr[FirstDecision.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}) @ &m : true].
+ rewrite Pr[mu_not].
  ring.
move: hpartition.
rewrite hgood htotal.
smt().
qed.

lemma checked_mode2_bounded_keygen_decision_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 mat_limit vec_limit eta_limit eta_limits :
  phoare [CheckedMode2BoundedKeygenDecision.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0 /\
    fuel = fuel0 /\ 0 <= fuel0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit /\
    checked_first_reject_window_ready
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 eta_limits
    ==>
    checked_mode2_bounded_keygen_decision_post
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res] = 1%r.
proof.
proc.
seq 1 :
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
     .checked_first_attempt_snapshot_facts
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace /\
   fuel = fuel0 /\ 0 <= fuel0 /\
   checked_first_reject_window_ready
     mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 eta_limits)
  1%r 1%r 0%r _ => //=.
+ call
    (checked_mode2_first_attempt_decision_snapshot_ll
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      mat_limit vec_limit eta_limit).
  auto => />.
if.
+ wp.
  exlim trace => trace0.
  call
    (Mode2FaithfulSecurityBoundedRetryTailPostFreeze
      .checked_mode2_bounded_retry_tail_ll
        (first_attempt_trace_retry1_inputs trace0).`1
        (first_attempt_trace_retry1_inputs trace0).`2
        (first_attempt_trace_retry1_inputs trace0).`3
        (first_attempt_trace_retry1_inputs trace0).`4
        (first_attempt_trace_retry1_inputs trace0).`5
        (first_attempt_trace_retry1_inputs trace0).`6
        (first_attempt_trace_retry1_inputs trace0).`7
        (first_attempt_trace_retry1_inputs trace0).`8
        1 fuel0 eta_limits).
  auto => />.
  move=> hsnapshot hfuel hwindow hreject.
  have hentry :=
    Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze
      .rejected_first_attempt_enters_retry_tail_state
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace0
        hsnapshot hreject.
  have htail :=
    rejected_first_attempt_retry1_inputs_tail_state trace0 hentry.
  have hprogress := hwindow trace0 hsnapshot hreject.
  move: htail.
  rewrite /checked_mode2_retry_tail_state.
  move=> [_ [_ [hcounter [_ [hmat hcanonical]]]]].
  split.
  + split; first exact hcounter.
    split; first exact hmat.
    exact hcanonical.
  split.
  + move=> offset hoff0 hofflt.
    apply
      (Mode2FaithfulSecurityBoundedRetryTailPostFreeze
        .checked_mode2_retry_window_progressE
          (first_attempt_trace_retry1_inputs trace0).`1
          1 fuel0 eta_limits offset hprogress).
    smt().
  move=> offset hoff0 hoffle.
  have hnowrap :=
    Mode2FaithfulSecurityBoundedRetryTailPostFreeze
      .checked_mode2_retry_window_nowrapE
        (first_attempt_trace_retry1_inputs trace0).`1
        1 fuel0 eta_limits offset hprogress _.
  + smt().
  move: hnowrap.
  rewrite /mode2_retry_eta_nowrap.
  done.
+ wp.
  rewrite /checked_mode2_bounded_keygen_decision_post /=.
  auto.
+ call
    (checked_mode2_first_attempt_decision_snapshot_complement0
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      mat_limit vec_limit eta_limit).
  auto => />.
qed.

lemma checked_mode2_bounded_keygen_decision_entry_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 mat_limit vec_limit eta_limit eta_limits :
  phoare [CheckedMode2BoundedKeygenDecision.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0 /\
    fuel = fuel0 /\ 0 <= fuel0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit /\
    checked_first_reject_window_ready
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 eta_limits
    ==>
    checked_mode2_bounded_keygen_decision_entry_post
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res] = 1%r.
proof.
conseq
  (checked_mode2_bounded_keygen_decision_ll
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    fuel0 mat_limit vec_limit eta_limit eta_limits) => //=.
move=> &hr hpre result.
rewrite /checked_mode2_bounded_keygen_decision_entry_post.
split.
+ move=> [hpost hentry].
  exact hpost.
move=> hpost.
split; first exact hpost.
exact
  (checked_mode2_bounded_keygen_decision_post_rejected_entry
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 result hpost).
qed.

end Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze.
