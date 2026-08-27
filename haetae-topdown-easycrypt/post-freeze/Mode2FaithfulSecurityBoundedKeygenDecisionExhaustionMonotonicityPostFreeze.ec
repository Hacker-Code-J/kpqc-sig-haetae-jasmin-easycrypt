require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import KeygenMode2ParentSpec TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
               Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
               Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailSmallProjectionPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailExhaustionMonotonicityPostFreeze.

theory Mode2FaithfulSecurityBoundedKeygenDecisionExhaustionMonotonicityPostFreeze.

import RealOrder.
import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailSmallProjectionPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailExhaustionMonotonicityPostFreeze.

module FirstDecision =
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .CheckedMode2FirstAttemptDecision.

module Decision =
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .CheckedMode2BoundedKeygenDecision.

module TailThenOneMore =
  Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze
    .CheckedMode2BoundedRetryTailThenOneMore.

(* This layer shares the checked first attempt and exposes the adjacent
   bounded-keygen decisions as one pair.  It targets decision-level tail
   exhaustion monotonicity only; no strict contraction, retry independence,
   sampled raw-seed lift, unbounded termination, packing, full key generation,
   or equality with [HAETAE.kg] is claimed. *)

type checked_mode2_bounded_keygen_decision_pair =
  checked_mode2_bounded_keygen_decision_result *
  checked_mode2_bounded_keygen_decision_result.

module CheckedMode2BoundedKeygenDecisionThenOneMore = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       raw_seed : BArray32.t, fuel : int)
      : checked_mode2_bounded_keygen_decision_pair = {
    var trace : first_attempt_trace;
    var tails : checked_mode2_retry_one_more_pair;
    var small, large : checked_mode2_bounded_keygen_decision_result;

    trace <@ FirstDecision.run
      (seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed);
    if (! first_attempt_trace_accepted trace) {
      tails <@ TailThenOneMore.run
        ((first_attempt_trace_retry1_inputs trace).`1,
         (first_attempt_trace_retry1_inputs trace).`2,
         (first_attempt_trace_retry1_inputs trace).`3,
         (first_attempt_trace_retry1_inputs trace).`4,
         (first_attempt_trace_retry1_inputs trace).`5,
         (first_attempt_trace_retry1_inputs trace).`6,
         (first_attempt_trace_retry1_inputs trace).`7,
         (first_attempt_trace_retry1_inputs trace).`8,
         1, fuel);
      small <- (trace, true, tails.`1);
      large <- (trace, true, tails.`2);
    } else {
      small <- (trace, false, witness);
      large <- small;
    }
    return (small, large);
  }
}.

lemma checked_mode2_bounded_keygen_decision_large_projection :
  equiv [Decision.run ~ CheckedMode2BoundedKeygenDecisionThenOneMore.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed} /\
    fuel{1} = fuel{2} + 1 /\ 0 <= fuel{2}
    ==>
    res{1} = res{2}.`2].
proof.
proc.
seq 1 1 :
  (trace{1} = trace{2} /\
   fuel{1} = fuel{2} + 1 /\ 0 <= fuel{2}).
+ call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  + auto => />.
if.
+ auto => />.
+ wp.
  call checked_mode2_bounded_retry_tail_succ_decomposition.
  auto => />.
+ auto => />.
qed.

lemma checked_mode2_bounded_keygen_decision_large_marginal_eq
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) fuel0 &m P :
  0 <= fuel0 =>
  Pr[Decision.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0 + 1) @ &m : P res] =
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0) @ &m : P res.`2].
proof.
move=> hfuel.
byequiv checked_mode2_bounded_keygen_decision_large_projection => //=.
qed.

op checked_mode2_bounded_keygen_rejected_tail_exhausted
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) fuel0
    (result : checked_mode2_bounded_keygen_decision_result) : bool =
  checked_mode2_bounded_keygen_decision_entry_post
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 result /\
  ! first_attempt_trace_accepted result.`1 /\
  result.`2 /\
  checked_mode2_bounded_retry_tail_rejected_exhaustion
    fuel0 result.`3.

op checked_mode2_bounded_keygen_then_one_more_good
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) fuel0
    (pair : checked_mode2_bounded_keygen_decision_pair) : bool =
  checked_mode2_bounded_keygen_decision_entry_post
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 pair.`1 /\
  checked_mode2_bounded_keygen_decision_entry_post
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 (fuel0 + 1) pair.`2 /\
  (checked_mode2_bounded_keygen_rejected_tail_exhausted
     mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 (fuel0 + 1) pair.`2 =>
   checked_mode2_bounded_keygen_rejected_tail_exhausted
     mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 pair.`1).

lemma checked_mode2_first_attempt_decision_snapshot_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  hoare [FirstDecision.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit
    ==>
    Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_first_attempt_snapshot_facts
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res].
proof.
conseq
  (checked_mode2_first_attempt_decision_snapshot_ll
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    mat_limit vec_limit eta_limit) => //=.
qed.

lemma checked_mode2_first_attempt_decision_self_snapshot
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  equiv [FirstDecision.run ~ FirstDecision.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed} /\
    seedbuf{2} = seedbuf0 /\ mat{2} = mat0 /\ avec{2} = avec0 /\
    s1{2} = s10 /\ s2{2} = s20 /\ bp{2} = bp0 /\
    s1hatp{2} = s1hat0 /\ raw_seed{2} = raw_seed0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit
    ==>
    res{1} = res{2} /\
    Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_first_attempt_snapshot_facts
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 res{2}].
proof.
conseq
  (: ={seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed}
     ==> ={res})
  _
  (checked_mode2_first_attempt_decision_snapshot_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    mat_limit vec_limit eta_limit) => //=.
by proc; sim.
qed.

lemma checked_mode2_bounded_keygen_decision_small_projection
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 mat_limit vec_limit eta_limit eta_limits :
  equiv [Decision.run ~ CheckedMode2BoundedKeygenDecisionThenOneMore.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed, fuel} /\
    seedbuf{2} = seedbuf0 /\ mat{2} = mat0 /\ avec{2} = avec0 /\
    s1{2} = s10 /\ s2{2} = s20 /\ bp{2} = bp0 /\
    s1hatp{2} = s1hat0 /\ raw_seed{2} = raw_seed0 /\
    fuel{2} = fuel0 /\ 0 <= fuel0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit /\
    checked_first_reject_window_ready
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      (fuel0 + 1) eta_limits
    ==>
    res{1} = res{2}.`1].
proof.
proc.
seq 1 1 :
  (trace{1} = trace{2} /\
   Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
     .checked_first_attempt_snapshot_facts
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace{2} /\
   fuel{1} = fuel0 /\ fuel{2} = fuel0 /\ 0 <= fuel0 /\
   checked_first_reject_window_ready
     mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
     (fuel0 + 1) eta_limits).
+ call
    (checked_mode2_first_attempt_decision_self_snapshot
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      mat_limit vec_limit eta_limit).
  auto => />.
if.
+ auto => />.
+ wp.
  exlim trace{2} => trace0.
  call
    (checked_mode2_bounded_retry_tail_small_projection
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
  + split.
    + exact hcounter.
    + split.
      + exact hmat.
      + exact hcanonical.
  move: hprogress.
  rewrite /checked_mode2_retry_window_progress
          /mode2_retry_eta_nowrap.
  move=> [hprogress0 hnowrap0].
  split.
  + move=> offset hoff0 hofflt.
    apply hprogress0.
    smt().
  + move=> offset hoff0 hoffle.
    apply hnowrap0.
    smt().
+ auto => />.
qed.

lemma checked_mode2_bounded_keygen_decision_small_marginal_eq
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 mat_limit vec_limit eta_limit eta_limits &m P :
  0 <= fuel0 =>
  KeygenMode2ParentSpec.mode2_sampler_prefix_progress
    raw_seed0 mat_limit vec_limit eta_limit =>
  checked_first_reject_window_ready
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    (fuel0 + 1) eta_limits =>
  Pr[Decision.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0) @ &m : P res] =
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0) @ &m : P res.`1].
proof.
move=> hfuel hprefix hwindow.
byequiv
  (checked_mode2_bounded_keygen_decision_small_projection
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    fuel0 mat_limit vec_limit eta_limit eta_limits) => //=.
qed.

lemma checked_mode2_bounded_keygen_then_one_more_good_rejected
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) fuel0
    (trace0 : first_attempt_trace)
    (tails : checked_mode2_retry_one_more_pair) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace0 =>
  ! first_attempt_trace_accepted trace0 =>
  first_attempt_rejected_retry1_tail_state trace0 =>
  checked_mode2_bounded_retry_tail_then_one_more_good
    (first_attempt_trace_retry1_inputs trace0).`1
    (first_attempt_trace_retry1_inputs trace0).`2
    (first_attempt_trace_retry1_inputs trace0).`3
    1 fuel0 tails =>
  checked_mode2_bounded_keygen_then_one_more_good
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0
    ((trace0, true, tails.`1), (trace0, true, tails.`2)).
proof.
rewrite /checked_mode2_bounded_keygen_then_one_more_good
        /checked_mode2_bounded_keygen_decision_entry_post
        /checked_mode2_bounded_keygen_decision_post
        /checked_mode2_bounded_keygen_rejected_tail_exhausted
        /checked_mode2_bounded_retry_tail_then_one_more_good /=.
move=> hsnapshot hreject hentry [hsmall [hlarge hmono]].
rewrite hreject /=.
smt().
qed.

lemma checked_mode2_bounded_keygen_then_one_more_good_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 mat_limit vec_limit eta_limit eta_limits :
  phoare [CheckedMode2BoundedKeygenDecisionThenOneMore.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0 /\
    fuel = fuel0 /\ 0 <= fuel0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit /\
    checked_first_reject_window_ready
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      (fuel0 + 1) eta_limits
    ==>
    checked_mode2_bounded_keygen_then_one_more_good
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res] = 1%r.
proof.
proc.
seq 1 :
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
     .checked_first_attempt_snapshot_facts
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace /\
   fuel = fuel0 /\ 0 <= fuel0 /\
   checked_first_reject_window_ready
     mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
     (fuel0 + 1) eta_limits)
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
    (checked_mode2_bounded_retry_tail_then_one_more_ll
      (first_attempt_trace_retry1_inputs trace0).`1
      (first_attempt_trace_retry1_inputs trace0).`2
      (first_attempt_trace_retry1_inputs trace0).`3
      (first_attempt_trace_retry1_inputs trace0).`4
      (first_attempt_trace_retry1_inputs trace0).`5
      (first_attempt_trace_retry1_inputs trace0).`6
      (first_attempt_trace_retry1_inputs trace0).`7
      (first_attempt_trace_retry1_inputs trace0).`8
      1 fuel0 eta_limits).
  auto.
  move=> &hr [htrace [[hsnapshot [hfuel_mem [hfuel hwindow]]] hreject]].
  subst trace0.
  have hentry :=
    rejected_first_attempt_enters_retry_tail_state
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 trace{hr}
      hsnapshot hreject.
  have htail :=
    rejected_first_attempt_retry1_inputs_tail_state trace{hr} hentry.
  have hprogress := hwindow trace{hr} hsnapshot hreject.
  split.
  + auto.
  + move=> _ result htail_good.
    exact
      (checked_mode2_bounded_keygen_then_one_more_good_rejected
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0
        trace{hr} result hsnapshot hreject hentry htail_good).
+ wp.
  rewrite /checked_mode2_bounded_keygen_then_one_more_good
          /checked_mode2_bounded_keygen_decision_entry_post
          /checked_mode2_bounded_keygen_decision_post
          /checked_mode2_bounded_keygen_rejected_tail_exhausted /=.
  auto.
+ call
    (checked_mode2_first_attempt_decision_snapshot_complement0
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      mat_limit vec_limit eta_limit).
  auto => />.
qed.

lemma checked_mode2_bounded_keygen_then_one_more_good_complement0
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 mat_limit vec_limit eta_limit eta_limits :
  phoare [CheckedMode2BoundedKeygenDecisionThenOneMore.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0 /\
    fuel = fuel0 /\ 0 <= fuel0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit /\
    checked_first_reject_window_ready
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      (fuel0 + 1) eta_limits
    ==>
    ! checked_mode2_bounded_keygen_then_one_more_good
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res] = 0%r.
proof.
bypr=> &m hpre.
have hgood :
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}, fuel{m}) @ &m :
     checked_mode2_bounded_keygen_then_one_more_good
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res] = 1%r.
+ by byphoare
    (checked_mode2_bounded_keygen_then_one_more_good_ll
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      fuel0 mat_limit vec_limit eta_limit eta_limits) => //.
have hpartition :
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}, fuel{m}) @ &m :
     checked_mode2_bounded_keygen_then_one_more_good
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res] +
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}, fuel{m}) @ &m :
     ! checked_mode2_bounded_keygen_then_one_more_good
         mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res] =
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}, fuel{m}) @ &m : true].
+ rewrite Pr[mu_not].
  ring.
have htotal_bound :
  0%r <=
    Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
         seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
         bp{m}, s1hatp{m}, raw_seed{m}, fuel{m}) @ &m : true]
  <= 1%r.
+ split.
  + by rewrite Pr[mu_ge0].
  + by rewrite Pr[mu_le1].
have hsum := hpartition.
rewrite hgood in hsum.
move: htotal_bound => [_ htotal_le].
have hsum_le :
  1%r +
    Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
         seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
         bp{m}, s1hatp{m}, raw_seed{m}, fuel{m}) @ &m :
       ! checked_mode2_bounded_keygen_then_one_more_good
           mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res]
  <= 1%r.
+ rewrite hsum.
  exact htotal_le.
have hbad_le0 :
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, raw_seed{m}, fuel{m}) @ &m :
     ! checked_mode2_bounded_keygen_then_one_more_good
         mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res]
  <= 0%r.
+ move: hsum_le.
  have hone : 1%r = 1%r + 0%r by ring.
  rewrite hone ler_add2l.
  done.
apply ler_anti.
split; first exact hbad_le0.
by rewrite Pr[mu_ge0].
qed.

lemma checked_mode2_bounded_keygen_then_one_more_exhaustion_le
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 mat_limit vec_limit eta_limit eta_limits &m :
  0 <= fuel0 =>
  KeygenMode2ParentSpec.mode2_sampler_prefix_progress
    raw_seed0 mat_limit vec_limit eta_limit =>
  checked_first_reject_window_ready
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    (fuel0 + 1) eta_limits =>
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0) @ &m :
     checked_mode2_bounded_keygen_rejected_tail_exhausted
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
       (fuel0 + 1) res.`2] <=
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0) @ &m :
     checked_mode2_bounded_keygen_rejected_tail_exhausted
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
       fuel0 res.`1].
proof.
move=> hfuel hprefix hwindow.
have hbad0 :
  Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0) @ &m :
     ! checked_mode2_bounded_keygen_then_one_more_good
         mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res] = 0%r.
+ by byphoare
    (checked_mode2_bounded_keygen_then_one_more_good_complement0
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
      fuel0 mat_limit vec_limit eta_limit eta_limits) => //.
apply
  (ler_trans
    (Pr[CheckedMode2BoundedKeygenDecisionThenOneMore.run(
          seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
          raw_seed0, fuel0) @ &m :
        checked_mode2_bounded_keygen_rejected_tail_exhausted
          mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res.`1 \/
        ! checked_mode2_bounded_keygen_then_one_more_good
            mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res])).
+ rewrite Pr[mu_sub]
          /checked_mode2_bounded_keygen_then_one_more_good.
  move=> &hr hlarge.
  case
    (checked_mode2_bounded_keygen_rejected_tail_exhausted
      mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res{hr}.`1)
    => hsmall.
  + by left.
  + smt().
trivial.
rewrite Pr[mu_or].
apply (mu_or_zero_le _ _ _ hbad0).
by rewrite Pr[mu_ge0].
qed.

lemma checked_mode2_bounded_keygen_rejected_tail_exhaustion_mass_prefix
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    fuel0 mat_limit vec_limit eta_limit eta_limits &m :
  0 <= fuel0 =>
  KeygenMode2ParentSpec.mode2_sampler_prefix_progress
    raw_seed0 mat_limit vec_limit eta_limit =>
  checked_first_reject_window_ready
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    (fuel0 + 1) eta_limits =>
  Pr[Decision.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0 + 1) @ &m :
     checked_mode2_bounded_keygen_rejected_tail_exhausted
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
       (fuel0 + 1) res] <=
  Pr[Decision.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       raw_seed0, fuel0) @ &m :
     checked_mode2_bounded_keygen_rejected_tail_exhausted
       mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 res].
proof.
move=> hfuel hprefix hwindow.
have hlarge :=
  checked_mode2_bounded_keygen_decision_large_marginal_eq
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    fuel0 &m
    (fun result =>
      checked_mode2_bounded_keygen_rejected_tail_exhausted
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
        (fuel0 + 1) result) hfuel.
have hsmall :=
  checked_mode2_bounded_keygen_decision_small_marginal_eq
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    fuel0 mat_limit vec_limit eta_limit eta_limits &m
    (fun result =>
      checked_mode2_bounded_keygen_rejected_tail_exhausted
        mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 result)
    hfuel hprefix hwindow.
have hpair :=
  checked_mode2_bounded_keygen_then_one_more_exhaustion_le
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0
    fuel0 mat_limit vec_limit eta_limit eta_limits &m
    hfuel hprefix hwindow.
rewrite hlarge hsmall.
exact hpair.
qed.

end Mode2FaithfulSecurityBoundedKeygenDecisionExhaustionMonotonicityPostFreeze.
