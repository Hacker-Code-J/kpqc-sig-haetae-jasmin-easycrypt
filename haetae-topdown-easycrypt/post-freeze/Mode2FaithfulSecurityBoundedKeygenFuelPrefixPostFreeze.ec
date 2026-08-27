require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import Mode2FaithfulSecurityCheckedRetryStepPostFreeze
               Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
               Mode2FaithfulSecurityRetryEtaProgressPostFreeze
               Mode2FaithfulSecurityRetryTailInvariantPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze.

theory Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.

import Mode2FaithfulSecurityRetryEtaProgressPostFreeze.
import Mode2FaithfulSecurityRetryTailInvariantPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze.

module RetryStep =
  Mode2FaithfulSecurityCheckedRetryStepPostFreeze.CheckedMode2RetryStep.

(* This file only exposes a proof-only one-more observer for adjacent bounded
   retry fuels.  It does not claim any distributional independence, sampled
   monotonicity, unbounded termination, packing, full key generation, or
   equality with [HAETAE.kg]. *)

lemma checked_mode2_retry_window_progress_prefix
    seedbuf0 retry0 fuel0 eta_limits :
  0 <= fuel0 =>
  checked_mode2_retry_window_progress
    seedbuf0 retry0 (fuel0 + 1) eta_limits =>
  checked_mode2_retry_window_progress
    seedbuf0 retry0 fuel0 eta_limits.
proof.
rewrite /checked_mode2_retry_window_progress.
move=> hfuel [hprogress hnowrap].
split.
+ move=> offset hoff.
   apply hprogress.
   smt().
move=> offset hoff.
apply hnowrap.
smt().
qed.

lemma checked_first_reject_window_ready_prefix
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) fuel0 eta_limits :
  0 <= fuel0 =>
  checked_first_reject_window_ready
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 (fuel0 + 1) eta_limits =>
  checked_first_reject_window_ready
    mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0 fuel0 eta_limits.
proof.
rewrite /checked_first_reject_window_ready.
move=> hfuel hready trace hsnapshot hreject.
apply
  (checked_mode2_retry_window_progress_prefix
    (first_attempt_trace_retry1_inputs trace).`1
    1 fuel0 eta_limits hfuel).
exact (hready trace hsnapshot hreject).
qed.

op checked_mode2_bounded_retry_tail_rejected_exhaustion
    fuel0
    (result : checked_mode2_bounded_retry_tail_result) : bool =
  result.`9 = W64.one /\ result.`11 = fuel0.

lemma w64_one_neq_zero : W64.one <> W64.zero.
proof.
rewrite W64.to_uint_eq W64.to_uint1 W64.to_uint0.
smt().
qed.

op checked_mode2_retry_one_more_result
    (small : checked_mode2_bounded_retry_tail_result)
    (snapshot :
      BArray128.t * BArray32768.t * BArray8192.t *
      BArray8192.t * BArray8192.t * W64.t *
      BArray8192.t * BArray8192.t *
      BArray8192.t * BArray8192.t *
      W64.t * W64.t * W64.t)
    : checked_mode2_bounded_retry_tail_result =
  (snapshot.`1, snapshot.`2, snapshot.`3, snapshot.`4,
   snapshot.`10, snapshot.`9, snapshot.`8, snapshot.`6,
   snapshot.`13, small.`10 + 1, small.`11 + 1).

lemma checked_mode2_bounded_retry_tail_post_accept_succ
    seedbuf0 mat0 avec0 retry0 fuel0 result :
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 result =>
  result.`9 = W64.zero =>
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 (fuel0 + 1) result.
proof.
rewrite /checked_mode2_bounded_retry_tail_post.
smt().
qed.

lemma checked_mode2_bounded_retry_tail_post_rejected_state
    seedbuf0 mat0 avec0 retry0 fuel0 result :
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 result =>
  result.`9 = W64.one =>
  checked_mode2_retry_tail_state
    seedbuf0 mat0 avec0 result.`4 result.`5 result.`6 result.`7
    result.`10 result.`8 result.`9 /\
  result.`10 = retry0 + fuel0 /\
  result.`11 = fuel0.
proof.
rewrite /checked_mode2_bounded_retry_tail_post.
move=> [hseed [hmat [havec [hsteps [hretry
  [hbinary [htail hstop]]]]]]] hreject.
have hstepsE : result.`11 = fuel0.
+ move: hstop.
  rewrite hreject w64_one_neq_zero /=.
  done.
have htail0 := htail hreject.
split.
+ move: htail0.
  rewrite hseed hmat havec.
  done.
split; smt().
qed.

lemma checked_mode2_bounded_retry_tail_post_rejected_progress
    seedbuf0 mat0 avec0 retry0 fuel0 result eta_limits :
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 result =>
  result.`9 = W64.one =>
  checked_mode2_retry_window_progress
    seedbuf0 retry0 (fuel0 + 1) eta_limits =>
  mode2_retry_eta_progress seedbuf0 result.`10 (eta_limits fuel0) /\
  mode2_retry_eta_nowrap (result.`10 + 1).
proof.
move=> hpost hreject hwindow.
have [htail [hretry hsteps]] :=
  checked_mode2_bounded_retry_tail_post_rejected_state
    seedbuf0 mat0 avec0 retry0 fuel0 result hpost hreject.
split.
+ have hprogress :=
     checked_mode2_retry_window_progressE
       seedbuf0 retry0 (fuel0 + 1) eta_limits fuel0 hwindow _.
   + smt().
   rewrite hretry.
   exact hprogress.
+ have hnowrap :=
     checked_mode2_retry_window_nowrapE
       seedbuf0 retry0 (fuel0 + 1) eta_limits (fuel0 + 1) hwindow _.
   + smt().
   have -> : result.`10 + 1 = retry0 + (fuel0 + 1) by smt().
   exact hnowrap.
qed.

lemma checked_mode2_retry_one_more_post
    seedbuf0 mat0 avec0 retry0 fuel0
    (small : checked_mode2_bounded_retry_tail_result)
    (snapshot :
      Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
        .retry_step_snapshot) :
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 small =>
  small.`9 = W64.one =>
  snapshot.`1 = seedbuf0 =>
  snapshot.`2 = mat0 =>
  snapshot.`3 = avec0 =>
  (snapshot.`13 = W64.zero \/ snapshot.`13 = W64.one) =>
  (snapshot.`13 = W64.one =>
    checked_mode2_retry_tail_state
      snapshot.`1 snapshot.`2 snapshot.`3 snapshot.`4 snapshot.`10
      snapshot.`9 snapshot.`8 (small.`10 + 1) snapshot.`6 snapshot.`13) =>
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 (fuel0 + 1)
    (checked_mode2_retry_one_more_result small snapshot).
proof.
rewrite /checked_mode2_bounded_retry_tail_post
        /checked_mode2_retry_one_more_result.
smt().
qed.

lemma checked_mode2_retry_one_more_step_pre
    seedbuf0 mat0 avec0 retry0 fuel0
    (small : checked_mode2_bounded_retry_tail_result) eta_limits :
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 small =>
  small.`9 = W64.one =>
  checked_mode2_retry_window_progress
    seedbuf0 retry0 (fuel0 + 1) eta_limits =>
  checked_mode2_retry_tail_state
    seedbuf0 mat0 avec0 small.`4 small.`5 small.`6 small.`7
    small.`10 small.`8 W64.one /\
  mode2_retry_eta_progress seedbuf0 small.`10 (eta_limits fuel0) /\
  mode2_retry_eta_nowrap (small.`10 + 1).
proof.
move=> hpost hreject hwindow.
have [htail _] :=
  checked_mode2_bounded_retry_tail_post_rejected_state
    seedbuf0 mat0 avec0 retry0 fuel0 small hpost hreject.
have [hprogress hnowrap] :=
  checked_mode2_bounded_retry_tail_post_rejected_progress
    seedbuf0 mat0 avec0 retry0 fuel0 small eta_limits
    hpost hreject hwindow.
split.
+ move: htail.
  rewrite hreject.
  done.
split; assumption.
qed.

lemma checked_mode2_retry_one_more_step_call_pre
    seedbuf0 mat0 avec0 retry0 fuel0
    (small : checked_mode2_bounded_retry_tail_result) eta_limits :
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 small =>
  small.`9 = W64.one =>
  checked_mode2_retry_window_progress
    seedbuf0 retry0 (fuel0 + 1) eta_limits =>
  small.`1 = seedbuf0 /\ small.`2 = mat0 /\ small.`3 = avec0 /\
  small.`4 = small.`4 /\ small.`5 = small.`5 /\
  small.`6 = small.`6 /\ small.`7 = small.`7 /\
  checked_mode2_retry_tail_state
    seedbuf0 mat0 avec0 small.`4 small.`5 small.`6 small.`7
    small.`10 small.`8 W64.one /\
  mode2_retry_eta_progress seedbuf0 small.`10 (eta_limits fuel0) /\
  mode2_retry_eta_nowrap (small.`10 + 1).
proof.
move=> hpost hreject hwindow.
have hstep :=
  checked_mode2_retry_one_more_step_pre
    seedbuf0 mat0 avec0 retry0 fuel0 small eta_limits
    hpost hreject hwindow.
have hpost0 := hpost.
rewrite /checked_mode2_bounded_retry_tail_post in hpost0.
move: hpost0 => [hseed [hmat [havec _]]].
move: hstep => [htail [hprogress hnowrap]].
split; first exact hseed.
split; first exact hmat.
split; first exact havec.
split; first done.
split; first done.
split; first done.
split; first done.
split; first exact htail.
split; assumption.
qed.

lemma checked_mode2_retry_one_more_reject_post
    seedbuf0 mat0 avec0 retry0 fuel0
    (small : checked_mode2_bounded_retry_tail_result)
    (snapshot :
      Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
        .retry_step_snapshot) :
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 small =>
  small.`9 = W64.one =>
  snapshot.`1 = seedbuf0 =>
  snapshot.`2 = mat0 =>
  snapshot.`3 = avec0 =>
  (snapshot.`13 = W64.zero \/ snapshot.`13 = W64.one) =>
  (snapshot.`13 = W64.one =>
    checked_mode2_retry_tail_state
      snapshot.`1 snapshot.`2 snapshot.`3 snapshot.`4 snapshot.`10
      snapshot.`9 snapshot.`8 (small.`10 + 1) snapshot.`6 snapshot.`13) =>
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 small /\
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 (fuel0 + 1)
      (checked_mode2_retry_one_more_result small snapshot) /\
  (checked_mode2_bounded_retry_tail_rejected_exhaustion
     (fuel0 + 1) (checked_mode2_retry_one_more_result small snapshot) =>
   checked_mode2_bounded_retry_tail_rejected_exhaustion fuel0 small).
proof.
move=> hpost hreject hseed hmat havec hbinary htail.
have hlarge :=
  checked_mode2_retry_one_more_post
    seedbuf0 mat0 avec0 retry0 fuel0 small snapshot
    hpost hreject hseed hmat havec hbinary htail.
have [_ [_ hsteps]] :=
  checked_mode2_bounded_retry_tail_post_rejected_state
    seedbuf0 mat0 avec0 retry0 fuel0 small hpost hreject.
split; first exact hpost.
split; first exact hlarge.
rewrite /checked_mode2_bounded_retry_tail_rejected_exhaustion
        /checked_mode2_retry_one_more_result.
smt().
qed.

lemma checked_mode2_retry_one_more_accept_post
    seedbuf0 mat0 avec0 retry0 fuel0
    (small : checked_mode2_bounded_retry_tail_result) :
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 small =>
  small.`9 <> W64.one =>
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 small /\
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 (fuel0 + 1) small /\
  (checked_mode2_bounded_retry_tail_rejected_exhaustion
     (fuel0 + 1) small =>
   checked_mode2_bounded_retry_tail_rejected_exhaustion fuel0 small).
proof.
move=> hpost hnotreject.
have hreject0 : small.`9 = W64.zero.
+ move: hpost hnotreject.
  rewrite /checked_mode2_bounded_retry_tail_post.
  smt().
have hlarge :=
  checked_mode2_bounded_retry_tail_post_accept_succ
    seedbuf0 mat0 avec0 retry0 fuel0 small hpost hreject0.
split; first exact hpost.
split; first exact hlarge.
rewrite /checked_mode2_bounded_retry_tail_rejected_exhaustion.
smt (w64_one_neq_zero).
qed.

type checked_mode2_retry_one_more_pair =
  checked_mode2_bounded_retry_tail_result *
  checked_mode2_bounded_retry_tail_result.

module CheckedMode2RetryOneMoreObserver = {
  proc run (small : checked_mode2_bounded_retry_tail_result)
      : checked_mode2_retry_one_more_pair = {
    var large : checked_mode2_bounded_retry_tail_result;
    var snapshot :
      Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze
        .retry_step_snapshot;

    if (small.`9 = W64.one) {
      snapshot <@ RetryStep.run
        (small.`1, small.`2, small.`3, small.`4,
         small.`5, small.`6, small.`7, small.`8);
      large <- checked_mode2_retry_one_more_result small snapshot;
    } else {
      large <- small;
    }
    return (small, large);
  }
}.

lemma checked_mode2_retry_one_more_observer_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 : BArray8192.t)
    retry0 fuel0 eta_limits
    (small0 : checked_mode2_bounded_retry_tail_result) :
  phoare [CheckedMode2RetryOneMoreObserver.run :
    small = small0 /\ 0 <= fuel0 /\
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 fuel0 small0 /\
    checked_mode2_retry_window_progress
      seedbuf0 retry0 (fuel0 + 1) eta_limits
    ==>
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 fuel0 res.`1 /\
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 (fuel0 + 1) res.`2 /\
    (checked_mode2_bounded_retry_tail_rejected_exhaustion
       (fuel0 + 1) res.`2 =>
     checked_mode2_bounded_retry_tail_rejected_exhaustion
       fuel0 res.`1)] = 1%r.
proof.
proc.
if.
+ wp.
  call
    (checked_mode2_retry_window_step_ll
      seedbuf0 mat0 avec0
      small0.`4 small0.`5 small0.`6 small0.`7
      small0.`10 (eta_limits fuel0)).
  auto.
  move=> &hr [[-> [_ [hpost hwindow]]] hreject].
  split.
  + exact
      (checked_mode2_retry_one_more_step_call_pre
        seedbuf0 mat0 avec0 retry0 fuel0 small0 eta_limits
        hpost hreject hwindow).
  move=> _ result [hseed [hmat [havec [_ [hbinary htail]]]]].
  exact
    (checked_mode2_retry_one_more_reject_post
      seedbuf0 mat0 avec0 retry0 fuel0 small0 result
      hpost hreject hseed hmat havec hbinary htail).
+ wp.
  auto.
  move=> &hr [[-> [_ [hpost _]]] hnotreject].
  exact
    (checked_mode2_retry_one_more_accept_post
      seedbuf0 mat0 avec0 retry0 fuel0 small0 hpost hnotreject).
qed.

end Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.
