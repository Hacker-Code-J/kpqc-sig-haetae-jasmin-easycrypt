require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
               Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailPostFreeze
               Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
               Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
               Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze
               Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze.

theory Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze.

import RealOrder.
import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecurityFirstRejectTailEntryPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze.
import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze.

module SampledDecision =
  Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
    .SampledBoundedKeygenDecision.

module SampledFirst =
  Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze
    .SampledFirstAttemptDecision.

module FixedDecision =
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .CheckedMode2BoundedKeygenDecision.

module FirstDecision =
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .CheckedMode2FirstAttemptDecision.

module BoundedTail =
  Mode2FaithfulSecurityBoundedRetryTailPostFreeze
    .CheckedMode2BoundedRetryTail.

(* At fuel zero a rejected first attempt enters a tail that executes no retry
   body.  This layer identifies the resulting exhaustion mass with the sampled
   first-attempt rejection mass.  It does not add a numeric rejection bound,
   a sampler-termination claim, strict contraction, unbounded termination,
   packing, full key generation, or equality with [HAETAE.kg]. *)

op checked_mode2_retry1_zero_tail_result
    (trace : first_attempt_trace) :
    checked_mode2_bounded_retry_tail_result =
  ((first_attempt_trace_retry1_inputs trace).`1,
   (first_attempt_trace_retry1_inputs trace).`2,
   (first_attempt_trace_retry1_inputs trace).`3,
   (first_attempt_trace_retry1_inputs trace).`4,
   (first_attempt_trace_retry1_inputs trace).`5,
   (first_attempt_trace_retry1_inputs trace).`6,
   (first_attempt_trace_retry1_inputs trace).`7,
   (first_attempt_trace_retry1_inputs trace).`8,
   W64.one, 1, 0).

lemma checked_mode2_bounded_retry_tail_zero_ll
    (trace0 : first_attempt_trace) :
  phoare [BoundedTail.run :
    seedbuf = (first_attempt_trace_retry1_inputs trace0).`1 /\
    mat = (first_attempt_trace_retry1_inputs trace0).`2 /\
    avec = (first_attempt_trace_retry1_inputs trace0).`3 /\
    s1 = (first_attempt_trace_retry1_inputs trace0).`4 /\
    s2 = (first_attempt_trace_retry1_inputs trace0).`5 /\
    bp = (first_attempt_trace_retry1_inputs trace0).`6 /\
    s1hatp = (first_attempt_trace_retry1_inputs trace0).`7 /\
    counter = (first_attempt_trace_retry1_inputs trace0).`8 /\
    retry = 1 /\ fuel = 0
    ==>
    res = checked_mode2_retry1_zero_tail_result trace0] = 1%r.
proof.
proc.
rcondf 4.
+ auto.
auto => />.
qed.

lemma checked_mode2_zero_fuel_rejected_exhausted
    (raw_seed0 : BArray32.t)
    (trace0 : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0 trace0 =>
  ! first_attempt_trace_accepted trace0 =>
  sampled_bounded_keygen_rejected_tail_exhausted
    raw_seed0 0
    (trace0, true, checked_mode2_retry1_zero_tail_result trace0).
proof.
move=> hsnapshot hreject.
have hentry :=
  rejected_first_attempt_enters_retry_tail_state
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    raw_seed0 trace0 hsnapshot hreject.
have htail :=
  rejected_first_attempt_retry1_inputs_tail_state trace0 hentry.
rewrite /sampled_bounded_keygen_rejected_tail_exhausted
        /checked_mode2_bounded_keygen_decision_entry_post
        /checked_mode2_bounded_keygen_decision_post
        /checked_mode2_bounded_retry_tail_post
        /checked_mode2_bounded_retry_tail_rejected_exhaustion
        /checked_mode2_retry1_zero_tail_result /=.
rewrite hreject /=.
smt().
qed.

lemma checked_mode2_zero_fuel_accepted_not_exhausted
    (raw_seed0 : BArray32.t)
    (trace0 : first_attempt_trace) :
  first_attempt_trace_accepted trace0 =>
  ! sampled_bounded_keygen_rejected_tail_exhausted
      raw_seed0 0 (trace0, false, witness).
proof.
rewrite /sampled_bounded_keygen_rejected_tail_exhausted.
smt().
qed.

lemma checked_mode2_first_attempt_decision_self_snapshot
    (raw_seed0 : BArray32.t) :
  equiv [FirstDecision.run ~ FirstDecision.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed} /\
    seedbuf{2} =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128 /\
    mat{2} =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768 /\
    avec{2} =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s1{2} =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s2{2} =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    bp{2} =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s1hatp{2} =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    raw_seed{2} = raw_seed0
    ==>
    res{1} = res{2} /\
    Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_first_attempt_snapshot_facts
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        raw_seed0 res{2}].
proof.
conseq
  (: ={seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed}
     ==> ={res})
  _
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_snapshot_correct
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0) => //=.
by proc; sim.
qed.

lemma sampled_bounded_keygen_zero_fuel_first_attempt_equiv :
  equiv [SampledDecision.main ~ SampledFirst.main :
    arg{1} = 0
    ==>
    SampledDecision.raw_current{1} = SampledFirst.raw_current{2} /\
    res{1}.`1 = res{2} /\
    (sampled_bounded_keygen_rejected_tail_exhausted
       SampledDecision.raw_current{1} 0 res{1} =
     ! first_attempt_trace_accepted res{2})].
proof.
proc.
seq 1 1 :
  (SampledDecision.raw_current{1} = SampledFirst.raw_current{2} /\
   fuel{1} = 0).
+ rnd.
  auto.
inline{1} FixedDecision.run.
sp 9 0.
exlim SampledFirst.raw_current{2} => raw0.
seq 1 1 :
  (trace{1} = trace{2} /\
   Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
     .checked_first_attempt_snapshot_facts
       Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
       Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
       Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
       Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
       Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
       Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
       raw0 trace{2} /\
   SampledFirst.raw_current{2} = raw0 /\
   fuel0{1} = 0 /\
   SampledDecision.raw_current{1} = SampledFirst.raw_current{2}).
+ call (checked_mode2_first_attempt_decision_self_snapshot raw0).
  auto.
if{1}.
+ wp.
  exlim trace{2} => trace0.
  ecall{1} (checked_mode2_bounded_retry_tail_zero_ll trace0).
  auto => />.
  move=> hsnapshot hreject.
  have hexhaust :=
    checked_mode2_zero_fuel_rejected_exhausted
      raw0 trace0 hsnapshot hreject.
  by rewrite hexhaust.
+ auto.
  move=> &1 &2
    [[htrace [hsnapshot [hraw0 [hfuel hraw]]]] haccept].
  have haccept2 := haccept.
  rewrite htrace in haccept2.
  have hnot :=
    checked_mode2_zero_fuel_accepted_not_exhausted
      raw0 trace{2} haccept2.
  smt().
qed.

lemma sampled_bounded_keygen_zero_fuel_exhaustion_massE &m :
  Pr[SampledDecision.main(0) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledDecision.raw_current 0 res] =
  Pr[SampledFirst.main() @ &m :
       ! first_attempt_trace_accepted res].
proof.
byequiv sampled_bounded_keygen_zero_fuel_first_attempt_equiv => //=.
smt().
qed.

lemma sampled_bounded_keygen_accepted_mass_first_reject_defect_bound
    fuel0 &m :
  0 <= fuel0 =>
  Pr[SampledDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_first_accept
         SampledDecision.raw_current fuel0 res] +
  Pr[SampledDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_accept
         SampledDecision.raw_current fuel0 res] >=
  1%r - delta_bounded_keygen_progress fuel0 -
  Pr[SampledFirst.main() @ &m :
       ! first_attempt_trace_accepted res] -
  finite_additive_defect_prefix
    delta_bounded_keygen_progress fuel0.
proof.
move=> hfuel.
have hbound :=
  sampled_bounded_keygen_accepted_mass_additive_defect_bound
    fuel0 &m hfuel.
rewrite sampled_bounded_keygen_zero_fuel_exhaustion_massE in hbound.
exact hbound.
qed.

end Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze.
