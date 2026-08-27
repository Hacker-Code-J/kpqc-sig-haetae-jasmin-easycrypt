require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecurityRawSeedDistributionPostFreeze
               Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
               Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailPostFreeze
               Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDecisionExhaustionMonotonicityPostFreeze.

theory Mode2FaithfulSecuritySampledBoundedKeygenExhaustionMonotonicityPostFreeze.

import RealOrder.
import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDecisionExhaustionMonotonicityPostFreeze.

module SampledDecision =
  Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
    .SampledBoundedKeygenDecision.

module FixedPair =
  Mode2FaithfulSecurityBoundedKeygenDecisionExhaustionMonotonicityPostFreeze
    .CheckedMode2BoundedKeygenDecisionThenOneMore.

module FixedDecision =
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .CheckedMode2BoundedKeygenDecision.

module TailObserver =
  Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze
    .CheckedMode2RetryOneMoreObserver.

module TailThenOneMore =
  Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze
    .CheckedMode2BoundedRetryTailThenOneMore.

op sampled_zero_seedbuf : BArray128.t =
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128.

op sampled_zero_mat : BArray32768.t =
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768.

op sampled_zero_vec : BArray8192.t =
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192.

(* This layer draws the raw seed once and exposes the adjacent bounded-keygen
   decisions through the already-certified shared-first-attempt pair.  It
   accounts explicitly for raw seeds outside the [fuel + 1] progress support.
   It does not claim a strict contraction factor, numeric rejection bound,
   unbounded termination, packing, full key generation, or equality with
   [HAETAE.kg]. *)

module SampledBoundedKeygenDecisionThenOneMore = {
  var raw_current : BArray32.t

  proc main (fuel : int) :
      checked_mode2_bounded_keygen_decision_pair = {
    var pair : checked_mode2_bounded_keygen_decision_pair;

    raw_current <$
      Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed;
    pair <@ FixedPair.run(
      sampled_zero_seedbuf,
      sampled_zero_mat,
      sampled_zero_vec,
      sampled_zero_vec,
      sampled_zero_vec,
      sampled_zero_vec,
      sampled_zero_vec,
      raw_current,
      fuel);
    return pair;
  }
}.

module CheckedMode2BoundedKeygenDecisionOneMoreObserver = {
  proc run (small : checked_mode2_bounded_keygen_decision_result) :
      checked_mode2_bounded_keygen_decision_pair = {
    var tails : checked_mode2_retry_one_more_pair;
    var large : checked_mode2_bounded_keygen_decision_result;

    if (! first_attempt_trace_accepted small.`1) {
      tails <@ TailObserver.run(small.`3);
      large <- (small.`1, true, tails.`2);
    } else {
      large <- small;
    }
    return (small, large);
  }
}.

module CheckedMode2BoundedKeygenDecisionPrefixThenOneMore = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       raw_seed : BArray32.t, fuel : int) :
      checked_mode2_bounded_keygen_decision_pair = {
    var small : checked_mode2_bounded_keygen_decision_result;
    var pair : checked_mode2_bounded_keygen_decision_pair;

    small <@ FixedDecision.run(
      seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed, fuel);
    pair <@ CheckedMode2BoundedKeygenDecisionOneMoreObserver.run(small);
    return pair;
  }
}.

lemma checked_mode2_retry_one_more_observer_self_first
    (smallx : checked_mode2_bounded_retry_tail_result) :
  equiv [TailObserver.run ~ TailObserver.run :
    ={arg} /\ small{1} = smallx
    ==>
    ={res} /\ res{1}.`1 = smallx].
proof.
proc.
if.
+ auto.
+ wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  + auto.
+ auto.
qed.

lemma checked_mode2_bounded_keygen_decision_observer_self_first
    (smallx : checked_mode2_bounded_keygen_decision_result) :
  equiv [CheckedMode2BoundedKeygenDecisionOneMoreObserver.run ~
         CheckedMode2BoundedKeygenDecisionOneMoreObserver.run :
    ={arg} /\ small{1} = smallx
    ==>
    ={res} /\ res{1}.`1 = smallx].
proof.
proc.
if.
+ auto.
+ wp.
  call (checked_mode2_retry_one_more_observer_self_first smallx.`3).
  auto.
+ auto.
qed.

lemma checked_mode2_bounded_keygen_pair_prefix_equiv :
  equiv [FixedPair.run ~
         CheckedMode2BoundedKeygenDecisionPrefixThenOneMore.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed, fuel}
    ==>
    ={res}].
proof.
proc.
inline FixedDecision.run TailThenOneMore.run
       CheckedMode2BoundedKeygenDecisionOneMoreObserver.run.
sp 0 9.
seq 1 1 : (trace{1} = trace{2} /\ fuel{1} = fuel0{2}).
+ call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  + auto.
if.
+ auto.
+ sp 10 0.
  seq 1 1 :
    (trace{1} = trace{2} /\
     ! first_attempt_trace_accepted trace{2} /\
     small0{1} = tail{2}).
  + call (_ : ={arg} ==> ={res}).
    + by proc; sim.
    + auto.
  rcondt{2} 4.
  + auto.
  sp 0 3.
  wp.
  exlim small0{1} => tail0.
  call (checked_mode2_retry_one_more_observer_self_first tail0).
  auto.
+ rcondf{2} 5.
  + auto.
  auto.
qed.

module SampledBoundedKeygenDecisionPrefixThenOneMore = {
  var raw_current : BArray32.t

  proc main (fuel : int) :
      checked_mode2_bounded_keygen_decision_pair = {
    var small : checked_mode2_bounded_keygen_decision_result;
    var pair : checked_mode2_bounded_keygen_decision_pair;

    small <@ SampledDecision.main(fuel);
    raw_current <- SampledDecision.raw_current;
    pair <@ CheckedMode2BoundedKeygenDecisionOneMoreObserver.run(small);
    return pair;
  }
}.

(* The prefix form is intentional: outside the certified progress support the
   observer suffix need not be lossless.  The pHoare split below therefore
   proves only that appending the suffix cannot increase the saved small-event
   mass, which is exactly the direction needed by the defect bound. *)

module SampledBoundedKeygenDecisionFixedPrefixThenOneMore = {
  var raw_current : BArray32.t

  proc main (fuel : int) :
      checked_mode2_bounded_keygen_decision_pair = {
    var pair : checked_mode2_bounded_keygen_decision_pair;

    raw_current <$
      Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed;
    pair <@ CheckedMode2BoundedKeygenDecisionPrefixThenOneMore.run(
      sampled_zero_seedbuf,
      sampled_zero_mat,
      sampled_zero_vec,
      sampled_zero_vec,
      sampled_zero_vec,
      sampled_zero_vec,
      sampled_zero_vec,
      raw_current,
      fuel);
    return pair;
  }
}.

lemma sampled_bounded_keygen_pair_fixed_prefix_equiv :
  equiv [SampledBoundedKeygenDecisionThenOneMore.main ~
         SampledBoundedKeygenDecisionFixedPrefixThenOneMore.main :
    ={arg}
    ==>
    SampledBoundedKeygenDecisionThenOneMore.raw_current{1} =
      SampledBoundedKeygenDecisionFixedPrefixThenOneMore.raw_current{2} /\
    ={res}].
proof.
proc.
seq 1 1 :
  (SampledBoundedKeygenDecisionThenOneMore.raw_current{1} =
     SampledBoundedKeygenDecisionFixedPrefixThenOneMore.raw_current{2} /\
   fuel{1} = fuel{2}).
+ rnd.
  auto.
+ call checked_mode2_bounded_keygen_pair_prefix_equiv.
  auto.
qed.

lemma checked_mode2_bounded_keygen_decision_self :
  equiv [FixedDecision.run ~ FixedDecision.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, raw_seed, fuel}
    ==>
    ={res}].
proof.
by proc; sim.
qed.

lemma sampled_bounded_keygen_fixed_prefix_direct_equiv :
  equiv [SampledBoundedKeygenDecisionFixedPrefixThenOneMore.main ~
         SampledBoundedKeygenDecisionPrefixThenOneMore.main :
    ={arg}
    ==>
    SampledBoundedKeygenDecisionFixedPrefixThenOneMore.raw_current{1} =
      SampledBoundedKeygenDecisionPrefixThenOneMore.raw_current{2} /\
    ={res}].
proof.
proc.
inline SampledDecision.main
       CheckedMode2BoundedKeygenDecisionPrefixThenOneMore.run.
sp 0 1.
seq 1 1 :
  (SampledBoundedKeygenDecisionFixedPrefixThenOneMore.raw_current{1} =
     SampledDecision.raw_current{2} /\
   fuel{1} = fuel0{2}).
+ rnd.
  auto.
+ sp 9 0.
  seq 1 1 :
    (small{1} = result{2} /\
     SampledBoundedKeygenDecisionFixedPrefixThenOneMore.raw_current{1} =
       SampledDecision.raw_current{2}).
  + call checked_mode2_bounded_keygen_decision_self.
    rewrite /sampled_zero_seedbuf /sampled_zero_mat /sampled_zero_vec.
    auto.
  sp 0 2.
  wp.
  exlim small{1} => small0.
  call
    (checked_mode2_bounded_keygen_decision_observer_self_first small0).
  auto.
qed.

op sampled_bounded_keygen_then_one_more_good
    fuel0
    (raw_seed0 : BArray32.t)
    (pair : checked_mode2_bounded_keygen_decision_pair) : bool =
  raw_seed_has_bounded_keygen_progress raw_seed0 (fuel0 + 1) /\
  checked_mode2_bounded_keygen_then_one_more_good
    sampled_zero_mat
    sampled_zero_vec sampled_zero_vec sampled_zero_vec
    sampled_zero_vec sampled_zero_vec
    raw_seed0 fuel0 pair.

op sampled_bounded_keygen_pair_rejected_tail_exhausted
    (raw_seed0 : BArray32.t) fuel0
    (result : checked_mode2_bounded_keygen_decision_result) : bool =
  checked_mode2_bounded_keygen_rejected_tail_exhausted
    sampled_zero_mat
    sampled_zero_vec sampled_zero_vec sampled_zero_vec
    sampled_zero_vec sampled_zero_vec
    raw_seed0 fuel0 result.

lemma sampled_bounded_keygen_rejected_tail_exhaustedE
    (raw_seed0 : BArray32.t) fuel0
    (result : checked_mode2_bounded_keygen_decision_result) :
  sampled_bounded_keygen_rejected_tail_exhausted
    raw_seed0 fuel0 result =
  sampled_bounded_keygen_pair_rejected_tail_exhausted
    raw_seed0 fuel0 result.
proof.
rewrite /sampled_bounded_keygen_rejected_tail_exhausted
        /sampled_bounded_keygen_pair_rejected_tail_exhausted
        /checked_mode2_bounded_keygen_rejected_tail_exhausted
        /checked_mode2_bounded_retry_tail_rejected_exhaustion.
have htail_ran :
  checked_mode2_bounded_keygen_decision_entry_post
    sampled_zero_mat
    sampled_zero_vec sampled_zero_vec sampled_zero_vec
    sampled_zero_vec sampled_zero_vec
    raw_seed0 fuel0 result =>
  ! first_attempt_trace_accepted result.`1 =>
  result.`2.
+ rewrite /checked_mode2_bounded_keygen_decision_entry_post
          /checked_mode2_bounded_keygen_decision_post.
  smt().
smt().
qed.

lemma sampled_bounded_keygen_decision_large_projection :
  equiv [SampledDecision.main ~ SampledBoundedKeygenDecisionThenOneMore.main :
    arg{1} = arg{2} + 1 /\ 0 <= arg{2}
    ==>
    SampledDecision.raw_current{1} =
      SampledBoundedKeygenDecisionThenOneMore.raw_current{2} /\
    res{1} = res{2}.`2].
proof.
proc.
seq 1 1 :
  (SampledDecision.raw_current{1} =
     SampledBoundedKeygenDecisionThenOneMore.raw_current{2} /\
   fuel{1} = fuel{2} + 1 /\ 0 <= fuel{2}).
+ rnd.
  auto.
+ call checked_mode2_bounded_keygen_decision_large_projection.
  auto.
qed.

lemma sampled_bounded_keygen_decision_large_marginal_eq
    fuel0 &m P :
  0 <= fuel0 =>
  Pr[SampledDecision.main(fuel0 + 1) @ &m :
       P SampledDecision.raw_current res] =
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       P SampledBoundedKeygenDecisionThenOneMore.raw_current res.`2].
proof.
move=> hfuel.
byequiv sampled_bounded_keygen_decision_large_projection => //=.
qed.

lemma checked_sampled_bounded_keygen_then_one_more_good_raw_ll
    (raw_seed0 : BArray32.t) fuel0 :
  phoare [FixedPair.run :
    seedbuf = sampled_zero_seedbuf /\
    mat = sampled_zero_mat /\
    avec = sampled_zero_vec /\ s1 = sampled_zero_vec /\
    s2 = sampled_zero_vec /\ bp = sampled_zero_vec /\
    s1hatp = sampled_zero_vec /\ raw_seed = raw_seed0 /\
    fuel = fuel0 /\ 0 <= fuel0 /\
    raw_seed_has_bounded_keygen_progress raw_seed0 (fuel0 + 1)
    ==>
    checked_mode2_bounded_keygen_then_one_more_good
      sampled_zero_mat
      sampled_zero_vec sampled_zero_vec sampled_zero_vec
      sampled_zero_vec sampled_zero_vec
      raw_seed0 fuel0 res] = 1%r.
proof.
conseq
  (checked_mode2_bounded_keygen_then_one_more_good_ll
    sampled_zero_seedbuf sampled_zero_mat
    sampled_zero_vec sampled_zero_vec sampled_zero_vec
    sampled_zero_vec sampled_zero_vec
    raw_seed0 fuel0
    (bounded_keygen_prefix_witness
      (selected_bounded_keygen_progress_witness
        raw_seed0 (fuel0 + 1))).`1
    (bounded_keygen_prefix_witness
      (selected_bounded_keygen_progress_witness
        raw_seed0 (fuel0 + 1))).`2
    (bounded_keygen_prefix_witness
      (selected_bounded_keygen_progress_witness
        raw_seed0 (fuel0 + 1))).`3
    (bounded_keygen_tail_window
      (selected_bounded_keygen_progress_witness
        raw_seed0 (fuel0 + 1)))) => //=.
move=> &hr
  [hseed [hmat [havec [hs1 [hs2 [hbp
    [hs1hat [hraw [hfueleq [hfuel hgood]]]]]]]]]].
have hselected :=
  selected_bounded_keygen_progress_witness_valid
    raw_seed0 (fuel0 + 1) hgood.
move: hselected => [hprefix hwindow].
smt().
qed.

lemma sampled_bounded_keygen_then_one_more_good_progress_mass fuel0 :
  phoare [SampledBoundedKeygenDecisionThenOneMore.main :
    arg = fuel0 /\ 0 <= fuel0
    ==>
    sampled_bounded_keygen_then_one_more_good
      fuel0
      SampledBoundedKeygenDecisionThenOneMore.raw_current
      res] >=
  (mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    (fun raw =>
      raw_seed_has_bounded_keygen_progress raw (fuel0 + 1))).
proof.
proc.
seq 1 :
  (fuel = fuel0 /\ 0 <= fuel0 /\
   raw_seed_has_bounded_keygen_progress
     SampledBoundedKeygenDecisionThenOneMore.raw_current
     (fuel0 + 1))
  (mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    (fun raw =>
      raw_seed_has_bounded_keygen_progress raw (fuel0 + 1)))
  1%r 0%r _ => //=.
+ rnd
    (fun raw =>
      raw_seed_has_bounded_keygen_progress raw (fuel0 + 1)).
  auto.
wp.
exlim SampledBoundedKeygenDecisionThenOneMore.raw_current => raw0.
conseq (: _ : = 1%r) => //=.
call
  (checked_sampled_bounded_keygen_then_one_more_good_raw_ll
    raw0 fuel0).
rewrite /sampled_bounded_keygen_then_one_more_good.
auto => />.
qed.

lemma sampled_bounded_keygen_then_one_more_good_mass fuel0 :
  phoare [SampledBoundedKeygenDecisionThenOneMore.main :
    arg = fuel0 /\ 0 <= fuel0
    ==>
    sampled_bounded_keygen_then_one_more_good
      fuel0
      SampledBoundedKeygenDecisionThenOneMore.raw_current
      res] >=
  (1%r - delta_bounded_keygen_progress (fuel0 + 1)).
proof.
rewrite -raw_seed_bounded_keygen_good_massE.
exact sampled_bounded_keygen_then_one_more_good_progress_mass.
qed.

lemma sampled_bounded_keygen_then_one_more_bad_mass_le
    fuel0 &m :
  0 <= fuel0 =>
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       ! sampled_bounded_keygen_then_one_more_good
           fuel0
           SampledBoundedKeygenDecisionThenOneMore.raw_current
           res] <=
  delta_bounded_keygen_progress (fuel0 + 1).
proof.
move=> hfuel.
have hgood :
  1%r - delta_bounded_keygen_progress (fuel0 + 1) <=
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       sampled_bounded_keygen_then_one_more_good
         fuel0
         SampledBoundedKeygenDecisionThenOneMore.raw_current
         res].
+ by byphoare
    (sampled_bounded_keygen_then_one_more_good_mass fuel0) => //.
have hpartition :
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       sampled_bounded_keygen_then_one_more_good
         fuel0
         SampledBoundedKeygenDecisionThenOneMore.raw_current
         res] +
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       ! sampled_bounded_keygen_then_one_more_good
           fuel0
           SampledBoundedKeygenDecisionThenOneMore.raw_current
           res] =
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m : true].
+ rewrite Pr[mu_not].
  ring.
have htotal_le :
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m : true]
  <= 1%r.
+ by rewrite Pr[mu_le1].
have hdelta := delta_bounded_keygen_progress_bounded (fuel0 + 1).
smt().
qed.

lemma sampled_bounded_keygen_then_one_more_exhaustion_le
    fuel0 &m :
  0 <= fuel0 =>
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       sampled_bounded_keygen_pair_rejected_tail_exhausted
         SampledBoundedKeygenDecisionThenOneMore.raw_current
         (fuel0 + 1) res.`2] <=
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       sampled_bounded_keygen_pair_rejected_tail_exhausted
         SampledBoundedKeygenDecisionThenOneMore.raw_current
         fuel0 res.`1] +
  delta_bounded_keygen_progress (fuel0 + 1).
proof.
move=> hfuel.
have hbad :=
  sampled_bounded_keygen_then_one_more_bad_mass_le fuel0 &m hfuel.
apply
  (ler_trans
    (Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       sampled_bounded_keygen_pair_rejected_tail_exhausted
         SampledBoundedKeygenDecisionThenOneMore.raw_current
         fuel0 res.`1 \/
       ! sampled_bounded_keygen_then_one_more_good
           fuel0
           SampledBoundedKeygenDecisionThenOneMore.raw_current
           res])).
+ rewrite Pr[mu_sub].
  move=> &hr hlarge.
  case
    (sampled_bounded_keygen_then_one_more_good fuel0
      SampledBoundedKeygenDecisionThenOneMore.raw_current{hr}
      res{hr}) => hgood.
  + left.
    move: hgood => [_ [_ [_ hmono]]].
    exact (hmono hlarge).
  + by right.
trivial.
rewrite Pr[mu_or].
have hinter :
  0%r <=
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       sampled_bounded_keygen_pair_rejected_tail_exhausted
         SampledBoundedKeygenDecisionThenOneMore.raw_current
         fuel0 res.`1 /\
       ! sampled_bounded_keygen_then_one_more_good
           fuel0
           SampledBoundedKeygenDecisionThenOneMore.raw_current
           res].
+ by rewrite Pr[mu_ge0].
smt().
qed.

lemma checked_mode2_bounded_keygen_decision_observer_first
    (small0 : checked_mode2_bounded_keygen_decision_result) :
  hoare [CheckedMode2BoundedKeygenDecisionOneMoreObserver.run :
    small = small0
    ==>
    res.`1 = small0].
proof.
proc.
if.
+ wp.
  call (_ : true).
  + auto.
  + auto.
+ auto.
qed.

lemma checked_mode2_bounded_keygen_decision_observer_false0
    (small0 : checked_mode2_bounded_keygen_decision_result) :
  phoare [CheckedMode2BoundedKeygenDecisionOneMoreObserver.run :
    small = small0 ==> false] = 0%r.
proof.
bypr=> &m hpre.
by rewrite Pr[mu_false].
qed.

lemma checked_mode2_bounded_keygen_decision_observer_first_event_zero
    (small0 : checked_mode2_bounded_keygen_decision_result) P :
  phoare [CheckedMode2BoundedKeygenDecisionOneMoreObserver.run :
    small = small0 /\ ! P small0
    ==>
    P res.`1] = 0%r.
proof.
conseq
  (checked_mode2_bounded_keygen_decision_observer_false0 small0)
  (checked_mode2_bounded_keygen_decision_observer_first small0) => //=.
smt().
qed.

lemma sampled_bounded_keygen_decision_self :
  equiv [SampledDecision.main ~ SampledDecision.main :
    ={arg}
    ==>
    SampledDecision.raw_current{1} = SampledDecision.raw_current{2} /\
    ={res}].
proof.
proc.
seq 1 1 :
  (SampledDecision.raw_current{1} = SampledDecision.raw_current{2} /\
   fuel{1} = fuel{2}).
+ rnd.
  auto.
+ call checked_mode2_bounded_keygen_decision_self.
  auto.
qed.

lemma sampled_bounded_keygen_decision_event_exact
    fuel0 &m P :
  phoare [SampledDecision.main :
    arg = fuel0
    ==>
    P SampledDecision.raw_current res] =
  Pr[SampledDecision.main(fuel0) @ &m :
       P SampledDecision.raw_current res].
proof.
bypr=> &m0 hpre.
byequiv sampled_bounded_keygen_decision_self => //=.
qed.

lemma sampled_bounded_keygen_prefix_small_mass_le
    fuel0 &m P :
  Pr[SampledBoundedKeygenDecisionPrefixThenOneMore.main(fuel0) @ &m :
       P SampledBoundedKeygenDecisionPrefixThenOneMore.raw_current
         res.`1] <=
  Pr[SampledDecision.main(fuel0) @ &m :
       P SampledDecision.raw_current res].
proof.
byphoare
  (_ : fuel = fuel0 ==>
       P SampledBoundedKeygenDecisionPrefixThenOneMore.raw_current
         res.`1) => //=.
proc.
seq 1 :
  (P SampledDecision.raw_current small)
  (Pr[SampledDecision.main(fuel0) @ &m :
       P SampledDecision.raw_current res])
  1%r _ 0%r => //=.
+ conseq
    (: _ : =
      Pr[SampledDecision.main(fuel0) @ &m :
           P SampledDecision.raw_current res]) => //=.
  call (sampled_bounded_keygen_decision_event_exact fuel0 &m P).
  auto.
+ auto.
+ sp 1.
  exlim SampledBoundedKeygenDecisionPrefixThenOneMore.raw_current => raw0.
  exlim small => small0.
  conseq (: _ : = 0%r) => //=.
  call
    (checked_mode2_bounded_keygen_decision_observer_first_event_zero
      small0 (fun result => P raw0 result)).
  auto.
qed.

lemma sampled_bounded_keygen_pair_small_mass_le
    fuel0 &m P :
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       P SampledBoundedKeygenDecisionThenOneMore.raw_current res.`1] <=
  Pr[SampledDecision.main(fuel0) @ &m :
       P SampledDecision.raw_current res].
proof.
have hfixed :
  Pr[SampledBoundedKeygenDecisionThenOneMore.main(fuel0) @ &m :
       P SampledBoundedKeygenDecisionThenOneMore.raw_current res.`1] =
  Pr[SampledBoundedKeygenDecisionFixedPrefixThenOneMore.main(fuel0) @ &m :
       P SampledBoundedKeygenDecisionFixedPrefixThenOneMore.raw_current
         res.`1].
+ by byequiv sampled_bounded_keygen_pair_fixed_prefix_equiv => //=.
have hprefix :
  Pr[SampledBoundedKeygenDecisionFixedPrefixThenOneMore.main(fuel0) @ &m :
       P SampledBoundedKeygenDecisionFixedPrefixThenOneMore.raw_current
         res.`1] =
  Pr[SampledBoundedKeygenDecisionPrefixThenOneMore.main(fuel0) @ &m :
       P SampledBoundedKeygenDecisionPrefixThenOneMore.raw_current res.`1].
+ by byequiv sampled_bounded_keygen_fixed_prefix_direct_equiv => //=.
rewrite hfixed hprefix.
exact (sampled_bounded_keygen_prefix_small_mass_le fuel0 &m P).
qed.

lemma sampled_bounded_keygen_rejected_tail_exhaustion_mass_prefix
    fuel0 &m :
  0 <= fuel0 =>
  Pr[SampledDecision.main(fuel0 + 1) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledDecision.raw_current (fuel0 + 1) res] <=
  Pr[SampledDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledDecision.raw_current fuel0 res] +
  delta_bounded_keygen_progress (fuel0 + 1).
proof.
move=> hfuel.
have hlarge :=
  sampled_bounded_keygen_decision_large_marginal_eq
    fuel0 &m
    (fun raw result =>
      sampled_bounded_keygen_pair_rejected_tail_exhausted
        raw (fuel0 + 1) result) hfuel.
have hpair :=
  sampled_bounded_keygen_then_one_more_exhaustion_le
    fuel0 &m hfuel.
have hsmall :=
  sampled_bounded_keygen_pair_small_mass_le
    fuel0 &m
    (fun raw result =>
      sampled_bounded_keygen_pair_rejected_tail_exhausted
        raw fuel0 result).
have hlarge_event :
  Pr[SampledDecision.main(fuel0 + 1) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledDecision.raw_current (fuel0 + 1) res] =
  Pr[SampledDecision.main(fuel0 + 1) @ &m :
       sampled_bounded_keygen_pair_rejected_tail_exhausted
         SampledDecision.raw_current (fuel0 + 1) res].
+ rewrite Pr[mu_eq].
  move=> &hr.
  by rewrite sampled_bounded_keygen_rejected_tail_exhaustedE.
  done.
have hsmall_event :
  Pr[SampledDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_pair_rejected_tail_exhausted
         SampledDecision.raw_current fuel0 res] =
  Pr[SampledDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledDecision.raw_current fuel0 res].
+ rewrite Pr[mu_eq].
  move=> &hr.
  by rewrite sampled_bounded_keygen_rejected_tail_exhaustedE.
  done.
rewrite hlarge_event hlarge.
smt().
qed.

end Mode2FaithfulSecuritySampledBoundedKeygenExhaustionMonotonicityPostFreeze.
