require import AllCore Distr List Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32 KeygenMode2ParentSpec.
require import HAETAE_Distributions.
require import TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecurityRawSeedDistributionPostFreeze
               Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
               Mode2FaithfulSecurityBoundedRetryTailPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze.

theory Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.

import RealOrder.
import HAETAE_Distributions.
import TargetKeygenM23FullFirstAttempt.

(* This file lifts the proof-only bounded keygen decision over the sampled
   raw-seed distribution with fixed zero scratch arrays.  It records only the
   conditional supported mass of that bounded decision and a sound outcome
   partition for executions satisfying the proved entry postcondition.  It does
   not claim a universal witness family, sampled numeric accept bounds,
   last-tail semantic witnesses, unbounded termination, packing, full key
   generation, or equality with [HAETAE.kg]. *)

type bounded_keygen_progress_witness =
  ((int -> int -> int) * (int -> int) * (int -> int)) *
  (int -> int -> int).

op bounded_keygen_prefix_witness
    (w : bounded_keygen_progress_witness) :
    (int -> int -> int) * (int -> int) * (int -> int) =
  w.`1.

op bounded_keygen_tail_window
    (w : bounded_keygen_progress_witness) : int -> int -> int =
  w.`2.

op bounded_keygen_progress_witness_valid
    (raw : BArray32.t) fuel0
    (w : bounded_keygen_progress_witness) : bool =
  KeygenMode2ParentSpec.mode2_sampler_prefix_progress
    raw
    (bounded_keygen_prefix_witness w).`1
    (bounded_keygen_prefix_witness w).`2
    (bounded_keygen_prefix_witness w).`3 /\
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .checked_first_reject_window_ready
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw fuel0 (bounded_keygen_tail_window w).

op raw_seed_has_bounded_keygen_progress
    (raw : BArray32.t) fuel0 : bool =
  exists w, bounded_keygen_progress_witness_valid raw fuel0 w.

op selected_bounded_keygen_progress_witness
    (raw : BArray32.t) fuel0 : bounded_keygen_progress_witness =
  choiceb (bounded_keygen_progress_witness_valid raw fuel0) witness.

lemma selected_bounded_keygen_progress_witness_valid raw fuel0 :
  raw_seed_has_bounded_keygen_progress raw fuel0 =>
  bounded_keygen_progress_witness_valid raw fuel0
    (selected_bounded_keygen_progress_witness raw fuel0).
proof.
rewrite /raw_seed_has_bounded_keygen_progress
        /selected_bounded_keygen_progress_witness.
exact (choicebP (bounded_keygen_progress_witness_valid raw fuel0) witness).
qed.

op delta_bounded_keygen_progress fuel0 : real =
  mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    (predC (fun raw => raw_seed_has_bounded_keygen_progress raw fuel0)).

lemma delta_bounded_keygen_progress_bounded fuel0 :
  0%r <= delta_bounded_keygen_progress fuel0 <= 1%r.
proof.
rewrite /delta_bounded_keygen_progress.
exact mu_bounded.
qed.

lemma raw_seed_bounded_keygen_good_massE fuel0 :
  mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    (fun raw => raw_seed_has_bounded_keygen_progress raw fuel0) =
  1%r - delta_bounded_keygen_progress fuel0.
proof.
have hnot :=
  mu_not Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    (fun raw => raw_seed_has_bounded_keygen_progress raw fuel0).
rewrite /delta_bounded_keygen_progress.
have hloss :=
  Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed_lossless.
move: hnot hloss.
rewrite /is_lossless.
move=> hnot hloss.
rewrite hnot hloss.
ring.
qed.

module SampledBoundedKeygenDecision = {
  var raw_current : BArray32.t

  proc main (fuel : int) :
    Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
      .checked_mode2_bounded_keygen_decision_result = {
    var result :
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .checked_mode2_bounded_keygen_decision_result;

    raw_current <$
      Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed;
    result <@
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .CheckedMode2BoundedKeygenDecision.run(
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          raw_current, fuel);
    return result;
  }
}.

lemma checked_bounded_keygen_good_raw_ll
    (raw_init : BArray32.t) fuel0 :
  phoare [Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
            .CheckedMode2BoundedKeygenDecision.run :
    seedbuf =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128 /\
    mat =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768 /\
    avec =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s1 = Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s2 = Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    bp = Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s1hatp =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    raw_seed = raw_init /\ fuel = fuel0 /\ 0 <= fuel0 /\
    raw_seed_has_bounded_keygen_progress raw_init fuel0
    ==>
    Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
      .checked_mode2_bounded_keygen_decision_entry_post
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        raw_init fuel0 res] >= 1%r.
proof.
conseq
  (Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .checked_mode2_bounded_keygen_decision_entry_ll
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_init fuel0
      (bounded_keygen_prefix_witness
        (selected_bounded_keygen_progress_witness raw_init fuel0)).`1
      (bounded_keygen_prefix_witness
        (selected_bounded_keygen_progress_witness raw_init fuel0)).`2
      (bounded_keygen_prefix_witness
        (selected_bounded_keygen_progress_witness raw_init fuel0)).`3
      (bounded_keygen_tail_window
        (selected_bounded_keygen_progress_witness raw_init fuel0))) => //=.
move=> &hr
  [hseed [hmat [havec [hs1 [hs2 [hbp
    [hs1hat [hraw [hfueleq [hfuel hgood]]]]]]]]]].
have hselected :=
  selected_bounded_keygen_progress_witness_valid raw_init fuel0 hgood.
move: hselected => [hprefix hwindow].
smt().
qed.

lemma sampled_bounded_keygen_entry_post_progress_mass fuel0 :
  phoare [SampledBoundedKeygenDecision.main :
    arg = fuel0 /\ 0 <= fuel0
    ==>
    Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
      .checked_mode2_bounded_keygen_decision_entry_post
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        SampledBoundedKeygenDecision.raw_current fuel0 res] >=
  (mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    (fun raw => raw_seed_has_bounded_keygen_progress raw fuel0)).
proof.
proc.
seq 1 :
  (fuel = fuel0 /\ 0 <= fuel0 /\
   raw_seed_has_bounded_keygen_progress
     SampledBoundedKeygenDecision.raw_current fuel0)
  (mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
     (fun raw => raw_seed_has_bounded_keygen_progress raw fuel0))
  1%r 0%r _ => //=.
+ rnd (fun raw => raw_seed_has_bounded_keygen_progress raw fuel0).
   auto.
wp.
exlim SampledBoundedKeygenDecision.raw_current => raw0.
call (checked_bounded_keygen_good_raw_ll raw0 fuel0).
auto => />.
qed.

lemma sampled_bounded_keygen_entry_post_mass fuel0 :
  phoare [SampledBoundedKeygenDecision.main :
    arg = fuel0 /\ 0 <= fuel0
    ==>
    Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
      .checked_mode2_bounded_keygen_decision_entry_post
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        SampledBoundedKeygenDecision.raw_current fuel0 res] >=
  (1%r - delta_bounded_keygen_progress fuel0).
proof.
rewrite -raw_seed_bounded_keygen_good_massE.
exact sampled_bounded_keygen_entry_post_progress_mass.
qed.

lemma sampled_bounded_keygen_termination_mass fuel0 :
  phoare [SampledBoundedKeygenDecision.main :
    arg = fuel0 /\ 0 <= fuel0 ==> true] >=
  (1%r - delta_bounded_keygen_progress fuel0).
proof.
conseq (sampled_bounded_keygen_entry_post_mass fuel0) => //=.
qed.

op sampled_bounded_keygen_first_accept
    (raw_seed0 : BArray32.t) fuel0
    (result :
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .checked_mode2_bounded_keygen_decision_result) : bool =
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .checked_mode2_bounded_keygen_decision_entry_post
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0 fuel0 result /\
  first_attempt_trace_accepted result.`1.

op sampled_bounded_keygen_rejected_tail_accept
    (raw_seed0 : BArray32.t) fuel0
    (result :
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .checked_mode2_bounded_keygen_decision_result) : bool =
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .checked_mode2_bounded_keygen_decision_entry_post
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0 fuel0 result /\
  ! first_attempt_trace_accepted result.`1 /\
  result.`3.`9 = W64.zero.

op sampled_bounded_keygen_rejected_tail_exhausted
    (raw_seed0 : BArray32.t) fuel0
    (result :
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .checked_mode2_bounded_keygen_decision_result) : bool =
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .checked_mode2_bounded_keygen_decision_entry_post
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0 fuel0 result /\
  ! first_attempt_trace_accepted result.`1 /\
  result.`3.`9 = W64.one /\
  result.`3.`11 = fuel0.

op sampled_bounded_keygen_outcome_union
    (raw_seed0 : BArray32.t) fuel0
    (result :
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .checked_mode2_bounded_keygen_decision_result) : bool =
  sampled_bounded_keygen_first_accept raw_seed0 fuel0 result \/
  sampled_bounded_keygen_rejected_tail_accept raw_seed0 fuel0 result \/
  sampled_bounded_keygen_rejected_tail_exhausted raw_seed0 fuel0 result.

lemma checked_mode2_bounded_keygen_entry_outcome_partition
    (raw_seed0 : BArray32.t) fuel0
    (result :
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .checked_mode2_bounded_keygen_decision_result) :
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .checked_mode2_bounded_keygen_decision_entry_post
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0 fuel0 result =>
  sampled_bounded_keygen_first_accept raw_seed0 fuel0 result \/
  sampled_bounded_keygen_rejected_tail_accept raw_seed0 fuel0 result \/
  sampled_bounded_keygen_rejected_tail_exhausted raw_seed0 fuel0 result.
proof.
move=> hentry.
rewrite /sampled_bounded_keygen_first_accept
        /sampled_bounded_keygen_rejected_tail_accept
        /sampled_bounded_keygen_rejected_tail_exhausted.
have hpost :
    Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
      .checked_mode2_bounded_keygen_decision_post
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
        raw_seed0 fuel0 result.
+ move: hentry.
   rewrite
     /Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
       .checked_mode2_bounded_keygen_decision_entry_post.
   smt().
case: (first_attempt_trace_accepted result.`1) => haccept.
+ left.
   smt().
right.
move: hpost.
rewrite
  /Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .checked_mode2_bounded_keygen_decision_post haccept /=
  /Mode2FaithfulSecurityBoundedRetryTailPostFreeze
    .checked_mode2_bounded_retry_tail_post.
smt().
qed.

lemma checked_mode2_bounded_keygen_entry_outcomes_pairwise_disjoint
    (raw_seed0 : BArray32.t) fuel0
    (result :
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .checked_mode2_bounded_keygen_decision_result) :
  ! (sampled_bounded_keygen_first_accept raw_seed0 fuel0 result /\
     sampled_bounded_keygen_rejected_tail_accept raw_seed0 fuel0 result) /\
  ! (sampled_bounded_keygen_first_accept raw_seed0 fuel0 result /\
     sampled_bounded_keygen_rejected_tail_exhausted raw_seed0 fuel0 result) /\
  ! (sampled_bounded_keygen_rejected_tail_accept raw_seed0 fuel0 result /\
     sampled_bounded_keygen_rejected_tail_exhausted raw_seed0 fuel0 result).
proof.
rewrite /sampled_bounded_keygen_first_accept
        /sampled_bounded_keygen_rejected_tail_accept
        /sampled_bounded_keygen_rejected_tail_exhausted.
smt().
qed.

lemma checked_mode2_bounded_keygen_entry_outcome_unionE
    (raw_seed0 : BArray32.t) fuel0
    (result :
      Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
        .checked_mode2_bounded_keygen_decision_result) :
  Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
    .checked_mode2_bounded_keygen_decision_entry_post
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw_seed0 fuel0 result <=>
  sampled_bounded_keygen_outcome_union raw_seed0 fuel0 result.
proof.
rewrite /sampled_bounded_keygen_outcome_union.
split.
+ exact
    (checked_mode2_bounded_keygen_entry_outcome_partition
      raw_seed0 fuel0 result).
rewrite /sampled_bounded_keygen_first_accept
        /sampled_bounded_keygen_rejected_tail_accept
        /sampled_bounded_keygen_rejected_tail_exhausted.
smt().
qed.

lemma sampled_bounded_keygen_outcome_union_mass fuel0 :
  phoare [SampledBoundedKeygenDecision.main :
    arg = fuel0 /\ 0 <= fuel0
    ==>
    sampled_bounded_keygen_outcome_union
      SampledBoundedKeygenDecision.raw_current fuel0 res] >=
  (1%r - delta_bounded_keygen_progress fuel0).
proof.
conseq (sampled_bounded_keygen_entry_post_mass fuel0) => //=.
move=> &hr hpre result raw_current hentry.
exact
  (checked_mode2_bounded_keygen_entry_outcome_partition
    raw_current fuel0 result hentry).
qed.

lemma sampled_bounded_keygen_entry_outcome_mass_partition fuel0 &m :
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_first_accept
         SampledBoundedKeygenDecision.raw_current fuel0 res] +
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_accept
         SampledBoundedKeygenDecision.raw_current fuel0 res] +
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledBoundedKeygenDecision.raw_current fuel0 res] =
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
         .checked_mode2_bounded_keygen_decision_entry_post
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           SampledBoundedKeygenDecision.raw_current fuel0 res].
proof.
have hentry_union :
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
         .checked_mode2_bounded_keygen_decision_entry_post
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           SampledBoundedKeygenDecision.raw_current fuel0 res] =
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_outcome_union
         SampledBoundedKeygenDecision.raw_current fuel0 res].
+ rewrite Pr[mu_eq].
  move=> &hr.
  exact
    (checked_mode2_bounded_keygen_entry_outcome_unionE
      SampledBoundedKeygenDecision.raw_current{hr} fuel0 res{hr}).
  done.
rewrite hentry_union.
rewrite /sampled_bounded_keygen_outcome_union.
rewrite Pr[mu_disjoint].
+ move=> &hr.
  have hdisjoint :=
    checked_mode2_bounded_keygen_entry_outcomes_pairwise_disjoint
      SampledBoundedKeygenDecision.raw_current{hr} fuel0 res{hr}.
  smt().
rewrite Pr[mu_disjoint].
+ move=> &hr.
  have hdisjoint :=
    checked_mode2_bounded_keygen_entry_outcomes_pairwise_disjoint
      SampledBoundedKeygenDecision.raw_current{hr} fuel0 res{hr}.
  smt().
ring.
qed.

lemma sampled_bounded_keygen_additive_outcome_mass_bound fuel0 &m :
  0 <= fuel0 =>
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_first_accept
         SampledBoundedKeygenDecision.raw_current fuel0 res] +
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_accept
         SampledBoundedKeygenDecision.raw_current fuel0 res] +
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_exhausted
         SampledBoundedKeygenDecision.raw_current fuel0 res] >=
  (1%r - delta_bounded_keygen_progress fuel0).
proof.
move=> hfuel.
have hentry_mass :
  Pr[SampledBoundedKeygenDecision.main(fuel0) @ &m :
       Mode2FaithfulSecurityBoundedKeygenDecisionPostFreeze
         .checked_mode2_bounded_keygen_decision_entry_post
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           SampledBoundedKeygenDecision.raw_current fuel0 res] >=
  (1%r - delta_bounded_keygen_progress fuel0).
+ by byphoare (sampled_bounded_keygen_entry_post_mass fuel0) => //.
have hpartition :=
  sampled_bounded_keygen_entry_outcome_mass_partition fuel0 &m.
smt().
qed.

end Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.
