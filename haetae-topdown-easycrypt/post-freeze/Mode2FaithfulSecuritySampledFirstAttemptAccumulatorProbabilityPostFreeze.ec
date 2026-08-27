require import AllCore Distr FSet Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32 BArray8192 BArray32768.
require import
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorProbability
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety
  KeygenM23FinalizeArraySemantics
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23SingularFFTInputBounds
  TargetKeygenM23FirstAttemptAccumulator
  TargetKeygenM23FirstAttemptAccumulatorProbability
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptDSeedScoreTailPostFreeze.

import RealOrder.
import Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.
import
  KeygenM23SingularFFTAccumulatorProbability
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety
  TargetKeygenM23SingularFFTInputBounds
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23FirstAttemptAccumulator
  TargetKeygenM23FirstAttemptAccumulatorProbability.

theory Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze.

module SampledFirst =
  Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze
    .SampledFirstAttemptDecision.

module SampledDSeed =
  Mode2FaithfulSecuritySampledFirstAttemptDSeedScoreTailPostFreeze
    .SampledDSeedFirstAttemptDecision.

(* This layer lifts the existing finite accumulator union bound to the actual
   dseed-sampled first-attempt program.  It leaves all four local marginal
   tails symbolic and does not claim a numeric keygen rejection rate, a
   score-tail/headroom inclusion, retry termination, or HAETAE.kg equality. *)

op sampled_dseed_first_attempt_accumulator_sample
    (trace : first_attempt_trace) : mode2_accumulator_sample =
  first_attempt_trace_accumulator_sample trace.

op sampled_dseed_first_attempt_prefix_lower_bad_at
    (trace : first_attempt_trace) (processed j : int) : bool =
  mode2_accumulator_prefix_lower_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) processed j.

op sampled_dseed_first_attempt_prefix_upper_bad_at
    (trace : first_attempt_trace) (processed j : int) : bool =
  mode2_accumulator_prefix_upper_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) processed j.

op sampled_dseed_first_attempt_prefix_headroom_bad_at
    (trace : first_attempt_trace) (processed j : int) : bool =
  mode2_accumulator_prefix_headroom_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) processed j.

op sampled_dseed_first_attempt_coordinate_real_bad_at
    (trace : first_attempt_trace) (slot j : int) : bool =
  mode2_accumulator_coordinate_real_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) slot j.

op sampled_dseed_first_attempt_coordinate_imag_bad_at
    (trace : first_attempt_trace) (slot j : int) : bool =
  mode2_accumulator_coordinate_imag_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) slot j.

op sampled_dseed_first_attempt_coordinate_headroom_bad_at
    (trace : first_attempt_trace) (slot j : int) : bool =
  mode2_accumulator_coordinate_headroom_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) slot j.

op sampled_dseed_first_attempt_prefix_headroom_bad
    (trace : first_attempt_trace) : bool =
  mode2_accumulator_prefix_headroom_bad
    (sampled_dseed_first_attempt_accumulator_sample trace).

op sampled_dseed_first_attempt_coordinate_headroom_bad
    (trace : first_attempt_trace) : bool =
  mode2_accumulator_coordinate_headroom_bad
    (sampled_dseed_first_attempt_accumulator_sample trace).

op sampled_dseed_first_attempt_headroom_family_union
    (trace : first_attempt_trace) : bool =
  sampled_dseed_first_attempt_prefix_headroom_bad trace \/
  sampled_dseed_first_attempt_coordinate_headroom_bad trace.

lemma sampled_dseed_first_attempt_trace_event_pr
    (E : first_attempt_trace -> bool) &m :
  Pr[SampledDSeed.main() @ &m : E res] =
  Pr[SampledFirst.main() @ &m : E res].
proof.
byequiv
  Mode2FaithfulSecuritySampledFirstAttemptDSeedScoreTailPostFreeze
    .sampled_dseed_first_attempt_score_tail_equiv => //=.
qed.

lemma sampled_dseed_first_attempt_prefix_lower_bad_atE trace processed j :
  sampled_dseed_first_attempt_prefix_lower_bad_at trace processed j =
  mode2_accumulator_prefix_lower_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) processed j.
proof. done. qed.

lemma sampled_dseed_first_attempt_prefix_upper_bad_atE trace processed j :
  sampled_dseed_first_attempt_prefix_upper_bad_at trace processed j =
  mode2_accumulator_prefix_upper_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) processed j.
proof. done. qed.

lemma sampled_dseed_first_attempt_prefix_headroom_bad_atE
    trace processed j :
  sampled_dseed_first_attempt_prefix_headroom_bad_at trace processed j =
  mode2_accumulator_prefix_headroom_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) processed j.
proof. done. qed.

lemma sampled_dseed_first_attempt_coordinate_real_bad_atE trace slot j :
  sampled_dseed_first_attempt_coordinate_real_bad_at trace slot j =
  mode2_accumulator_coordinate_real_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) slot j.
proof. done. qed.

lemma sampled_dseed_first_attempt_coordinate_imag_bad_atE trace slot j :
  sampled_dseed_first_attempt_coordinate_imag_bad_at trace slot j =
  mode2_accumulator_coordinate_imag_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) slot j.
proof. done. qed.

lemma sampled_dseed_first_attempt_coordinate_headroom_bad_atE
    trace slot j :
  sampled_dseed_first_attempt_coordinate_headroom_bad_at trace slot j =
  mode2_accumulator_coordinate_headroom_bad_at
    (sampled_dseed_first_attempt_accumulator_sample trace) slot j.
proof. done. qed.

lemma sampled_dseed_first_attempt_prefix_headroom_badE trace :
  sampled_dseed_first_attempt_prefix_headroom_bad trace =
  mode2_accumulator_prefix_headroom_bad
    (sampled_dseed_first_attempt_accumulator_sample trace).
proof. done. qed.

lemma sampled_dseed_first_attempt_coordinate_headroom_badE trace :
  sampled_dseed_first_attempt_coordinate_headroom_bad trace =
  mode2_accumulator_coordinate_headroom_bad
    (sampled_dseed_first_attempt_accumulator_sample trace).
proof. done. qed.

lemma sampled_dseed_first_attempt_accumulator_headroom_bad_cover trace :
  first_attempt_trace_accumulator_headroom_bad trace =>
  sampled_dseed_first_attempt_prefix_headroom_bad trace \/
  sampled_dseed_first_attempt_coordinate_headroom_bad trace.
proof.
move=> hbad.
rewrite sampled_dseed_first_attempt_prefix_headroom_badE
        sampled_dseed_first_attempt_coordinate_headroom_badE.
rewrite first_attempt_trace_accumulator_headroom_badE in hbad.
exact (mode2_accumulator_headroom_bad_event_cover _ hbad).
qed.

lemma sampled_dseed_first_attempt_fset_trace_bad_pr_le
    (s : (int * int) fset)
    (p : (int * int) -> first_attempt_trace -> bool)
    (bd : real) &m :
  (forall ij, ij \in s =>
    Pr[SampledDSeed.main() @ &m : p ij res] <= bd) =>
  Pr[SampledDSeed.main() @ &m :
       exists ij, ij \in s /\ p ij res] <=
    (card s)%r * bd.
proof.
elim/fset_ind: s.
+ have -> :
    Pr[SampledDSeed.main() @ &m :
         exists ij, ij \in fset0 /\ p ij res] =
    Pr[SampledDSeed.main() @ &m : false].
  + rewrite Pr[mu_eq] => //.
    by move=> &hr; smt(in_fset0).
  by rewrite Pr[mu_false] fcards0.
move=> ij s hijfresh ih hbd.
have -> :
  Pr[SampledDSeed.main() @ &m :
       exists ij0, ij0 \in (s `|` fset1 ij) /\ p ij0 res] =
  Pr[SampledDSeed.main() @ &m :
       p ij res \/
       (exists ij0, ij0 \in s /\ p ij0 res)].
+ rewrite Pr[mu_eq] => //.
  move=> &hr.
  by split; smt(in_fsetU1 in_fset1).
rewrite Pr[mu_or].
have hinter :
    0%r <=
    Pr[SampledDSeed.main() @ &m :
         p ij res /\
         (exists ij0, ij0 \in s /\ p ij0 res)].
+ by rewrite Pr[mu_ge0].
have hijbd :
    Pr[SampledDSeed.main() @ &m : p ij res] <= bd.
+ apply hbd.
  by rewrite in_fsetU1.
have hsbd :
    Pr[SampledDSeed.main() @ &m :
         exists ij0, ij0 \in s /\ p ij0 res] <=
    (card s)%r * bd.
+ apply ih => ij0 hij0.
  have hij0U : ij0 \in (s `|` fset1 ij).
  + by rewrite in_fsetU1 hij0.
  exact (hbd ij0 hij0U).
rewrite fcardU1 hijfresh /b2i /=.
smt().
qed.

lemma sampled_dseed_first_attempt_prefix_headroom_bad_at_pr_le_split
    processed j delta_lower delta_upper &m :
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_prefix_lower_bad_at
         res processed j] <= delta_lower =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_prefix_upper_bad_at
         res processed j] <= delta_upper =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_prefix_headroom_bad_at
         res processed j] <=
    delta_lower + delta_upper.
proof.
move=> hlower hupper.
move: hlower; rewrite /sampled_dseed_first_attempt_prefix_lower_bad_at
  => hlower.
move: hupper; rewrite /sampled_dseed_first_attempt_prefix_upper_bad_at
  => hupper.
rewrite /sampled_dseed_first_attempt_prefix_headroom_bad_at
        /mode2_accumulator_prefix_headroom_bad_at.
rewrite Pr[mu_or].
have hinter :
    0%r <=
    Pr[SampledDSeed.main() @ &m :
         mode2_accumulator_prefix_lower_bad_at
           (sampled_dseed_first_attempt_accumulator_sample res)
           processed j /\
         mode2_accumulator_prefix_upper_bad_at
           (sampled_dseed_first_attempt_accumulator_sample res)
           processed j].
+ by rewrite Pr[mu_ge0].
smt().
qed.

lemma sampled_dseed_first_attempt_coordinate_headroom_bad_at_pr_le_split
    slot j delta_real delta_imag &m :
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_coordinate_real_bad_at
         res slot j] <= delta_real =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_coordinate_imag_bad_at
         res slot j] <= delta_imag =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_coordinate_headroom_bad_at
         res slot j] <=
    delta_real + delta_imag.
proof.
move=> hreal himag.
move: hreal; rewrite /sampled_dseed_first_attempt_coordinate_real_bad_at
  => hreal.
move: himag; rewrite /sampled_dseed_first_attempt_coordinate_imag_bad_at
  => himag.
rewrite /sampled_dseed_first_attempt_coordinate_headroom_bad_at
        /mode2_accumulator_coordinate_headroom_bad_at.
rewrite Pr[mu_or].
have hinter :
    0%r <=
    Pr[SampledDSeed.main() @ &m :
         mode2_accumulator_coordinate_real_bad_at
           (sampled_dseed_first_attempt_accumulator_sample res)
           slot j /\
         mode2_accumulator_coordinate_imag_bad_at
           (sampled_dseed_first_attempt_accumulator_sample res)
           slot j].
+ by rewrite Pr[mu_ge0].
smt().
qed.

lemma sampled_dseed_first_attempt_prefix_headroom_bad_pr_le
    delta_lower delta_upper &m :
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_lower_bad_at
           res processed j] <= delta_lower) =>
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_upper_bad_at
           res processed j] <= delta_upper) =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_prefix_headroom_bad res] <=
    1536%r * (delta_lower + delta_upper).
proof.
move=> hlower hupper.
rewrite /sampled_dseed_first_attempt_prefix_headroom_bad.
rewrite -mode2_prefix_site_set_card.
apply (sampled_dseed_first_attempt_fset_trace_bad_pr_le
         mode2_prefix_site_set
         (fun (ij : int * int) trace =>
           sampled_dseed_first_attempt_prefix_headroom_bad_at
             trace ij.`1 ij.`2)
         (delta_lower + delta_upper) &m).
move=> ij hij.
case: ij hij => processed j hij /=.
move: hij.
rewrite mode2_prefix_site_set_mem.
move=> [hprocessed hj].
apply
  (sampled_dseed_first_attempt_prefix_headroom_bad_at_pr_le_split
     processed j delta_lower delta_upper &m).
+ exact (hlower processed j hprocessed hj).
exact (hupper processed j hprocessed hj).
qed.

lemma sampled_dseed_first_attempt_coordinate_headroom_bad_pr_le
    delta_real delta_imag &m :
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_coordinate_real_bad_at
           res slot j] <= delta_real) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_coordinate_imag_bad_at
           res slot j] <= delta_imag) =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_coordinate_headroom_bad res] <=
    1280%r * (delta_real + delta_imag).
proof.
move=> hreal himag.
rewrite /sampled_dseed_first_attempt_coordinate_headroom_bad.
rewrite -mode2_coordinate_site_set_card.
apply (sampled_dseed_first_attempt_fset_trace_bad_pr_le
         mode2_coordinate_site_set
         (fun (ij : int * int) trace =>
           sampled_dseed_first_attempt_coordinate_headroom_bad_at
             trace ij.`1 ij.`2)
         (delta_real + delta_imag) &m).
move=> ij hij.
case: ij hij => slot j hij /=.
move: hij.
rewrite mode2_coordinate_site_set_mem.
move=> [hslot hj].
apply
  (sampled_dseed_first_attempt_coordinate_headroom_bad_at_pr_le_split
     slot j delta_real delta_imag &m).
+ exact (hreal slot j hslot hj).
exact (himag slot j hslot hj).
qed.

lemma sampled_dseed_first_attempt_headroom_families_pr_or_le &m :
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_headroom_family_union res] <=
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_prefix_headroom_bad res] +
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_coordinate_headroom_bad res].
proof.
rewrite /sampled_dseed_first_attempt_headroom_family_union Pr[mu_or].
have hinter :
    0%r <=
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_headroom_bad res /\
         sampled_dseed_first_attempt_coordinate_headroom_bad res].
+ by rewrite Pr[mu_ge0].
smt().
qed.

lemma sampled_dseed_first_attempt_headroom_pr_chain x y &m :
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res] <=
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_headroom_family_union res] =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_headroom_family_union res] <=
    Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_prefix_headroom_bad res] +
    Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_coordinate_headroom_bad res] =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_prefix_headroom_bad res] <= x =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_coordinate_headroom_bad res] <= y =>
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res] <= x + y.
proof.
move=> hcover hunion hprefix hcoord.
have hsum :
    Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_prefix_headroom_bad res] +
    Pr[SampledDSeed.main() @ &m :
       sampled_dseed_first_attempt_coordinate_headroom_bad res] <= x + y.
+ smt().
move: hcover hunion hsum.
smt().
qed.

lemma sampled_dseed_first_attempt_accumulator_headroom_bad_pr_le_split
    delta_lower delta_upper delta_real delta_imag &m :
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_lower_bad_at
           res processed j] <= delta_lower) =>
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_upper_bad_at
           res processed j] <= delta_upper) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_coordinate_real_bad_at
           res slot j] <= delta_real) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_coordinate_imag_bad_at
           res slot j] <= delta_imag) =>
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res] <=
    1536%r * (delta_lower + delta_upper) +
    1280%r * (delta_real + delta_imag).
proof.
move=> hlower hupper hreal himag.
apply
  (sampled_dseed_first_attempt_headroom_pr_chain
    (1536%r * (delta_lower + delta_upper))
    (1280%r * (delta_real + delta_imag)) &m).
+ rewrite /sampled_dseed_first_attempt_headroom_family_union Pr[mu_sub].
  move=> &hr hbad.
  exact
    (sampled_dseed_first_attempt_accumulator_headroom_bad_cover
      res{hr} hbad).
  trivial.
+ apply (sampled_dseed_first_attempt_headroom_families_pr_or_le &m).
+ apply
    (sampled_dseed_first_attempt_prefix_headroom_bad_pr_le
      delta_lower delta_upper &m).
  + exact hlower.
  exact hupper.
+ apply
    (sampled_dseed_first_attempt_coordinate_headroom_bad_pr_le
      delta_real delta_imag &m).
  + exact hreal.
  exact himag.
qed.

lemma checked_first_attempt_snapshot_fft_inputs_bound2
    (raw0 : BArray32.t) (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw0 trace =>
  first_attempt_trace_fft_inputs_bound2 trace.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite
  /checked_first_attempt_snapshot_facts
  /first_attempt_trace_fft_inputs_bound2 /=.
move=> [hsampler [_ [_ [harray _]]]].
exact
  (mode2_fft_inputs_bound2_of_mode2_sampler_finalize
    seedbuf mat avec s1 sampled_s2 counter
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    raw0
    pre_bp final_bp final_s2 hsampler harray).
qed.

lemma checked_first_attempt_snapshot_accumulator_safe_outside_headroom_bad
    (raw0 : BArray32.t) (trace : first_attempt_trace) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw0 trace =>
  ! first_attempt_trace_accumulator_headroom_bad trace =>
  first_attempt_trace_accumulator_safe trace.
proof.
move=> hsnapshot hnotbad.
have hinputs :=
  checked_first_attempt_snapshot_fft_inputs_bound2 raw0 trace hsnapshot.
case: trace hsnapshot hnotbad hinputs =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject /= hsnapshot hnotbad hinputs.
rewrite /first_attempt_trace_accumulator_safe /=.
have hheadroom :
    mode2_accumulator_headroom_trace
      s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i.
+ have hiff :=
    mode2_accumulator_headroom_trace_iff_no_bad_event
      s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i _.
  + rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i.
    smt().
  exact (iffRL _ _ hiff hnotbad).
rewrite /first_attempt_trace_fft_inputs_bound2 in hinputs.
have haccinputs : mode2_accumulator_inputs_bound2 s1 final_s2.
+ move: hinputs.
  rewrite
    /TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
    /mode2_accumulator_inputs_bound2.
  done.
apply
  (mode2_actual_accumulate_safe_from_headroom
    s1 final_s2 KeygenM23SingularFFTSpec.mode2_slice_count_i).
+ rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i.
  smt().
+ done.
+ exact haccinputs.
exact hheadroom.
qed.

lemma checked_first_attempt_snapshot_accumulator_error_outside_headroom_bad
    (raw0 : BArray32.t) (trace : first_attempt_trace) (j : int) :
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw0 trace =>
  ! first_attempt_trace_accumulator_headroom_bad trace =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  first_attempt_trace_accumulator_error_at trace j.
proof.
move=> hsnapshot hnotbad hj.
have hsafe :=
  checked_first_attempt_snapshot_accumulator_safe_outside_headroom_bad
    raw0 trace hsnapshot hnotbad.
have hinputs :=
  checked_first_attempt_snapshot_fft_inputs_bound2 raw0 trace hsnapshot.
case: trace hsnapshot hnotbad hsafe hinputs =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject /=
  hsnapshot hnotbad hsafe hinputs.
rewrite /first_attempt_trace_accumulator_safe in hsafe.
rewrite /first_attempt_trace_accumulator_error_at /=.
rewrite /first_attempt_trace_fft_inputs_bound2 in hinputs.
have haccinputs : mode2_accumulator_inputs_bound2 s1 final_s2.
+ move: hinputs.
  rewrite
    /TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
    /mode2_accumulator_inputs_bound2.
  done.
exact
  (mode2_actual_accumulate_full_error
    s1 final_s2 j hj haccinputs hsafe).
qed.

lemma sampled_dseed_checked_snapshot_accumulator_unsafe_pr_le_headroom_bad
    &m :
  Pr[SampledDSeed.main() @ &m :
       Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
         .checked_first_attempt_snapshot_facts
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           SampledDSeed.raw_current res /\
       ! first_attempt_trace_accumulator_safe res] <=
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res].
proof.
rewrite Pr[mu_sub].
move=> &hr [hsnapshot hunsafe].
case (first_attempt_trace_accumulator_headroom_bad res{hr}) => hbad.
+ trivial.
have hnotbad :
    ! first_attempt_trace_accumulator_headroom_bad res{hr} by
  rewrite hbad.
have hsafe :=
  checked_first_attempt_snapshot_accumulator_safe_outside_headroom_bad
    SampledDSeed.raw_current{hr} res{hr} hsnapshot hnotbad.
smt().
trivial.
qed.

lemma sampled_dseed_checked_snapshot_accumulator_error_failure_pr_le_headroom_bad
    (j : int) &m :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  Pr[SampledDSeed.main() @ &m :
       Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
         .checked_first_attempt_snapshot_facts
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           SampledDSeed.raw_current res /\
       ! first_attempt_trace_accumulator_error_at res j] <=
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res].
proof.
move=> hj.
rewrite Pr[mu_sub].
move=> &hr [hsnapshot herror].
case (first_attempt_trace_accumulator_headroom_bad res{hr}) => hbad.
+ trivial.
have hnotbad :
    ! first_attempt_trace_accumulator_headroom_bad res{hr} by
  rewrite hbad.
have hbound :=
  checked_first_attempt_snapshot_accumulator_error_outside_headroom_bad
    SampledDSeed.raw_current{hr} res{hr} j hsnapshot hnotbad hj.
smt().
trivial.
qed.

lemma sampled_dseed_checked_snapshot_accumulator_unsafe_pr_le_split
    delta_lower delta_upper delta_real delta_imag &m :
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_lower_bad_at
           res processed j] <= delta_lower) =>
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_upper_bad_at
           res processed j] <= delta_upper) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_coordinate_real_bad_at
           res slot j] <= delta_real) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_coordinate_imag_bad_at
           res slot j] <= delta_imag) =>
  Pr[SampledDSeed.main() @ &m :
       Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
         .checked_first_attempt_snapshot_facts
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           SampledDSeed.raw_current res /\
       ! first_attempt_trace_accumulator_safe res] <=
    1536%r * (delta_lower + delta_upper) +
    1280%r * (delta_real + delta_imag).
proof.
move=> hlower hupper hreal himag.
have hunsafe :=
  sampled_dseed_checked_snapshot_accumulator_unsafe_pr_le_headroom_bad &m.
have hheadroom :=
  sampled_dseed_first_attempt_accumulator_headroom_bad_pr_le_split
    delta_lower delta_upper delta_real delta_imag &m
    hlower hupper hreal himag.
exact (ler_trans _ _ _ hunsafe hheadroom).
qed.

lemma sampled_dseed_checked_snapshot_accumulator_error_failure_pr_le_split
    (j : int) delta_lower delta_upper delta_real delta_imag &m :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  (forall processed j0,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j0 < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_lower_bad_at
           res processed j0] <= delta_lower) =>
  (forall processed j0,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j0 < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_prefix_upper_bad_at
           res processed j0] <= delta_upper) =>
  (forall slot j0,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j0 < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_coordinate_real_bad_at
           res slot j0] <= delta_real) =>
  (forall slot j0,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j0 < KeygenM23SingularSpec.singular_words_i =>
    Pr[SampledDSeed.main() @ &m :
         sampled_dseed_first_attempt_coordinate_imag_bad_at
           res slot j0] <= delta_imag) =>
  Pr[SampledDSeed.main() @ &m :
       Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
         .checked_first_attempt_snapshot_facts
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
           SampledDSeed.raw_current res /\
       ! first_attempt_trace_accumulator_error_at res j] <=
    1536%r * (delta_lower + delta_upper) +
    1280%r * (delta_real + delta_imag).
proof.
move=> hj hlower hupper hreal himag.
have herror :=
  sampled_dseed_checked_snapshot_accumulator_error_failure_pr_le_headroom_bad
    j &m hj.
have hheadroom :=
  sampled_dseed_first_attempt_accumulator_headroom_bad_pr_le_split
    delta_lower delta_upper delta_real delta_imag &m
    hlower hupper hreal himag.
exact (ler_trans _ _ _ herror hheadroom).
qed.

end Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze.
