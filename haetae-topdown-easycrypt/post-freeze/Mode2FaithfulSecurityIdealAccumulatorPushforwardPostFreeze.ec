require import AllCore Distr IntDiv List Real StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  Fq
  KeygenEtaSamplerSpec
  KeygenSamplerCallersSpec
  KeygenM23MatrixSpec
  KeygenM23FinalizeSpec
  KeygenM23FinalizeArraySemantics
  KeygenM23SingularFFTAccumulatorProbability
  TargetKeygenM23SingularFFTInputBounds
  Mode2KeygenCoreEquation
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze.

import RealOrder.
import KeygenM23SingularFFTAccumulatorProbability.

theory Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze.

(* This file only pushes the already-proved iid 3+2 eta law through the pure
   mode-2 finalizer skeleton.  The pre-final [pre_bp] and [avec] arrays remain
   parameters: this does not yet build the actual correlated matrix/expand law,
   and it does not account for any actual-to-ideal SHAKE distance or numeric
   tail estimate.  Because the finalizer can be non-injective, we also do not
   transfer the pre-final [(1/3)^1280] point mass or uniformity statements
   through the pushforward. *)

type ideal_eta_packed_secret_pair =
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_packed_secret_pair.

op pure_final_bp_word
    (pre_bp sampled_s2 avec : BArray8192.t) (i : int) : W32.t =
  if 0 <= i < KeygenM23MatrixSpec.mode2_b_words_i then
    KeygenM23FinalizeSpec.finalize_b_word
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 sampled_s2 i)
      (BArray8192.get32 avec i)
  else BArray8192.get32 pre_bp i.

op pure_final_s2_word
    (pre_bp sampled_s2 avec : BArray8192.t) (i : int) : W32.t =
  if 0 <= i < KeygenM23MatrixSpec.mode2_b_words_i then
    KeygenM23FinalizeSpec.finalize_s2_word
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 sampled_s2 i)
      (BArray8192.get32 avec i)
  else BArray8192.get32 sampled_s2 i.

op pure_final_bp_words
    (pre_bp sampled_s2 avec : BArray8192.t) : W32.t list =
  map (pure_final_bp_word pre_bp sampled_s2 avec)
      (iota_ 0 KeygenM23MatrixSpec.array_words_i).

op pure_final_s2_words
    (pre_bp sampled_s2 avec : BArray8192.t) : W32.t list =
  map (pure_final_s2_word pre_bp sampled_s2 avec)
      (iota_ 0 KeygenM23MatrixSpec.array_words_i).

op pure_final_bp
    (pre_bp sampled_s2 avec : BArray8192.t) : BArray8192.t =
  BArray8192.of_list32 (pure_final_bp_words pre_bp sampled_s2 avec).

op pure_final_s2
    (pre_bp sampled_s2 avec : BArray8192.t) : BArray8192.t =
  BArray8192.of_list32 (pure_final_s2_words pre_bp sampled_s2 avec).

op ideal_mode2_finalize_context_valid
    (pre_bp avec : BArray8192.t) : bool =
  (forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    Fq.bw32 (BArray8192.get32 pre_bp i) 16) /\
  Mode2KeygenCoreEquation.canonical_a_active avec.

op ideal_mode2_accumulator_sample
    (pre_bp avec : BArray8192.t)
    (pair : ideal_eta_packed_secret_pair) : mode2_accumulator_sample =
  (pair.`1, pure_final_s2 pre_bp pair.`2 avec).

op ideal_mode2_accumulator_distribution
    (pre_bp avec : BArray8192.t) : mode2_accumulator_sample distr =
  dmap
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_packed_secret_pair_distribution
    (ideal_mode2_accumulator_sample pre_bp avec).

op ideal_mode2_decoded_accumulator_distribution
    (pre_bp avec : BArray8192.t) : mode2_accumulator_sample distr =
  dmap
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_decoded_packed_secret_pair_distribution
    (ideal_mode2_accumulator_sample pre_bp avec).

op ideal_mode2_accumulator_sample_valid
    (pre_bp avec : BArray8192.t)
    (sample : mode2_accumulator_sample) : bool =
  exists pair,
    pair \in
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_packed_secret_pair_distribution /\
    sample = ideal_mode2_accumulator_sample pre_bp avec pair.

lemma pure_final_bp_words_size pre_bp sampled_s2 avec :
  size (pure_final_bp_words pre_bp sampled_s2 avec) * 4 = BArray8192.size.
proof.
rewrite /pure_final_bp_words size_map size_iota.
rewrite /KeygenM23MatrixSpec.array_words_i /BArray8192.size.
ring.
qed.

lemma pure_final_s2_words_size pre_bp sampled_s2 avec :
  size (pure_final_s2_words pre_bp sampled_s2 avec) * 4 = BArray8192.size.
proof.
rewrite /pure_final_s2_words size_map size_iota.
rewrite /KeygenM23MatrixSpec.array_words_i /BArray8192.size.
ring.
qed.

lemma pure_final_bp_get32
    pre_bp sampled_s2 avec i :
  0 <= i < KeygenM23MatrixSpec.array_words_i =>
  BArray8192.get32 (pure_final_bp pre_bp sampled_s2 avec) i =
  pure_final_bp_word pre_bp sampled_s2 avec i.
proof.
move=> hi.
rewrite /pure_final_bp BArray8192.get32_of_list32.
+ exact (pure_final_bp_words_size pre_bp sampled_s2 avec).
rewrite /pure_final_bp_words.
have hi_iota :
    0 <= i < size (iota_ 0 KeygenM23MatrixSpec.array_words_i).
+ by rewrite size_iota.
have -> :
    nth W32.zero
      (map (pure_final_bp_word pre_bp sampled_s2 avec)
           (iota_ 0 KeygenM23MatrixSpec.array_words_i)) i =
    pure_final_bp_word pre_bp sampled_s2 avec
      (nth 0 (iota_ 0 KeygenM23MatrixSpec.array_words_i) i).
+ exact
    (nth_map 0 W32.zero
      (pure_final_bp_word pre_bp sampled_s2 avec)
      i (iota_ 0 KeygenM23MatrixSpec.array_words_i) hi_iota).
by rewrite nth_iota.
qed.

lemma pure_final_s2_get32
    pre_bp sampled_s2 avec i :
  0 <= i < KeygenM23MatrixSpec.array_words_i =>
  BArray8192.get32 (pure_final_s2 pre_bp sampled_s2 avec) i =
  pure_final_s2_word pre_bp sampled_s2 avec i.
proof.
move=> hi.
rewrite /pure_final_s2 BArray8192.get32_of_list32.
+ exact (pure_final_s2_words_size pre_bp sampled_s2 avec).
rewrite /pure_final_s2_words.
have hi_iota :
    0 <= i < size (iota_ 0 KeygenM23MatrixSpec.array_words_i).
+ by rewrite size_iota.
have -> :
    nth W32.zero
      (map (pure_final_s2_word pre_bp sampled_s2 avec)
           (iota_ 0 KeygenM23MatrixSpec.array_words_i)) i =
    pure_final_s2_word pre_bp sampled_s2 avec
      (nth 0 (iota_ 0 KeygenM23MatrixSpec.array_words_i) i).
+ exact
    (nth_map 0 W32.zero
      (pure_final_s2_word pre_bp sampled_s2 avec)
      i (iota_ 0 KeygenM23MatrixSpec.array_words_i) hi_iota).
by rewrite nth_iota.
qed.

lemma pure_final_bp_get32_active
    pre_bp sampled_s2 avec i :
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  BArray8192.get32 (pure_final_bp pre_bp sampled_s2 avec) i =
  KeygenM23FinalizeSpec.finalize_b_word
    (BArray8192.get32 pre_bp i)
    (BArray8192.get32 sampled_s2 i)
    (BArray8192.get32 avec i).
proof.
move=> hi.
have hi_array : 0 <= i < KeygenM23MatrixSpec.array_words_i.
+ move: hi.
  rewrite /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i
          /KeygenM23MatrixSpec.array_words_i
          /BArray8192.size.
  smt().
have -> :=
  pure_final_bp_get32 pre_bp sampled_s2 avec i hi_array.
rewrite /pure_final_bp_word.
by rewrite ifT.
qed.

lemma pure_final_s2_get32_active
    pre_bp sampled_s2 avec i :
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  BArray8192.get32 (pure_final_s2 pre_bp sampled_s2 avec) i =
  KeygenM23FinalizeSpec.finalize_s2_word
    (BArray8192.get32 pre_bp i)
    (BArray8192.get32 sampled_s2 i)
    (BArray8192.get32 avec i).
proof.
move=> hi.
have hi_array : 0 <= i < KeygenM23MatrixSpec.array_words_i.
+ move: hi.
  rewrite /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i
          /KeygenM23MatrixSpec.array_words_i
          /BArray8192.size.
  smt().
have -> :=
  pure_final_s2_get32 pre_bp sampled_s2 avec i hi_array.
rewrite /pure_final_s2_word.
by rewrite ifT.
qed.

lemma pure_final_bp_get32_tail
    pre_bp sampled_s2 avec i :
  KeygenM23MatrixSpec.mode2_b_words_i <= i <
    KeygenM23MatrixSpec.array_words_i =>
  BArray8192.get32 (pure_final_bp pre_bp sampled_s2 avec) i =
  BArray8192.get32 pre_bp i.
proof.
move=> hi.
have hi_array : 0 <= i < KeygenM23MatrixSpec.array_words_i by smt().
have -> :=
  pure_final_bp_get32 pre_bp sampled_s2 avec i hi_array.
rewrite /pure_final_bp_word.
by rewrite ifF; smt().
qed.

lemma pure_final_s2_get32_tail
    pre_bp sampled_s2 avec i :
  KeygenM23MatrixSpec.mode2_b_words_i <= i <
    KeygenM23MatrixSpec.array_words_i =>
  BArray8192.get32 (pure_final_s2 pre_bp sampled_s2 avec) i =
  BArray8192.get32 sampled_s2 i.
proof.
move=> hi.
have hi_array : 0 <= i < KeygenM23MatrixSpec.array_words_i by smt().
have -> :=
  pure_final_s2_get32 pre_bp sampled_s2 avec i hi_array.
rewrite /pure_final_s2_word.
by rewrite ifF; smt().
qed.

lemma pure_final_bp_tail_frame pre_bp sampled_s2 avec :
  KeygenM23MatrixSpec.word_tail_frame
    pre_bp (pure_final_bp pre_bp sampled_s2 avec)
    KeygenM23MatrixSpec.mode2_b_words_i.
proof.
rewrite /KeygenM23MatrixSpec.word_tail_frame.
move=> i hi.
exact (pure_final_bp_get32_tail pre_bp sampled_s2 avec i hi).
qed.

lemma pure_final_s2_tail_frame pre_bp sampled_s2 avec :
  KeygenM23MatrixSpec.word_tail_frame
    sampled_s2 (pure_final_s2 pre_bp sampled_s2 avec)
    KeygenM23MatrixSpec.mode2_b_words_i.
proof.
rewrite /KeygenM23MatrixSpec.word_tail_frame.
move=> i hi.
exact (pure_final_s2_get32_tail pre_bp sampled_s2 avec i hi).
qed.

lemma pure_finalize_output pre_bp sampled_s2 avec :
  KeygenM23FinalizeSpec.finalize_output
    pre_bp sampled_s2 avec
    (pure_final_bp pre_bp sampled_s2 avec)
    (pure_final_s2 pre_bp sampled_s2 avec).
proof.
rewrite /KeygenM23FinalizeSpec.finalize_output
        /KeygenM23FinalizeSpec.finalize_prefix.
split.
+ rewrite /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i.
  smt().
split.
+ exact (pure_final_bp_get32_active pre_bp sampled_s2 avec).
split.
+ exact (pure_final_s2_get32_active pre_bp sampled_s2 avec).
split.
+ exact (pure_final_bp_tail_frame pre_bp sampled_s2 avec).
exact (pure_final_s2_tail_frame pre_bp sampled_s2 avec).
qed.

lemma pure_finalize_semantic_output pre_bp sampled_s2 avec :
  KeygenM23FinalizeArraySemantics.finalize_reachable_inputs
    pre_bp sampled_s2 avec =>
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    pre_bp sampled_s2 avec
    (pure_final_bp pre_bp sampled_s2 avec)
    (pure_final_s2 pre_bp sampled_s2 avec).
proof.
move=> hreachable.
apply KeygenM23FinalizeArraySemantics.finalize_output_semantics.
+ exact hreachable.
exact (pure_finalize_output pre_bp sampled_s2 avec).
qed.

lemma ideal_mode2_decoded_accumulator_distribution_eq_iid
    pre_bp avec :
  ideal_mode2_decoded_accumulator_distribution pre_bp avec =
  ideal_mode2_accumulator_distribution pre_bp avec.
proof.
rewrite
  /ideal_mode2_decoded_accumulator_distribution
  /ideal_mode2_accumulator_distribution
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_decoded_packed_secret_pair_eq_iid.
trivial.
qed.

lemma ideal_mode2_accumulator_distribution_lossless
    pre_bp avec :
  is_lossless (ideal_mode2_accumulator_distribution pre_bp avec).
proof.
rewrite /ideal_mode2_accumulator_distribution.
apply dmap_ll.
exact
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_packed_secret_pair_lossless.
qed.

lemma ideal_mode2_accumulator_distribution_support
    pre_bp avec sample :
  sample \in ideal_mode2_accumulator_distribution pre_bp avec <=>
  ideal_mode2_accumulator_sample_valid pre_bp avec sample.
proof.
rewrite
  /ideal_mode2_accumulator_distribution
  /ideal_mode2_accumulator_sample_valid supp_dmap.
trivial.
qed.

lemma ideal_eta_centered_s2_active (s2 : BArray8192.t) :
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s2 KeygenSamplerCallersSpec.mode2_k_i =>
  Mode2KeygenCoreEquation.centered_s2_active s2.
proof.
move=> hcenter.
rewrite /Mode2KeygenCoreEquation.centered_s2_active.
move=> i hi.
rewrite /KeygenSamplerCallersSpec.eta_vector_centered8192
        /KeygenSamplerCallersSpec.eta_vector_words_i
        /KeygenSamplerCallersSpec.mode2_k_i
        /KeygenEtaSamplerSpec.centered_interval8192
        /KeygenEtaSamplerSpec.eta_poly_words_i /= in hcenter.
apply (hcenter i).
move: hi.
rewrite /KeygenM23MatrixSpec.mode2_b_words_i
        /KeygenM23MatrixSpec.mode2_rows_i
        /KeygenM23MatrixSpec.poly_words_i.
smt().
qed.

lemma ideal_mode2_reachable_inputs_of_context
    pre_bp avec (pair : ideal_eta_packed_secret_pair) :
  ideal_mode2_finalize_context_valid pre_bp avec =>
  pair \in
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_packed_secret_pair_distribution =>
  KeygenM23FinalizeArraySemantics.finalize_reachable_inputs
    pre_bp pair.`2 avec.
proof.
move=> [hbp hcanonical] hpair.
have [_ hs2center] :=
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_packed_secret_pair_centered pair hpair.
have hs2active := ideal_eta_centered_s2_active pair.`2 hs2center.
rewrite /KeygenM23FinalizeArraySemantics.finalize_reachable_inputs.
move=> i hi.
rewrite /KeygenM23FinalizeArraySemantics.reachable_word_inputs.
split.
+ exact (hbp i hi).
split.
+ exact (hs2active i hi).
exact (hcanonical i hi).
qed.

lemma ideal_mode2_accumulator_sample_bound2
    pre_bp avec (pair : ideal_eta_packed_secret_pair) :
  pair \in
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_packed_secret_pair_distribution =>
  KeygenM23FinalizeArraySemantics.finalize_reachable_inputs
    pre_bp pair.`2 avec =>
  TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
    pair.`1 (pure_final_s2 pre_bp pair.`2 avec).
proof.
move=> hpair hreachable.
have [hs1center hs2center] :=
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_packed_secret_pair_centered pair hpair.
have hsemantic :=
  pure_finalize_semantic_output pre_bp pair.`2 avec hreachable.
exact
  (TargetKeygenM23SingularFFTInputBounds
    .mode2_fft_inputs_bound2_of_sampler_finalize
      pair.`1 pre_bp pair.`2 avec
      (pure_final_bp pre_bp pair.`2 avec)
      (pure_final_s2 pre_bp pair.`2 avec)
      hs1center hs2center hsemantic).
qed.

lemma ideal_mode2_accumulator_distribution_support_bound2
    pre_bp avec :
  (forall pair,
    pair \in
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_packed_secret_pair_distribution =>
    KeygenM23FinalizeArraySemantics.finalize_reachable_inputs
      pre_bp pair.`2 avec) =>
  forall sample,
    sample \in ideal_mode2_accumulator_distribution pre_bp avec =>
    TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
      sample.`1 sample.`2.
proof.
move=> hreachable sample.
rewrite ideal_mode2_accumulator_distribution_support.
move=> [pair [hpair ->]].
exact
  (ideal_mode2_accumulator_sample_bound2
    pre_bp avec pair hpair (hreachable pair hpair)).
qed.

lemma ideal_mode2_accumulator_distribution_support_bound2_of_context
    pre_bp avec :
  ideal_mode2_finalize_context_valid pre_bp avec =>
  forall sample,
    sample \in ideal_mode2_accumulator_distribution pre_bp avec =>
    TargetKeygenM23SingularFFTInputBounds.mode2_fft_inputs_bound2
      sample.`1 sample.`2.
proof.
move=> hctx.
apply (ideal_mode2_accumulator_distribution_support_bound2 pre_bp avec).
move=> pair hpair.
exact (ideal_mode2_reachable_inputs_of_context pre_bp avec pair hctx hpair).
qed.

lemma ideal_mode2_accumulator_headroom_bad_mu_le_split
    pre_bp avec epsilon_lower epsilon_upper epsilon_real epsilon_imag :
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
    .ideal_accumulator_local_tail_certificate
      (ideal_mode2_accumulator_distribution pre_bp avec)
      epsilon_lower epsilon_upper epsilon_real epsilon_imag =>
  mu (ideal_mode2_accumulator_distribution pre_bp avec)
       mode2_accumulator_trace_headroom_bad <=
    1536%r * (epsilon_lower + epsilon_upper) +
    1280%r * (epsilon_real + epsilon_imag).
proof.
move=> hlocal.
exact
  (Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze
    .ideal_accumulator_headroom_bad_mu_le_split
      (ideal_mode2_accumulator_distribution pre_bp avec)
      epsilon_lower epsilon_upper epsilon_real epsilon_imag
      hlocal).
qed.

end Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze.
