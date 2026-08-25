require import AllCore Distr List Real.

require import VerifyChallengeM23FixedAcceptedSamplerPostFreeze
               VerifyChallengeM23FlatAcceptedStepPostFreeze
               VerifyChallengeM23UniformRoundsPostFreeze
               VerifyChallengeM23UniformSamplerBridgePostFreeze.

theory VerifyChallengeM23UniformFlatSamplerPostFreeze.

(* Probability transport from the fixed accepted-index model through the
   grouped rejection sampler to the original monolithic flat byte loop.  The
   result remains conditional on the ideal uniform-byte model; deterministic
   XOF randomness and the explicit binomial denominator remain separate. *)

module FixedAcceptedIndexSampler =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.FixedAcceptedIndexSampler.
module GroupedAcceptedIndexSampler =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.GroupedAcceptedIndexSampler.
module FlatMode2RejectionSampler =
  VerifyChallengeM23FlatAcceptedStepPostFreeze.FlatMode2RejectionSampler.

op challenge_words : int =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.challenge_words.
op mode2_tau : int =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.mode2_tau.
op support_prefix =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.support_prefix.
op valid_subset =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.valid_subset.
op reservoir_rounds =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.reservoir_rounds.

lemma grouped_fixed_support_pr &m1 &m2 P :
  Pr[GroupedAcceptedIndexSampler.sample() @ &m1 :
       P (support_prefix res.`1 res.`2)] =
  Pr[FixedAcceptedIndexSampler.sample() @ &m2 :
       P (support_prefix res.`1 res.`2)].
proof.
byequiv
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.grouped_fixed_accepted_indices
  => //=.
qed.

lemma grouped_support_pr &m P :
  Pr[GroupedAcceptedIndexSampler.sample() @ &m :
       P (support_prefix res.`1 res.`2)] =
  mu (reservoir_rounds mode2_tau) P.
proof.
rewrite
  (grouped_fixed_support_pr &m &m P)
  (VerifyChallengeM23UniformSamplerBridgePostFreeze.fixed_support_pr &m P).
trivial.
qed.

lemma flat_grouped_support_pr &m1 &m2 P :
  Pr[FlatMode2RejectionSampler.sample() @ &m1 :
       P (support_prefix res.`1 res.`2)] =
  Pr[GroupedAcceptedIndexSampler.sample() @ &m2 :
       P (support_prefix res.`1 res.`2)].
proof.
byequiv
  VerifyChallengeM23FlatAcceptedStepPostFreeze.flat_existing_grouped_sampler
  => //=.
qed.

lemma flat_support_pr &m P :
  Pr[FlatMode2RejectionSampler.sample() @ &m :
       P (support_prefix res.`1 res.`2)] =
  mu (reservoir_rounds mode2_tau) P.
proof.
rewrite
  (flat_grouped_support_pr &m &m P)
  (grouped_support_pr &m P).
trivial.
qed.

lemma flat_support_point &m t :
  Pr[FlatMode2RejectionSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = t] =
  if valid_subset challenge_words mode2_tau t
  then
    1%r /
    (size
       (Finite.to_seq
          (support (reservoir_rounds mode2_tau))))%r
  else 0%r.
proof.
rewrite (flat_support_pr &m (pred1 t)).
exact
  (VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds_final_point t).
qed.

lemma flat_support_uniform &m t u :
  valid_subset challenge_words mode2_tau t =>
  valid_subset challenge_words mode2_tau u =>
  Pr[FlatMode2RejectionSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = t] =
  Pr[FlatMode2RejectionSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = u].
proof.
move=> ht hu.
rewrite !flat_support_point ht hu.
trivial.
qed.

end VerifyChallengeM23UniformFlatSamplerPostFreeze.
