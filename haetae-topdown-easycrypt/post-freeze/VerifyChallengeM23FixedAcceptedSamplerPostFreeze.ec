require import AllCore DInterval List.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyChallengeM23ProbabilisticSamplerPostFreeze
               VerifyChallengeM23RejectionIndexPostFreeze
               Mode2VerifyPrepareNorm.

theory VerifyChallengeM23FixedAcceptedSamplerPostFreeze.

module RejectionLoop =
  VerifyChallengeM23RejectionIndexPostFreeze.RejectionIndexSampling.SampleW.
module DirectIndex =
  VerifyChallengeM23RejectionIndexPostFreeze.DirectIndexSampler.

op challenge_words : int =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_words.
op mode2_start : int =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start.
op mode2_tau : int =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_tau.
op mode2_zero_challenge : BArray1024.t =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_zero_challenge.
op challenge_shuffle_update =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_shuffle_update.
op challenge_weight =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_weight.
op challenge_of_barray =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_of_barray.
op mode2_cardinality_wf =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_cardinality_wf.

lemma index_0_255 i :
  0 <= i => i <= 255 => 0 <= i <= 255.
proof. smt(). qed.

(* This layer groups byte rejections into one accepted-index call, then
   replaces that call with the direct conditional law dinter 0 i.  It does
   not yet identify the original monolithic flat loop with the grouped loop
   or claim uniformity of the final 58-element support. *)

equiv rejection_loop_direct_index :
  RejectionLoop.sample ~ DirectIndex.sample :
  ={arg} /\ 0 <= arg{1} /\ arg{1} <= 255 ==> ={res}.
proof.
bypr (res{1}) (res{2}) => /> &1 &2 a <- hlo hupper.
have hi := index_0_255 i{1} hlo hupper.
rewrite
  (VerifyChallengeM23RejectionIndexPostFreeze.rejection_index_loop_pr
    &1 i{1} (pred1 a) hi).
rewrite
  (VerifyChallengeM23RejectionIndexPostFreeze.direct_index_sampler_pr
    &2 i{1} (pred1 a) hi).
trivial.
qed.

module GroupedAcceptedIndexSampler = {
  var accepted_indices : int list

  proc sample () : BArray1024.t * int = {
    var cp : BArray1024.t;
    var i : int;
    var b : int;

    cp <- mode2_zero_challenge;
    i <- mode2_start;
    accepted_indices <- [];
    while (i < challenge_words) {
      b <@ RejectionLoop.sample(i);
      accepted_indices <- rcons accepted_indices b;
      cp <- challenge_shuffle_update cp i b;
      i <- i + 1;
    }
    return (cp, i);
  }
}.

module FixedAcceptedIndexSampler = {
  var accepted_indices : int list

  proc sample () : BArray1024.t * int = {
    var cp : BArray1024.t;
    var i : int;
    var b : int;

    cp <- mode2_zero_challenge;
    i <- mode2_start;
    accepted_indices <- [];
    while (i < challenge_words) {
      b <@ DirectIndex.sample(i);
      accepted_indices <- rcons accepted_indices b;
      cp <- challenge_shuffle_update cp i b;
      i <- i + 1;
    }
    return (cp, i);
  }
}.

equiv grouped_fixed_accepted_indices :
  GroupedAcceptedIndexSampler.sample ~ FixedAcceptedIndexSampler.sample :
  true ==>
  ={res} /\
  GroupedAcceptedIndexSampler.accepted_indices{1} =
    FixedAcceptedIndexSampler.accepted_indices{2}.
proof.
proc.
while
  (={cp, i} /\
   mode2_start <= i{1} <= challenge_words /\
   GroupedAcceptedIndexSampler.accepted_indices{1} =
     FixedAcceptedIndexSampler.accepted_indices{2}).
+ wp.
  call rejection_loop_direct_index.
  auto => />; smt().
+ auto => />.
qed.

lemma fixed_accepted_index_sampler_lossless :
  islossless FixedAcceptedIndexSampler.sample.
proof.
proc.
inline DirectIndex.sample.
while
  (mode2_start <= i <= challenge_words)
  (challenge_words - i).
+ move=> z.
  auto => />; smt(dinter_ll).
+ auto => />; smt().
qed.

lemma fixed_accepted_index_sampler_canonical_weight :
  hoare [FixedAcceptedIndexSampler.sample :
    true ==>
    res.`2 = challenge_words /\
    Mode2VerifyPrepareNorm.canonical_challenge res.`1 /\
    challenge_weight res.`1 = mode2_tau].
proof.
proc.
wp.
while
  (VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_sampling_inv cp i).
+ inline DirectIndex.sample.
  auto => />.
  move=> &hr hcanonical hstart hupper htail hweight hloop b hb.
  have hinv :
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_sampling_inv
        cp{hr} i{hr}.
  + rewrite /VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_sampling_inv.
    split; first exact hcanonical.
    split; first exact hstart.
    split; first exact hupper.
    split; [exact htail | exact hweight].
  have hnonneg : 0 <= i{hr}.
  + have hs :=
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start_index_range.
    smt().
  have hbyte : 0 <= b <= i{hr}.
  + move: hb.
    rewrite
      (VerifyChallengeM23RejectionIndexPostFreeze.direct_index_support
        i{hr} b hnonneg).
    trivial.
  exact
    (VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_sampling_inv_accept
      cp{hr} i{hr} b hinv hloop hbyte).
+ auto => />;
  smt(VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_sampling_inv_init
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_sampling_inv_final
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.finished_index_explicit).
qed.

lemma fixed_accepted_index_sampler_cardinality :
  hoare [FixedAcceptedIndexSampler.sample :
    true ==>
    res.`2 = challenge_words /\
    mode2_cardinality_wf (challenge_of_barray res.`1)].
proof.
conseq fixed_accepted_index_sampler_canonical_weight.
move=> &hr _ result [hfinal [hcanonical hweight]].
split; first exact hfinal.
exact
  (VerifyChallengeM23ProbabilisticSamplerPostFreeze.canonical_weight_implies_mode2_cardinality
    result.`1 hcanonical hweight).
qed.

end VerifyChallengeM23FixedAcceptedSamplerPostFreeze.
