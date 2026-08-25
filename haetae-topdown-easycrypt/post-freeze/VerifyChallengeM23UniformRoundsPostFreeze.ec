require import AllCore Distr FSet List Real StdOrder.

require import VerifyChallengeM23ProbabilisticSamplerPostFreeze
               VerifyChallengeM23UniformSubsetPostFreeze.

theory VerifyChallengeM23UniformRoundsPostFreeze.

import IntOrder RealOrder.

(* Distribution-level iteration of the ideal reservoir step.  This layer
   closes the 58-round induction, but deliberately leaves the operational
   sampler coupling and the binomial support count to subsequent layers. *)

op challenge_words : int =
  VerifyChallengeM23UniformSubsetPostFreeze.challenge_words.
op mode2_start : int =
  VerifyChallengeM23UniformSubsetPostFreeze.mode2_start.
op mode2_tau : int =
  VerifyChallengeM23UniformSubsetPostFreeze.mode2_tau.
op valid_subset =
  VerifyChallengeM23UniformSubsetPostFreeze.valid_subset.
op reservoir_lift =
  VerifyChallengeM23UniformSubsetPostFreeze.reservoir_lift.

op reservoir_rounds (n : int) : int fset distr =
  iteri n
    (fun j d => reservoir_lift d (mode2_start + j))
    (dunit FSet.fset0).

lemma mode2_round_constants :
  0 <= mode2_tau /\
  mode2_start + mode2_tau = challenge_words.
proof.
rewrite /mode2_tau /mode2_start /challenge_words
        /VerifyChallengeM23UniformSubsetPostFreeze.mode2_tau
        /VerifyChallengeM23UniformSubsetPostFreeze.mode2_start
        /VerifyChallengeM23UniformSubsetPostFreeze.challenge_words.
trivial.
qed.

lemma reservoir_rounds0 :
  reservoir_rounds 0 = dunit FSet.fset0.
proof. by rewrite /reservoir_rounds iteri0. qed.

lemma reservoir_roundsS n :
  0 <= n =>
  reservoir_rounds (n + 1) =
  reservoir_lift (reservoir_rounds n) (mode2_start + n).
proof. by move=> hn; rewrite /reservoir_rounds iteriS. qed.

lemma valid_subset_zero n s :
  valid_subset n 0 s <=> s = FSet.fset0.
proof.
rewrite /valid_subset
        /VerifyChallengeM23UniformSubsetPostFreeze.valid_subset.
split.
+ move=> [_ hcard].
  move/FSet.fcard_eq0: hcard.
  trivial.
+ move=> ->.
  split.
  + exact (FSet.sub0set (FSet.rangeset 0 n)).
  + exact FSet.fcards0.
qed.

lemma reservoir_lift_support d i k t :
  0 <= i =>
  0 <= k =>
  (forall s, s \in d <=> valid_subset i k s) =>
  (t \in reservoir_lift d i <=> valid_subset (i + 1) (k + 1) t).
proof.
move=> hi hk hdsupport.
split.
+ apply
    (VerifyChallengeM23UniformSubsetPostFreeze.reservoir_lift_output_valid
       d i k t hi).
  move=> s hs.
  move: (hdsupport s) => [hforward _].
  exact (hforward hs).
+ move=> htvalid.
  have htcard : FSet.card t = k + 1.
  + move: htvalid.
    rewrite /valid_subset
            /VerifyChallengeM23UniformSubsetPostFreeze.valid_subset.
    smt().
  have htne : t <> FSet.fset0.
  + rewrite -FSet.fcard_eq0.
    smt().
  have hpick : FSet.pick t \in t.
  + exact (FSet.mem_pick t htne).
  have hpre :=
    VerifyChallengeM23UniformSubsetPostFreeze.reservoir_predecessor_valid
      t i k (FSet.pick t) htvalid hpick.
  move: hpre => [hprevalid hpickrange].
  rewrite /reservoir_lift
          /VerifyChallengeM23UniformSubsetPostFreeze.reservoir_lift
          supp_dmap.
  exists
    (VerifyChallengeM23UniformSubsetPostFreeze.reservoir_predecessor
       t i (FSet.pick t),
     FSet.pick t).
  split.
  + rewrite
      VerifyChallengeM23UniformSubsetPostFreeze.reservoir_pair_support
      hdsupport.
    split; [exact hprevalid | exact hpickrange].
  + simplify.
    rewrite eq_sym.
    exact
      (VerifyChallengeM23UniformSubsetPostFreeze.reservoir_predecessor_step
         t i k (FSet.pick t) htvalid hpick).
qed.

lemma reservoir_rounds_support :
  forall n, 0 <= n =>
  forall s,
    s \in reservoir_rounds n <=>
    valid_subset (mode2_start + n) n s.
proof.
apply
  (intind
    (fun n =>
      forall s,
        s \in reservoir_rounds n <=>
        valid_subset (mode2_start + n) n s)).
+ move=> s.
  rewrite reservoir_rounds0 supp_dunit valid_subset_zero.
+ trivial.
+ move=> n hn ih s.
  rewrite reservoir_roundsS 1:hn.
  have hindex :
      mode2_start + (n + 1) = (mode2_start + n) + 1 by ring.
  rewrite hindex.
  apply reservoir_lift_support.
  + have :=
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start_index_range.
    smt().
  + exact hn.
  + exact ih.
qed.

lemma reservoir_rounds_uniform :
  forall n, 0 <= n => is_uniform (reservoir_rounds n).
proof.
apply (intind (fun n => is_uniform (reservoir_rounds n))).
+ trivial.
+ simplify.
  rewrite reservoir_rounds0.
  exact (dunit_uni FSet.fset0).
+ move=> n hn ih.
  simplify.
  rewrite reservoir_roundsS 1:hn.
  apply
    (VerifyChallengeM23UniformSubsetPostFreeze.reservoir_lift_uniform
       (reservoir_rounds n) (mode2_start + n) n).
  + have :=
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start_index_range.
    smt().
  + exact ih.
  + exact (reservoir_rounds_support n hn).
qed.

lemma reservoir_rounds_lossless :
  forall n, 0 <= n => is_lossless (reservoir_rounds n).
proof.
apply (intind (fun n => is_lossless (reservoir_rounds n))).
+ trivial.
+ simplify.
  rewrite reservoir_rounds0.
  exact (dunit_ll FSet.fset0).
+ move=> n hn ih.
  simplify.
  rewrite reservoir_roundsS 1:hn.
  apply
    (VerifyChallengeM23UniformSubsetPostFreeze.reservoir_lift_lossless
       (reservoir_rounds n) (mode2_start + n)).
  + exact ih.
  + have :=
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start_index_range.
    smt().
qed.

lemma reservoir_rounds_final_support s :
  s \in reservoir_rounds mode2_tau <=>
  valid_subset challenge_words mode2_tau s.
proof.
have hconstants := mode2_round_constants.
move: hconstants => [htau hfinal].
rewrite (reservoir_rounds_support mode2_tau htau s) hfinal.
trivial.
qed.

lemma reservoir_rounds_final_uniform :
  is_uniform (reservoir_rounds mode2_tau).
proof.
have hconstants := mode2_round_constants.
move: hconstants => [htau _].
exact (reservoir_rounds_uniform mode2_tau htau).
qed.

lemma reservoir_rounds_final_lossless :
  is_lossless (reservoir_rounds mode2_tau).
proof.
have hconstants := mode2_round_constants.
move: hconstants => [htau _].
exact (reservoir_rounds_lossless mode2_tau htau).
qed.

lemma reservoir_rounds_final_point s :
  mu1 (reservoir_rounds mode2_tau) s =
  if valid_subset challenge_words mode2_tau s
  then
    1%r /
    (size
       (Finite.to_seq
          (support (reservoir_rounds mode2_tau))))%r
  else 0%r.
proof.
rewrite
  (mu1_uni_ll (reservoir_rounds mode2_tau) s
     reservoir_rounds_final_uniform reservoir_rounds_final_lossless).
rewrite reservoir_rounds_final_support.
trivial.
qed.

end VerifyChallengeM23UniformRoundsPostFreeze.
