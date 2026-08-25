require import AllCore Binomial Distr FSet Finite List Real StdOrder.

require import VerifyChallengeM23UniformFlatSamplerPostFreeze
               VerifyChallengeM23ProbabilisticSamplerPostFreeze
               VerifyChallengeM23UniformRoundsPostFreeze
               VerifyChallengeM23UniformSamplerBridgePostFreeze
               VerifyChallengeM23UniformSubsetPostFreeze.

theory VerifyChallengeM23SubsetBinomialPostFreeze.

import IntOrder.

(* Combinatorial counting layer for the valid support family.  A subset is
   represented canonically by the unique subsequence of range 0 n containing
   its elements.  The Fixed/Flat corollaries inherit the ideal uniform-byte
   boundary and make no deterministic-XOF randomness claim. *)

op choose_lists ['a] (xs : 'a list) (k : int) : 'a list list =
  filter (fun ys => size ys = k) (subseqs xs).

lemma choose_lists_mem ['a] (xs ys : 'a list) k :
  ys \in choose_lists xs k <=> subseq ys xs /\ size ys = k.
proof.
rewrite /choose_lists mem_filter -subseqsP.
smt().
qed.

lemma choose_lists_uniq ['a] (xs : 'a list) k :
  uniq xs => uniq (choose_lists xs k).
proof.
move=> huniq.
apply filter_uniq.
exact (subseqs_uniq xs huniq).
qed.

lemma choose_lists_size ['a] (xs : 'a list) k :
  size (choose_lists xs k) = bin (size xs) k.
proof.
elim: xs k => [|x xs ih] k.
+ rewrite /choose_lists /= bin0n.
  case (k = 0) => hk /=; smt().
+ rewrite /choose_lists /= filter_cat size_cat filter_map !size_map.
  have hfilter :
      filter
        (preim ((::) x) (fun ys : 'a list => size ys = k))
        (subseqs xs) =
      filter (fun ys : 'a list => size ys = k - 1) (subseqs xs).
  + apply eq_filter => ys.
    rewrite /preim /=.
    smt().
  rewrite hfilter (ih (k - 1)) (ih k).
  case (k < 0) => hkneg.
  + rewrite !bin_lt0r 1..3:/#.
    trivial.
  case (k = 0) => hk0.
  + subst k.
    rewrite bin_lt0r 1:/#.
    have hxge : 0 <= size xs by smt(size_ge0).
    have hxSge : 0 <= size xs + 1 by smt().
    have hzero := bin0 (size xs) hxge.
    have hzeroS := bin0 (size xs + 1) hxSge.
    smt().
  have hkprev : 0 <= k - 1 by smt().
  have hxge : 0 <= size xs by smt(size_ge0).
  have hpascal := binSn (size xs) (k - 1) hxge hkprev.
  move: hpascal.
  have -> : k - 1 + 1 = k by ring.
  move=> hpascal.
  smt().
qed.

op valid_subset =
  VerifyChallengeM23UniformSubsetPostFreeze.valid_subset.

op canonical_subset_list (n : int) (s : int fset) : int list =
  filter (FSet.mem s) (range 0 n).

op ksubsets (n k : int) : int fset list =
  map FSet.oflist (choose_lists (range 0 n) k).

lemma canonical_subset_list_subseq n s :
  subseq (canonical_subset_list n s) (range 0 n).
proof. exact (filter_subseq (FSet.mem s) (range 0 n)). qed.

lemma canonical_subset_list_oflist n s :
  s \subset FSet.rangeset 0 n =>
  FSet.oflist (canonical_subset_list n s) = s.
proof.
move=> hsub.
apply/FSet.fsetP => x.
rewrite FSet.mem_oflist /canonical_subset_list mem_filter.
split.
+ move=> [hxin _]; exact hxin.
+ move=> hxin.
  split; first exact hxin.
  have hxrange := hsub x hxin.
  move: hxrange.
  rewrite FSet.mem_rangeset mem_range.
  trivial.
qed.

lemma canonical_subset_list_uniq n s :
  uniq (canonical_subset_list n s).
proof.
apply filter_uniq.
exact (range_uniq 0 n).
qed.

lemma canonical_subset_list_size n s :
  s \subset FSet.rangeset 0 n =>
  size (canonical_subset_list n s) = FSet.card s.
proof.
move=> hsub.
have hcard :=
  FSet.uniq_card_oflist
    (canonical_subset_list n s)
    (canonical_subset_list_uniq n s).
move: hcard.
rewrite (canonical_subset_list_oflist n s hsub).
smt().
qed.

lemma ksubsets_mem n k s :
  s \in ksubsets n k <=> valid_subset n k s.
proof.
rewrite /ksubsets.
split.
+ move/mapP => [ys [hchoose ->]].
  move/choose_lists_mem: hchoose => [hsubseq hsize].
  have hyuniq :=
    subseq_uniq ys (range 0 n) hsubseq (range_uniq 0 n).
  rewrite /valid_subset
          /VerifyChallengeM23UniformSubsetPostFreeze.valid_subset.
  split.
  + move=> x hx.
    move: hx; rewrite FSet.mem_oflist => hx.
    have hxrange := subseq_mem ys (range 0 n) x hsubseq hx.
    move: hxrange.
    rewrite mem_range FSet.mem_rangeset.
    smt().
  + rewrite FSet.uniq_card_oflist 1:hyuniq hsize.
    trivial.
+ move=> [hsub hcard].
  apply/mapP.
  exists (canonical_subset_list n s).
  split.
  + apply/choose_lists_mem.
    split.
    * exact (canonical_subset_list_subseq n s).
    * rewrite (canonical_subset_list_size n s hsub) hcard.
      trivial.
  + rewrite (canonical_subset_list_oflist n s hsub).
    trivial.
qed.

lemma ksubsets_uniq n k :
  uniq (ksubsets n k).
proof.
rewrite /ksubsets.
apply map_inj_in_uniq.
+ move=> xs ys hxs hys heq.
  move/choose_lists_mem: hxs => [hxsub hxsize].
  move/choose_lists_mem: hys => [hysub hysize].
  have hxuniq :=
    subseq_uniq xs (range 0 n) hxsub (range_uniq 0 n).
  have hyuniq :=
    subseq_uniq ys (range 0 n) hysub (range_uniq 0 n).
  have hperm := FSet.perm_eq_oflist xs ys heq.
  move: hperm.
  rewrite !undup_id 1:hxuniq 1:hyuniq.
  move=> hperm.
  apply
    (uniq_subseq_eq
       (range 0 n) xs ys (range_uniq 0 n) hxsub hysub).
  move=> z.
  apply/eq_iff.
  exact (perm_eq_mem xs ys hperm z).
+ apply choose_lists_uniq.
  exact (range_uniq 0 n).
qed.

lemma ksubsets_size n k :
  0 <= n => size (ksubsets n k) = bin n k.
proof.
move=> hn.
rewrite /ksubsets size_map choose_lists_size size_range.
have -> : max 0 (n - 0) = n by smt().
trivial.
qed.

lemma ksubsets_finite_for n k :
  is_finite_for (valid_subset n k) (ksubsets n k).
proof.
split.
+ exact (ksubsets_uniq n k).
+ move=> s; exact (ksubsets_mem n k s).
qed.

lemma valid_subset_finite n k :
  is_finite (valid_subset n k).
proof.
rewrite /is_finite.
exists (ksubsets n k).
exact (ksubsets_finite_for n k).
qed.

lemma valid_subset_to_seq_size n k :
  0 <= n =>
  size (Finite.to_seq (valid_subset n k)) = bin n k.
proof.
move=> hn.
have hfin := valid_subset_finite n k.
have hto := Finite.to_seq_finite (valid_subset n k) hfin.
move: hto => [htouniq htomem].
have hperm :
    perm_eq (Finite.to_seq (valid_subset n k)) (ksubsets n k).
+ apply uniq_perm_eq.
  + exact htouniq.
  + exact (ksubsets_uniq n k).
  + move=> s.
    rewrite htomem ksubsets_mem.
    trivial.
have hsize :=
  perm_eq_size
    (Finite.to_seq (valid_subset n k)) (ksubsets n k) hperm.
move: hsize.
rewrite (ksubsets_size n k hn).
trivial.
qed.

op challenge_words : int =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.challenge_words.
op mode2_tau : int =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.mode2_tau.
op reservoir_rounds =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.reservoir_rounds.

lemma challenge_words_nonnegative :
  0 <= challenge_words.
proof.
have hstart :=
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start_index_range.
have hconstants :=
  VerifyChallengeM23UniformSamplerBridgePostFreeze.mode2_round_constants.
move: hconstants => [htau hfinal].
smt().
qed.

lemma reservoir_rounds_support_size_binomial :
  size
    (Finite.to_seq
       (support (reservoir_rounds mode2_tau))) =
  bin challenge_words mode2_tau.
proof.
have hsupportfinite :
    is_finite (support (reservoir_rounds mode2_tau)).
+ apply uniform_finite.
  exact
    VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds_final_uniform.
have hvalidfinite := valid_subset_finite challenge_words mode2_tau.
have hperm :
    perm_eq
      (Finite.to_seq (support (reservoir_rounds mode2_tau)))
      (Finite.to_seq (valid_subset challenge_words mode2_tau)).
+ apply uniq_perm_eq.
  + exact (Finite.uniq_to_seq (support (reservoir_rounds mode2_tau))).
  + exact
      (Finite.uniq_to_seq
         (valid_subset challenge_words mode2_tau)).
  + move=> s.
    rewrite
      (Finite.mem_to_seq
         (support (reservoir_rounds mode2_tau)) s hsupportfinite)
      (Finite.mem_to_seq
         (valid_subset challenge_words mode2_tau) s hvalidfinite).
    exact
      (VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds_final_support
         s).
have hsize :=
  perm_eq_size
    (Finite.to_seq (support (reservoir_rounds mode2_tau)))
    (Finite.to_seq (valid_subset challenge_words mode2_tau))
    hperm.
have hvalidsize :=
  valid_subset_to_seq_size
    challenge_words mode2_tau challenge_words_nonnegative.
smt().
qed.

module FixedAcceptedIndexSampler =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.FixedAcceptedIndexSampler.
module FlatMode2RejectionSampler =
  VerifyChallengeM23UniformFlatSamplerPostFreeze.FlatMode2RejectionSampler.

op support_prefix =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.support_prefix.

lemma reservoir_rounds_final_point_binomial t :
  mu1 (reservoir_rounds mode2_tau) t =
  if valid_subset challenge_words mode2_tau t
  then 1%r / (bin challenge_words mode2_tau)%r
  else 0%r.
proof.
rewrite
  VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds_final_point
  reservoir_rounds_support_size_binomial.
trivial.
qed.

lemma fixed_support_point_binomial &m t :
  Pr[FixedAcceptedIndexSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = t] =
  if valid_subset challenge_words mode2_tau t
  then 1%r / (bin challenge_words mode2_tau)%r
  else 0%r.
proof.
rewrite
  (VerifyChallengeM23UniformSamplerBridgePostFreeze.fixed_support_point &m t)
  reservoir_rounds_support_size_binomial.
trivial.
qed.

lemma flat_support_point_binomial &m t :
  Pr[FlatMode2RejectionSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = t] =
  if valid_subset challenge_words mode2_tau t
  then 1%r / (bin challenge_words mode2_tau)%r
  else 0%r.
proof.
rewrite
  (VerifyChallengeM23UniformFlatSamplerPostFreeze.flat_support_point &m t)
  reservoir_rounds_support_size_binomial.
trivial.
qed.

lemma mode2_parameters_explicit :
  challenge_words = 256 /\ mode2_tau = 58.
proof.
rewrite
  /challenge_words /mode2_tau
  /VerifyChallengeM23UniformSamplerBridgePostFreeze.challenge_words
  /VerifyChallengeM23UniformSamplerBridgePostFreeze.mode2_tau
  /VerifyChallengeM23UniformSubsetPostFreeze.challenge_words
  /VerifyChallengeM23UniformSubsetPostFreeze.mode2_tau.
trivial.
qed.

lemma reservoir_rounds_final_point_256_58 t :
  mu1 (reservoir_rounds 58) t =
  if valid_subset 256 58 t
  then 1%r / (bin 256 58)%r
  else 0%r.
proof.
have hpoint := reservoir_rounds_final_point_binomial t.
have hparams := mode2_parameters_explicit.
move: hparams => [hwords htau].
move: hpoint.
rewrite hwords htau.
trivial.
qed.

lemma fixed_support_point_256_58 &m t :
  Pr[FixedAcceptedIndexSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = t] =
  if valid_subset 256 58 t
  then 1%r / (bin 256 58)%r
  else 0%r.
proof.
have hpoint := fixed_support_point_binomial &m t.
have hparams := mode2_parameters_explicit.
move: hparams => [hwords htau].
move: hpoint.
rewrite hwords htau.
trivial.
qed.

lemma flat_support_point_256_58 &m t :
  Pr[FlatMode2RejectionSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = t] =
  if valid_subset 256 58 t
  then 1%r / (bin 256 58)%r
  else 0%r.
proof.
have hpoint := flat_support_point_binomial &m t.
have hparams := mode2_parameters_explicit.
move: hparams => [hwords htau].
move: hpoint.
rewrite hwords htau.
trivial.
qed.

end VerifyChallengeM23SubsetBinomialPostFreeze.
