require import AllCore Distr DInterval FSet List Real StdBigop StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyChallengeM23SamplerStructurePostFreeze
               VerifyChallengeM23ProbabilisticSamplerPostFreeze
               VerifyChallengeM23FixedAcceptedSamplerPostFreeze
               VerifyChallengeM23XofSamplerSpecPostFreeze.

theory VerifyChallengeM23UniformSubsetPostFreeze.

import IntOrder RealOrder Bigreal.BRA.

(* Pure reservoir-combinatorics layer for the ideal accepted-index law.  It
   proves the exact machine support transition, the regular predecessor
   fibers, and preservation of uniformity by one reservoir step.  The full
   58-step distributional induction and the explicit binomial denominator
   remain separate obligations. *)

op challenge_words : int =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.challenge_words.
op mode2_start : int =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.mode2_start.
op mode2_tau : int =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.mode2_tau.
op mode2_zero_challenge : BArray1024.t =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.mode2_zero_challenge.

op support_prefix (cp : BArray1024.t) (n : int) : int fset =
  FSet.filter
    (fun j => BArray1024.get32 cp j = W32.one)
    (FSet.rangeset 0 n).

op reservoir_step (s : int fset) (i b : int) : int fset =
  if b \in s then s `|` FSet.fset1 i else s `|` FSet.fset1 b.

op valid_subset (n k : int) (s : int fset) : bool =
  s \subset FSet.rangeset 0 n /\ FSet.card s = k.

op reservoir_predecessor (t : int fset) (i x : int) : int fset =
  if i \in t then t `\` FSet.fset1 i else t `\` FSet.fset1 x.

op reservoir_fiber (t : int fset) (i : int) : (int fset * int) list =
  map (fun x => (reservoir_predecessor t i x, x)) (FSet.elems t).

lemma support_prefix_mem cp n j :
  j \in support_prefix cp n <=>
  0 <= j < n /\ BArray1024.get32 cp j = W32.one.
proof.
rewrite /support_prefix FSet.in_filter FSet.mem_rangeset.
smt().
qed.

lemma mode2_support_init :
  support_prefix mode2_zero_challenge mode2_start = FSet.fset0.
proof.
apply/FSet.fsetP => j.
rewrite support_prefix_mem FSet.in_fset0.
split.
move=> [hj hget].
rewrite
  VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_zero_challenge_get32
  in hget.
have :=
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start_index_range;
smt().
smt().
smt().
qed.

lemma support_prefix_shuffle_step cp i b :
  0 <= b <= i =>
  i < challenge_words =>
  support_prefix
    (VerifyChallengeM23FixedAcceptedSamplerPostFreeze.challenge_shuffle_update
      cp i b)
    (i + 1) =
  reservoir_step (support_prefix cp i) i b.
proof.
move=> hb hi.
apply/FSet.fsetP => j.
rewrite support_prefix_mem /reservoir_step.
case (b \in support_prefix cp i) => hbin.
+ rewrite FSet.in_fsetU FSet.in_fset1.
  move/support_prefix_mem: hbin => [hbr hbget].
  rewrite /VerifyChallengeM23FixedAcceptedSamplerPostFreeze.challenge_shuffle_update
          /VerifyChallengeM23SamplerStructurePostFreeze.challenge_shuffle_update.
  rewrite !BArray1024.get_set32E 1:/# 1:/# 1:/# 1:/#.
  case (j = b) => hjb.
  + subst j; rewrite !ifT 1:/# support_prefix_mem; smt().
  rewrite ifF 1:/#.
  case (j = i) => hji.
  + subst j; rewrite ifT 1:/# hbget support_prefix_mem; smt().
  rewrite ifF 1:/# support_prefix_mem.
  smt().
+ rewrite FSet.in_fsetU FSet.in_fset1.
  have hbnot :
      !(0 <= b < i /\ BArray1024.get32 cp b = W32.one).
  + move: hbin; rewrite support_prefix_mem; trivial.
  rewrite /VerifyChallengeM23FixedAcceptedSamplerPostFreeze.challenge_shuffle_update
          /VerifyChallengeM23SamplerStructurePostFreeze.challenge_shuffle_update.
  rewrite !BArray1024.get_set32E 1:/# 1:/# 1:/# 1:/#.
  case (j = b) => hjb.
  + subst j; rewrite !ifT 1:/#; smt().
  rewrite ifF 1:/#.
  case (j = i) => hji.
  + subst j; rewrite ifT 1:/# support_prefix_mem; smt().
  rewrite ifF 1:/# support_prefix_mem.
  smt().
qed.

lemma mode2_valid_subset_init :
  valid_subset mode2_start 0
    (support_prefix mode2_zero_challenge mode2_start).
proof.
rewrite mode2_support_init /valid_subset.
split; first exact (FSet.sub0set (FSet.rangeset 0 mode2_start)).
exact FSet.fcards0.
qed.

lemma valid_subset_current_notin s i k :
  valid_subset i k s => i \notin s.
proof.
move=> [hsub _].
apply/negP => hiin.
move: (hsub i hiin).
rewrite FSet.mem_rangeset.
smt().
qed.

lemma fset_remove_restore (s : int fset) x :
  x \in s => (s `\` FSet.fset1 x) `|` FSet.fset1 x = s.
proof.
move=> hxin.
apply/FSet.fsetP => y.
rewrite FSet.in_fsetU1 FSet.in_fsetD1.
smt().
qed.

lemma fset_add_remove_new (s : int fset) x :
  x \notin s => (s `|` FSet.fset1 x) `\` FSet.fset1 x = s.
proof.
move=> hxnot.
apply/FSet.fsetP => y.
rewrite FSet.in_fsetD1 FSet.in_fsetU1.
smt().
qed.

lemma reservoir_predecessor_valid t i k x :
  valid_subset (i + 1) (k + 1) t =>
  x \in t =>
  valid_subset i k (reservoir_predecessor t i x) /\
  0 <= x <= i.
proof.
move=> [hsub hcard] hxin.
have hxrange := hsub x hxin.
rewrite FSet.mem_rangeset in hxrange.
rewrite /reservoir_predecessor.
case (i \in t) => hiin.
+ split.
  + rewrite /valid_subset.
    split.
    * move=> y.
      rewrite FSet.in_fsetD1 FSet.mem_rangeset.
      move=> [hyin hyneq].
      move: (hsub y hyin).
      rewrite FSet.mem_rangeset.
      smt().
    * move: (FSet.fcardD1 t i).
      rewrite hiin hcard /=.
      smt().
  + smt().
+ split.
  + rewrite /valid_subset.
    split.
    * move=> y.
      rewrite FSet.in_fsetD1 FSet.mem_rangeset.
      move=> [hyin hyneq].
      have hyrange := hsub y hyin.
      rewrite FSet.mem_rangeset in hyrange.
      have hynei : y <> i by smt().
      smt().
    * move: (FSet.fcardD1 t x).
      rewrite hxin hcard /=.
      smt().
  + smt().
qed.

lemma reservoir_predecessor_step t i k x :
  valid_subset (i + 1) (k + 1) t =>
  x \in t =>
  reservoir_step (reservoir_predecessor t i x) i x = t.
proof.
move=> hvalid hxin.
rewrite /reservoir_predecessor.
case (i \in t) => hiin.
+ case (x = i) => hxi.
  + subst x.
    rewrite /reservoir_step FSet.in_fsetD1 hiin /=.
    exact (fset_remove_restore t i hiin).
  + have hxpred : x \in t `\` FSet.fset1 i.
    + rewrite FSet.in_fsetD1; smt().
    rewrite /reservoir_step hxpred.
    exact (fset_remove_restore t i hiin).
+ have hxnotpred : x \notin t `\` FSet.fset1 x.
  + rewrite FSet.in_fsetD1; smt().
  rewrite /reservoir_step hxnotpred.
  exact (fset_remove_restore t x hxin).
qed.

lemma reservoir_step_predecessorK s i k b :
  valid_subset i k s =>
  0 <= b <= i =>
  reservoir_predecessor (reservoir_step s i b) i b = s.
proof.
move=> hvalid hb.
have hinotin := valid_subset_current_notin s i k hvalid.
rewrite /reservoir_step.
case (b \in s) => hbin.
+ rewrite /reservoir_predecessor FSet.in_fsetU1.
  rewrite hinotin /=.
  exact (fset_add_remove_new s i hinotin).
+ case (b = i) => hbi.
  + subst b.
    rewrite /reservoir_predecessor FSet.in_fsetU1 /=.
    exact (fset_add_remove_new s i hinotin).
  + rewrite /reservoir_predecessor FSet.in_fsetU1.
    have hineb : i <> b by smt().
    rewrite hinotin hineb /=.
    exact (fset_add_remove_new s b hbin).
qed.

lemma reservoir_fiber_size t i :
  size (reservoir_fiber t i) = FSet.card t.
proof. by rewrite /reservoir_fiber size_map FSet.cardE. qed.

lemma reservoir_fiber_uniq t i :
  uniq (reservoir_fiber t i).
proof.
rewrite /reservoir_fiber.
rewrite List.map_inj_in_uniq.
+ move=> x y _ _ hxy.
  smt().
+ exact FSet.uniq_elems.
qed.

lemma reservoir_fiber_mem t i p :
  p \in reservoir_fiber t i <=>
  exists x,
    x \in t /\ p = (reservoir_predecessor t i x, x).
proof.
rewrite /reservoir_fiber.
split.
+ move/List.mapP => [x [hxin ->]].
  exists x.
  split; first by rewrite FSet.memE.
  trivial.
+ move=> [x [hxin ->]].
  apply/List.mapP.
  exists x.
  split; first by rewrite -FSet.memE.
  trivial.
qed.

lemma reservoir_step_contains_choice s i b :
  b \in reservoir_step s i b.
proof.
rewrite /reservoir_step.
case (b \in s) => hbin.
+ rewrite FSet.in_fsetU1; smt().
+ rewrite FSet.in_fsetU1; smt().
qed.

lemma reservoir_fiberP t i k s b :
  valid_subset (i + 1) (k + 1) t =>
  ((s, b) \in reservoir_fiber t i <=>
   valid_subset i k s /\
   0 <= b <= i /\
   reservoir_step s i b = t).
proof.
move=> htvalid.
split.
+ move/reservoir_fiber_mem => [x [hx hp]].
  move: hp => [-> ->].
  have hpvalid := reservoir_predecessor_valid t i k x htvalid hx.
  move: hpvalid => [hprev hxr].
  split; first exact hprev.
  split; first exact hxr.
  exact (reservoir_predecessor_step t i k x htvalid hx).
+ move=> [hsvalid [hb hstep]].
  have hbin : b \in t.
  + rewrite -hstep.
    exact (reservoir_step_contains_choice s i b).
  have hpred : reservoir_predecessor t i b = s.
  + have hpred0 := reservoir_step_predecessorK s i k b hsvalid hb.
    rewrite hstep in hpred0.
    exact hpred0.
  apply/reservoir_fiber_mem.
  exists b.
  split; first exact hbin.
  by rewrite hpred.
qed.

lemma uniform_mu_mem_same_size ['a]
    (d : 'a distr) (xs ys : 'a list) :
  is_uniform d =>
  uniq xs =>
  uniq ys =>
  (forall x, x \in xs => x \in d) =>
  (forall y, y \in ys => y \in d) =>
  size xs = size ys =>
  mu d (mem xs) = mu d (mem ys).
proof.
elim: xs ys => [|x xs ih] [|y ys] //=.
+ smt(size_ge0).
+ smt(size_ge0).
+ move=> huni [hxnot huxs] [hynot huys] hxs hys hsize.
  rewrite !mu_mem_uniq 1:/# 1:/# !big_cons /predT /=.
  have hxd : x \in d by apply hxs; trivial.
  have hyd : y \in d by apply hys; trivial.
  rewrite (huni x y hxd hyd).
  congr.
  rewrite -!mu_mem_uniq 1:huxs 1:huys.
  apply (ih ys huni huxs huys).
  + move=> z hz; apply hxs; smt().
  + move=> z hz; apply hys; smt().
  + smt().
qed.

op reservoir_pair_distr (d : int fset distr) (i : int) :
    (int fset * int) distr =
  d `*` dinter 0 i.

op reservoir_lift (d : int fset distr) (i : int) : int fset distr =
  dmap (reservoir_pair_distr d i)
    (fun (p : int fset * int) => reservoir_step p.`1 i p.`2).

lemma reservoir_pair_support d i s b :
  (s, b) \in reservoir_pair_distr d i <=>
  s \in d /\ 0 <= b <= i.
proof.
rewrite /reservoir_pair_distr supp_dprod supp_dinter.
smt().
qed.

lemma reservoir_fiber_source d i k t s b :
  (forall u, u \in d <=> valid_subset i k u) =>
  valid_subset (i + 1) (k + 1) t =>
  (((s, b) \in reservoir_pair_distr d i /\
     reservoir_step s i b = t) <=>
    (s, b) \in reservoir_fiber t i).
proof.
move=> hdsupport htvalid.
rewrite reservoir_pair_support hdsupport.
have hfiber := reservoir_fiberP t i k s b htvalid.
move: hfiber => [hforward hbackward].
split.
+ move=> [[hsvalid hb] hstep].
  apply hbackward.
  split; first exact hsvalid.
  split; [exact hb | exact hstep].
+ move/hforward => [hsvalid [hb hstep]].
  split.
  + split; [exact hsvalid | exact hb].
  + exact hstep.
qed.

lemma reservoir_step_valid s i k b :
  0 <= i =>
  valid_subset i k s =>
  0 <= b <= i =>
  valid_subset (i + 1) (k + 1) (reservoir_step s i b).
proof.
move=> hi [hsub hcard] hb.
rewrite /reservoir_step.
case (b \in s) => hbin.
+ have hinotin : i \notin s.
  + apply/negP => hiin.
    move: (hsub i hiin).
    rewrite FSet.mem_rangeset.
    smt().
  split.
  + move=> x.
    rewrite FSet.in_fsetU1 !FSet.mem_rangeset.
    move=> [hxin | ->].
    * move: (hsub x hxin).
      rewrite FSet.mem_rangeset.
      smt().
    * smt().
  + rewrite FSet.fcardU1 hinotin hcard.
    smt().
+ split.
  + move=> x.
    rewrite FSet.in_fsetU1 !FSet.mem_rangeset.
    move=> [hxin | ->].
    * move: (hsub x hxin).
      rewrite FSet.mem_rangeset.
      smt().
    * smt().
  + rewrite FSet.fcardU1 hbin hcard.
    smt().
qed.

lemma reservoir_lift_output_valid d i k t :
  0 <= i =>
  (forall s, s \in d => valid_subset i k s) =>
  t \in reservoir_lift d i =>
  valid_subset (i + 1) (k + 1) t.
proof.
move=> hi hvalid.
rewrite /reservoir_lift supp_dmap.
move=> [[s b] [hsupport ->]] /=.
move: hsupport.
rewrite reservoir_pair_support.
move=> [hs hb].
exact (reservoir_step_valid s i k b hi (hvalid s hs) hb).
qed.

lemma reservoir_lift_point_fiber d i k t :
  (forall s, s \in d <=> valid_subset i k s) =>
  valid_subset (i + 1) (k + 1) t =>
  mu1 (reservoir_lift d i) t =
  mu (reservoir_pair_distr d i) (mem (reservoir_fiber t i)).
proof.
move=> hdsupport htvalid.
rewrite /reservoir_lift dmap1E.
apply mu_eq_support => [[s b]] hpair /=.
rewrite /pred1 /(\o).
have hfiber := reservoir_fiber_source d i k t s b hdsupport htvalid.
move: hfiber => [hforward hbackward].
apply/eq_iff.
split.
+ move=> hstep.
  apply hforward.
  split; [exact hpair | exact hstep].
+ move/hbackward => [_ hstep].
  exact hstep.
qed.

lemma reservoir_lift_lossless d i :
  is_lossless d =>
  0 <= i =>
  is_lossless (reservoir_lift d i).
proof.
move=> hdll hi.
rewrite /reservoir_lift.
apply dmap_ll.
rewrite /reservoir_pair_distr.
apply dprod_ll_auto.
+ exact hdll.
+ apply dinter_ll; smt().
qed.

lemma reservoir_lift_uniform d i k :
  0 <= i =>
  is_uniform d =>
  (forall s, s \in d <=> valid_subset i k s) =>
  is_uniform (reservoir_lift d i).
proof.
move=> hi hduni hdsupport t u ht hu.
have htvalid : valid_subset (i + 1) (k + 1) t.
+ apply (reservoir_lift_output_valid d i k t hi).
  + move=> s hs.
    move: hdsupport => /(_ s) [hforward _].
    apply hforward; exact hs.
  + exact ht.
have huvalid : valid_subset (i + 1) (k + 1) u.
+ apply (reservoir_lift_output_valid d i k u hi).
  + move=> s hs.
    move: hdsupport => /(_ s) [hforward _].
    apply hforward; exact hs.
  + exact hu.
rewrite (reservoir_lift_point_fiber d i k t hdsupport htvalid).
rewrite (reservoir_lift_point_fiber d i k u hdsupport huvalid).
apply uniform_mu_mem_same_size.
+ rewrite /reservoir_pair_distr.
  apply dprod_uni.
  + exact hduni.
  + exact (dinter_uni 0 i).
+ exact (reservoir_fiber_uniq t i).
+ exact (reservoir_fiber_uniq u i).
+ move=> [s b] hp.
  have hfiber := reservoir_fiber_source d i k t s b hdsupport htvalid.
  move: hfiber => [_ hbackward].
  move: (hbackward hp) => [hsrc _].
  exact hsrc.
+ move=> [s b] hp.
  have hfiber := reservoir_fiber_source d i k u s b hdsupport huvalid.
  move: hfiber => [_ hbackward].
  move: (hbackward hp) => [hsrc _].
  exact hsrc.
+ rewrite !reservoir_fiber_size.
  move: htvalid huvalid.
  rewrite /valid_subset.
  smt().
qed.

module ReservoirSubsetSampler = {
  proc sample () : int fset * int = {
    var s : int fset;
    var i : int;
    var b : int;

    s <- FSet.fset0;
    i <- mode2_start;
    while (i < challenge_words) {
      b <$ dinter 0 i;
      s <- reservoir_step s i b;
      i <- i + 1;
    }
    return (s, i);
  }
}.

lemma reservoir_subset_sampler_indexed_valid :
  hoare [ReservoirSubsetSampler.sample :
    true ==>
    res.`2 = challenge_words /\
    valid_subset res.`2 (res.`2 - mode2_start) res.`1].
proof.
proc.
seq 2 :
  (valid_subset i (i - mode2_start) s /\
   mode2_start <= i <= challenge_words).
+ auto => />.
  smt(mode2_valid_subset_init
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start_index_range).
wp.
while (valid_subset i (i - mode2_start) s /\
       mode2_start <= i <= challenge_words).
+ auto => />.
  move=> &hr hsub hcard hstart hupper hloop b hb.
  have hbyte : 0 <= b <= i{hr}.
  + move: hb; rewrite supp_dinter; smt().
  have hnext :
      valid_subset (i{hr} + 1)
        ((i{hr} - mode2_start) + 1)
        (reservoir_step s{hr} i{hr} b).
  + apply reservoir_step_valid.
    * have :=
        VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start_index_range.
      smt().
    * rewrite /valid_subset.
      split; [exact hsub | exact hcard].
    * exact hbyte.
  move: hnext.
  rewrite /valid_subset.
  move=> [hsubnext hcardnext].
  split.
  + split.
    * exact hsubnext.
    * rewrite hcardnext.
      ring.
  + smt().
+ auto => />; smt().
qed.

lemma reservoir_subset_sampler_valid :
  hoare [ReservoirSubsetSampler.sample :
    true ==>
    res.`2 = challenge_words /\
    valid_subset challenge_words mode2_tau res.`1].
proof.
conseq reservoir_subset_sampler_indexed_valid.
move=> &hr _ result [hfinal hvalid].
split; first exact hfinal.
rewrite hfinal in hvalid.
have hdelta : challenge_words - mode2_start = mode2_tau.
+ rewrite /challenge_words /mode2_start /mode2_tau.
  trivial.
rewrite -hdelta.
exact hvalid.
qed.

end VerifyChallengeM23UniformSubsetPostFreeze.
