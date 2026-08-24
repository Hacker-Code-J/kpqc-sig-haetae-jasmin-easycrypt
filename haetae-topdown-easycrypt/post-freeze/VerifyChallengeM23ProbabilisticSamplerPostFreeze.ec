require import AllCore Distr DInterval DList IntDiv List Real StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyChallengeM23SamplerStructurePostFreeze
               VerifyChallengeM23StreamSamplerPostFreeze
               VerifyChallengeM23WeightPostFreeze
               VerifyChallengeM23XofSamplerSpecPostFreeze
               VerifyActualChallengeSupportPostFreeze
               Mode2VerifyPrepareNorm.

theory VerifyChallengeM23ProbabilisticSamplerPostFreeze.

(* Probabilistic reference model for the concrete mode-2 rejection/shuffle
   transition.  The oracle below supplies independent uniform bytes; no claim
   is made that deterministic SHAKE output is itself an iid uniform stream,
   nor that this sampler equals the frozen challenge_from_seed abstraction. *)

op challenge_words : int =
  VerifyChallengeM23StreamSamplerPostFreeze.challenge_words.
op mode2_tau : int =
  VerifyChallengeM23StreamSamplerPostFreeze.mode2_tau.
op mode2_start : int = challenge_words - mode2_tau.
op mode2_zero_challenge : BArray1024.t =
  VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_zero_challenge.
op stream_sampler_replay =
  VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_replay.
op challenge_shuffle_update =
  VerifyChallengeM23SamplerStructurePostFreeze.challenge_shuffle_update.
op challenge_weight =
  VerifyChallengeM23WeightPostFreeze.challenge_weight.
op challenge_tail_zero =
  VerifyChallengeM23WeightPostFreeze.challenge_tail_zero.
op challenge_prefix_weight =
  VerifyChallengeM23WeightPostFreeze.challenge_prefix_weight.
op challenge_of_barray =
  VerifyActualChallengeSupportPostFreeze.challenge_of_barray.
op mode2_cardinality_wf =
  VerifyActualChallengeSupportPostFreeze.mode2_cardinality_wf.

lemma mode2_start_index_range :
  0 <= mode2_start < challenge_words.
proof.
rewrite /mode2_start /mode2_tau /challenge_words.
trivial.
qed.

lemma current_index_range i :
  mode2_start <= i < challenge_words =>
  0 <= i < challenge_words.
proof.
move=> hi.
have := mode2_start_index_range.
smt().
qed.

lemma accepted_index_lower i :
  mode2_start <= i => mode2_start <= i + 1.
proof. smt(). qed.

lemma accepted_index_upper i :
  i < challenge_words => i + 1 <= challenge_words.
proof. smt(). qed.

lemma make_index_range i :
  mode2_start <= i =>
  i < challenge_words =>
  mode2_start <= i < challenge_words.
proof.
move=> hlo hhi.
split; first exact hlo.
move=> _.
exact hhi.
qed.

lemma accepted_byte_range b i :
  0 <= b <= 255 => b <= i => 0 <= b <= i.
proof. smt(). qed.

lemma rejected_byte_range b i :
  0 <= b <= 255 => !(b <= i) => !(0 <= b <= i).
proof. smt(). qed.

lemma finished_index_explicit i :
  mode2_start <= i =>
  i <= challenge_words =>
  !(i < challenge_words) =>
  i = challenge_words.
proof. smt(). qed.

op mode2_sampling_inv (cp : BArray1024.t) (i : int) : bool =
  Mode2VerifyPrepareNorm.canonical_challenge cp /\
  mode2_start <= i /\
  i <= challenge_words /\
  challenge_tail_zero cp i /\
  challenge_prefix_weight cp i = i - mode2_start.

lemma mode2_sampling_inv_init :
  mode2_sampling_inv mode2_zero_challenge mode2_start.
proof.
rewrite /mode2_sampling_inv.
split.
+ exact
    (VerifyChallengeM23SamplerStructurePostFreeze.zero_challenge_prefix_canonical
      mode2_zero_challenge
      VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_zero_challenge_zero_prefix).
split.
+ trivial.
split.
+ have := mode2_start_index_range.
  smt().
split.
+ apply VerifyChallengeM23WeightPostFreeze.zero_prefix_tail_zero.
  + have := mode2_start_index_range.
    smt().
  + exact
      VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_zero_challenge_zero_prefix.
have hbound : 0 <= mode2_start <= challenge_words.
+ have := mode2_start_index_range.
  smt().
have hzero_start :
    VerifyChallengeM23SamplerStructurePostFreeze.zero_challenge_prefix
      mode2_zero_challenge mode2_start.
+ move=> j hj.
  apply
    VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_zero_challenge_zero_prefix.
  smt().
have hpw :=
  VerifyChallengeM23WeightPostFreeze.zero_prefix_weight
    mode2_zero_challenge mode2_start hbound
    hzero_start.
rewrite /challenge_prefix_weight.
have hzero : mode2_start - mode2_start = 0 by ring.
rewrite hzero.
exact hpw.
qed.

lemma mode2_sampling_inv_accept cp i b :
  mode2_sampling_inv cp i =>
  i < challenge_words =>
  0 <= b <= i =>
  mode2_sampling_inv (challenge_shuffle_update cp i b) (i + 1).
proof.
move=> [hcanonical [hstart [hupper [htail hweight]]]] hloop hbyte.
rewrite /mode2_sampling_inv.
split.
+ exact
    (VerifyChallengeM23WeightPostFreeze.challenge_shuffle_update_canonical
      cp i b hcanonical (current_index_range i (make_index_range i hstart hloop))
      hbyte).
split; first exact (accepted_index_lower i hstart).
split; first exact (accepted_index_upper i hloop).
split.
+ apply VerifyChallengeM23WeightPostFreeze.challenge_shuffle_update_tail_zero.
  + smt().
  + exact htail.
have hbi : 0 <= b <= i < challenge_words by smt().
have hstep :=
  VerifyChallengeM23WeightPostFreeze.challenge_shuffle_update_weight_step
    cp i b hbi htail.
rewrite /challenge_prefix_weight in hweight.
rewrite /VerifyChallengeM23WeightPostFreeze.challenge_shuffle_update in hstep.
rewrite /challenge_prefix_weight /challenge_shuffle_update.
have hrhs : i + 1 - mode2_start = (i - mode2_start) + 1 by ring.
rewrite hrhs -hweight.
exact hstep.
qed.

lemma mode2_sampling_inv_final cp i :
  mode2_sampling_inv cp i =>
  i = challenge_words =>
  Mode2VerifyPrepareNorm.canonical_challenge cp /\
  challenge_weight cp = mode2_tau.
proof.
move=> hinv hfinal.
move: hinv => [hcanonical [hstart [hupper [htail hweight]]]].
rewrite hfinal in hweight.
rewrite /challenge_prefix_weight in hweight.
split; first exact hcanonical.
rewrite /challenge_weight
        /VerifyChallengeM23WeightPostFreeze.challenge_weight.
have hdelta : challenge_words - mode2_start = mode2_tau.
+ rewrite /mode2_start.
  ring.
rewrite -hdelta.
exact hweight.
qed.

op uniform_byte : int distr = dinter 0 255.

op dchallenge_bytes (k : int) : int list distr =
  dlist uniform_byte k.

op replay_mode2_prefix (bytes : int list) : BArray1024.t * int =
  stream_sampler_replay mode2_zero_challenge mode2_start bytes.

op dreplay_mode2_prefix (k : int) : (BArray1024.t * int) distr =
  dmap (dchallenge_bytes k) replay_mode2_prefix.

lemma uniform_byte_lossless : is_lossless uniform_byte.
proof. by rewrite /uniform_byte; apply dinter_ll. qed.

lemma uniform_byte_support b :
  b \in uniform_byte => 0 <= b <= 255.
proof.
by rewrite /uniform_byte supp_dinter.
qed.

lemma uniform_byte_point b :
  mu uniform_byte (pred1 b) =
  if 0 <= b <= 255 then 1%r / 256%r else 0%r.
proof.
rewrite /uniform_byte dinter1E /pred1 /=.
case (0 <= b <= 255) => hb; first by rewrite /#.
by rewrite /#.
qed.

lemma uniform_byte_point_bound b :
  mu uniform_byte (pred1 b) <= 1%r / 256%r.
proof.
rewrite uniform_byte_point.
case (0 <= b <= 255) => //=.
by smt().
qed.

lemma dchallenge_bytes_lossless k :
  is_lossless (dchallenge_bytes k).
proof.
rewrite /dchallenge_bytes.
by apply dlist_ll; apply uniform_byte_lossless.
qed.

lemma dchallenge_bytes_support k bytes :
  0 <= k =>
  bytes \in dchallenge_bytes k =>
  size bytes = k /\ all (fun b => 0 <= b <= 255) bytes.
proof.
move=> hk.
rewrite /dchallenge_bytes supp_dlist 1:hk.
move=> [hsize hall].
split; first exact hsize.
apply/List.allP => b hb.
move/List.allP: hall => hall.
exact (uniform_byte_support b (hall _ hb)).
qed.

module ReplayMode2PrefixSampler = {
  var observed_bytes : int list

  proc sample (k : int) : BArray1024.t * int = {
    observed_bytes <$ dchallenge_bytes k;
    return replay_mode2_prefix observed_bytes;
  }
}.

lemma replay_mode2_prefix_sampler_support (k0 : int) :
  hoare [ReplayMode2PrefixSampler.sample :
    arg = k0 /\ 0 <= k0 ==>
    size ReplayMode2PrefixSampler.observed_bytes = k0 /\
    all (fun b => 0 <= b <= 255)
      ReplayMode2PrefixSampler.observed_bytes /\
    res = replay_mode2_prefix ReplayMode2PrefixSampler.observed_bytes].
proof.
proc.
wp.
rnd.
skip => />.
move=> hk bs hbs.
have [hsize hall] := dchallenge_bytes_support k0 bs hk hbs.
split; [exact hsize | exact hall].
qed.

module FlatMode2RejectionSampler = {
  var observed_bytes : int list

  proc sample () : BArray1024.t * int = {
    var cp : BArray1024.t;
    var i : int;
    var b : int;

    cp <- mode2_zero_challenge;
    i <- mode2_start;
    observed_bytes <- [];
    while (i < challenge_words) {
      b <$ uniform_byte;
      observed_bytes <- rcons observed_bytes b;
      if (b <= i) {
        cp <- challenge_shuffle_update cp i b;
        i <- i + 1;
      }
    }
    return (cp, i);
  }
}.

lemma flat_mode2_rejection_sampler_lossless :
  phoare [FlatMode2RejectionSampler.sample : true ==> true] = 1%r.
proof.
(* Byte 0 is accepted at every live index, so each iteration decreases the
   finite variant with probability at least 1/256. *)
proc.
wp.
sp.
conseq (: (mode2_start <= i <= challenge_words) ==> true) => //.
while
  (mode2_start <= i <= challenge_words)
  (challenge_words - i)
  mode2_tau
  (1%r / 256%r) => //.
+ by smt().
+ move=> ih.
   seq 3 :
     (mode2_start <= i <= challenge_words)
     1%r 1%r 0%r 0%r.
   + by auto.
   + auto => />; smt(dinter_ll supp_dinter).
   + exact ih.
   + by hoare; auto => />; smt(supp_dinter).
   + trivial.
   + auto => />; smt(dinter_ll supp_dinter).
+ split.
   + move=> &hr _.
     smt().
   + move=> z.
     wp.
     rnd (fun b => b <= i).
     auto => />.
     move=> &hr hlo hhi hlt.
     split.
     + have hsub :
         mu (dinter 0 255) (pred1 0) <=
         mu (dinter 0 255) (fun b0 => b0 <= i{hr}).
       * apply mu_sub => x.
         rewrite /pred1.
         smt().
       rewrite dinter1E /= in hsub.
       exact hsub.
     + move=> _ v hv hvi.
       smt().
qed.

lemma flat_mode2_rejection_sampler_replay :
  hoare [FlatMode2RejectionSampler.sample :
    true ==>
    stream_sampler_replay
      mode2_zero_challenge mode2_start
      FlatMode2RejectionSampler.observed_bytes = res /\
    res.`2 = challenge_words].
proof.
proc.
wp.
while
  (mode2_start <= i /\
   i <= challenge_words /\
   stream_sampler_replay
     mode2_zero_challenge mode2_start
     FlatMode2RejectionSampler.observed_bytes = (cp, i)).
+ auto => />.
  move=> &hr hstart hupper hrep hloop b hb.
  have hbyte : 0 <= b <= 255.
  + exact (uniform_byte_support b hb).
  have hi := make_index_range i{hr} hstart hloop.
  split.
  + move=> haccept.
    split; first exact (accepted_index_lower i{hr} hstart).
    split; first exact (accepted_index_upper i{hr} hloop).
    rewrite /stream_sampler_replay foldl_rcons.
    rewrite /stream_sampler_replay in hrep.
    rewrite hrep.
    exact
      (VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_step_accept
        cp{hr} i{hr} b
        (current_index_range i{hr} hi)
        (accepted_byte_range b i{hr} hbyte haccept)).
  + move=> hreject.
    rewrite /stream_sampler_replay foldl_rcons.
    rewrite /stream_sampler_replay in hrep.
    rewrite hrep.
    exact
      (VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_step_reject
        cp{hr} i{hr} b
        (current_index_range i{hr} hi)
        (rejected_byte_range b i{hr} hbyte hreject)).
+ auto => />.
  move=> observed cp i hdone hstart hupper hrep.
  exact (finished_index_explicit i hstart hupper hdone).
qed.

lemma flat_mode2_rejection_sampler_canonical_weight :
  hoare [FlatMode2RejectionSampler.sample :
    true ==>
    res.`2 = challenge_words /\
    Mode2VerifyPrepareNorm.canonical_challenge res.`1 /\
    challenge_weight res.`1 = mode2_tau].
proof.
proc.
wp.
while (mode2_sampling_inv cp i).
+ auto => />.
  move=> &hr hcanonical hstart hupper htail hweight hloop b hb.
  have hinv : mode2_sampling_inv cp{hr} i{hr}.
  + rewrite /mode2_sampling_inv.
    split; first exact hcanonical.
    split; first exact hstart.
    split; first exact hupper.
    split; [exact htail | exact hweight].
  have hbyte : 0 <= b <= 255.
  + exact (uniform_byte_support b hb).
  move=> haccept.
  exact
    (mode2_sampling_inv_accept cp{hr} i{hr} b hinv hloop
      (accepted_byte_range b i{hr} hbyte haccept)).
+ auto => />;
  smt(mode2_sampling_inv_init mode2_sampling_inv_final
      finished_index_explicit).
qed.

lemma canonical_weight_implies_mode2_cardinality cp :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  challenge_weight cp = mode2_tau =>
  mode2_cardinality_wf (challenge_of_barray cp).
proof.
move=> hcanonical hweight.
exact
  (VerifyActualChallengeSupportPostFreeze.canonical_machine_weight_implies_mode2_cardinality_wf
    cp hcanonical hweight).
qed.

lemma flat_mode2_rejection_sampler_cardinality :
  hoare [FlatMode2RejectionSampler.sample :
    true ==>
    res.`2 = challenge_words /\
    mode2_cardinality_wf (challenge_of_barray res.`1)].
proof.
conseq flat_mode2_rejection_sampler_canonical_weight.
move=> &hr _ result [hfinal [hcanonical hweight]].
split; first exact hfinal.
exact (canonical_weight_implies_mode2_cardinality result.`1 hcanonical hweight).
qed.

end VerifyChallengeM23ProbabilisticSamplerPostFreeze.
