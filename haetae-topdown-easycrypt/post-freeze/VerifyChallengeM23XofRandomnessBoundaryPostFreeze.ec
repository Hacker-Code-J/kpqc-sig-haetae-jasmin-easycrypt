require import AllCore Binomial DInterval Distr FSet List Real StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyChallengeAbsorbStatePostFreeze
               VerifyChallengeM23ProbabilisticSamplerPostFreeze
               VerifyChallengeM23StreamSamplerPostFreeze
               VerifyChallengeM23SubsetBinomialPostFreeze
               VerifyChallengeM23UniformSamplerBridgePostFreeze
               VerifyChallengeM23XofSamplerSpecPostFreeze.

theory VerifyChallengeM23XofRandomnessBoundaryPostFreeze.

(* Explicit randomness boundary for the concrete-XOF-facing challenge model.
   The implementation proof exposes a deterministic squeeze transcript; it
   does not make that transcript random.  The sampler below therefore takes a
   byte distribution as an explicit parameter.  Its final law is conditional
   on a full-support uniform-byte contract, which an RO/XOF game must justify
   before instantiating this layer. *)

module FlatMode2RejectionSampler =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.FlatMode2RejectionSampler.

op challenge_words : int =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_words.
op mode2_start : int =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start.
op mode2_zero_challenge =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_zero_challenge.
op challenge_shuffle_update =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_shuffle_update.
op uniform_byte : int distr =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte.
op support_prefix =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.support_prefix.
op valid_subset =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.valid_subset.
op reservoir_rounds =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.reservoir_rounds.

op replayed_support (bytes : int list) : int fset =
  let result =
    VerifyChallengeM23ProbabilisticSamplerPostFreeze.replay_mode2_prefix bytes
  in support_prefix result.`1 result.`2.

(* Local distributional obligation used by the support theorem: the stopped
   XOF transcript, after deterministic replay, has exactly the ideal reservoir
   support distribution.  No concrete stopped-transcript distribution is
   postulated here. *)
op stopped_transcript_replayed_support_distribution_law
    (dstopped : int list distr) : bool =
  forall P,
    mu (dmap dstopped replayed_support) P =
    mu (reservoir_rounds 58) P.

lemma stopped_transcript_support_point_256_58 dstopped t :
  stopped_transcript_replayed_support_distribution_law dstopped =>
  mu1 (dmap dstopped replayed_support) t =
  if valid_subset 256 58 t
  then 1%r / (bin 256 58)%r
  else 0%r.
proof.
move=> hlaw.
have hpointlaw :
    mu1 (dmap dstopped replayed_support) t =
    mu1 (reservoir_rounds 58) t.
+ exact (hlaw (pred1 t)).
rewrite hpointlaw.
exact
  (VerifyChallengeM23SubsetBinomialPostFreeze.reservoir_rounds_final_point_256_58
     t).
qed.

(* Stronger reusable sufficient condition.  Repeated calls to sample(dbyte)
   are independent by the probabilistic program semantics; this contract
   fixes their common marginal to the full uniform byte law. *)
op xof_byte_distribution_ok (dbyte : int distr) : bool =
  is_lossless dbyte /\
  is_uniform dbyte /\
  (forall b, b \in dbyte <=> 0 <= b <= 255).

lemma xof_byte_distribution_ok_eq_uniform dbyte :
  xof_byte_distribution_ok dbyte => dbyte = uniform_byte.
proof.
move=> [hdll [hduni hsupport]].
have huniformll : is_lossless uniform_byte.
+ exact
    VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte_lossless.
have huniform : is_uniform uniform_byte.
+ rewrite /uniform_byte
          /VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte.
  exact (dinter_uni 0 255).
have hsupporteq : support dbyte = support uniform_byte.
+ apply fun_ext => b.
  rewrite hsupport /uniform_byte
          /VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte
          supp_dinter.
  smt().
apply/eq_distr => b.
rewrite
  (mu1_uni_ll dbyte b hduni hdll)
  (mu1_uni_ll uniform_byte b huniform huniformll)
  hsupporteq.
trivial.
qed.

lemma uniform_byte_distribution_ok :
  xof_byte_distribution_ok uniform_byte.
proof.
rewrite /xof_byte_distribution_ok.
split.
+ exact
    VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte_lossless.
split.
+ rewrite /uniform_byte
          /VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte.
  exact (dinter_uni 0 255).
+ move=> b.
  rewrite /uniform_byte
          /VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte
          supp_dinter.
  smt().
qed.

module ParametricXofByteSampler = {
  var observed_bytes : int list

  proc sample(dbyte : int distr) : BArray1024.t * int = {
    var cp : BArray1024.t;
    var i : int;
    var b : int;

    cp <- mode2_zero_challenge;
    i <- mode2_start;
    observed_bytes <- [];
    while (i < challenge_words) {
      b <$ dbyte;
      observed_bytes <- rcons observed_bytes b;
      if (b <= i) {
        cp <- challenge_shuffle_update cp i b;
        i <- i + 1;
      }
    }
    return (cp, i);
  }
}.

equiv parametric_xof_byte_flat :
  ParametricXofByteSampler.sample ~ FlatMode2RejectionSampler.sample :
  dbyte{1} = uniform_byte ==>
  ={res} /\
  ParametricXofByteSampler.observed_bytes{1} =
    FlatMode2RejectionSampler.observed_bytes{2}.
proof.
proc.
while
  (dbyte{1} = uniform_byte /\
   ={cp, i} /\
   ParametricXofByteSampler.observed_bytes{1} =
     FlatMode2RejectionSampler.observed_bytes{2}).
+ wp.
  rnd.
  auto => />.
+ auto => />.
qed.

lemma parametric_xof_flat_support_pr &m1 &m2 dbyte P :
  xof_byte_distribution_ok dbyte =>
  Pr[ParametricXofByteSampler.sample(dbyte) @ &m1 :
       P (support_prefix res.`1 res.`2)] =
  Pr[FlatMode2RejectionSampler.sample() @ &m2 :
       P (support_prefix res.`1 res.`2)].
proof.
move=> hbyte.
have hbyteeq := xof_byte_distribution_ok_eq_uniform dbyte hbyte.
byequiv parametric_xof_byte_flat => //=.
qed.

lemma parametric_xof_flat_transcript_pr &m1 &m2 dbyte P :
  xof_byte_distribution_ok dbyte =>
  Pr[ParametricXofByteSampler.sample(dbyte) @ &m1 :
       P ParametricXofByteSampler.observed_bytes] =
  Pr[FlatMode2RejectionSampler.sample() @ &m2 :
       P FlatMode2RejectionSampler.observed_bytes].
proof.
move=> hbyte.
have hbyteeq := xof_byte_distribution_ok_eq_uniform dbyte hbyte.
byequiv parametric_xof_byte_flat => //=.
qed.

lemma parametric_xof_support_point_256_58 &m dbyte t :
  xof_byte_distribution_ok dbyte =>
  Pr[ParametricXofByteSampler.sample(dbyte) @ &m :
       support_prefix res.`1 res.`2 = t] =
  if valid_subset 256 58 t
  then 1%r / (bin 256 58)%r
  else 0%r.
proof.
move=> hbyte.
rewrite
  (parametric_xof_flat_support_pr &m &m dbyte (pred1 t) hbyte).
exact
  (VerifyChallengeM23SubsetBinomialPostFreeze.flat_support_point_256_58
     &m t).
qed.

op mode2_xof_sampler_relation =
  VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_xof_sampler_relation.

lemma concrete_xof_relation_exposes_replay
    (highp : BArray1152.t) (lsbp mup : BArray32.t)
    (actual : BArray1024.t) :
  mode2_xof_sampler_relation highp lsbp mup actual =>
  exists bytes,
    VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_replay
      VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_zero_challenge
      VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_start
      bytes =
    (actual, VerifyChallengeM23XofSamplerSpecPostFreeze.challenge_words).
proof.
rewrite /mode2_xof_sampler_relation
        /VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_xof_sampler_relation.
move=> hrelation.
move: hrelation => [blocks pos].
move=> [hblocks [hpos hreplay]].
exists
  (VerifyChallengeM23StreamSamplerPostFreeze.challenge_squeeze_consumed_prefix
     (VerifyChallengeAbsorbStatePostFreeze.mode2_state highp lsbp mup)
     blocks pos).
exact hreplay.
qed.

lemma concrete_xof_relation_exposes_model_replay
    (highp : BArray1152.t) (lsbp mup : BArray32.t)
    (actual : BArray1024.t) :
  mode2_xof_sampler_relation highp lsbp mup actual =>
  exists bytes,
    VerifyChallengeM23ProbabilisticSamplerPostFreeze.replay_mode2_prefix
      bytes = (actual, challenge_words).
proof.
move=> hrelation.
have hreplay :=
  concrete_xof_relation_exposes_replay highp lsbp mup actual hrelation.
move: hreplay => [bytes hreplay].
exists bytes.
exact hreplay.
qed.

end VerifyChallengeM23XofRandomnessBoundaryPostFreeze.
