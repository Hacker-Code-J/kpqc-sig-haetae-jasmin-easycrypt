require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget KeygenShakeStreamSpec
               Mode2VerifyPrepareNorm
               VerifyChallengeM23SamplerStructurePostFreeze
               VerifyChallengeM23StreamSamplerPostFreeze
               VerifyChallengeAbsorbStatePostFreeze
               VerifyChallengeM23WeightPostFreeze
               HAETAE_Params
               HAETAE_Algebra.

theory VerifyChallengeM23XofSamplerSpecPostFreeze.

module Verify = VerifyCoreTarget.M.
module Trace =
  VerifyChallengeM23StreamSamplerPostFreeze.ActualVerifyChallengeM23StreamTrace.

op mode2_tau : int =
  VerifyChallengeM23StreamSamplerPostFreeze.mode2_tau.
op challenge_words : int =
  VerifyChallengeM23StreamSamplerPostFreeze.challenge_words.
op mode2_start : int =
  VerifyChallengeM23WeightPostFreeze.mode2_start.
op mode2_highlen : int =
  VerifyChallengeAbsorbStatePostFreeze.mode2_highlen.
op challenge_weight =
  VerifyChallengeM23WeightPostFreeze.challenge_weight.

op mode2_zero_challenge : BArray1024.t =
  BArray1024.of_list32 (nseq challenge_words W32.zero).

op challenge_of_barray
    (cp : BArray1024.t) : HAETAE_Algebra.challenge =
  mkseq
    (fun i => W32.to_uint (BArray1024.get32 cp i))
    Mode2VerifyPrepareNorm.challenge_words.

(* Implementation-faithful partial-correctness specification.  Unlike the
   historical challenge_from_seed candidate, this relation exposes the actual
   zero-initialized shuffle over a concrete SHAKE256 squeeze prefix.  It does
   not claim termination, a distributional result, or paper-hash equality. *)
op mode2_xof_sampler_relation
    (highp : BArray1152.t) (lsbp mup : BArray32.t)
    (actual : BArray1024.t) : bool =
  exists (blocks pos : int),
    1 <= blocks /\
    0 <= pos <= 136 /\
    VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_replay
      mode2_zero_challenge mode2_start
      (VerifyChallengeM23StreamSamplerPostFreeze.challenge_squeeze_consumed_prefix
        (VerifyChallengeAbsorbStatePostFreeze.mode2_state highp lsbp mup)
        blocks pos) =
      (actual, challenge_words).

lemma mode2_zero_challenge_get32 i :
  0 <= i < challenge_words =>
  BArray1024.get32 mode2_zero_challenge i = W32.zero.
proof.
move=> hi.
rewrite /mode2_zero_challenge BArray1024.get32_of_list32.
+ rewrite size_nseq /challenge_words
          /VerifyChallengeM23StreamSamplerPostFreeze.challenge_words
          /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
          /Mode2VerifyPrepareNorm.challenge_words /=.
  trivial.
by rewrite (nth_nseq W32.zero i challenge_words W32.zero hi).
qed.

lemma mode2_zero_challenge_zero_prefix :
  VerifyChallengeM23SamplerStructurePostFreeze.zero_challenge_prefix
    mode2_zero_challenge challenge_words.
proof.
rewrite /VerifyChallengeM23SamplerStructurePostFreeze.zero_challenge_prefix.
move=> i hi.
exact (mode2_zero_challenge_get32 i hi).
qed.

lemma zero_challenge_prefix_eq_mode2_zero cp :
  VerifyChallengeM23SamplerStructurePostFreeze.zero_challenge_prefix
    cp challenge_words =>
  cp = mode2_zero_challenge.
proof.
move=> hzero.
apply BArray1024.ext_eq32 => i hi.
rewrite mode2_zero_challenge_get32.
+ move: hi.
  rewrite /challenge_words
          /VerifyChallengeM23StreamSamplerPostFreeze.challenge_words
          /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
          /Mode2VerifyPrepareNorm.challenge_words /=.
  smt().
apply hzero.
move: hi.
rewrite /challenge_words
        /VerifyChallengeM23StreamSamplerPostFreeze.challenge_words
        /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
        /Mode2VerifyPrepareNorm.challenge_words /=.
smt().
qed.

lemma poly_challenge_m23_init_mode2_zero (cp0 : BArray1024.t) :
  hoare [Verify._poly_challenge_m23_init :
    cp = cp0 ==> res = mode2_zero_challenge].
proof.
conseq
  (VerifyChallengeM23SamplerStructurePostFreeze.poly_challenge_m23_init_zero_prefix
    cp0).
move=> &hr _ result hzero.
exact (zero_challenge_prefix_eq_mode2_zero result hzero).
qed.

lemma challenge_of_barray_size (cp : BArray1024.t) :
  size (challenge_of_barray cp) = HAETAE_Params.n.
proof.
by rewrite /challenge_of_barray size_mkseq
           /Mode2VerifyPrepareNorm.challenge_words /HAETAE_Params.n.
qed.

lemma canonical_challenge_implies_challenge_wf
    (cp : BArray1024.t) :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  HAETAE_Algebra.challenge_wf (challenge_of_barray cp).
proof.
move=> hcanonical.
rewrite /HAETAE_Algebra.challenge_wf.
split.
+ rewrite /HAETAE_Algebra.poly_wf challenge_of_barray_size.
   trivial.
+ apply/List.allP => x hx.
   move: hx => /mkseqP [i [hi ->]].
   move: (hcanonical i hi) => [[hlo hhi] _].
   rewrite /HAETAE_Algebra.challenge_coeff_ok.
   smt().
qed.

lemma mode2_xof_sampler_relation_intro
    (highp : BArray1152.t) (lsbp mup : BArray32.t)
    (actual init_cp : BArray1024.t)
    (start_i blocks pos final_i : int) (bytes : int list) :
  init_cp = mode2_zero_challenge =>
  start_i = mode2_start =>
  1 <= blocks =>
  0 <= pos <= 136 =>
  bytes =
    VerifyChallengeM23StreamSamplerPostFreeze.challenge_squeeze_consumed_prefix
      (VerifyChallengeAbsorbStatePostFreeze.mode2_state highp lsbp mup)
      blocks pos =>
  VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_replay
    init_cp start_i bytes = (actual, final_i) =>
  final_i = challenge_words =>
  mode2_xof_sampler_relation highp lsbp mup actual.
proof.
move=> hinit hstart hblocks hpos hbytes hreplay hfinal.
rewrite /mode2_xof_sampler_relation.
exists blocks.
exists pos.
split; first exact hblocks.
split; first exact hpos.
by rewrite -hinit -hstart -hbytes hreplay hfinal.
qed.

lemma verify_challenge_m23_stream_trace_zero_init_start :
  hoare [Trace.run :
    tau = W64.of_int mode2_tau ==>
    Trace.observed_init_cp = mode2_zero_challenge /\
    Trace.observed_start_i = mode2_start].
proof.
proc.
sp 16.
seq 1 : (tau = W64.of_int mode2_tau).
+ call (_ : true ==> true); first by auto.
  auto.
sp 1.
seq 1 : (tau = W64.of_int mode2_tau).
+ call (_ : true ==> true); first by auto.
  auto.
sp 4.
exlim cp => cp0.
seq 1 : (tau = W64.of_int mode2_tau /\ cp = mode2_zero_challenge).
+ call (poly_challenge_m23_init_mode2_zero cp0).
  auto.
sp 4.
wp.
while
  (Trace.observed_init_cp = mode2_zero_challenge /\
   Trace.observed_start_i = mode2_start).
+ wp.
  if.
  + wp.
    call (_ : true ==> true); first by auto.
    auto.
  + auto.
+ auto => />.
qed.

lemma verify_challenge_m23_stream_trace_mode2_xof_sampler_relation
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [Trace.run :
    tau = W64.of_int mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    mode2_xof_sampler_relation high0 lsb0 mu0 res].
proof.
conseq
  (verify_challenge_m23_stream_trace_zero_init_start)
  (VerifyChallengeAbsorbStatePostFreeze.verify_challenge_m23_stream_trace_mode2_concrete_squeeze_replay
    high0 lsb0 mu0).
+ auto.
+ smt(mode2_xof_sampler_relation_intro).
qed.

lemma verify_challenge_m23_actual_mode2_xof_sampler_relation
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [Verify.__verify_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    mode2_xof_sampler_relation high0 lsb0 mu0 res].
proof.
conseq
  VerifyChallengeM23StreamSamplerPostFreeze.verify_challenge_m23_exact_stream_trace
  (verify_challenge_m23_stream_trace_mode2_xof_sampler_relation
    high0 lsb0 mu0).
+ move=> &1 hpre.
   exists Glob.mem{1}.
   exists (cp{1}, highp{1}, highlen{1}, lsbp{1}, mup{1}, tau{1}).
   by auto.
+ move=> &1 &2 [_ hres] hpost.
   rewrite hres.
   exact hpost.
qed.

lemma canonical_weight_implies_challenge_wf_weight
    (cp : BArray1024.t) :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  challenge_weight cp = mode2_tau =>
  HAETAE_Algebra.challenge_wf (challenge_of_barray cp) /\
  challenge_weight cp = 58.
proof.
move=> hcanon hweight.
split.
+ exact (canonical_challenge_implies_challenge_wf cp hcanon).
+ rewrite hweight /mode2_tau /VerifyChallengeM23StreamSamplerPostFreeze.mode2_tau.
   trivial.
qed.

lemma verify_challenge_m23_mode2_xof_sampler_relation_wf_weight
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [Verify.__verify_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    mode2_xof_sampler_relation high0 lsb0 mu0 res /\
    HAETAE_Algebra.challenge_wf (challenge_of_barray res) /\
    challenge_weight res = 58].
proof.
conseq
  (verify_challenge_m23_actual_mode2_xof_sampler_relation
    high0 lsb0 mu0)
  VerifyChallengeM23WeightPostFreeze.verify_challenge_m23_tau58_canonical_weight.
+ auto.
+ smt(canonical_weight_implies_challenge_wf_weight).
qed.

end VerifyChallengeM23XofSamplerSpecPostFreeze.
