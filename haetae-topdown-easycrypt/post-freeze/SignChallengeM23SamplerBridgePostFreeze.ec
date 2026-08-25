require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget RawVerifyApiTarget
               SignTranscriptTarget VerifyTranscriptTarget
               SignChallengeM23AbsorbComponentsPostFreeze
               SignChallengeM23HighbufPositionPostFreeze
               VerifyChallengeAbsorbStatePostFreeze
               VerifyChallengeM23XofSamplerSpecPostFreeze
               VerifyChallengeM23TailXofSamplerPostFreeze.

theory SignChallengeM23SamplerBridgePostFreeze.

(* Partial correctness and deterministic transport only.  The bridge proves
   that Sign consumes the same Mode-2 transcript prefix and reaches the same
   concrete-XOF replay result as Verify.  It does not assert termination,
   SHAKE randomness, the dmode2 carrier distribution, or challenge_from_seed
   equality. *)

module RawSign = RawSignApiTarget.M.
module RawVerify = RawVerifyApiTarget.M.
module Sign = SignTranscriptTarget.M.
module Verify = VerifyTranscriptTarget.M.

op mode2_highlen : int =
  SignChallengeM23HighbufPositionPostFreeze.mode2_highlen.

op mu32_prefix =
  SignChallengeM23AbsorbComponentsPostFreeze.mu32_prefix.

op mode2_tau : int =
  VerifyChallengeM23TailXofSamplerPostFreeze.mode2_tau.

op mode2_xof_sampler_relation =
  VerifyChallengeM23TailXofSamplerPostFreeze.mode2_xof_sampler_relation.

op mode2_xof_sampler_output =
  VerifyChallengeM23TailXofSamplerPostFreeze.mode2_xof_sampler_output.

lemma mode2_highlen_tailE :
  mode2_highlen =
  VerifyChallengeM23TailXofSamplerPostFreeze.mode2_highlen.
proof.
by rewrite /mode2_highlen
           /SignChallengeM23HighbufPositionPostFreeze.mode2_highlen
           /SignChallengeM23AbsorbComponentsPostFreeze.mode2_highlen
           /VerifyChallengeM23TailXofSamplerPostFreeze.mode2_highlen
           /VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_highlen
           /VerifyChallengeAbsorbStatePostFreeze.mode2_highlen.
qed.

lemma raw_sign_challenge_absorb_equiv_focused :
  equiv [RawSign.__sign_challenge_absorb ~ Sign.__sign_challenge_absorb :
    ={sp_0, highp, highlen, lsbp, mup} ==> ={res}].
proof. by proc; sim. qed.

lemma raw_verify_challenge_absorb_equiv_focused :
  equiv [RawVerify.__verify_challenge_absorb ~ Verify.__verify_challenge_absorb :
    ={sp_0, highp, highlen, lsbp, mup} ==> ={res}].
proof. by proc; sim. qed.

lemma raw_sign_verify_challenge_absorb_mode2 :
  equiv [RawSign.__sign_challenge_absorb ~
         RawVerify.__verify_challenge_absorb :
    ={sp_0, highp, highlen, lsbp} /\
    highlen{1} = W64.of_int mode2_highlen /\
    mu32_prefix mup{1} mup{2}
    ==>
    ={res}].
proof.
transitivity Sign.__sign_challenge_absorb
  (={sp_0, highp, highlen, lsbp, mup} ==> ={res})
  (={sp_0, highp, highlen, lsbp} /\
   highlen{1} = W64.of_int mode2_highlen /\
   mu32_prefix mup{1} mup{2}
   ==>
   ={res}).
+ move=> &1 &2 hpre.
  exists (sp_0{1}, highp{1}, highlen{1}, lsbp{1}, mup{1}).
  by auto.
+ move=> &1 &m &2 hleft hright.
  by rewrite hleft hright.
+ exact raw_sign_challenge_absorb_equiv_focused.
+ transitivity Verify.__verify_challenge_absorb
    (={sp_0, highp, highlen, lsbp} /\
     highlen{1} = W64.of_int mode2_highlen /\
     mu32_prefix mup{1} mup{2}
     ==>
     ={res})
    (={sp_0, highp, highlen, lsbp, mup} ==> ={res}).
  + move=> &1 &2 hpre.
    exists (sp_0{2}, highp{2}, highlen{2}, lsbp{2}, mup{2}).
    by auto.
  + move=> &1 &m &2 hleft hright.
    by rewrite hleft hright.
  + exact
      SignChallengeM23HighbufPositionPostFreeze.sign_verify_challenge_absorb_mode2.
  + by proc; sim.
qed.

lemma raw_sign_verify_challenge_m23_mode2 :
  equiv [RawSign.__sign_challenge_m23 ~
         RawVerify.__verify_challenge_m23 :
    ={cp, highp, highlen, lsbp, tau} /\
    highlen{1} = W64.of_int mode2_highlen /\
    mu32_prefix mup{1} mup{2}
    ==>
    ={res}].
proof.
proc.
seq 7 7 : (={cp, sp_0, bp, tau}).
+ call raw_sign_verify_challenge_absorb_mode2.
  auto.
+ sim.
qed.

lemma raw_sign_challenge_m23_tau58_mode2_xof_sampler_relation
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [RawSign.__sign_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mu32_prefix mup mu0
    ==>
    mode2_xof_sampler_relation high0 lsb0 mu0 res].
proof.
conseq
  raw_sign_verify_challenge_m23_mode2
  (VerifyChallengeM23TailXofSamplerPostFreeze.raw_verify_challenge_m23_tau58_mode2_xof_sampler_relation
    high0 lsb0 mu0).
+ move=> &1 hpre.
  exists (cp{1}, highp{1}, highlen{1}, lsbp{1}, mu0, tau{1}).
  rewrite mode2_highlen_tailE /mode2_tau in hpre.
  rewrite mode2_highlen_tailE /mode2_tau.
  smt().
+ move=> &1 &2 hres hpost.
  rewrite hres.
  exact hpost.
qed.

lemma raw_sign_challenge_m23_tau58_mode2_xof_sampler_output
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [RawSign.__sign_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mu32_prefix mup mu0
    ==>
    mode2_xof_sampler_output res].
proof.
conseq
  (raw_sign_challenge_m23_tau58_mode2_xof_sampler_relation
    high0 lsb0 mu0).
move=> &hr _ result hrelation.
exact
  (VerifyChallengeM23TailXofSamplerPostFreeze.mode2_xof_sampler_relation_implies_output
    high0 lsb0 mu0 result hrelation).
qed.

end SignChallengeM23SamplerBridgePostFreeze.
