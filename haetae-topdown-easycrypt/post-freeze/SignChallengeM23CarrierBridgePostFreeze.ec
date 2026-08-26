require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2VerifyPrepareNorm RawSignApiTarget
               SignChallengeM23SamplerBridgePostFreeze
               VerifyChallengeM23SamplerStructurePostFreeze
               VerifyChallengeM23WeightPostFreeze
               VerifyChallengeM23TailWeightPostFreeze
               Mode2ChallengeROMAdapterPostFreeze
               Mode2ChallengeCarrierValidityPostFreeze.

theory SignChallengeM23CarrierBridgePostFreeze.

(* Structural partial correctness only.  This layer shows that every
   terminating raw Sign challenge call returns on the exact 0/1 weight-58
   carrier.  It does not prove sampler termination, SHAKE randomness, the
   dmode2 carrier distribution, or challenge_from_seed equality.
   RawSignApiTarget must resolve from the same generated extraction surface
   as the Verify tail theorems; otherwise their BArray1024 types are nominally
   distinct. *)

module RawSign = RawSignApiTarget.M.

op mode2_highlen : int =
  SignChallengeM23SamplerBridgePostFreeze.mode2_highlen.

op mode2_tau : int =
  Mode2ChallengeCarrierValidityPostFreeze.mode2_tau.

op mu32_prefix =
  SignChallengeM23SamplerBridgePostFreeze.mu32_prefix.

op challenge_weight =
  Mode2ChallengeCarrierValidityPostFreeze.challenge_weight.

op challenge_of_barray =
  Mode2ChallengeCarrierValidityPostFreeze.challenge_of_barray.

op valid_mode2_carrier_challenge =
  Mode2ChallengeCarrierValidityPostFreeze.valid_mode2_carrier_challenge.

lemma mode2_tau_tail_weightE :
  mode2_tau = VerifyChallengeM23TailWeightPostFreeze.mode2_tau.
proof.
by rewrite /mode2_tau
           /Mode2ChallengeCarrierValidityPostFreeze.mode2_tau
           /Mode2ChallengeROMAdapterPostFreeze.mode2_tau
           /VerifyChallengeM23TailWeightPostFreeze.mode2_tau
           /VerifyChallengeM23WeightPostFreeze.mode2_tau
           /VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau.
qed.

lemma challenge_weight_tailE cp :
  challenge_weight cp =
  VerifyChallengeM23TailWeightPostFreeze.challenge_weight cp.
proof.
by rewrite /challenge_weight
           /Mode2ChallengeCarrierValidityPostFreeze.challenge_weight
           /VerifyChallengeM23TailWeightPostFreeze.challenge_weight.
qed.

lemma raw_sign_challenge_m23_mode2_canonical_weight
    (mu0 : BArray32.t) :
  hoare [RawSign.__sign_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highlen = W64.of_int mode2_highlen /\
    mu32_prefix mup mu0
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res /\
    challenge_weight res = mode2_tau].
proof.
conseq
  SignChallengeM23SamplerBridgePostFreeze.raw_sign_verify_challenge_m23_mode2
  VerifyChallengeM23TailWeightPostFreeze.raw_verify_challenge_m23_tau58_canonical_weight.
+ move=> &1 hpre.
  exists (cp{1}, highp{1}, highlen{1}, lsbp{1}, mu0, tau{1}).
  rewrite mode2_tau_tail_weightE in hpre.
  smt().
+ move=> &1 &2 hres hpost.
  rewrite hres.
  move: hpost => [hcanonical hweight].
  split; first exact hcanonical.
  by rewrite challenge_weight_tailE mode2_tau_tail_weightE.
qed.

lemma raw_sign_challenge_m23_mode2_valid_carrier
    (mu0 : BArray32.t) :
  hoare [RawSign.__sign_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highlen = W64.of_int mode2_highlen /\
    mu32_prefix mup mu0
    ==>
    valid_mode2_carrier_challenge (challenge_of_barray res)].
proof.
conseq (raw_sign_challenge_m23_mode2_canonical_weight mu0).
move=> &hr _ result [hcanonical hweight].
exact
  (Mode2ChallengeCarrierValidityPostFreeze.canonical_weight_implies_valid_mode2_carrier
    result hcanonical hweight).
qed.

end SignChallengeM23CarrierBridgePostFreeze.
