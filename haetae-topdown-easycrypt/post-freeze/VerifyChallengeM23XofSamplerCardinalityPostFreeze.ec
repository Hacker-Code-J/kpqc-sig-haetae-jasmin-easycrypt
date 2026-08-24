require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget
               Mode2VerifyPrepareNorm HAETAE_Params
               VerifyChallengeM23SamplerStructurePostFreeze
               VerifyChallengeM23WeightPostFreeze
               VerifyChallengeM23XofSamplerSpecPostFreeze
               VerifyActualChallengeSupportPostFreeze.

theory VerifyChallengeM23XofSamplerCardinalityPostFreeze.

module Verify = VerifyCoreTarget.M.

op mode2_tau : int =
  VerifyChallengeM23WeightPostFreeze.mode2_tau.
op mode2_highlen : int =
  VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_highlen.
op challenge_weight =
  VerifyChallengeM23WeightPostFreeze.challenge_weight.
op challenge_of_barray =
  VerifyActualChallengeSupportPostFreeze.challenge_of_barray.
op mode2_cardinality_wf =
  VerifyActualChallengeSupportPostFreeze.mode2_cardinality_wf.
op mode2_xof_sampler_relation =
  VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_xof_sampler_relation.

(* Partial correctness only.  This composes the concrete XOF/rejection trace
   with the established algebraic support-size result; it deliberately makes
   no challenge_from_seed equality, termination, or distributional claim. *)
lemma canonical_weight_implies_mode2_cardinality
    (cp : BArray1024.t) :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  challenge_weight cp = mode2_tau =>
  mode2_cardinality_wf (challenge_of_barray cp).
proof.
move=> hcanonical hweight.
apply
  VerifyActualChallengeSupportPostFreeze.canonical_machine_weight_implies_mode2_cardinality_wf.
+ exact hcanonical.
exact hweight.
qed.

lemma verify_challenge_m23_mode2_xof_sampler_cardinality
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [Verify.__verify_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    mode2_xof_sampler_relation high0 lsb0 mu0 res /\
    mode2_cardinality_wf (challenge_of_barray res)].
proof.
conseq
  (VerifyChallengeM23XofSamplerSpecPostFreeze.verify_challenge_m23_actual_mode2_xof_sampler_relation
      high0 lsb0 mu0)
  VerifyChallengeM23WeightPostFreeze.verify_challenge_m23_tau58_canonical_weight.
+ auto.
+ smt(canonical_weight_implies_mode2_cardinality).
qed.

end VerifyChallengeM23XofSamplerCardinalityPostFreeze.
