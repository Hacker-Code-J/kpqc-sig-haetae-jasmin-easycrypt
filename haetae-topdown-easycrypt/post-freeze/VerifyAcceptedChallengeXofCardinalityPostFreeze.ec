require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import RawVerifyApiTarget RawApiVerifyMuTrace
               VerifyChallengeM23TailXofSamplerPostFreeze
               VerifyActualChallengeSupportPostFreeze.

theory VerifyAcceptedChallengeXofCardinalityPostFreeze.

(* Partial correctness only.  This leaf combines provenance and algebraic
   support facts already proved for accepting executions.  It does not prove
   termination, distributional equivalence, challenge_sparse, or equality
   with challenge_from_seed / a paper-level challenge hash. *)

module Raw = RawVerifyApiTarget.M.
module FullMode2MuTrace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module InternalMode2MuTrace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module RawApiMuTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module CryptolabMuTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

op mode2_xof_sampler_output =
  VerifyChallengeM23TailXofSamplerPostFreeze.mode2_xof_sampler_output.
op challenge_of_barray =
  VerifyActualChallengeSupportPostFreeze.challenge_of_barray.
op mode2_cardinality_wf =
  VerifyActualChallengeSupportPostFreeze.mode2_cardinality_wf.

op accepted_observed_mode2_xof_cardinality_challenges
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) : bool =
  reject = W64.zero =>
  mode2_xof_sampler_output parsed_cp /\
  mode2_xof_sampler_output cprime /\
  parsed_cp = cprime /\
  mode2_cardinality_wf (challenge_of_barray parsed_cp) /\
  mode2_cardinality_wf (challenge_of_barray cprime) /\
  challenge_of_barray parsed_cp = challenge_of_barray cprime.

lemma accepted_xof_and_cardinality_imply_unified
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) :
  VerifyChallengeM23TailXofSamplerPostFreeze.accepted_observed_mode2_xof_sampler_outputs
      reject parsed_cp cprime =>
  VerifyActualChallengeSupportPostFreeze.accepted_observed_mode2_cardinality_challenges
      reject parsed_cp cprime =>
  accepted_observed_mode2_xof_cardinality_challenges
    reject parsed_cp cprime.
proof.
move=> hxof hcard hzero.
move: (hxof hzero) => [hparsed_xof [hcprime_xof heq]].
move: (hcard hzero) => [hparsed_card [hcprime_card hchallenge_eq]].
split; first exact hparsed_xof.
split; first exact hcprime_xof.
split; first exact heq.
split; first exact hparsed_card.
split; first exact hcprime_card.
exact hchallenge_eq.
qed.

lemma verify_full_mode2_mu_trace_accept_xof_cardinality :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    accepted_observed_mode2_xof_cardinality_challenges
      res FullMode2MuTrace.observed_cp FullMode2MuTrace.observed_cprime].
proof.
conseq
  VerifyChallengeM23TailXofSamplerPostFreeze.verify_full_mode2_mu_trace_accept_mode2_xof_sampler_outputs
  VerifyActualChallengeSupportPostFreeze.verify_full_mode2_mu_trace_accept_mode2_cardinality_challenges => //=.
move=> result observed_cp observed_cprime [hxof hcard].
exact
  (accepted_xof_and_cardinality_imply_unified
    result observed_cp observed_cprime hxof hcard).
qed.

lemma verify_internal_mode2_mu_trace_accept_xof_cardinality :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    accepted_observed_mode2_xof_cardinality_challenges
      res InternalMode2MuTrace.observed_cp
      InternalMode2MuTrace.observed_cprime].
proof.
conseq
  VerifyChallengeM23TailXofSamplerPostFreeze.verify_internal_mode2_mu_trace_accept_mode2_xof_sampler_outputs
  VerifyActualChallengeSupportPostFreeze.verify_internal_mode2_mu_trace_accept_mode2_cardinality_challenges => //=.
move=> result observed_cp observed_cprime [hxof hcard].
exact
  (accepted_xof_and_cardinality_imply_unified
    result observed_cp observed_cprime hxof hcard).
qed.

lemma verify_raw_api_mu_trace_accept_xof_cardinality :
  hoare [RawApiMuTrace.run :
    true
    ==>
    accepted_observed_mode2_xof_cardinality_challenges
      res RawApiMuTrace.observed_cp RawApiMuTrace.observed_cprime].
proof.
conseq
  VerifyChallengeM23TailXofSamplerPostFreeze.verify_raw_api_mu_trace_accept_mode2_xof_sampler_outputs
  VerifyActualChallengeSupportPostFreeze.verify_raw_api_mu_trace_accept_mode2_cardinality_challenges => //=.
move=> result observed_cp observed_cprime [hxof hcard].
exact
  (accepted_xof_and_cardinality_imply_unified
    result observed_cp observed_cprime hxof hcard).
qed.

lemma verify_cryptolab_mu_trace_accept_xof_cardinality :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    accepted_observed_mode2_xof_cardinality_challenges
      res CryptolabMuTrace.observed_cp CryptolabMuTrace.observed_cprime].
proof.
conseq
  VerifyChallengeM23TailXofSamplerPostFreeze.verify_cryptolab_mu_trace_accept_mode2_xof_sampler_outputs
  VerifyActualChallengeSupportPostFreeze.verify_cryptolab_mu_trace_accept_mode2_cardinality_challenges => //=.
move=> result observed_cp observed_cprime [hxof hcard].
exact
  (accepted_xof_and_cardinality_imply_unified
    result observed_cp observed_cprime hxof hcard).
qed.

lemma actual_verify_full_mode2_accept_xof_cardinality :
  equiv [Raw._verify_full_mode2 ~ FullMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_xof_cardinality_challenges
      res{1} FullMode2MuTrace.observed_cp{2}
      FullMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_full_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_full_mode2_mu_trace_accept_xof_cardinality => //=.
qed.

lemma actual_verify_internal_mode2_accept_xof_cardinality :
  equiv [Raw.sign_verify_internal_mode2_jazz ~ InternalMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_xof_cardinality_challenges
      res{1} InternalMode2MuTrace.observed_cp{2}
      InternalMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_internal_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_internal_mode2_mu_trace_accept_xof_cardinality => //=.
qed.

lemma actual_verify_raw_api_accept_xof_cardinality :
  equiv [Raw._api_verify_mode2_raw ~ RawApiMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_xof_cardinality_challenges
      res{1} RawApiMuTrace.observed_cp{2}
      RawApiMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace
  (_ : true ==> true)
  verify_raw_api_mu_trace_accept_xof_cardinality => //=.
qed.

lemma actual_verify_cryptolab_accept_xof_cardinality :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ CryptolabMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_xof_cardinality_challenges
      res{1} CryptolabMuTrace.observed_cp{2}
      CryptolabMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace
  (_ : true ==> true)
  verify_cryptolab_mu_trace_accept_xof_cardinality => //=.
qed.

end VerifyAcceptedChallengeXofCardinalityPostFreeze.
