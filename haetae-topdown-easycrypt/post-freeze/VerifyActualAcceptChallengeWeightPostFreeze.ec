require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 Mode2VerifyPrepareNorm RawVerifyApiTarget
               RawApiVerifyAcceptTrace RawApiVerifyMuTrace
               VerifyChallengeM23TailWeightPostFreeze
               VerifyActualAcceptChallengeEqualityRawPostFreeze.

theory VerifyActualAcceptChallengeWeightPostFreeze.

(* Partial correctness only: these Hoare/equiv results compose accepting
   executions of the actual verify traces. They do not prove termination,
   characterize SHAKE outputs, or identify the observed challenges with any
   paper-level challenge object beyond the explicit canonical/equality/weight
   facts stated below. *)

module Raw = RawVerifyApiTarget.M.
module FullMode2MuTrace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module InternalMode2MuTrace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module RawApiMuTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module CryptolabMuTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

op mode2_tau : int = VerifyChallengeM23TailWeightPostFreeze.mode2_tau.
op challenge_weight = VerifyChallengeM23TailWeightPostFreeze.challenge_weight.

op accepted_observed_canonical_weight_challenges
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) : bool =
  reject = W64.zero =>
  Mode2VerifyPrepareNorm.canonical_challenge parsed_cp /\
  Mode2VerifyPrepareNorm.canonical_challenge cprime /\
  parsed_cp = cprime /\
  challenge_weight parsed_cp = mode2_tau /\
  challenge_weight cprime = mode2_tau.

lemma accepted_tail_reached_and_cprime_weight
    (reject : W64.t) (tail_reached : bool) (cprime : BArray1024.t) :
  (reject = W64.zero => tail_reached) =>
  (tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge cprime /\
    challenge_weight cprime = mode2_tau) =>
  reject = W64.zero =>
  challenge_weight cprime = mode2_tau.
proof.
move=> htail hweight hzero.
have hreach := htail hzero.
have [_ hcw] := hweight hreach.
exact hcw.
qed.

lemma accepted_observed_canonical_equal_and_cprime_weight
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) :
  (reject = W64.zero =>
    Mode2VerifyPrepareNorm.canonical_challenge parsed_cp /\
    Mode2VerifyPrepareNorm.canonical_challenge cprime /\
    parsed_cp = cprime) =>
  (reject = W64.zero => challenge_weight cprime = mode2_tau) =>
  accepted_observed_canonical_weight_challenges reject parsed_cp cprime.
proof.
move=> hcanon hweight hzero.
move: (hcanon hzero) => [hcp [hcprime heq]].
split; first exact hcp.
split; first exact hcprime.
split; first exact heq.
split.
+ by rewrite heq; exact (hweight hzero).
+ exact (hweight hzero).
qed.

lemma verify_full_mode2_mu_trace_accept_cprime_weight :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    res = W64.zero =>
    challenge_weight FullMode2MuTrace.observed_cprime = mode2_tau].
proof.
conseq RawApiVerifyAcceptTrace.verify_full_mode2_trace_accept_implies_tail_reached VerifyChallengeM23TailWeightPostFreeze.verify_full_mode2_mu_trace_tail_canonical_weight => //=.
move=> result observed_cprime tail_reached [htail hweight] hzero.
exact
  (accepted_tail_reached_and_cprime_weight
    result tail_reached observed_cprime htail hweight hzero).
qed.

lemma verify_internal_mode2_mu_trace_accept_cprime_weight :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    res = W64.zero =>
    challenge_weight InternalMode2MuTrace.observed_cprime = mode2_tau].
proof.
conseq RawApiVerifyAcceptTrace.verify_internal_mode2_trace_accept_implies_tail_reached VerifyChallengeM23TailWeightPostFreeze.verify_internal_mode2_mu_trace_tail_canonical_weight => //=.
move=> result observed_cprime tail_reached [htail hweight] hzero.
exact
  (accepted_tail_reached_and_cprime_weight
    result tail_reached observed_cprime htail hweight hzero).
qed.

lemma verify_raw_api_mu_trace_accept_cprime_weight :
  hoare [RawApiMuTrace.run :
    true
    ==>
    res = W64.zero =>
    challenge_weight RawApiMuTrace.observed_cprime = mode2_tau].
proof.
conseq RawApiVerifyAcceptTrace.verify_raw_api_trace_accept_implies_tail_reached VerifyChallengeM23TailWeightPostFreeze.verify_raw_api_mu_trace_tail_canonical_weight => //=.
move=> result observed_cprime tail_reached [htail hweight] hzero.
exact
  (accepted_tail_reached_and_cprime_weight
    result tail_reached observed_cprime htail hweight hzero).
qed.

lemma verify_cryptolab_mu_trace_accept_cprime_weight :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    res = W64.zero =>
    challenge_weight CryptolabMuTrace.observed_cprime = mode2_tau].
proof.
conseq RawApiVerifyAcceptTrace.verify_cryptolab_trace_accept_implies_tail_reached VerifyChallengeM23TailWeightPostFreeze.verify_cryptolab_mu_trace_tail_canonical_weight => //=.
move=> result observed_cprime tail_reached [htail hweight] hzero.
exact
  (accepted_tail_reached_and_cprime_weight
    result tail_reached observed_cprime htail hweight hzero).
qed.

lemma verify_full_mode2_mu_trace_accept_canonical_weight_challenges :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    accepted_observed_canonical_weight_challenges
      res FullMode2MuTrace.observed_cp FullMode2MuTrace.observed_cprime].
proof.
conseq VerifyActualAcceptChallengeEqualityRawPostFreeze.verify_full_mode2_mu_trace_accept_canonical_challenges verify_full_mode2_mu_trace_accept_cprime_weight => //=.
move=> result observed_cp observed_cprime [hcanon hweight].
exact
  (accepted_observed_canonical_equal_and_cprime_weight
    result observed_cp observed_cprime hcanon hweight).
qed.

lemma verify_internal_mode2_mu_trace_accept_canonical_weight_challenges :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    accepted_observed_canonical_weight_challenges
      res InternalMode2MuTrace.observed_cp
      InternalMode2MuTrace.observed_cprime].
proof.
conseq VerifyActualAcceptChallengeEqualityRawPostFreeze.verify_internal_mode2_mu_trace_accept_canonical_challenges verify_internal_mode2_mu_trace_accept_cprime_weight => //=.
move=> result observed_cp observed_cprime [hcanon hweight].
exact
  (accepted_observed_canonical_equal_and_cprime_weight
    result observed_cp observed_cprime hcanon hweight).
qed.

lemma verify_raw_api_mu_trace_accept_canonical_weight_challenges :
  hoare [RawApiMuTrace.run :
    true
    ==>
    accepted_observed_canonical_weight_challenges
      res RawApiMuTrace.observed_cp RawApiMuTrace.observed_cprime].
proof.
conseq VerifyActualAcceptChallengeEqualityRawPostFreeze.verify_raw_api_mu_trace_accept_canonical_challenges verify_raw_api_mu_trace_accept_cprime_weight => //=.
move=> result observed_cp observed_cprime [hcanon hweight].
exact
  (accepted_observed_canonical_equal_and_cprime_weight
    result observed_cp observed_cprime hcanon hweight).
qed.

lemma verify_cryptolab_mu_trace_accept_canonical_weight_challenges :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    accepted_observed_canonical_weight_challenges
      res CryptolabMuTrace.observed_cp CryptolabMuTrace.observed_cprime].
proof.
conseq VerifyActualAcceptChallengeEqualityRawPostFreeze.verify_cryptolab_mu_trace_accept_canonical_challenges verify_cryptolab_mu_trace_accept_cprime_weight => //=.
move=> result observed_cp observed_cprime [hcanon hweight].
exact
  (accepted_observed_canonical_equal_and_cprime_weight
    result observed_cp observed_cprime hcanon hweight).
qed.

lemma actual_verify_full_mode2_accept_observed_canonical_weight_challenges :
  equiv [Raw._verify_full_mode2 ~ FullMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_canonical_weight_challenges
      res{1} FullMode2MuTrace.observed_cp{2}
      FullMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_full_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_full_mode2_mu_trace_accept_canonical_weight_challenges => //=.
qed.

lemma actual_verify_internal_mode2_accept_observed_canonical_weight_challenges :
  equiv [Raw.sign_verify_internal_mode2_jazz ~ InternalMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_canonical_weight_challenges
      res{1} InternalMode2MuTrace.observed_cp{2}
      InternalMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_internal_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_internal_mode2_mu_trace_accept_canonical_weight_challenges => //=.
qed.

lemma actual_verify_raw_api_accept_observed_canonical_weight_challenges :
  equiv [Raw._api_verify_mode2_raw ~ RawApiMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_canonical_weight_challenges
      res{1} RawApiMuTrace.observed_cp{2}
      RawApiMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace
  (_ : true ==> true)
  verify_raw_api_mu_trace_accept_canonical_weight_challenges => //=.
qed.

lemma actual_verify_cryptolab_accept_observed_canonical_weight_challenges :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ CryptolabMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_canonical_weight_challenges
      res{1} CryptolabMuTrace.observed_cp{2}
      CryptolabMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace
  (_ : true ==> true)
  verify_cryptolab_mu_trace_accept_canonical_weight_challenges => //=.
qed.

end VerifyActualAcceptChallengeWeightPostFreeze.
