require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import RawVerifyApiTarget RawApiVerifyAcceptTrace RawApiVerifyMuTrace
               VerifyChallengeM23XofSamplerSpecPostFreeze
               VerifyChallengeM23TailCanonicalPostFreeze
               VerifyActualAcceptChallengeEqualityRawPostFreeze.

theory VerifyChallengeM23TailXofSamplerPostFreeze.

(* Partial correctness only: these results lift the implementation-faithful
   SHAKE-prefix rejection-sampler relation through the raw/tail/full verify
   traces. They do not prove termination, characterize the XOF distribution,
   or identify the observed challenges with challenge_from_seed or any paper
   hash-level object. *)

module Raw = RawVerifyApiTarget.M.
module TailMuTrace = RawApiVerifyMuTrace.VerifyTailMuTrace.
module FullM23MuTrace = RawApiVerifyMuTrace.VerifyFullM23MuTrace.
module FullMode2MuTrace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module InternalMode2MuTrace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module RawApiMuTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module CryptolabMuTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

op mode2_tau : int =
  VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_tau.
op mode2_highlen : int =
  VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_highlen.
op mode2_xof_sampler_relation =
  VerifyChallengeM23XofSamplerSpecPostFreeze.mode2_xof_sampler_relation.

op mode2_xof_sampler_output (actual : BArray1024.t) : bool =
  exists (highp : BArray1152.t) (lsbp mu : BArray32.t),
    mode2_xof_sampler_relation highp lsbp mu actual.

op accepted_observed_mode2_xof_sampler_outputs
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) : bool =
  reject = W64.zero =>
  mode2_xof_sampler_output parsed_cp /\
  mode2_xof_sampler_output cprime /\
  parsed_cp = cprime.

lemma mode2_xof_sampler_relation_implies_output
    (highp : BArray1152.t) (lsbp mu : BArray32.t)
    (actual : BArray1024.t) :
  mode2_xof_sampler_relation highp lsbp mu actual =>
  mode2_xof_sampler_output actual.
proof.
move=> hrelation.
rewrite /mode2_xof_sampler_output.
exists highp.
exists lsbp.
exists mu.
exact hrelation.
qed.

lemma raw_verify_challenge_m23_tau58_mode2_xof_sampler_relation
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [Raw.__verify_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    mode2_xof_sampler_relation high0 lsb0 mu0 res].
proof.
conseq
  VerifyChallengeM23TailCanonicalPostFreeze.raw_verify_challenge_m23_equiv_focused
  (VerifyChallengeM23XofSamplerSpecPostFreeze.verify_challenge_m23_actual_mode2_xof_sampler_relation
    high0 lsb0 mu0).
+ move=> &1 [htau [hhigh [hhighlen [hlsb hmu]]]].
   exists Glob.mem{1}.
   exists (cp{1}, highp{1}, highlen{1}, lsbp{1}, mup{1}, tau{1}).
   by auto.
+ move=> &1 &2 [_ hres] hpost.
   rewrite hres.
   exact hpost.
qed.

lemma verify_tail_mu_trace_tau58_mode2_xof_sampler_relation :
  hoare [TailMuTrace.run :
    highbits_len_i = mode2_highlen /\ tau_i = mode2_tau
    ==>
    mode2_xof_sampler_relation
      TailMuTrace.observed_highp
      TailMuTrace.observed_lsbp
      TailMuTrace.observed_mu
      TailMuTrace.observed_cprime].
proof.
proc.
seq 62 :
  (highlen = W64.of_int mode2_highlen /\
   tau = W64.of_int mode2_tau /\
   TailMuTrace.observed_highp = highp /\
   TailMuTrace.observed_lsbp = lsbp /\
   TailMuTrace.observed_mu = mup).
+ wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  auto => />.
  rewrite /protect_ptr /protect_64.
  auto.
+ wp.
  call (_ : true ==> true); first by auto.
  wp.
  exlim highp => high0.
  exlim lsbp => lsb0.
  exlim mup => mu0.
  call
    (raw_verify_challenge_m23_tau58_mode2_xof_sampler_relation
      high0 lsb0 mu0).
  auto => />.
qed.

lemma verify_tail_mu_trace_tau58_mode2_xof_sampler_output :
  hoare [TailMuTrace.run :
    highbits_len_i = mode2_highlen /\ tau_i = mode2_tau
    ==>
    mode2_xof_sampler_output TailMuTrace.observed_cprime].
proof.
conseq verify_tail_mu_trace_tau58_mode2_xof_sampler_relation => //=.
smt(mode2_xof_sampler_relation_implies_output).
qed.

lemma verify_full_m23_mu_trace_tail_mode2_xof_sampler_output :
  hoare [FullM23MuTrace.run :
    highbits_len_i = mode2_highlen /\ tau_i = mode2_tau
    ==>
    FullM23MuTrace.tail_reached =>
    mode2_xof_sampler_output FullM23MuTrace.observed_cprime].
proof.
proc.
sp 38.
if.
+ auto => />.
+ seq 11 :
    (highbits_len_i = mode2_highlen /\ tau_i = mode2_tau /\
     !FullM23MuTrace.tail_reached).
   + call (_ : true ==> true); first by auto.
     auto.
   + sp 5.
     seq 1 :
       (highbits_len_i = mode2_highlen /\ tau_i = mode2_tau /\
        !FullM23MuTrace.tail_reached).
     + if; auto.
     + seq 15 :
         (highbits_len_i = mode2_highlen /\ tau_i = mode2_tau /\
          !FullM23MuTrace.tail_reached).
       + auto => />; rewrite /protect_ptr; smt().
       + seq 1 :
           (highbits_len_i = mode2_highlen /\ tau_i = mode2_tau /\
            !FullM23MuTrace.tail_reached).
         + call (_ : true ==> true); first by auto.
           auto.
         + sp 5.
           if.
           + auto => />.
           + seq 12 :
               (highbits_len_i = mode2_highlen /\ tau_i = mode2_tau /\
                !FullM23MuTrace.tail_reached).
             + call (_ : true ==> true); first by auto.
               auto.
             + seq 9 :
                 (highbits_len_i = mode2_highlen /\ tau_i = mode2_tau /\
                  !FullM23MuTrace.tail_reached).
               + call (_ : true ==> true); first by auto.
                 auto.
               + seq 12 :
                   (highbits_len_i = mode2_highlen /\ tau_i = mode2_tau /\
                    !FullM23MuTrace.tail_reached).
                 + call (_ : true ==> true); first by auto.
                   auto.
                 + seq 7 :
                     (highbits_len_i = mode2_highlen /\ tau_i = mode2_tau /\
                      !FullM23MuTrace.tail_reached).
                   + call (_ : true ==> true); first by auto.
                     auto.
                   + sp 2.
                     if.
                     + wp.
                       call verify_tail_mu_trace_tau58_mode2_xof_sampler_output.
                       auto => />.
                     + auto => />.
qed.

lemma verify_full_mode2_mu_trace_tail_mode2_xof_sampler_output :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    FullMode2MuTrace.tail_reached =>
    mode2_xof_sampler_output FullMode2MuTrace.observed_cprime].
proof.
proc.
wp.
call verify_full_m23_mu_trace_tail_mode2_xof_sampler_output.
auto.
qed.

lemma verify_internal_mode2_mu_trace_tail_mode2_xof_sampler_output :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    InternalMode2MuTrace.tail_reached =>
    mode2_xof_sampler_output InternalMode2MuTrace.observed_cprime].
proof.
proc.
wp.
call verify_full_mode2_mu_trace_tail_mode2_xof_sampler_output.
auto.
qed.

lemma verify_raw_api_mu_trace_tail_mode2_xof_sampler_output :
  hoare [RawApiMuTrace.run :
    true
    ==>
    RawApiMuTrace.tail_reached =>
    mode2_xof_sampler_output RawApiMuTrace.observed_cprime].
proof.
proc.
sp 15.
if.
+ auto.
+ wp.
   call verify_internal_mode2_mu_trace_tail_mode2_xof_sampler_output.
   wp.
   call (_ : true ==> true); first by auto.
   wp.
   call (_ : true ==> true); first by auto.
   auto => />.
qed.

lemma verify_cryptolab_mu_trace_tail_mode2_xof_sampler_output :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    CryptolabMuTrace.tail_reached =>
    mode2_xof_sampler_output CryptolabMuTrace.observed_cprime].
proof.
proc.
seq 2 :
  (RawApiMuTrace.tail_reached =>
   mode2_xof_sampler_output RawApiMuTrace.observed_cprime).
+ inline Raw._verify_publish_reject.
   wp.
   call verify_raw_api_mu_trace_tail_mode2_xof_sampler_output.
   auto => />.
+ if.
   + auto.
   + wp.
     call (_ : true ==> true); first by auto.
     auto => />.
qed.

lemma accepted_tail_reached_and_cprime_output
    (reject : W64.t) (tail_reached : bool) (cprime : BArray1024.t) :
  (reject = W64.zero => tail_reached) =>
  (tail_reached => mode2_xof_sampler_output cprime) =>
  reject = W64.zero =>
  mode2_xof_sampler_output cprime.
proof.
move=> htail houtput hzero.
have hreach := htail hzero.
exact (houtput hreach).
qed.

lemma accepted_observed_equal_and_cprime_output
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) :
  (reject = W64.zero => parsed_cp = cprime) =>
  (reject = W64.zero => mode2_xof_sampler_output cprime) =>
  accepted_observed_mode2_xof_sampler_outputs reject parsed_cp cprime.
proof.
move=> hequal houtput hzero.
have heq := hequal hzero.
split.
+ by rewrite heq; exact (houtput hzero).
+ split.
   + exact (houtput hzero).
   + exact heq.
qed.

lemma verify_full_mode2_mu_trace_accept_cprime_output :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    res = W64.zero =>
    mode2_xof_sampler_output FullMode2MuTrace.observed_cprime].
proof.
conseq
  RawApiVerifyAcceptTrace.verify_full_mode2_trace_accept_implies_tail_reached
  verify_full_mode2_mu_trace_tail_mode2_xof_sampler_output => //=.
move=> result observed_cprime tail_reached [htail houtput] hzero.
exact
  (accepted_tail_reached_and_cprime_output
    result tail_reached observed_cprime htail houtput hzero).
qed.

lemma verify_internal_mode2_mu_trace_accept_cprime_output :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    res = W64.zero =>
    mode2_xof_sampler_output InternalMode2MuTrace.observed_cprime].
proof.
conseq
  RawApiVerifyAcceptTrace.verify_internal_mode2_trace_accept_implies_tail_reached
  verify_internal_mode2_mu_trace_tail_mode2_xof_sampler_output => //=.
move=> result observed_cprime tail_reached [htail houtput] hzero.
exact
  (accepted_tail_reached_and_cprime_output
    result tail_reached observed_cprime htail houtput hzero).
qed.

lemma verify_raw_api_mu_trace_accept_cprime_output :
  hoare [RawApiMuTrace.run :
    true
    ==>
    res = W64.zero =>
    mode2_xof_sampler_output RawApiMuTrace.observed_cprime].
proof.
conseq
  RawApiVerifyAcceptTrace.verify_raw_api_trace_accept_implies_tail_reached
  verify_raw_api_mu_trace_tail_mode2_xof_sampler_output => //=.
move=> result observed_cprime tail_reached [htail houtput] hzero.
exact
  (accepted_tail_reached_and_cprime_output
    result tail_reached observed_cprime htail houtput hzero).
qed.

lemma verify_cryptolab_mu_trace_accept_cprime_output :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    res = W64.zero =>
    mode2_xof_sampler_output CryptolabMuTrace.observed_cprime].
proof.
conseq
  RawApiVerifyAcceptTrace.verify_cryptolab_trace_accept_implies_tail_reached
  verify_cryptolab_mu_trace_tail_mode2_xof_sampler_output => //=.
move=> result observed_cprime tail_reached [htail houtput] hzero.
exact
  (accepted_tail_reached_and_cprime_output
    result tail_reached observed_cprime htail houtput hzero).
qed.

lemma verify_full_mode2_mu_trace_accept_mode2_xof_sampler_outputs :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    accepted_observed_mode2_xof_sampler_outputs
      res FullMode2MuTrace.observed_cp FullMode2MuTrace.observed_cprime].
proof.
conseq
  VerifyActualAcceptChallengeEqualityRawPostFreeze.verify_full_mode2_mu_trace_accept_challenges_equal
  verify_full_mode2_mu_trace_accept_cprime_output => //=.
move=> result observed_cp observed_cprime [hequal houtput].
exact
  (accepted_observed_equal_and_cprime_output
    result observed_cp observed_cprime hequal houtput).
qed.

lemma verify_internal_mode2_mu_trace_accept_mode2_xof_sampler_outputs :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    accepted_observed_mode2_xof_sampler_outputs
      res InternalMode2MuTrace.observed_cp
      InternalMode2MuTrace.observed_cprime].
proof.
conseq
  VerifyActualAcceptChallengeEqualityRawPostFreeze.verify_internal_mode2_mu_trace_accept_challenges_equal
  verify_internal_mode2_mu_trace_accept_cprime_output => //=.
move=> result observed_cp observed_cprime [hequal houtput].
exact
  (accepted_observed_equal_and_cprime_output
    result observed_cp observed_cprime hequal houtput).
qed.

lemma verify_raw_api_mu_trace_accept_mode2_xof_sampler_outputs :
  hoare [RawApiMuTrace.run :
    true
    ==>
    accepted_observed_mode2_xof_sampler_outputs
      res RawApiMuTrace.observed_cp RawApiMuTrace.observed_cprime].
proof.
conseq
  VerifyActualAcceptChallengeEqualityRawPostFreeze.verify_raw_api_mu_trace_accept_challenges_equal
  verify_raw_api_mu_trace_accept_cprime_output => //=.
move=> result observed_cp observed_cprime [hequal houtput].
exact
  (accepted_observed_equal_and_cprime_output
    result observed_cp observed_cprime hequal houtput).
qed.

lemma verify_cryptolab_mu_trace_accept_mode2_xof_sampler_outputs :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    accepted_observed_mode2_xof_sampler_outputs
      res CryptolabMuTrace.observed_cp CryptolabMuTrace.observed_cprime].
proof.
conseq
  VerifyActualAcceptChallengeEqualityRawPostFreeze.verify_cryptolab_mu_trace_accept_challenges_equal
  verify_cryptolab_mu_trace_accept_cprime_output => //=.
move=> result observed_cp observed_cprime [hequal houtput].
exact
  (accepted_observed_equal_and_cprime_output
    result observed_cp observed_cprime hequal houtput).
qed.

lemma actual_verify_full_m23_tail_mode2_xof_sampler_output :
  equiv [Raw._verify_full_m23 ~ FullM23MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp, k_i, l_i, m_i, sigbytes_i,
      vkbytes_i, highbits_len_i, tau_i, b2sq_i, hb_count_i, hb_m_i,
      hb_offset_i, h_count_i, h_m_i, h_offset_i, base_hb_i, base_h_i,
      payload_limit_i} /\
    highbits_len_i{1} = mode2_highlen /\ tau_i{1} = mode2_tau
    ==>
    ={Glob.mem, res} /\
    (FullM23MuTrace.tail_reached{2} =>
      mode2_xof_sampler_output FullM23MuTrace.observed_cprime{2})].
proof.
conseq RawApiVerifyMuTrace.verify_full_m23_exact_mu_trace
  (_ : true ==> true)
  verify_full_m23_mu_trace_tail_mode2_xof_sampler_output => //=.
move=> &1 &2 [heq [hhighlen htau]].
split; first exact heq.
move: heq hhighlen htau.
smt().
qed.

lemma actual_verify_full_mode2_accept_observed_mode2_xof_sampler_outputs :
  equiv [Raw._verify_full_mode2 ~ FullMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_xof_sampler_outputs
      res{1} FullMode2MuTrace.observed_cp{2}
      FullMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_full_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_full_mode2_mu_trace_accept_mode2_xof_sampler_outputs => //=.
qed.

lemma actual_verify_internal_mode2_accept_observed_mode2_xof_sampler_outputs :
  equiv [Raw.sign_verify_internal_mode2_jazz ~ InternalMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_xof_sampler_outputs
      res{1} InternalMode2MuTrace.observed_cp{2}
      InternalMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_internal_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_internal_mode2_mu_trace_accept_mode2_xof_sampler_outputs => //=.
qed.

lemma actual_verify_raw_api_accept_observed_mode2_xof_sampler_outputs :
  equiv [Raw._api_verify_mode2_raw ~ RawApiMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_xof_sampler_outputs
      res{1} RawApiMuTrace.observed_cp{2}
      RawApiMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace
  (_ : true ==> true)
  verify_raw_api_mu_trace_accept_mode2_xof_sampler_outputs => //=.
qed.

lemma actual_verify_cryptolab_accept_observed_mode2_xof_sampler_outputs :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ CryptolabMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_xof_sampler_outputs
      res{1} CryptolabMuTrace.observed_cp{2}
      CryptolabMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace
  (_ : true ==> true)
  verify_cryptolab_mu_trace_accept_mode2_xof_sampler_outputs => //=.
qed.

end VerifyChallengeM23TailXofSamplerPostFreeze.
