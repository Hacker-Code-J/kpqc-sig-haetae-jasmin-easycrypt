require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 RawVerifyApiTarget
               Mode2VerifyTailChallenge RawApiVerifyMuTrace
               RawApiVerifyAcceptTrace VerifyTailRawBoundaryPostFreeze.

import VerifyTailRawBoundaryPostFreeze.

theory VerifyActualAcceptMismatchRawPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Focused = VerifyCoreTarget.M.
module TailMuTrace = RawApiVerifyMuTrace.VerifyTailMuTrace.
module FullM23MuTrace = RawApiVerifyMuTrace.VerifyFullM23MuTrace.
module FullMode2MuTrace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module InternalMode2MuTrace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module RawApiMuTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module CryptolabMuTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

lemma raw_poly_mismatch_equiv_focused :
  equiv [Raw._poly_mismatch ~ Focused._poly_mismatch :
    ={Glob.mem, ap, bp}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_poly_mismatch_mode2_word_exact
    (ap0 bp0 : BArray1024.t) :
  hoare [Raw._poly_mismatch :
    ap = ap0 /\ bp = bp0
    ==>
    res = Mode2VerifyTailChallenge.poly_mismatch_result_word
      (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
        ap0 bp0 Mode2VerifyTailChallenge.mode2_challenge_words)].
proof.
conseq raw_poly_mismatch_equiv_focused
  (Mode2VerifyTailChallenge.poly_mismatch_mode2_word_exact ap0 bp0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists (ap{1}, bp{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

lemma verify_tail_mu_trace_mismatch_word_exact
    (cp0 : BArray1024.t) :
  hoare [TailMuTrace.run :
    cp = cp0
    ==>
    TailMuTrace.observed_cp = cp0 /\
    res = Mode2VerifyTailChallenge.poly_mismatch_result_word
      (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
        TailMuTrace.observed_cp TailMuTrace.observed_cprime
        Mode2VerifyTailChallenge.mode2_challenge_words)].
proof.
proc.
seq 66 :
  (cp = cp0 /\ TailMuTrace.observed_cp = cp0 /\
   cprimep = TailMuTrace.observed_cprime).
+ wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  auto.
+ wp.
  exlim cprimep => cprime0.
  call (raw_poly_mismatch_mode2_word_exact cp0 cprime0).
  auto => &hr />.
qed.

(* Both arrays are the concrete values recorded at the real comparison call;
   keeping them explicit avoids an unconstrained equal-array witness. *)
op accepted_observed_mismatch_word_zero
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) : bool =
  reject = W64.zero =>
  Mode2VerifyTailChallenge.poly_mismatch_result_word
    (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
      parsed_cp cprime Mode2VerifyTailChallenge.mode2_challenge_words) =
    W64.zero.

lemma verify_full_m23_mu_trace_accept_mismatch_word_zero :
  hoare [FullM23MuTrace.run :
    true
    ==>
    accepted_observed_mismatch_word_zero
      res FullM23MuTrace.observed_cp FullM23MuTrace.observed_cprime].
proof.
proc.
sp 38.
if.
+ auto => />.
  rewrite /accepted_observed_mismatch_word_zero.
  smt(W64.WRingA.oner_neq0).
+ seq 11 : true.
  + call (_ : true ==> true); first by auto.
    auto.
  + sp 5.
    seq 1 : true.
    + if; auto.
    + seq 16 : true.
      + call (_ : true ==> true); first by auto.
        auto.
      + sp 5.
        if.
        + auto => />.
          rewrite /accepted_observed_mismatch_word_zero.
          smt(W64.WRingA.oner_neq0).
        + seq 12 : true.
          + call (_ : true ==> true); first by auto.
            auto.
          + seq 9 : true.
            + call (_ : true ==> true); first by auto.
              auto.
            + seq 12 : true.
              + call (_ : true ==> true); first by auto.
                auto.
              + seq 7 : true.
                + call (_ : true ==> true); first by auto.
                  auto.
                + sp 2.
                  if.
                  + wp.
                    exlim cp => parsed_cp0.
                    call
                      (verify_tail_mu_trace_mismatch_word_exact parsed_cp0).
                    auto => />.
                  + auto => />.
                    rewrite /accepted_observed_mismatch_word_zero.
                    smt().
qed.

lemma verify_full_mode2_mu_trace_accept_mismatch_word_zero :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    accepted_observed_mismatch_word_zero
      res FullMode2MuTrace.observed_cp FullMode2MuTrace.observed_cprime].
proof.
proc.
wp.
call verify_full_m23_mu_trace_accept_mismatch_word_zero.
auto.
qed.

lemma verify_internal_mode2_mu_trace_accept_mismatch_word_zero :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    accepted_observed_mismatch_word_zero
      res InternalMode2MuTrace.observed_cp
      InternalMode2MuTrace.observed_cprime].
proof.
proc.
wp.
call verify_full_mode2_mu_trace_accept_mismatch_word_zero.
auto.
qed.

lemma verify_raw_api_mu_trace_accept_mismatch_word_zero :
  hoare [RawApiMuTrace.run :
    true
    ==>
    accepted_observed_mismatch_word_zero
      res RawApiMuTrace.observed_cp RawApiMuTrace.observed_cprime].
proof.
proc.
sp 15.
if.
+ auto => />.
  rewrite /accepted_observed_mismatch_word_zero.
  smt(W64.WRingA.oner_neq0).
+ wp.
  call verify_internal_mode2_mu_trace_accept_mismatch_word_zero.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  auto.
qed.

lemma verify_cryptolab_mu_trace_accept_mismatch_word_zero :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    accepted_observed_mismatch_word_zero
      res CryptolabMuTrace.observed_cp CryptolabMuTrace.observed_cprime].
proof.
proc.
seq 2 :
  (accepted_observed_mismatch_word_zero
     reject RawApiMuTrace.observed_cp RawApiMuTrace.observed_cprime).
+ inline Raw._verify_publish_reject.
  wp.
  call verify_raw_api_mu_trace_accept_mismatch_word_zero.
  auto => />; rewrite /protect_64; auto.
+ if.
  + auto.
  + wp.
    call RawApiVerifyAcceptTrace.api_reject_returns_nonzero.
    auto => />.
    rewrite /accepted_observed_mismatch_word_zero.
    smt().
qed.

lemma actual_verify_full_m23_accept_observed_mismatch_word_zero :
  equiv [Raw._verify_full_m23 ~ FullM23MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp, k_i, l_i, m_i, sigbytes_i,
      vkbytes_i, highbits_len_i, tau_i, b2sq_i, hb_count_i, hb_m_i,
      hb_offset_i, h_count_i, h_m_i, h_offset_i, base_hb_i, base_h_i,
      payload_limit_i}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mismatch_word_zero
      res{1} FullM23MuTrace.observed_cp{2}
      FullM23MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_full_m23_exact_mu_trace
  (_ : true ==> true)
  verify_full_m23_mu_trace_accept_mismatch_word_zero => //=.
qed.

lemma actual_verify_full_mode2_accept_observed_mismatch_word_zero :
  equiv [Raw._verify_full_mode2 ~ FullMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mismatch_word_zero
      res{1} FullMode2MuTrace.observed_cp{2}
      FullMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_full_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_full_mode2_mu_trace_accept_mismatch_word_zero => //=.
qed.

lemma actual_verify_internal_mode2_accept_observed_mismatch_word_zero :
  equiv [Raw.sign_verify_internal_mode2_jazz ~ InternalMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mismatch_word_zero
      res{1} InternalMode2MuTrace.observed_cp{2}
      InternalMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_internal_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_internal_mode2_mu_trace_accept_mismatch_word_zero => //=.
qed.

lemma actual_verify_raw_api_accept_observed_mismatch_word_zero :
  equiv [Raw._api_verify_mode2_raw ~ RawApiMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mismatch_word_zero
      res{1} RawApiMuTrace.observed_cp{2}
      RawApiMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace
  (_ : true ==> true)
  verify_raw_api_mu_trace_accept_mismatch_word_zero => //=.
qed.

lemma actual_verify_cryptolab_accept_observed_mismatch_word_zero :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ CryptolabMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mismatch_word_zero
      res{1} CryptolabMuTrace.observed_cp{2}
      CryptolabMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace
  (_ : true ==> true)
  verify_cryptolab_mu_trace_accept_mismatch_word_zero => //=.
qed.

end VerifyActualAcceptMismatchRawPostFreeze.
