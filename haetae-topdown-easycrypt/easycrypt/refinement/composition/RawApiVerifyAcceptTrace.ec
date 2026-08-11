require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawVerifyApiTarget ExactMuTopControl.
require import RawApiVerifyMuTrace.

theory RawApiVerifyAcceptTrace.

module Verify = RawVerifyApiTarget.M.
module VerifyTailTrace = RawApiVerifyMuTrace.VerifyTailMuTrace.
module VerifyFullM23Trace = RawApiVerifyMuTrace.VerifyFullM23MuTrace.
module VerifyFullMode2Trace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module VerifyInternalMode2Trace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module VerifyRawApiTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module VerifyCryptolabTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

lemma verify_publish_reject_identity
    (reject0 : W64.t) :
  hoare [Verify._verify_publish_reject :
    reject = reject0
    ==>
    res = reject0].
proof.
proc; auto.
qed.

lemma api_reject_returns_nonzero :
  hoare [Verify._api_reject :
    true
    ==>
    res <> W64.zero].
proof.
proc.
auto => />.
rewrite /W64.zero /=.
smt().
qed.

lemma verify_full_m23_trace_accept_implies_tail_reached :
  hoare [VerifyFullM23Trace.run :
    true
    ==>
    res = W64.zero => VerifyFullM23Trace.tail_reached].
proof.
proc.
sp 38.
if.
+ auto => />.
  rewrite /W64.one /W64.zero /=.
  smt().
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
          rewrite /W64.one /W64.zero /=.
          smt().
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
                    call (_ : true ==> true); first by auto.
                    auto.
                  + auto.
qed.

lemma verify_full_mode2_trace_accept_implies_tail_reached :
  hoare [VerifyFullMode2Trace.run :
    true
    ==>
    res = W64.zero => VerifyFullMode2Trace.tail_reached].
proof.
proc.
wp.
call verify_full_m23_trace_accept_implies_tail_reached.
auto => />.
qed.

lemma verify_internal_mode2_trace_accept_implies_tail_reached :
  hoare [VerifyInternalMode2Trace.run :
    true
    ==>
    res = W64.zero => VerifyInternalMode2Trace.tail_reached].
proof.
proc.
wp.
call verify_full_mode2_trace_accept_implies_tail_reached.
auto => />.
qed.

lemma verify_raw_api_trace_accept_implies_tail_reached :
  hoare [VerifyRawApiTrace.run :
    true
    ==>
    res = W64.zero => VerifyRawApiTrace.tail_reached].
proof.
proc.
sp 15.
if.
+ auto => />.
  rewrite /W64.one /W64.zero /=.
  smt().
+ wp.
  call verify_internal_mode2_trace_accept_implies_tail_reached.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  auto.
qed.

lemma verify_cryptolab_trace_accept_implies_tail_reached :
  hoare [VerifyCryptolabTrace.run :
    true
    ==>
    res = W64.zero => VerifyCryptolabTrace.tail_reached].
proof.
proc.
seq 2 : (reject = W64.zero => VerifyRawApiTrace.tail_reached).
+ inline Verify._verify_publish_reject.
  wp.
  call verify_raw_api_trace_accept_implies_tail_reached.
  auto => />; rewrite /protect_64; auto.
+ if.
  + auto.
  + wp.
    call api_reject_returns_nonzero.
    auto => />; smt().
qed.

lemma verify_full_m23_actual_accept_implies_trace_tail_reached :
  equiv [Verify._verify_full_m23 ~ VerifyFullM23Trace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp, k_i, l_i, m_i, sigbytes_i,
      vkbytes_i, highbits_len_i, tau_i, b2sq_i, hb_count_i, hb_m_i,
      hb_offset_i, h_count_i, h_m_i, h_offset_i, base_hb_i, base_h_i,
      payload_limit_i}
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero => VerifyFullM23Trace.tail_reached{2})].
proof.
conseq RawApiVerifyMuTrace.verify_full_m23_exact_mu_trace
  (_ : true ==> true)
  verify_full_m23_trace_accept_implies_tail_reached => //=.
qed.

lemma verify_full_mode2_actual_accept_implies_trace_tail_reached :
  equiv [Verify._verify_full_mode2 ~ VerifyFullMode2Trace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero => VerifyFullMode2Trace.tail_reached{2})].
proof.
conseq RawApiVerifyMuTrace.verify_full_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_full_mode2_trace_accept_implies_tail_reached => //=.
qed.

lemma verify_internal_mode2_actual_accept_implies_trace_tail_reached :
  equiv [Verify.sign_verify_internal_mode2_jazz ~ VerifyInternalMode2Trace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero => VerifyInternalMode2Trace.tail_reached{2})].
proof.
conseq RawApiVerifyMuTrace.verify_internal_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_internal_mode2_trace_accept_implies_tail_reached => //=.
qed.

lemma verify_raw_api_actual_accept_implies_trace_tail_reached :
  equiv [Verify._api_verify_mode2_raw ~ VerifyRawApiTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero => VerifyRawApiTrace.tail_reached{2})].
proof.
conseq RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace
  (_ : true ==> true)
  verify_raw_api_trace_accept_implies_tail_reached => //=.
qed.

lemma verify_cryptolab_actual_accept_implies_trace_tail_reached :
  equiv [Verify.cryptolab_haetae_mode2_verify_internal ~ VerifyCryptolabTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero => VerifyCryptolabTrace.tail_reached{2})].
proof.
conseq RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace
  (_ : true ==> true)
  verify_cryptolab_trace_accept_implies_tail_reached => //=.
qed.

lemma verify_tail_trace_binds_hash_inputs
    (vku0 : int) (prep0 prelen0 mp0 mlen0 : W64.t) :
  hoare [VerifyTailTrace.run :
    RawApiVerifyMuTrace.mode2_verify_desc
      descp vku0 prep0 prelen0 mp0 mlen0 /\
    vklen_i = RawApiVerifyMuTrace.mode2_vkbytes
    ==>
    VerifyTailTrace.observed_vkp = W64.of_int vku0 /\
    VerifyTailTrace.observed_prep = prep0 /\
    VerifyTailTrace.observed_prelen = prelen0 /\
    VerifyTailTrace.observed_mp = mp0 /\
    VerifyTailTrace.observed_mlen = mlen0 /\
    VerifyTailTrace.observed_vklen =
      W64.of_int RawApiVerifyMuTrace.mode2_vkbytes].
proof.
proc.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
auto => />.
qed.

lemma verify_full_m23_trace_accept_binds_hash_inputs
    (vku0 : int) (prep0 prelen0 mp0 mlen0 : W64.t) :
  hoare [VerifyFullM23Trace.run :
    RawApiVerifyMuTrace.mode2_verify_desc
      descp vku0 prep0 prelen0 mp0 mlen0 /\
    vkbytes_i = RawApiVerifyMuTrace.mode2_vkbytes
    ==>
    res = W64.zero =>
    VerifyFullM23Trace.tail_reached /\
    VerifyFullM23Trace.observed_vkp = W64.of_int vku0 /\
    VerifyFullM23Trace.observed_prep = prep0 /\
    VerifyFullM23Trace.observed_prelen = prelen0 /\
    VerifyFullM23Trace.observed_mp = mp0 /\
    VerifyFullM23Trace.observed_mlen = mlen0 /\
    VerifyFullM23Trace.observed_vklen =
      W64.of_int RawApiVerifyMuTrace.mode2_vkbytes].
proof.
proc.
sp 38.
if.
+ auto => />.
  rewrite /W64.one /W64.zero /=.
  smt().
+ seq 11 : (RawApiVerifyMuTrace.mode2_verify_desc
              copydescp vku0 prep0 prelen0 mp0 mlen0 /\
             vkbytes_i = RawApiVerifyMuTrace.mode2_vkbytes).
  + call (_ : true ==> true); first by auto.
    auto => />.
    rewrite /RawApiVerifyMuTrace.mode2_verify_desc /=.
  + sp 5.
    seq 1 : (RawApiVerifyMuTrace.mode2_verify_desc
               copydescp vku0 prep0 prelen0 mp0 mlen0 /\
              vkbytes_i = RawApiVerifyMuTrace.mode2_vkbytes).
    + if; auto.
    + seq 16 : (RawApiVerifyMuTrace.mode2_verify_desc
                  copydescp vku0 prep0 prelen0 mp0 mlen0 /\
                 vkbytes_i = RawApiVerifyMuTrace.mode2_vkbytes).
      + call (_ : true ==> true); first by auto.
        auto.
      + sp 5.
        if.
        + auto => />.
          rewrite /W64.one /W64.zero /=.
          smt().
        + seq 12 : (RawApiVerifyMuTrace.mode2_verify_desc
                      copydescp vku0 prep0 prelen0 mp0 mlen0 /\
                     vkbytes_i = RawApiVerifyMuTrace.mode2_vkbytes).
          + call (_ : true ==> true); first by auto.
            auto.
          + seq 9 : (RawApiVerifyMuTrace.mode2_verify_desc
                       copydescp vku0 prep0 prelen0 mp0 mlen0 /\
                      vkbytes_i = RawApiVerifyMuTrace.mode2_vkbytes).
            + call (_ : true ==> true); first by auto.
              auto.
            + seq 12 : (RawApiVerifyMuTrace.mode2_verify_desc
                          copydescp vku0 prep0 prelen0 mp0 mlen0 /\
                         vkbytes_i = RawApiVerifyMuTrace.mode2_vkbytes).
              + call (_ : true ==> true); first by auto.
                auto.
              + seq 7 : (RawApiVerifyMuTrace.mode2_verify_desc
                           copydescp vku0 prep0 prelen0 mp0 mlen0 /\
                          vkbytes_i = RawApiVerifyMuTrace.mode2_vkbytes).
                + call (_ : true ==> true); first by auto.
                  auto.
                + sp 2.
                  if.
                  + wp.
                    call (verify_tail_trace_binds_hash_inputs
                            vku0 prep0 prelen0 mp0 mlen0).
                    auto => />.
                  + auto.
qed.

lemma verify_full_mode2_trace_accept_binds_hash_inputs
    (vku0 : int) (prep0 prelen0 mp0 mlen0 : W64.t) :
  hoare [VerifyFullMode2Trace.run :
    RawApiVerifyMuTrace.mode2_verify_desc
      descp vku0 prep0 prelen0 mp0 mlen0
    ==>
    res = W64.zero =>
    VerifyFullMode2Trace.tail_reached /\
    VerifyFullMode2Trace.observed_vkp = W64.of_int vku0 /\
    VerifyFullMode2Trace.observed_prep = prep0 /\
    VerifyFullMode2Trace.observed_prelen = prelen0 /\
    VerifyFullMode2Trace.observed_mp = mp0 /\
    VerifyFullMode2Trace.observed_mlen = mlen0 /\
    VerifyFullMode2Trace.observed_vklen =
      W64.of_int RawApiVerifyMuTrace.mode2_vkbytes].
proof.
proc.
wp.
call (verify_full_m23_trace_accept_binds_hash_inputs
        vku0 prep0 prelen0 mp0 mlen0).
auto => />.
qed.

lemma verify_internal_mode2_trace_accept_binds_hash_inputs
    (vku0 : int) (prep0 prelen0 mp0 mlen0 : W64.t) :
  hoare [VerifyInternalMode2Trace.run :
    RawApiVerifyMuTrace.mode2_verify_desc
      descp vku0 prep0 prelen0 mp0 mlen0
    ==>
    res = W64.zero =>
    VerifyInternalMode2Trace.tail_reached /\
    VerifyInternalMode2Trace.observed_vkp = W64.of_int vku0 /\
    VerifyInternalMode2Trace.observed_prep = prep0 /\
    VerifyInternalMode2Trace.observed_prelen = prelen0 /\
    VerifyInternalMode2Trace.observed_mp = mp0 /\
    VerifyInternalMode2Trace.observed_mlen = mlen0 /\
    VerifyInternalMode2Trace.observed_vklen =
      W64.of_int RawApiVerifyMuTrace.mode2_vkbytes].
proof.
proc.
wp.
call (verify_full_mode2_trace_accept_binds_hash_inputs
        vku0 prep0 prelen0 mp0 mlen0).
auto => />.
qed.

lemma verify_raw_api_trace_accept_binds_hash_inputs
    (vku0 : int) (preu0 prelen0 mu0 mlen0 : W64.t) :
  hoare [VerifyRawApiTrace.run :
    siglen = W64.of_int RawApiVerifyMuTrace.mode2_sigbytes /\
    mu = mu0 /\ mlen = mlen0 /\
    preu = preu0 /\ prelen = prelen0 /\ vku = vku0
    ==>
    res = W64.zero =>
    VerifyRawApiTrace.tail_reached /\
    VerifyRawApiTrace.observed_vkp = W64.of_int vku0 /\
    VerifyRawApiTrace.observed_prep = preu0 /\
    VerifyRawApiTrace.observed_prelen = prelen0 /\
    VerifyRawApiTrace.observed_mp = mu0 /\
    VerifyRawApiTrace.observed_mlen = mlen0 /\
    VerifyRawApiTrace.observed_vklen =
      W64.of_int RawApiVerifyMuTrace.mode2_vkbytes].
proof.
proc.
sp 15.
if.
+ auto.
+ wp.
  call (verify_internal_mode2_trace_accept_binds_hash_inputs
          vku0 preu0 prelen0 mu0 mlen0).
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  auto => />.
qed.

lemma verify_raw_api_actual_accept_binds_hash_inputs
    (vku0 : int) (preu0 prelen0 mu0 mlen0 : W64.t) :
  equiv [Verify._api_verify_mode2_raw ~ VerifyRawApiTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku} /\
    siglen{1} = W64.of_int RawApiVerifyMuTrace.mode2_sigbytes /\
    mu{1} = mu0 /\ mlen{1} = mlen0 /\
    preu{1} = preu0 /\ prelen{1} = prelen0 /\ vku{1} = vku0
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero =>
      VerifyRawApiTrace.tail_reached{2} /\
      VerifyRawApiTrace.observed_vkp{2} = W64.of_int vku0 /\
      VerifyRawApiTrace.observed_prep{2} = preu0 /\
      VerifyRawApiTrace.observed_prelen{2} = prelen0 /\
      VerifyRawApiTrace.observed_mp{2} = mu0 /\
      VerifyRawApiTrace.observed_mlen{2} = mlen0 /\
      VerifyRawApiTrace.observed_vklen{2} =
        W64.of_int RawApiVerifyMuTrace.mode2_vkbytes)].
proof.
conseq RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace
  (_ : true ==> true)
  (verify_raw_api_trace_accept_binds_hash_inputs
     vku0 preu0 prelen0 mu0 mlen0) => //=.
smt().
qed.

lemma verify_cryptolab_trace_accept_binds_hash_inputs
    (vku0 preu0 prelen0 mu0 mlen0 : int) :
  hoare [VerifyCryptolabTrace.run :
    siglen = RawApiVerifyMuTrace.mode2_sigbytes /\
    vku = vku0 /\ preu = preu0 /\ prelen = prelen0 /\
    mu = mu0 /\ mlen = mlen0
    ==>
    res = W64.zero =>
    VerifyCryptolabTrace.tail_reached /\
    VerifyCryptolabTrace.observed_vkp = W64.of_int vku0 /\
    VerifyCryptolabTrace.observed_prep = W64.of_int preu0 /\
    VerifyCryptolabTrace.observed_prelen = W64.of_int prelen0 /\
    VerifyCryptolabTrace.observed_mp = W64.of_int mu0 /\
    VerifyCryptolabTrace.observed_mlen = W64.of_int mlen0 /\
    VerifyCryptolabTrace.observed_vklen =
      W64.of_int RawApiVerifyMuTrace.mode2_vkbytes].
proof.
proc.
seq 2 :
  (reject = W64.zero =>
   VerifyRawApiTrace.tail_reached /\
   VerifyRawApiTrace.observed_vkp = W64.of_int vku0 /\
   VerifyRawApiTrace.observed_prep = W64.of_int preu0 /\
   VerifyRawApiTrace.observed_prelen = W64.of_int prelen0 /\
   VerifyRawApiTrace.observed_mp = W64.of_int mu0 /\
   VerifyRawApiTrace.observed_mlen = W64.of_int mlen0 /\
   VerifyRawApiTrace.observed_vklen =
     W64.of_int RawApiVerifyMuTrace.mode2_vkbytes).
+ inline Verify._verify_publish_reject.
  wp.
  call (verify_raw_api_trace_accept_binds_hash_inputs
          vku0 (W64.of_int preu0) (W64.of_int prelen0)
          (W64.of_int mu0) (W64.of_int mlen0)).
  auto => />; rewrite /protect_64; auto.
+ if.
  + auto.
  + wp.
    call api_reject_returns_nonzero.
    auto => />; smt().
qed.

lemma verify_cryptolab_actual_accept_binds_hash_inputs
    (vku0 preu0 prelen0 mu0 mlen0 : int) :
  equiv [Verify.cryptolab_haetae_mode2_verify_internal ~
         VerifyCryptolabTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku} /\
    siglen{1} = RawApiVerifyMuTrace.mode2_sigbytes /\
    vku{1} = vku0 /\ preu{1} = preu0 /\ prelen{1} = prelen0 /\
    mu{1} = mu0 /\ mlen{1} = mlen0
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero =>
      VerifyCryptolabTrace.tail_reached{2} /\
      VerifyCryptolabTrace.observed_vkp{2} = W64.of_int vku0 /\
      VerifyCryptolabTrace.observed_prep{2} = W64.of_int preu0 /\
      VerifyCryptolabTrace.observed_prelen{2} = W64.of_int prelen0 /\
      VerifyCryptolabTrace.observed_mp{2} = W64.of_int mu0 /\
      VerifyCryptolabTrace.observed_mlen{2} = W64.of_int mlen0 /\
      VerifyCryptolabTrace.observed_vklen{2} =
        W64.of_int RawApiVerifyMuTrace.mode2_vkbytes)].
proof.
conseq RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace
  (_ : true ==> true)
  (verify_cryptolab_trace_accept_binds_hash_inputs
     vku0 preu0 prelen0 mu0 mlen0) => //=.
smt().
qed.

end RawApiVerifyAcceptTrace.
