require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawVerifyApiTarget.
require import SignMuHashTarget VerifyMuHashTarget.
require import ApiKeyMemoryBridge RawApiAddressBridge.
require import ExtractedMuHashPrefix ExactMuTopControl.
require import RawApiMuReachability RawApiCallerMuTrace.
require import RawApiVerifyMuTrace.
require import RawApiKeygenSequentialExport RawApiVerifyAcceptTrace.
require import ExactMode2RawMuComposition.

theory RawApiAcceptedMuComposition.

module RawVerify = RawVerifyApiTarget.M.
module Week3Sign = SignMuHashTarget.M.
module Week3Verify = VerifyMuHashTarget.M.
module SignTrace = RawApiCallerMuTrace.SignRawApiMuTrace.
module VerifyTailTrace = RawApiVerifyMuTrace.VerifyTailMuTrace.
module VerifyRawTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module RawKeygen = RawApiKeygenSequentialExport.Raw.
module RawSign = RawApiCallerMuTrace.Sign.
module GeneratedSignChallenge =
  ExactMode2RawMuComposition.GeneratedSignRawMuThenChallenge.
module GeneratedVerifyChallenge =
  ExactMode2RawMuComposition.GeneratedVerifyRawMuThenChallenge.

op mode2_vkbytes : int = ApiKeyMemoryBridge.mode2_vkbytes.
op mode2_skbytes : int = ApiKeyMemoryBridge.mode2_skbytes.
op mode2_sigbytes : int = RawApiVerifyMuTrace.mode2_sigbytes.

lemma verify_tail_trace_binds_hash_inputs
    (vku0 : int) (prep0 prelen0 mp0 mlen0 : W64.t) :
  hoare [VerifyTailTrace.run :
    RawApiVerifyMuTrace.mode2_verify_desc
      descp vku0 prep0 prelen0 mp0 mlen0 /\
    vklen_i = mode2_vkbytes
    ==>
    VerifyTailTrace.observed_vkp = W64.of_int vku0 /\
    VerifyTailTrace.observed_prep = prep0 /\
    VerifyTailTrace.observed_prelen = prelen0 /\
    VerifyTailTrace.observed_mp = mp0 /\
    VerifyTailTrace.observed_mlen = mlen0 /\
    VerifyTailTrace.observed_vklen = W64.of_int mode2_vkbytes].
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

lemma generated_hash_calls_mu_zero_loss_from_raw_api_regions
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (sku0 vku0 : int) :
  W64.to_uint (W64.of_int vku0) + mode2_vkbytes < W64.modulus =>
  RawApiAddressBridge.canonical_region vku0 mode2_vkbytes =>
  equiv [Week3Sign._sf_mu_rawpre ~ Week3Verify.__verify_hash_mu :
    ={Glob.mem} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    ApiKeyMemoryBridge.imported_prefix sk0 mem0 sku0 mode2_vkbytes /\
    RawApiMuReachability.external_key_prefix_match mem0 sku0 vku0 /\
    vkp{2} = W64.of_int vku0 /\
    vkbytes{1} = W64.of_int mode2_vkbytes /\
    vklen{2} = W64.of_int mode2_vkbytes /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    ExactMuTopControl.raw_prelen prelen{2} /\
    ExactMuTopControl.valid_region prep{2} prelen{2} /\
    ExactMuTopControl.valid_region mp{2} mlen{2}
    ==>
    ExtractedMuHashPrefix.mu32_prefix res{1} res{2}].
proof.
move=> hnowrap hvku.
conseq (ExactMuTopControl.sign_verify_generated_raw_mu_prefix
          sk0 mem0 (W64.of_int vku0) hnowrap) => //=.
move=> &1 &2
  [hglob [hsk [hmem [himport [hmatch [hvkp [hvkb [hvkl [hprep
  [hprelen [hmp [hmlen [hraw [hvalid_pre hvalid_msg]]]]]]]]]]]]]].
split; first exact hglob.
split; first exact hsk.
split; first exact hmem.
split; first exact hvkp.
split; first exact hvkb.
split; first exact hvkl.
split; first exact hprep.
split; first exact hprelen.
split; first exact hmp.
split; first exact hmlen.
split; first exact hraw.
split; first exact hvalid_pre.
split; first exact hvalid_msg.
exact (RawApiMuReachability.raw_api_region_reaches_mu_zero_loss
         sk0 mem0 sku0 vku0 hvku himport hmatch).
qed.

lemma actual_raw_keygen_exports_matching_prefixes
    (vku0 sku0 seedu0 : int) :
  hoare [RawKeygen.cryptolab_haetae_mode2_keypair_internal :
    vku = vku0 /\ sku = sku0 /\ seedu = seedu0 /\
    ApiKeyMemoryBridge.valid_region_int
      seedu0 RawApiKeygenSequentialExport.seedbytes /\
    RawApiAddressBridge.canonical_region vku0 mode2_vkbytes /\
    RawApiAddressBridge.canonical_region sku0 mode2_skbytes /\
    ApiKeyMemoryBridge.disjoint_regions
      vku0 mode2_vkbytes sku0 mode2_skbytes
    ==>
    res = W64.zero /\
    RawApiMuReachability.external_key_prefix_match Glob.mem sku0 vku0].
proof.
exact (RawApiKeygenSequentialExport.keypair_raw_api_exports_matching_prefixes
         vku0 sku0 seedu0).
qed.

lemma actual_raw_sign_exact_mu_trace :
  equiv [RawSign.cryptolab_haetae_mode2_signature_internal ~ SignTrace.run :
    ={Glob.mem, sigu, siglenu, mu, mlen, preu, prelen, rndu, sku}
    ==>
    ={Glob.mem, res}].
proof.
exact RawApiCallerMuTrace.sign_raw_api_exact_mu_trace.
qed.

lemma actual_raw_verify_accept_binds_hash_inputs
    (vku0 : int) (preu0 prelen0 mu0 mlen0 : W64.t) :
  equiv [RawVerify._api_verify_mode2_raw ~ VerifyRawTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku} /\
    siglen{1} = W64.of_int mode2_sigbytes /\
    mu{1} = mu0 /\ mlen{1} = mlen0 /\
    preu{1} = preu0 /\ prelen{1} = prelen0 /\ vku{1} = vku0
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero =>
      VerifyRawTrace.tail_reached{2} /\
      VerifyRawTrace.observed_vkp{2} = W64.of_int vku0 /\
      VerifyRawTrace.observed_prep{2} = preu0 /\
      VerifyRawTrace.observed_prelen{2} = prelen0 /\
      VerifyRawTrace.observed_mp{2} = mu0 /\
      VerifyRawTrace.observed_mlen{2} = mlen0 /\
      VerifyRawTrace.observed_vklen{2} = W64.of_int mode2_vkbytes)].
proof.
exact (RawApiVerifyAcceptTrace.verify_raw_api_actual_accept_binds_hash_inputs
         vku0 preu0 prelen0 mu0 mlen0).
qed.

(* The trace globals in this theorem are not assumptions about the hash.
   They are the post-state facts supplied by the exact Sign trace and the
   accepted Verify trace above.  The programs on both sides remain the real
   generated hash procedures. *)
lemma raw_api_accepting_execution_hash_mu_zero_loss
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (sku0 vku0 : int) :
  W64.to_uint (W64.of_int vku0) + mode2_vkbytes < W64.modulus =>
  RawApiAddressBridge.canonical_region vku0 mode2_vkbytes =>
  equiv [Week3Sign._sf_mu_rawpre ~ Week3Verify.__verify_hash_mu :
    ={Glob.mem} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    ApiKeyMemoryBridge.imported_prefix sk0 mem0 sku0 mode2_vkbytes /\
    RawApiMuReachability.external_key_prefix_match mem0 sku0 vku0 /\
    SignTrace.observed_sk{1} = sk0 /\
    SignTrace.observed_vkbytes{1} = W64.of_int mode2_vkbytes /\
    SignTrace.observed_preaddr{1} = preaddr{1} /\
    SignTrace.observed_prelen{1} = prelen{1} /\
    SignTrace.observed_maddr{1} = maddr{1} /\
    SignTrace.observed_mlen{1} = mlen{1} /\
    VerifyRawTrace.tail_reached{2} /\
    VerifyRawTrace.observed_vkp{2} = vkp{2} /\
    VerifyRawTrace.observed_prep{2} = prep{2} /\
    VerifyRawTrace.observed_prelen{2} = prelen{2} /\
    VerifyRawTrace.observed_mp{2} = mp{2} /\
    VerifyRawTrace.observed_mlen{2} = mlen{2} /\
    VerifyRawTrace.observed_vklen{2} = vklen{2} /\
    vkp{2} = W64.of_int vku0 /\
    vkbytes{1} = W64.of_int mode2_vkbytes /\
    vklen{2} = W64.of_int mode2_vkbytes /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    ExactMuTopControl.raw_prelen prelen{2} /\
    ExactMuTopControl.valid_region prep{2} prelen{2} /\
    ExactMuTopControl.valid_region mp{2} mlen{2}
    ==>
    ExtractedMuHashPrefix.mu32_prefix res{1} res{2}].
proof.
move=> hnowrap hvku.
conseq (generated_hash_calls_mu_zero_loss_from_raw_api_regions
          sk0 mem0 sku0 vku0 hnowrap hvku) => //=.
qed.

(* This is the strongest current suffix result.  It uses the actual generated
   hash and absorb helpers, but not yet the surrounding Sign-core and Verify-
   tail challenge call sites; those need new challenge-entry trace fields. *)
lemma raw_api_accepting_execution_generated_challenge_suffix_zero_loss
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (sku0 vku0 : int) :
  W64.to_uint (W64.of_int vku0) + mode2_vkbytes < W64.modulus =>
  RawApiAddressBridge.canonical_region vku0 mode2_vkbytes =>
  equiv [GeneratedSignChallenge.run ~ GeneratedVerifyChallenge.run :
    ={Glob.mem, challenge_state, challenge_pos} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    ApiKeyMemoryBridge.imported_prefix sk0 mem0 sku0 mode2_vkbytes /\
    RawApiMuReachability.external_key_prefix_match mem0 sku0 vku0 /\
    SignTrace.observed_sk{1} = sk0 /\
    VerifyRawTrace.tail_reached{2} /\
    vkp{2} = W64.of_int vku0 /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    ExactMuTopControl.raw_prelen prelen{2} /\
    ExactMuTopControl.valid_region prep{2} prelen{2} /\
    ExactMuTopControl.valid_region mp{2} mlen{2} /\
    BArray16.get64 challenge_pos{1} 0 = W64.of_int 64
    ==>
    ={res}].
proof.
move=> hnowrap hvku.
conseq (ExactMode2RawMuComposition.generated_raw_mu_to_challenge_suffix_zero_loss
          sk0 mem0 (W64.of_int vku0) hnowrap) => //=.
move=> &1 &2 h.
case: h => hmem h.
case: h => hstate h.
case: h => hpos h.
case: h => hsk h.
case: h => hmem0 h.
case: h => himport h.
case: h => hmatch h.
case: h => htrace h.
case: h => htail h.
case: h => hvkp h.
case: h => hprea h.
case: h => hprel h.
case: h => hmaddr h.
case: h => hmlen h.
case: h => hraw h.
split; first exact hmem.
split; first exact hstate.
split; first exact hpos.
split; first exact htrace.
split; first exact htail.
split; first exact hvkp.
split; first exact hprea.
split; first exact hprel.
split; first exact hmaddr.
split; first exact hmlen.
split; first exact hraw.
split.
+ exact (RawApiMuReachability.raw_api_region_reaches_mu_zero_loss
           sk0 mem0 sku0 vku0 hvku hsk hmem0).
+ exact h.
qed.

end RawApiAcceptedMuComposition.
