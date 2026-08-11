require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget RawVerifyApiTarget.
require import RawApiCallerMuTrace RawApiVerifyMuTrace.
require import RawApiVerifyAcceptTrace RawApiSignOutputFrame.
require import RawApiAddressBridge RawApiMuReachability.
require import ApiKeyMemoryBridge ExactMuTopControl.
require import RegionLocalMuEquivalence RegionLocalMuTop.

theory RawApiDirectObservedMu.

module Sign = RawSignApiTarget.M.
module Verify = RawVerifyApiTarget.M.
module SignTrace = RawApiCallerMuTrace.SignRawApiMuTrace.
module VerifyTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

(* The raw ABI parameter called [mu] in the generated source is the message
   address.  The harness deliberately calls it [msgaddr] to keep that ABI
   value distinct from the 64/32-byte hash outputs observed by the traces. *)
module RawSignThenVerifyActual = {
  proc run (sigu : int, siglenu : int,
            msgaddr : int, mlen : int, preu : int, prelen : int,
            rndu : int, sku : int, siglen : int, vku : int)
      : W64.t * W64.t = {
    var sign_result : W64.t;
    var verify_result : W64.t;

    sign_result <@ Sign.cryptolab_haetae_mode2_signature_internal
      (sigu, siglenu, msgaddr, mlen, preu, prelen, rndu, sku);
    verify_result <@ Verify.cryptolab_haetae_mode2_verify_internal
      (sigu, siglen, msgaddr, mlen, preu, prelen, vku);
    return (sign_result, verify_result);
  }
}.

module RawSignThenAcceptedVerifyTrace = {
  proc run (sigu : int, siglenu : int,
            msgaddr : int, mlen : int, preu : int, prelen : int,
            rndu : int, sku : int, siglen : int, vku : int)
      : W64.t * W64.t = {
    var sign_result : W64.t;
    var verify_result : W64.t;

    sign_result <@ SignTrace.run
      (sigu, siglenu, msgaddr, mlen, preu, prelen, rndu, sku);
    verify_result <@ VerifyTrace.run
      (sigu, siglen, msgaddr, mlen, preu, prelen, vku);
    return (sign_result, verify_result);
  }
}.

(* Both sides execute the full signing and verification residual
   computations.  The right side only adds ghost observations at the actual
   generated mu calls. *)
lemma raw_sign_then_verify_actual_exact_trace :
  equiv [RawSignThenVerifyActual.run ~ RawSignThenAcceptedVerifyTrace.run :
    ={Glob.mem, sigu, siglenu, msgaddr, mlen, preu, prelen,
      rndu, sku, siglen, vku}
    ==>
    ={Glob.mem, res}].
proof.
proc.
call RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace.
call RawApiCallerMuTrace.sign_raw_api_exact_mu_trace.
auto.
qed.

(* Acceptance is learned from the actual Verify trace result.  No
   [tail_reached] or observed hash value is assumed in the precondition. *)
lemma sign_then_verify_trace_accept_implies_tail_reached :
  hoare [RawSignThenAcceptedVerifyTrace.run :
    true
    ==>
    res.`2 = W64.zero => VerifyTrace.tail_reached].
proof.
proc.
wp.
call RawApiVerifyAcceptTrace.verify_cryptolab_trace_accept_implies_tail_reached.
call (_ : true); first by auto.
auto.
qed.

(* The caller plumbing fixes both hash calls to the same raw pre/message
   descriptor values on every accepted execution.  The observed values below
   are post-state facts produced by the two trace calls. *)
lemma sign_then_verify_accept_binds_observed_inputs
    (vku0 preu0 prelen0 msgaddr0 mlen0 : int) :
  hoare [RawSignThenAcceptedVerifyTrace.run :
    siglen = RawApiVerifyMuTrace.mode2_sigbytes /\
    vku = vku0 /\ preu = preu0 /\ prelen = prelen0 /\
    msgaddr = msgaddr0 /\ mlen = mlen0
    ==>
    res.`2 = W64.zero =>
      VerifyTrace.tail_reached /\
      SignTrace.observed_vkbytes =
        W64.of_int RawApiCallerMuTrace.mode2_vkbytes /\
      SignTrace.observed_preaddr = W64.of_int preu0 /\
      SignTrace.observed_prelen = W64.of_int prelen0 /\
      SignTrace.observed_maddr = W64.of_int msgaddr0 /\
      SignTrace.observed_mlen = W64.of_int mlen0 /\
      VerifyTrace.observed_vkp = W64.of_int vku0 /\
      VerifyTrace.observed_prep = W64.of_int preu0 /\
      VerifyTrace.observed_prelen = W64.of_int prelen0 /\
      VerifyTrace.observed_mp = W64.of_int msgaddr0 /\
      VerifyTrace.observed_mlen = W64.of_int mlen0 /\
      VerifyTrace.observed_vklen =
        W64.of_int RawApiVerifyMuTrace.mode2_vkbytes].
proof.
proc.
wp.
call (RawApiVerifyAcceptTrace.verify_cryptolab_trace_accept_binds_hash_inputs
        vku0 preu0 prelen0 msgaddr0 mlen0).
call (RawApiCallerMuTrace.sign_raw_api_trace_binds_hash_inputs
        preu0 prelen0 msgaddr0 mlen0).
auto.
qed.

(* This pure bridge is the exact region-local premise produced by the Sign
   frame.  It intentionally stops before claiming anything about the two
   already-recorded [observed_mu] values: applying a relational hash theorem
   to values from two completed calls requires a product/replay argument that
   is not supplied by a frame fact alone. *)
lemma sign_frame_establishes_raw_mu_read_relation
    (sk0 : BArray2752.t) (mem0 mem1 : global_mem_t)
    (sku0 vku0 preu0 prelen0 msgaddr0 mlen0 : int) :
  RawApiAddressBridge.canonical_region vku0 992 =>
  RawApiAddressBridge.canonical_ui64_address preu0 =>
  RawApiAddressBridge.canonical_ui64_address prelen0 =>
  RawApiAddressBridge.canonical_ui64_address msgaddr0 =>
  RawApiAddressBridge.canonical_ui64_address mlen0 =>
  RawApiAddressBridge.canonical_region preu0 prelen0 =>
  RawApiAddressBridge.canonical_region msgaddr0 mlen0 =>
  ExactMuTopControl.raw_prelen (W64.of_int prelen0) =>
  ApiKeyMemoryBridge.imported_prefix sk0 mem0 sku0 992 =>
  RawApiMuReachability.external_key_prefix_match mem0 sku0 vku0 =>
  RawApiMuReachability.stable_region mem0 mem1 sku0 1408 =>
  RawApiMuReachability.stable_region mem0 mem1 vku0 992 =>
  RawApiMuReachability.stable_region mem0 mem1 preu0 prelen0 =>
  RawApiMuReachability.stable_region mem0 mem1 msgaddr0 mlen0 =>
  RegionLocalMuEquivalence.raw_mu_read_relation
    mem0 mem1 sk0 (W64.of_int vku0)
    (W64.of_int preu0) (W64.of_int prelen0)
    (W64.of_int msgaddr0) (W64.of_int mlen0).
proof.
move=> hvku hpre_addr hpre_len_addr hmsg_addr hmsg_len_addr
        hpre hmsg hraw himport hmatch hsk hvk hpre_stable hmsg_stable.
have hpre_bridge :=
  RawApiAddressBridge.canonical_region_valid_region_w64
    preu0 prelen0 hpre.
have hmsg_bridge :=
  RawApiAddressBridge.canonical_region_valid_region_w64
    msgaddr0 mlen0 hmsg.
have hpre_base : W64.to_uint (W64.of_int preu0) = preu0.
+ exact (RawApiAddressBridge.canonical_ui64_address_roundtrip
           preu0 hpre_addr).
have hpre_len : W64.to_uint (W64.of_int prelen0) = prelen0.
+ exact (RawApiAddressBridge.canonical_ui64_address_roundtrip
           prelen0 hpre_len_addr).
have hmsg_base : W64.to_uint (W64.of_int msgaddr0) = msgaddr0.
+ exact (RawApiAddressBridge.canonical_ui64_address_roundtrip
           msgaddr0 hmsg_addr).
have hmsg_len : W64.to_uint (W64.of_int mlen0) = mlen0.
+ exact (RawApiAddressBridge.canonical_ui64_address_roundtrip
           mlen0 hmsg_len_addr).
have hsk_prefix : RawApiMuReachability.stable_region mem0 mem1 sku0 992.
+ rewrite /RawApiMuReachability.stable_region => i hi.
  apply hsk; smt().
have himport1 : ApiKeyMemoryBridge.imported_prefix sk0 mem1 sku0 992.
+ rewrite /ApiKeyMemoryBridge.imported_prefix => i hi.
  rewrite (hsk_prefix i hi).
  exact (himport i hi).
have hmatch1 :
    RawApiMuReachability.external_key_prefix_match mem1 sku0 vku0.
+ apply (RawApiMuReachability.external_prefix_survives_stability
           mem0 mem1 sku0 vku0 hmatch hsk_prefix hvk).
have hkey := RawApiMuReachability.raw_api_region_reaches_mu_zero_loss
  sk0 mem1 sku0 vku0 hvku himport1 hmatch1.
rewrite /RegionLocalMuEquivalence.raw_mu_read_relation.
split; first exact hkey.
split.
+ rewrite /RegionLocalMuEquivalence.region_eq hpre_base hpre_len => i hi.
  rewrite (hpre_stable i hi).
  trivial.
split.
+ rewrite /RegionLocalMuEquivalence.region_eq hmsg_base hmsg_len => i hi.
  rewrite (hmsg_stable i hi).
  trivial.
split; first exact hraw.
split.
+ exact hpre_bridge.
+ exact hmsg_bridge.
qed.

end RawApiDirectObservedMu.
