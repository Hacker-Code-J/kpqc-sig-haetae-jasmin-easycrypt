require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget RawVerifyApiTarget.
require import SignMuHashTarget VerifyMuHashTarget.
require import ApiKeyMemoryBridge RawApiAddressBridge.
require import ExtractedMuHashPrefix.
require import RawApiKeygenExportComposition RawApiCallerMuTrace.
require import RawApiVerifyMuTrace ExactMuTopControl.

theory RawApiMuReachability.

module RawSign = RawSignApiTarget.M.
module RawVerify = RawVerifyApiTarget.M.
module Week3Sign = SignMuHashTarget.M.
module Week3Verify = VerifyMuHashTarget.M.

op mode2_vkbytes : int = 992.

op external_key_prefix_match
    (mem : global_mem_t) (sku vku : int) : bool =
  forall i, 0 <= i < mode2_vkbytes =>
    loadW8 mem (sku + i) = loadW8 mem (vku + i).

op stable_region
    (before after : global_mem_t) (base len : int) : bool =
  forall i, 0 <= i < len =>
    loadW8 after (base + i) = loadW8 before (base + i).

lemma raw_sign_hash_extraction_identity :
  equiv [RawSign._sf_mu_rawpre ~ Week3Sign._sf_mu_rawpre :
    ={Glob.mem, mup, skp, vkbytes, preaddr, prelen, maddr, mlen}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_verify_hash_extraction_identity :
  equiv [RawVerify.__verify_hash_mu ~ Week3Verify.__verify_hash_mu :
    ={Glob.mem, mup, vkp, prep, prelen, mp, mlen, vklen}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma stable_region_refl
    (mem : global_mem_t) (base len : int) :
  stable_region mem mem base len.
proof.
rewrite /stable_region.
trivial.
qed.

lemma stable_region_trans
    (mem0 mem1 mem2 : global_mem_t) (base len : int) :
  stable_region mem0 mem1 base len =>
  stable_region mem1 mem2 base len =>
  stable_region mem0 mem2 base len.
proof.
move=> h01 h12.
rewrite /stable_region => i hi.
rewrite (h12 i hi) (h01 i hi).
trivial.
qed.

lemma external_prefix_survives_stability
    (mem0 mem1 : global_mem_t) (sku vku : int) :
  external_key_prefix_match mem0 sku vku =>
  stable_region mem0 mem1 sku mode2_vkbytes =>
  stable_region mem0 mem1 vku mode2_vkbytes =>
  external_key_prefix_match mem1 sku vku.
proof.
move=> hmatch hsk hvk.
rewrite /external_key_prefix_match => i hi.
rewrite (hsk i hi) (hvk i hi).
exact (hmatch i hi).
qed.

(* This is the stores-free memory premise needed by the Week-3 generated
   Sign/Verify hash theorem.  The memory is the caller's actual external
   memory; no existentially constructed store sequence appears here. *)
lemma raw_api_key_memory_reaches_mu_zero_loss
    (sk_local : BArray2752.t) (mem : global_mem_t)
    (sku vku : int) :
  RawApiAddressBridge.canonical_ui64_address vku =>
  ApiKeyMemoryBridge.imported_prefix
    sk_local mem sku mode2_vkbytes =>
  external_key_prefix_match mem sku vku =>
  W64.to_uint (W64.of_int vku) = vku /\
  ExtractedMuHashPrefix.sk_memory_prefix
    sk_local mem (W64.of_int vku).
proof.
move=> hcanonical himported hmatch.
have haddr := RawApiAddressBridge.canonical_ui64_address_roundtrip
                vku hcanonical.
split; first exact haddr.
apply (ApiKeyMemoryBridge.imported_sign_sk_reaches_mu_memory
         sk_local mem sku (W64.of_int vku)).
+ exact himported.
+ move=> i hi.
  rewrite haddr.
  exact (hmatch i hi).
qed.

lemma raw_api_region_reaches_mu_zero_loss
    (sk_local : BArray2752.t) (mem : global_mem_t)
    (sku vku : int) :
  RawApiAddressBridge.canonical_region vku mode2_vkbytes =>
  ApiKeyMemoryBridge.imported_prefix
    sk_local mem sku mode2_vkbytes =>
  external_key_prefix_match mem sku vku =>
  ExtractedMuHashPrefix.sk_memory_prefix
    sk_local mem (W64.of_int vku).
proof.
move=> hregion himported hmatch.
have hbridge := RawApiAddressBridge.mode2_vk_region_bridge vku hregion.
case: hbridge => hcanonical _.
have hreach := raw_api_key_memory_reaches_mu_zero_loss
                 sk_local mem sku vku hcanonical himported hmatch.
case: hreach => _ hprefix.
exact hprefix.
qed.

end RawApiMuReachability.
