require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawKeygenApiTarget.
require import PackedKeyPrefix ApiKeyMemoryBridge.
require import RawApiAddressBridge RawApiKeygenExportComposition.
require import RawApiMuReachability.

theory RawApiKeygenSequentialExport.

module Raw = RawKeygenApiTarget.M.
module Trace = RawApiKeygenExportComposition.RawKeygenExportTrace.

op mode2_vkbytes : int = ApiKeyMemoryBridge.mode2_vkbytes.
op mode2_skbytes : int = ApiKeyMemoryBridge.mode2_skbytes.
op seedbytes : int = RawApiKeygenExportComposition.seedbytes.

lemma raw_keygen_export_vk_live (vku0 : int) :
  hoare [Raw.__kp_api_copy_2080_to_addr :
    dstp = W64.of_int vku0 /\
    srcp = Trace.observed_vk /\
    len = W64.of_int mode2_vkbytes /\
    ApiKeyMemoryBridge.valid_region_w64
      (W64.of_int vku0) (W64.of_int mode2_vkbytes)
    ==>
    res = W64.of_int vku0 /\
    ApiKeyMemoryBridge.mem2080_prefix
      Glob.mem (W64.of_int vku0) Trace.observed_vk mode2_vkbytes].
proof.
proc.
while (dstp = W64.of_int vku0 /\
       srcp = Trace.observed_vk /\
       len = W64.of_int mode2_vkbytes /\
       ApiKeyMemoryBridge.valid_region_w64
         (W64.of_int vku0) (W64.of_int mode2_vkbytes) /\
       0 <= W64.to_uint i <= mode2_vkbytes /\
       ApiKeyMemoryBridge.mem2080_prefix
         Glob.mem (W64.of_int vku0) Trace.observed_vk (W64.to_uint i)).
+ auto => /> &hr hvalid hi0 hile hpref hult.
  have hi_lt : W64.to_uint i{hr} < mode2_vkbytes by
    move: hult; rewrite W64.ultE W64.of_uintK /= /mode2_vkbytes; smt().
  have hi_succ :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  split; first rewrite hi_succ; smt().
  rewrite hi_succ /ApiKeyMemoryBridge.mem2080_prefix => j hj.
  rewrite /loadW8 /storeW8 get_setE.
  have hsum :
      W64.to_uint (W64.of_int vku0) + W64.to_uint i{hr} < W64.modulus.
  + move: hvalid.
    rewrite /ApiKeyMemoryBridge.valid_region_w64 W64.of_uintK /=
            /mode2_vkbytes.
    smt().
  have hadd :
      W64.to_uint (W64.of_int vku0 + i{hr}) =
      W64.to_uint (W64.of_int vku0) + W64.to_uint i{hr} by
    rewrite W64.to_uintD_small 1:hsum.
  rewrite hadd.
  case: (j = W64.to_uint i{hr}) => [-> | hne].
  + rewrite ifT 1:/#.
    trivial.
  + rewrite ifF 1:/#.
    rewrite -/loadW8.
    apply hpref; smt().
auto => /> &hr hvalid.
split.
+ move=> idx hidx.
  smt().
+ move=> mem i hdone hi0 hile hpref.
  have hge : mode2_vkbytes <= W64.to_uint i.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /= /mode2_vkbytes.
    smt().
  have heq : W64.to_uint i = mode2_vkbytes by smt().
  rewrite -heq.
  exact hpref.
qed.

lemma raw_keygen_export_sk_live_frames_observed_vk
    (vku0 sku0 : int) :
  hoare [Raw.__kp_api_copy_2752_to_addr :
    dstp = W64.of_int sku0 /\
    srcp = Trace.observed_sk /\
    len = W64.of_int mode2_skbytes /\
    ApiKeyMemoryBridge.valid_region_w64
      (W64.of_int sku0) (W64.of_int mode2_skbytes) /\
    ApiKeyMemoryBridge.valid_region_w64
      (W64.of_int vku0) (W64.of_int mode2_vkbytes) /\
    ApiKeyMemoryBridge.disjoint_regions
      (W64.to_uint (W64.of_int vku0)) mode2_vkbytes
      (W64.to_uint (W64.of_int sku0)) mode2_skbytes /\
    ApiKeyMemoryBridge.mem2080_prefix
      Glob.mem (W64.of_int vku0) Trace.observed_vk mode2_vkbytes
    ==>
    res = W64.of_int sku0 /\
    ApiKeyMemoryBridge.mem2752_prefix
      Glob.mem (W64.of_int sku0) Trace.observed_sk mode2_skbytes /\
    ApiKeyMemoryBridge.mem2080_prefix
      Glob.mem (W64.of_int vku0) Trace.observed_vk mode2_vkbytes].
proof.
proc.
while (dstp = W64.of_int sku0 /\
       srcp = Trace.observed_sk /\
       len = W64.of_int mode2_skbytes /\
       ApiKeyMemoryBridge.valid_region_w64
         (W64.of_int sku0) (W64.of_int mode2_skbytes) /\
       ApiKeyMemoryBridge.valid_region_w64
         (W64.of_int vku0) (W64.of_int mode2_vkbytes) /\
       ApiKeyMemoryBridge.disjoint_regions
         (W64.to_uint (W64.of_int vku0)) mode2_vkbytes
         (W64.to_uint (W64.of_int sku0)) mode2_skbytes /\
       0 <= W64.to_uint i <= mode2_skbytes /\
       ApiKeyMemoryBridge.mem2080_prefix
         Glob.mem (W64.of_int vku0) Trace.observed_vk mode2_vkbytes /\
       ApiKeyMemoryBridge.mem2752_prefix
         Glob.mem (W64.of_int sku0) Trace.observed_sk (W64.to_uint i)).
+ auto => /> &hr hskvalid hvkvalid hdis hi0 hile hvkpref hskpref hult.
  have hi_lt : W64.to_uint i{hr} < mode2_skbytes by
    move: hult; rewrite W64.ultE W64.of_uintK /= /mode2_skbytes; smt().
  have hi_succ :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  have hsum :
      W64.to_uint (W64.of_int sku0) + W64.to_uint i{hr} < W64.modulus.
  + move: hskvalid.
    rewrite /ApiKeyMemoryBridge.valid_region_w64 W64.of_uintK /=
            /mode2_skbytes.
    smt().
  have hadd :
      W64.to_uint (W64.of_int sku0 + i{hr}) =
      W64.to_uint (W64.of_int sku0) + W64.to_uint i{hr} by
    rewrite W64.to_uintD_small 1:hsum.
  split; first rewrite hi_succ; smt().
  split.
  + apply ApiKeyMemoryBridge.mem2080_prefix_store_frame => //.
    move=> j hj.
    rewrite hadd.
    move: hdis hj hi_lt.
    rewrite /ApiKeyMemoryBridge.disjoint_regions
            /mode2_vkbytes /mode2_skbytes.
    smt().
  + rewrite hi_succ /ApiKeyMemoryBridge.mem2752_prefix => j hj.
    rewrite /loadW8 /storeW8 get_setE hadd.
    case: (j = W64.to_uint i{hr}) => [-> | hne].
    * rewrite ifT 1:/#.
      trivial.
    * rewrite ifF 1:/#.
      rewrite -/loadW8.
      apply hskpref; smt().
auto => /> &hr hskvalid hvkvalid hdis hvkpref.
split.
+ rewrite /ApiKeyMemoryBridge.mem2752_prefix; smt().
+ move=> mem i hdone hi0 hile hvkframe hskpref.
  have hge : mode2_skbytes <= W64.to_uint i.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /= /mode2_skbytes.
    smt().
  have heq : W64.to_uint i = mode2_skbytes by smt().
  rewrite -heq.
  exact hskpref.
qed.

lemma keypair_raw_api_trace_export_observations
    (vku0 sku0 seedu0 : int) :
  hoare [Trace.run :
    vku = vku0 /\ sku = sku0 /\ seedu = seedu0 /\
    ApiKeyMemoryBridge.valid_region_int seedu0 seedbytes /\
    RawApiAddressBridge.canonical_region vku0 mode2_vkbytes /\
    RawApiAddressBridge.canonical_region sku0 mode2_skbytes /\
    ApiKeyMemoryBridge.disjoint_regions
      vku0 mode2_vkbytes sku0 mode2_skbytes
    ==>
    res = W64.zero /\
    PackedKeyPrefix.vk_prefix_eq
      Trace.observed_sk Trace.observed_vk mode2_vkbytes /\
    ApiKeyMemoryBridge.mem2080_prefix
      Glob.mem (W64.of_int vku0) Trace.observed_vk mode2_vkbytes /\
    ApiKeyMemoryBridge.mem2752_prefix
      Glob.mem (W64.of_int sku0) Trace.observed_sk mode2_skbytes].
proof.
proc.
seq 20 :
  (vkua = W64.of_int vku0 /\
     skua = W64.of_int sku0 /\
     vkp = Trace.observed_vk /\
     skp = Trace.observed_sk /\
     PackedKeyPrefix.vk_prefix_eq
       Trace.observed_sk Trace.observed_vk mode2_vkbytes /\
     RawApiAddressBridge.canonical_region vku0 mode2_vkbytes /\
     RawApiAddressBridge.canonical_region sku0 mode2_skbytes /\
     ApiKeyMemoryBridge.disjoint_regions
       vku0 mode2_vkbytes sku0 mode2_skbytes).
+ wp.
  wp.
  call RawApiKeygenExportComposition.raw_keypair_internal_mode2_return_prefix.
  wp.
  call (_: true); first by auto.
  auto => />; rewrite /protect_64.
+ wp.
  call (raw_keygen_export_sk_live_frames_observed_vk vku0 sku0).
  wp.
  call (raw_keygen_export_vk_live vku0).
  auto => /> &hr hpref hvku0 hvkn hvub hsku0 hskn hsub hdis.
  split.
  + rewrite /ApiKeyMemoryBridge.valid_region_w64
            /mode2_vkbytes /ApiKeyMemoryBridge.mode2_vkbytes
            !W64.of_uintK /=.
    smt().
  + move=> _ _ mem hvkmem.
    split.
    * rewrite /ApiKeyMemoryBridge.valid_region_w64
              /mode2_skbytes /ApiKeyMemoryBridge.mode2_skbytes
              !W64.of_uintK /=.
      smt().
    * move: hdis.
      rewrite /ApiKeyMemoryBridge.disjoint_regions
              /mode2_vkbytes /mode2_skbytes
              /ApiKeyMemoryBridge.mode2_vkbytes
              /ApiKeyMemoryBridge.mode2_skbytes
              !W64.of_uintK /=.
      smt().
qed.

lemma keypair_raw_api_trace_exports_matching_prefixes
    (vku0 sku0 seedu0 : int) :
  hoare [Trace.run :
    vku = vku0 /\ sku = sku0 /\ seedu = seedu0 /\
    ApiKeyMemoryBridge.valid_region_int seedu0 seedbytes /\
    RawApiAddressBridge.canonical_region vku0 mode2_vkbytes /\
    RawApiAddressBridge.canonical_region sku0 mode2_skbytes /\
    ApiKeyMemoryBridge.disjoint_regions
      vku0 mode2_vkbytes sku0 mode2_skbytes
    ==>
    res = W64.zero /\
    RawApiMuReachability.external_key_prefix_match Glob.mem sku0 vku0].
proof.
conseq (keypair_raw_api_trace_export_observations vku0 sku0 seedu0) => //=.
move=> &1 [hvku_eq [hsku_eq [hseed_eq [hseed [hvku [hsku hdis]]]]]]
          result mem observed_sk observed_vk
          [hz [hpref [hvk hsk]]].
split; first exact hz.
rewrite /RawApiMuReachability.external_key_prefix_match => i hi.
have hvr := RawApiAddressBridge.mode2_vk_region_bridge vku0 hvku.
have hsr := RawApiAddressBridge.mode2_sk_region_bridge sku0 hsku.
case: hvr => _ [_ [_ hvku_round]].
case: hsr => _ [_ [_ hsku_round]].
rewrite -hsku_round -hvku_round.
exact (RawApiKeygenExportComposition.keypair_raw_api_exports_matching_prefixes_from_copy_posts
         mem (W64.of_int vku0) (W64.of_int sku0)
         observed_vk observed_sk
         hpref hsk hvk i hi).
qed.

lemma keypair_raw_api_exports_matching_prefixes
    (vku0 sku0 seedu0 : int) :
  hoare [Raw.cryptolab_haetae_mode2_keypair_internal :
    vku = vku0 /\ sku = sku0 /\ seedu = seedu0 /\
    ApiKeyMemoryBridge.valid_region_int seedu0 seedbytes /\
    RawApiAddressBridge.canonical_region vku0 mode2_vkbytes /\
    RawApiAddressBridge.canonical_region sku0 mode2_skbytes /\
    ApiKeyMemoryBridge.disjoint_regions
      vku0 mode2_vkbytes sku0 mode2_skbytes
    ==>
    res = W64.zero /\
    RawApiMuReachability.external_key_prefix_match Glob.mem sku0 vku0].
proof.
conseq RawApiKeygenExportComposition.keypair_raw_api_exact_export_trace
  (keypair_raw_api_trace_exports_matching_prefixes vku0 sku0 seedu0) => //=.
move=> &1 hpre.
exists Glob.mem{1}.
exists (vku{1}, sku{1}, seedu{1}) => //=.
qed.

end RawApiKeygenSequentialExport.
