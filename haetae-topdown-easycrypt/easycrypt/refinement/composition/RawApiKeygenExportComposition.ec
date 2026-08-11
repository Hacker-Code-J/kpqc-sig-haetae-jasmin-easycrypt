require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawKeygenApiTarget KeygenMode2ParentTarget KeygenApiCopyTarget.
require import PackedKeyPrefix ExtractedPackedKeyPrefix ApiKeyMemoryBridge.

theory RawApiKeygenExportComposition.

module Raw = RawKeygenApiTarget.M.
module Parent = KeygenMode2ParentTarget.M.
module ApiCopy = KeygenApiCopyTarget.M.

op mode2_vkbytes : int = 992.
op mode2_skbytes : int = 1408.
op seedbytes : int = 32.

module RawKeygenExportTrace = {
  var observed_vk : BArray2080.t
  var observed_sk : BArray2752.t

  proc run (vku : int, sku : int, seedu : int) : W64.t = {
    var vk : BArray2080.t;
    var vkp : BArray2080.t;
    var sk : BArray2752.t;
    var skp : BArray2752.t;
    var seed : BArray32.t;
    var seedp : BArray32.t;
    var vkua : W64.t;
    var skua : W64.t;
    var seedua : W64.t;
    var ms : W64.t;

    seed <- witness;
    seedp <- witness;
    sk <- witness;
    skp <- witness;
    vk <- witness;
    vkp <- witness;
    vkp <- vk;
    skp <- sk;
    seedp <- seed;
    vkua <- W64.of_int vku;
    skua <- W64.of_int sku;
    seedua <- W64.of_int seedu;
    ms <- init_msf;
    vkua <- protect_64 vkua ms;
    skua <- protect_64 skua ms;
    seedua <- protect_64 seedua ms;
    seedp <@ Raw.__kp_api_copy_addr_to_32 (seedp, seedua);
    (vkp, skp) <@ Raw.crypto_sign_keypair_internal_mode2_jazz
      (vkp, skp, seedp);
    observed_vk <- vkp;
    observed_sk <- skp;
    vkua <@ Raw.__kp_api_copy_2080_to_addr
      (vkua, vkp, W64.of_int 992);
    skua <@ Raw.__kp_api_copy_2752_to_addr
      (skua, skp, W64.of_int 1408);
    return W64.of_int 0;
  }
}.

op imported32_prefix
    (a : BArray32.t) (mem : global_mem_t)
    (base : W64.t) (n : int) : bool =
  forall j, 0 <= j < n =>
    BArray32.get8 a j = loadW8 mem (W64.to_uint base + j).

op raw_keypair_export_post
    (mem : global_mem_t) (vku sku : int) : bool =
  exists vk_local sk_local,
    ApiKeyMemoryBridge.mem2080_prefix
      mem (W64.of_int vku) vk_local mode2_vkbytes /\
    ApiKeyMemoryBridge.mem2752_prefix
      mem (W64.of_int sku) sk_local mode2_skbytes /\
    PackedKeyPrefix.vk_prefix_eq sk_local vk_local mode2_vkbytes /\
    (forall i, 0 <= i < mode2_vkbytes =>
       loadW8 mem (sku + i) = loadW8 mem (vku + i)).

op raw_keypair_trace_export_post
    (mem : global_mem_t) (vku sku : int) : bool =
  forall i, 0 <= i < mode2_vkbytes =>
    loadW8 mem (sku + i) = loadW8 mem (vku + i).

lemma valid_region_int_to_w64
    (base len : int) :
  ApiKeyMemoryBridge.valid_region_int base len =>
  ApiKeyMemoryBridge.valid_region_w64
    (W64.of_int base) (W64.of_int len).
proof.
rewrite /ApiKeyMemoryBridge.valid_region_int
        /ApiKeyMemoryBridge.valid_region_w64.
move=> [hbase [hlen hsum]].
rewrite !W64.of_uintK /=.
smt().
qed.

lemma raw_copy_2080_to_addr_equiv :
  equiv [Raw.__kp_api_copy_2080_to_addr ~ ApiCopy.__kp_api_copy_2080_to_addr :
    ={Glob.mem, dstp, srcp, len} ==> ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_copy_2752_to_addr_equiv :
  equiv [Raw.__kp_api_copy_2752_to_addr ~ ApiCopy.__kp_api_copy_2752_to_addr :
    ={Glob.mem, dstp, srcp, len} ==> ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_internal_mode2_equiv :
  equiv [Raw.crypto_sign_keypair_internal_mode2_jazz ~
         Parent.crypto_sign_keypair_internal_mode2_jazz :
    ={vkp, skp, seedp} ==> ={res}].
proof.
proc; sim.
qed.

lemma raw_seed_copy_addr_to_32_preserves_mem
    (src0 : W64.t) (mem0 : global_mem_t) :
  hoare [Raw.__kp_api_copy_addr_to_32 :
    Glob.mem = mem0 /\ srcp = src0 /\
    ApiKeyMemoryBridge.valid_region_w64 src0 (W64.of_int seedbytes)
    ==>
    Glob.mem = mem0].
proof.
proc.
while (Glob.mem = mem0).
+ auto.
auto.
qed.

lemma raw_keypair_internal_mode2_return_prefix :
  hoare [Raw.crypto_sign_keypair_internal_mode2_jazz :
    true
    ==>
    PackedKeyPrefix.vk_prefix_eq res.`2 res.`1 mode2_vkbytes].
proof.
conseq raw_internal_mode2_equiv
  ExtractedPackedKeyPrefix.keypair_internal_mode2_return_prefix => //=.
move=> &1.
exists (vkp{1}, skp{1}, seedp{1}) => />.
qed.

lemma raw_keygen_export_vk_mode2_prefix
    (dst0 : W64.t) (vk0 : BArray2080.t) (mem0 : global_mem_t) :
  hoare [Raw.__kp_api_copy_2080_to_addr :
    Glob.mem = mem0 /\ dstp = dst0 /\ srcp = vk0 /\
    len = W64.of_int mode2_vkbytes /\
    ApiKeyMemoryBridge.valid_region_w64 dst0 (W64.of_int mode2_vkbytes)
    ==>
    res = dst0 /\
    ApiKeyMemoryBridge.mem2080_prefix Glob.mem dst0 vk0 mode2_vkbytes].
proof.
conseq raw_copy_2080_to_addr_equiv
  (ApiKeyMemoryBridge.keygen_export_vk_mode2_prefix dst0 vk0 mem0) => //=.
move=> &1 [hmem [hdst [hsrc [hlen hvalid]]]].
exists mem0 => /=.
exists (dst0, vk0, W64.of_int mode2_vkbytes) => />.
qed.

lemma raw_keygen_export_sk_mode2_prefix_frames_vk
    (sku vku : W64.t) (sk0 : BArray2752.t) (vk0 : BArray2080.t)
    (mem0 : global_mem_t) :
  hoare [Raw.__kp_api_copy_2752_to_addr :
    Glob.mem = mem0 /\ dstp = sku /\ srcp = sk0 /\
    len = W64.of_int mode2_skbytes /\
    ApiKeyMemoryBridge.valid_region_w64 sku (W64.of_int mode2_skbytes) /\
    ApiKeyMemoryBridge.valid_region_w64 vku (W64.of_int mode2_vkbytes) /\
    ApiKeyMemoryBridge.disjoint_regions (W64.to_uint vku) mode2_vkbytes
                                        (W64.to_uint sku) mode2_skbytes /\
    ApiKeyMemoryBridge.mem2080_prefix mem0 vku vk0 mode2_vkbytes
    ==>
    res = sku /\
    ApiKeyMemoryBridge.mem2752_prefix Glob.mem sku sk0 mode2_skbytes /\
    ApiKeyMemoryBridge.mem2080_prefix Glob.mem vku vk0 mode2_vkbytes].
proof.
conseq raw_copy_2752_to_addr_equiv
  (ApiKeyMemoryBridge.keygen_export_sk_mode2_prefix_frames_vk
     sku vku sk0 vk0 mem0) => //=.
move=> &1 [hmem [hdst [hsrc [hlen [hsk [hvk [hdis hvkpref]]]]]]].
exists mem0 => /=.
exists (sku, sk0, W64.of_int mode2_skbytes) => />.
qed.

lemma keypair_raw_api_exact_export_trace :
  equiv [Raw.cryptolab_haetae_mode2_keypair_internal ~
         RawKeygenExportTrace.run :
    ={Glob.mem, vku, sku, seedu} ==> ={Glob.mem, res}].
proof.
proc.
seq 18 20 : (={Glob.mem, vkp, skp, vkua, skua}).
+ sim.
+ wp.
  call (_ : ={Glob.mem, dstp, srcp, len} ==> ={Glob.mem, res}).
  + proc; sim.
  + call (_ : ={Glob.mem, dstp, srcp, len} ==> ={Glob.mem, res}).
    + proc; sim.
    + auto.
qed.

lemma keypair_raw_api_exports_matching_prefixes_from_copy_posts
    (mem : global_mem_t) (vku sku : W64.t)
    (vk : BArray2080.t) (sk : BArray2752.t) :
  PackedKeyPrefix.vk_prefix_eq sk vk mode2_vkbytes =>
  ApiKeyMemoryBridge.mem2752_prefix mem sku sk mode2_skbytes =>
  ApiKeyMemoryBridge.mem2080_prefix mem vku vk mode2_vkbytes =>
  forall i, 0 <= i < mode2_vkbytes =>
    loadW8 mem (W64.to_uint sku + i) =
    loadW8 mem (W64.to_uint vku + i).
proof.
move=> hpref hsk hvk.
exact (ApiKeyMemoryBridge.exported_mode2_regions_agree
         sk vk mem sku vku hpref hsk hvk).
qed.

end RawApiKeygenExportComposition.
