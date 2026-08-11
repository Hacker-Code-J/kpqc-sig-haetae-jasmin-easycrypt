require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenApiCopyTarget SignApiCopyTarget VerifyApiCopyTarget.
require import PackedKeyPrefix ExtractedMuHashPrefix.

theory ApiKeyMemoryBridge.

module KeyGen = KeygenApiCopyTarget.M.
module Sign = SignApiCopyTarget.M.
module Verify = VerifyApiCopyTarget.M.

op mode2_vkbytes : int = 992.
op mode2_skbytes : int = 1408.

op valid_region_int (base len : int) : bool =
  0 <= base /\ 0 <= len /\ base + len <= W64.modulus.

op valid_region_w64 (base len : W64.t) : bool =
  W64.to_uint base + W64.to_uint len <= W64.modulus.

op disjoint_regions
    (base1 len1 base2 len2 : int) : bool =
  base1 + len1 <= base2 \/ base2 + len2 <= base1.

op mem2080_prefix
    (mem : global_mem_t) (base : W64.t)
    (src : BArray2080.t) (n : int) : bool =
  forall j, 0 <= j < n =>
    loadW8 mem (W64.to_uint base + j) = BArray2080.get8 src j.

op mem2752_prefix
    (mem : global_mem_t) (base : W64.t)
    (src : BArray2752.t) (n : int) : bool =
  forall j, 0 <= j < n =>
    loadW8 mem (W64.to_uint base + j) = BArray2752.get8 src j.

op imported_prefix
    (a : BArray2752.t) (mem : global_mem_t)
    (base n : int) : bool =
  forall j, 0 <= j < n =>
    BArray2752.get8 a j = loadW8 mem (base + j).

op local_2752_prefix_eq
    (a b : BArray2752.t) (n : int) : bool =
  forall j, 0 <= j < n =>
    BArray2752.get8 a j = BArray2752.get8 b j.

lemma mode2_api_region_contract_satisfiable :
  valid_region_w64 W64.zero (W64.of_int mode2_vkbytes) /\
  valid_region_w64 (W64.of_int mode2_vkbytes)
                   (W64.of_int mode2_skbytes) /\
  valid_region_int 0 mode2_vkbytes /\
  valid_region_int mode2_vkbytes mode2_skbytes /\
  disjoint_regions 0 mode2_vkbytes mode2_vkbytes mode2_skbytes.
proof.
rewrite /valid_region_w64 /valid_region_int /disjoint_regions
        /mode2_vkbytes /mode2_skbytes /=.
smt().
qed.

lemma mem2080_prefix_store_frame
    (mem : global_mem_t) (base : W64.t) (src : BArray2080.t)
    (n addr : int) (b : W8.t) :
  mem2080_prefix mem base src n =>
  (forall j, 0 <= j < n => W64.to_uint base + j <> addr) =>
  mem2080_prefix (storeW8 mem addr b) base src n.
proof.
move=> hpref hneq.
rewrite /mem2080_prefix => j hj.
rewrite /loadW8 /storeW8 get_setE.
have hne := hneq j hj.
have hold := hpref j hj.
rewrite /loadW8 in hold.
smt().
qed.

lemma sign_verify_api_importer_same_inputs :
  equiv [Sign._api_copy_raw_to_2752_prefix ~
         Verify._api_copy_raw_to_2752_prefix :
    ={Glob.mem, dstp, srcp, len} /\
    valid_region_int srcp{1} len{1} /\
    0 <= len{1} <= 2752
    ==>
    ={res, Glob.mem}].
proof.
proc; sim.
qed.

lemma sign_import_mode2_sk_prefix
    (src0 : int) (mem0 : global_mem_t) :
  hoare [Sign._api_copy_raw_to_2752_prefix :
    Glob.mem = mem0 /\ srcp = src0 /\ len = mode2_skbytes /\
    valid_region_int src0 mode2_skbytes
    ==>
    Glob.mem = mem0 /\
    imported_prefix res mem0 src0 mode2_vkbytes].
proof.
proc.
while (len = mode2_skbytes /\ Glob.mem = mem0 /\ srcp = src0 /\
       valid_region_int src0 mode2_skbytes /\
       mode2_skbytes <= i <= 2752 /\
       imported_prefix dstp mem0 src0 mode2_vkbytes).
+ auto => /> &hr hbase hlen hsum hi_ge hi_le hpref hguard.
  split; first smt().
  rewrite /imported_prefix => j hj.
  rewrite BArray2752.get_set_if.
  have hiword : W64.to_uint (W64.of_int i{hr}) = i{hr} by
    rewrite W64.of_uintK /=; smt().
  rewrite hiword.
  have hjlt : j < 992 by
    move: hj; rewrite /mode2_vkbytes; smt().
  have hige : 1408 <= i{hr} by
    move: hi_ge; rewrite /mode2_skbytes; smt().
  rewrite ifF 1:/#.
  exact (hpref j hj).
while (len = mode2_skbytes /\ Glob.mem = mem0 /\ srcp = src0 /\
       valid_region_int src0 mode2_skbytes /\
       0 <= i <= mode2_skbytes /\
       forall j, 0 <= j < i =>
         BArray2752.get8 dstp j = loadW8 mem0 (src0 + j)).
+ auto => /> &hr hbase hlen hsum hi_ge hi_le hpref hguard.
  split; first smt().
  move=> j hj0 hjlt.
  have hiword : W64.to_uint (W64.of_int i{hr}) = i{hr} by
    rewrite W64.of_uintK /=; rewrite /mode2_skbytes in hguard; smt().
  rewrite BArray2752.get_set_if hiword.
  case: (j = i{hr}) => [-> | hne].
  + rewrite ifT 1:/#.
    trivial.
  + rewrite ifF 1:/#.
    apply hpref; smt().
auto => />.
move=> &hr hbase hlen hsum.
split; first smt().
move=> dst i hdone hi0 hile hpref.
split.
+ split; rewrite /mode2_skbytes; smt().
+ rewrite /imported_prefix => j hj.
  apply hpref.
  move: hdone hile hj.
  rewrite /mode2_vkbytes /mode2_skbytes.
  smt().
qed.

lemma verify_import_mode2_vk_prefix
    (src0 : int) (mem0 : global_mem_t) :
  hoare [Verify._api_copy_raw_to_2752_prefix :
    Glob.mem = mem0 /\ srcp = src0 /\ len = mode2_vkbytes /\
    valid_region_int src0 mode2_vkbytes
    ==>
    Glob.mem = mem0 /\
    imported_prefix res mem0 src0 mode2_vkbytes].
proof.
proc.
while (len = mode2_vkbytes /\ Glob.mem = mem0 /\ srcp = src0 /\
       valid_region_int src0 mode2_vkbytes /\
       mode2_vkbytes <= i <= 2752 /\
       imported_prefix dstp mem0 src0 mode2_vkbytes).
+ auto => /> &hr hbase hlen hsum hi_ge hi_le hpref hguard.
  split; first smt().
  rewrite /imported_prefix => j hj.
  rewrite BArray2752.get_set_if.
  have hiword : W64.to_uint (W64.of_int i{hr}) = i{hr} by
    rewrite W64.of_uintK /=; smt().
  rewrite hiword.
  have hjlt : j < 992 by
    move: hj; rewrite /mode2_vkbytes; smt().
  have hige : 992 <= i{hr} by
    move: hi_ge; rewrite /mode2_vkbytes; smt().
  rewrite ifF 1:/#.
  exact (hpref j hj).
while (len = mode2_vkbytes /\ Glob.mem = mem0 /\ srcp = src0 /\
       valid_region_int src0 mode2_vkbytes /\
       0 <= i <= mode2_vkbytes /\
       forall j, 0 <= j < i =>
         BArray2752.get8 dstp j = loadW8 mem0 (src0 + j)).
+ auto => /> &hr hbase hlen hsum hi_ge hi_le hpref hguard.
  split; first smt().
  move=> j hj0 hjlt.
  have hiword : W64.to_uint (W64.of_int i{hr}) = i{hr} by
    rewrite W64.of_uintK /=; rewrite /mode2_vkbytes in hguard; smt().
  rewrite BArray2752.get_set_if hiword.
  case: (j = i{hr}) => [-> | hne].
  + rewrite ifT 1:/#.
    trivial.
  + rewrite ifF 1:/#.
    apply hpref; smt().
auto => />.
move=> &hr hbase hlen hsum.
split; first smt().
move=> dst i hdone hi0 hile hpref.
split.
+ split; rewrite /mode2_vkbytes; smt().
+ rewrite /imported_prefix => j hj.
  apply hpref.
  move: hdone hile hj.
  rewrite /mode2_vkbytes.
  smt().
qed.

lemma keygen_export_vk_mode2_prefix
    (dst0 : W64.t) (vk0 : BArray2080.t) (mem0 : global_mem_t) :
  hoare [KeyGen.__kp_api_copy_2080_to_addr :
    Glob.mem = mem0 /\ dstp = dst0 /\ srcp = vk0 /\
    len = W64.of_int mode2_vkbytes /\
    valid_region_w64 dst0 (W64.of_int mode2_vkbytes)
    ==>
    res = dst0 /\
    mem2080_prefix Glob.mem dst0 vk0 mode2_vkbytes].
proof.
proc.
while (dstp = dst0 /\ srcp = vk0 /\
       len = W64.of_int mode2_vkbytes /\
       valid_region_w64 dst0 (W64.of_int mode2_vkbytes) /\
       0 <= W64.to_uint i <= mode2_vkbytes /\
       mem2080_prefix Glob.mem dst0 vk0 (W64.to_uint i)).
+ auto => /> &hr hvalid hi0 hile hpref hult.
  have hi_lt : W64.to_uint i{hr} < mode2_vkbytes by
    move: hult; rewrite W64.ultE W64.of_uintK /= /mode2_vkbytes; smt().
  have hi_succ :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  split; first rewrite hi_succ; smt().
  rewrite hi_succ /mem2080_prefix => j hj.
  rewrite /loadW8 /storeW8 get_setE.
  have hsum :
      W64.to_uint dst0 + W64.to_uint i{hr} < W64.modulus.
  + move: hvalid.
    rewrite /valid_region_w64 W64.of_uintK /= /mode2_vkbytes.
    smt().
  have hadd :
      W64.to_uint (dst0 + i{hr}) =
      W64.to_uint dst0 + W64.to_uint i{hr} by
    rewrite W64.to_uintD_small 1:hsum.
  rewrite hadd.
  case: (j = W64.to_uint i{hr}) => [-> | hne].
  + rewrite ifT 1:/#.
    trivial.
  + rewrite ifF 1:/#.
    rewrite -/loadW8.
    apply hpref; smt().
auto => />.
move=> hvalid.
split.
+ rewrite /mem2080_prefix; smt().
+ move=> mem i hdone hi0 hile hpref.
  have hge : mode2_vkbytes <= W64.to_uint i.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /= /mode2_vkbytes.
    smt().
  have heq : W64.to_uint i = mode2_vkbytes by smt().
  rewrite -heq.
  exact hpref.
qed.

lemma keygen_export_sk_mode2_prefix
    (dst0 : W64.t) (sk0 : BArray2752.t) (mem0 : global_mem_t) :
  hoare [KeyGen.__kp_api_copy_2752_to_addr :
    Glob.mem = mem0 /\ dstp = dst0 /\ srcp = sk0 /\
    len = W64.of_int mode2_skbytes /\
    valid_region_w64 dst0 (W64.of_int mode2_skbytes)
    ==>
    res = dst0 /\
    mem2752_prefix Glob.mem dst0 sk0 mode2_skbytes].
proof.
proc.
while (dstp = dst0 /\ srcp = sk0 /\
       len = W64.of_int mode2_skbytes /\
       valid_region_w64 dst0 (W64.of_int mode2_skbytes) /\
       0 <= W64.to_uint i <= mode2_skbytes /\
       mem2752_prefix Glob.mem dst0 sk0 (W64.to_uint i)).
+ auto => /> &hr hvalid hi0 hile hpref hult.
  have hi_lt : W64.to_uint i{hr} < mode2_skbytes by
    move: hult; rewrite W64.ultE W64.of_uintK /= /mode2_skbytes; smt().
  have hi_succ :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  split; first rewrite hi_succ; smt().
  rewrite hi_succ /mem2752_prefix => j hj.
  rewrite /loadW8 /storeW8 get_setE.
  have hsum :
      W64.to_uint dst0 + W64.to_uint i{hr} < W64.modulus.
  + move: hvalid.
    rewrite /valid_region_w64 W64.of_uintK /= /mode2_skbytes.
    smt().
  have hadd :
      W64.to_uint (dst0 + i{hr}) =
      W64.to_uint dst0 + W64.to_uint i{hr} by
    rewrite W64.to_uintD_small 1:hsum.
  rewrite hadd.
  case: (j = W64.to_uint i{hr}) => [-> | hne].
  + rewrite ifT 1:/#.
    trivial.
  + rewrite ifF 1:/#.
    rewrite -/loadW8.
    apply hpref; smt().
auto => />.
move=> hvalid.
split.
+ rewrite /mem2752_prefix; smt().
+ move=> mem i hdone hi0 hile hpref.
  have hge : mode2_skbytes <= W64.to_uint i.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /= /mode2_skbytes.
    smt().
  have heq : W64.to_uint i = mode2_skbytes by smt().
  rewrite -heq.
exact hpref.
qed.

lemma keygen_export_sk_mode2_prefix_frames_vk
    (sku vku : W64.t) (sk0 : BArray2752.t) (vk0 : BArray2080.t)
    (mem0 : global_mem_t) :
  hoare [KeyGen.__kp_api_copy_2752_to_addr :
    Glob.mem = mem0 /\ dstp = sku /\ srcp = sk0 /\
    len = W64.of_int mode2_skbytes /\
    valid_region_w64 sku (W64.of_int mode2_skbytes) /\
    valid_region_w64 vku (W64.of_int mode2_vkbytes) /\
    disjoint_regions (W64.to_uint vku) mode2_vkbytes
                     (W64.to_uint sku) mode2_skbytes /\
    mem2080_prefix mem0 vku vk0 mode2_vkbytes
    ==>
    res = sku /\
    mem2752_prefix Glob.mem sku sk0 mode2_skbytes /\
    mem2080_prefix Glob.mem vku vk0 mode2_vkbytes].
proof.
proc.
while (dstp = sku /\ srcp = sk0 /\
       len = W64.of_int mode2_skbytes /\
       valid_region_w64 sku (W64.of_int mode2_skbytes) /\
       valid_region_w64 vku (W64.of_int mode2_vkbytes) /\
       disjoint_regions (W64.to_uint vku) mode2_vkbytes
                        (W64.to_uint sku) mode2_skbytes /\
       0 <= W64.to_uint i <= mode2_skbytes /\
       mem2080_prefix Glob.mem vku vk0 mode2_vkbytes /\
       mem2752_prefix Glob.mem sku sk0 (W64.to_uint i)).
+ auto => /> &hr hskvalid hvkvalid hdis hi0 hile hvkpref hskpref hult.
  have hi_lt : W64.to_uint i{hr} < mode2_skbytes by
    move: hult; rewrite W64.ultE W64.of_uintK /= /mode2_skbytes; smt().
  have hi_succ :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  have hsum :
      W64.to_uint sku + W64.to_uint i{hr} < W64.modulus.
  + move: hskvalid.
    rewrite /valid_region_w64 W64.of_uintK /= /mode2_skbytes.
    smt().
  have hadd :
      W64.to_uint (sku + i{hr}) =
      W64.to_uint sku + W64.to_uint i{hr} by
    rewrite W64.to_uintD_small 1:hsum.
  split; first rewrite hi_succ; smt().
  split.
  + apply mem2080_prefix_store_frame => //.
    move=> j hj.
    rewrite hadd.
    move: hdis hj hi_lt.
    rewrite /disjoint_regions /mode2_vkbytes /mode2_skbytes.
    smt().
  + rewrite hi_succ /mem2752_prefix => j hj.
    rewrite /loadW8 /storeW8 get_setE hadd.
    case: (j = W64.to_uint i{hr}) => [-> | hne].
    * rewrite ifT 1:/#.
      trivial.
    * rewrite ifF 1:/#.
      rewrite -/loadW8.
      apply hskpref; smt().
auto => />.
move=> hskvalid hvkvalid hdis hvkpref.
split.
+ rewrite /mem2752_prefix; smt().
+ move=> mem i hdone hi0 hile hvkframe hskpref.
  have hge : mode2_skbytes <= W64.to_uint i.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /= /mode2_skbytes.
    smt().
  have heq : W64.to_uint i = mode2_skbytes by smt().
  rewrite -heq.
  exact hskpref.
qed.

lemma exported_mode2_regions_agree
    (sk : BArray2752.t) (vk : BArray2080.t)
    (mem : global_mem_t) (sku vku : W64.t) :
  PackedKeyPrefix.vk_prefix_eq sk vk mode2_vkbytes =>
  mem2752_prefix mem sku sk mode2_skbytes =>
  mem2080_prefix mem vku vk mode2_vkbytes =>
  forall i, 0 <= i < mode2_vkbytes =>
    loadW8 mem (W64.to_uint sku + i) =
    loadW8 mem (W64.to_uint vku + i).
proof.
move=> hpref hsk hvk i hi.
rewrite (hsk i) 1:/# (hvk i hi).
exact (hpref i hi).
qed.

lemma imported_prefixes_agree
    (sk_local vk_local : BArray2752.t)
    (mem : global_mem_t) (sku vku : int) :
  imported_prefix sk_local mem sku mode2_vkbytes =>
  imported_prefix vk_local mem vku mode2_vkbytes =>
  (forall i, 0 <= i < mode2_vkbytes =>
     loadW8 mem (sku + i) = loadW8 mem (vku + i)) =>
  local_2752_prefix_eq sk_local vk_local mode2_vkbytes.
proof.
move=> hsk hvk hmem.
rewrite /local_2752_prefix_eq => i hi.
rewrite (hsk i hi) (hvk i hi).
exact (hmem i hi).
qed.

lemma imported_sign_sk_reaches_mu_memory
    (sk_local : BArray2752.t) (mem : global_mem_t)
    (sku : int) (vku : W64.t) :
  imported_prefix sk_local mem sku mode2_vkbytes =>
  (forall i, 0 <= i < mode2_vkbytes =>
     loadW8 mem (sku + i) =
     loadW8 mem (W64.to_uint vku + i)) =>
  ExtractedMuHashPrefix.sk_memory_prefix sk_local mem vku.
proof.
move=> hsk hmem.
rewrite /ExtractedMuHashPrefix.sk_memory_prefix => i hi.
rewrite (hsk i hi).
exact (hmem i hi).
qed.

end ApiKeyMemoryBridge.
