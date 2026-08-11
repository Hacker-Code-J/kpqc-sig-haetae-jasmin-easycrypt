require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget.
require import ApiKeyMemoryBridge RawApiAddressBridge.
require import RawApiMuReachability RawApiCallerMuTrace.

theory RawApiSignOutputFrame.

module Sign = RawSignApiTarget.M.
module SignTrace = RawApiCallerMuTrace.SignRawApiMuTrace.
module SignInternalTrace = RawApiCallerMuTrace.SignInternalMuTrace.

op mode2_vkbytes : int = 992.
op mode2_skbytes : int = 1408.
op mode2_sigbytes : int = 1474.
op siglenbytes : int = 8.

op signature_prefix
    (mem : global_mem_t) (base : int)
    (sig : BArray2948.t) (len : int) : bool =
  forall i, 0 <= i < len =>
    loadW8 mem (base + i) = BArray2948.get8 sig i.

op byte_frame_outside
    (before after : global_mem_t) (base len : int) : bool =
  forall addr, !(base <= addr < base + len) =>
    loadW8 after addr = loadW8 before addr.

op reused_regions_stable
    (before after : global_mem_t)
    (vku sku preu prelen msgaddr mlen : int) : bool =
  RawApiMuReachability.stable_region before after vku mode2_vkbytes /\
  RawApiMuReachability.stable_region before after sku mode2_skbytes /\
  RawApiMuReachability.stable_region before after preu prelen /\
  RawApiMuReachability.stable_region before after msgaddr mlen.

op signature_disjoint_from_reused
    (sigu vku sku preu prelen msgaddr mlen : int) : bool =
  ApiKeyMemoryBridge.disjoint_regions
    sigu mode2_sigbytes vku mode2_vkbytes /\
  ApiKeyMemoryBridge.disjoint_regions
    sigu mode2_sigbytes sku mode2_skbytes /\
  ApiKeyMemoryBridge.disjoint_regions sigu mode2_sigbytes preu prelen /\
  ApiKeyMemoryBridge.disjoint_regions sigu mode2_sigbytes msgaddr mlen.

op output_disjoint_from_reused
    (sigu siglenu vku sku preu prelen msgaddr mlen : int) : bool =
  ApiKeyMemoryBridge.disjoint_regions
    sigu mode2_sigbytes vku mode2_vkbytes /\
  ApiKeyMemoryBridge.disjoint_regions
    sigu mode2_sigbytes sku mode2_skbytes /\
  ApiKeyMemoryBridge.disjoint_regions sigu mode2_sigbytes preu prelen /\
  ApiKeyMemoryBridge.disjoint_regions sigu mode2_sigbytes msgaddr mlen /\
  ApiKeyMemoryBridge.disjoint_regions siglenu siglenbytes vku mode2_vkbytes /\
  ApiKeyMemoryBridge.disjoint_regions siglenu siglenbytes sku mode2_skbytes /\
  ApiKeyMemoryBridge.disjoint_regions siglenu siglenbytes preu prelen /\
  ApiKeyMemoryBridge.disjoint_regions siglenu siglenbytes msgaddr mlen /\
  ApiKeyMemoryBridge.disjoint_regions
    sigu mode2_sigbytes siglenu siglenbytes.

lemma sign_output_frame_contract_satisfiable :
  exists sigu siglenu vku sku preu prelen msgaddr mlen,
    ApiKeyMemoryBridge.valid_region_int sigu mode2_sigbytes /\
    output_disjoint_from_reused
      sigu siglenu vku sku preu prelen msgaddr mlen.
proof.
exists 6000 8000 0 2000 4000 1 5000 1.
rewrite /ApiKeyMemoryBridge.valid_region_int
        /output_disjoint_from_reused
        /ApiKeyMemoryBridge.disjoint_regions
        /mode2_sigbytes /mode2_vkbytes /mode2_skbytes /siglenbytes /=.
smt().
qed.

lemma stable_region_storeW8_outside
    (mem : global_mem_t) (addr base len : int) (b : W8.t) :
  (forall i, 0 <= i < len => base + i <> addr) =>
  RawApiMuReachability.stable_region
    mem (storeW8 mem addr b) base len.
proof.
move=> hout.
rewrite /RawApiMuReachability.stable_region => i hi.
rewrite /loadW8 /storeW8 get_setE.
by rewrite ifF 1:(hout i hi).
qed.

lemma stable_region_storeW64_disjoint
    (mem : global_mem_t) (addr base len : int) (w : W64.t) :
  ApiKeyMemoryBridge.disjoint_regions addr siglenbytes base len =>
  RawApiMuReachability.stable_region
    mem (storeW64 mem addr w) base len.
proof.
move=> hdis.
rewrite /RawApiMuReachability.stable_region => i hi.
rewrite /loadW8 storeW64E get_storesE /=.
have hout : !(addr <= base + i < addr + 8).
+ move: hdis hi.
  rewrite /ApiKeyMemoryBridge.disjoint_regions /siglenbytes.
  smt().
by rewrite hout.
qed.

lemma loadW64_storeW64_same
    (mem : global_mem_t) (addr : int) (w : W64.t) :
  loadW64 (storeW64 mem addr w) addr = w.
proof.
rewrite /loadW64 -(W8u8.unpack8K w); congr.
apply W8u8.Pack.ext_eq => i hi.
rewrite W8u8.get_unpack8 //= W8u8.Pack.initiE //=.
rewrite storeW64E get_storesE /=.
have hrange : addr <= addr + i < addr + 8 by smt().
rewrite hrange /=.
have -> : addr + i - addr = i by ring.
smt().
qed.

lemma int_prefix_old_index (j i : int) :
  0 <= j < i + 1 => j <> i => 0 <= j < i.
proof. smt(). qed.

lemma outside_region_not_current
    (base len i addr : int) :
  0 <= i < len =>
  !(base <= addr < base + len) =>
  addr <> base + i.
proof. smt(). qed.

lemma signature_prefix_store_step
    (mem : global_mem_t) (base i : int)
    (sig : BArray2948.t) (b : W8.t) :
  0 <= i =>
  b = BArray2948.get8 sig i =>
  signature_prefix mem base sig i =>
  signature_prefix (storeW8 mem (base + i) b) base sig (i + 1).
proof.
move=> hi hb hpref.
rewrite /signature_prefix in hpref.
rewrite /signature_prefix => j hj.
move: hj => [hj0 hjlt].
rewrite /loadW8 /storeW8 get_setE.
case: (base + i = base + j) => heq.
+ have -> : j = i by smt().
  rewrite hb.
  trivial.
+ have hbounds : 0 <= j < i by smt().
  rewrite ifF 1:/#.
  exact (hpref j hbounds).
qed.

lemma byte_frame_outside_store_step
    (before mem : global_mem_t) (base len i : int) (b : W8.t) :
  0 <= i < len =>
  byte_frame_outside before mem base len =>
  byte_frame_outside before (storeW8 mem (base + i) b) base len.
proof.
move=> hi hframe.
rewrite /byte_frame_outside in hframe.
rewrite /byte_frame_outside => addr hout.
rewrite /loadW8 /storeW8 get_setE ifF.
+ exact (outside_region_not_current base len i addr hi hout).
+ exact (hframe addr hout).
qed.

lemma sign_output_copy_exact_and_frames_reused
    (mem0 : global_mem_t) (sig0 : BArray2948.t)
    (sigu0 : int) :
  hoare [Sign._api_copy_2948_to_raw :
    Glob.mem = mem0 /\ dstp = sigu0 /\ srcp = sig0 /\
    len = mode2_sigbytes /\
    ApiKeyMemoryBridge.valid_region_int sigu0 mode2_sigbytes
    ==>
    res = sigu0 /\
    signature_prefix Glob.mem sigu0 sig0 mode2_sigbytes /\
    byte_frame_outside mem0 Glob.mem sigu0 mode2_sigbytes].
proof.
proc.
while
  (dstp = sigu0 /\ srcp = sig0 /\ len = mode2_sigbytes /\
   ApiKeyMemoryBridge.valid_region_int sigu0 mode2_sigbytes /\
   0 <= i <= mode2_sigbytes /\
   signature_prefix Glob.mem sigu0 srcp i /\
   byte_frame_outside mem0 Glob.mem sigu0 mode2_sigbytes).
+ auto => /> &hr hbase hlen hsum hi0 hile hpref hframe hguard.
  have hilt : i{hr} < mode2_sigbytes.
  + rewrite /mode2_sigbytes.
    exact hguard.
  split.
  + clear hpref hframe hbase hlen hsum.
    smt().
  split.
  + apply (signature_prefix_store_step
             Glob.mem{hr} sigu0 i{hr} sig0
             (BArray2948.get8 sig0
                (W64.to_uint (W64.of_int i{hr})))); first exact hi0.
    * rewrite W64.of_uintK /=.
      - trivial.
      - rewrite /mode2_sigbytes in hilt; smt().
    * exact hpref.
  + apply (byte_frame_outside_store_step
             mem0 Glob.mem{hr} sigu0 mode2_sigbytes i{hr}
             (BArray2948.get8 sig0
                (W64.to_uint (W64.of_int i{hr})))); first smt().
    exact hframe.
auto => />.
move=> &hr hbase hsum.
split; first smt().
rewrite /byte_frame_outside; trivial.
move=> mem i hdone hi0 hile hsig hframe.
have hi_eq : i = mode2_sigbytes by smt().
rewrite -hi_eq.
exact hsig.
qed.

(* Frame-only form of the generated copy theorem.  Unlike the exact-copy
   theorem above it does not name the procedure-local source array, so it can
   be called after the full signing continuation has produced [sigp]. *)
lemma sign_output_copy_frames_outside
    (mem0 : global_mem_t) (sigu0 : int) :
  hoare [Sign._api_copy_2948_to_raw :
    Glob.mem = mem0 /\ dstp = sigu0 /\ len = mode2_sigbytes /\
    ApiKeyMemoryBridge.valid_region_int sigu0 mode2_sigbytes
    ==>
    res = sigu0 /\
    byte_frame_outside mem0 Glob.mem sigu0 mode2_sigbytes].
proof.
proc.
while
  (dstp = sigu0 /\ len = mode2_sigbytes /\
   ApiKeyMemoryBridge.valid_region_int sigu0 mode2_sigbytes /\
   0 <= i <= mode2_sigbytes /\
   byte_frame_outside mem0 Glob.mem sigu0 mode2_sigbytes).
+ auto => /> &hr hbase hlen hsum hi0 hile hframe hguard.
  split; first smt().
  apply (byte_frame_outside_store_step
           mem0 Glob.mem{hr} sigu0 mode2_sigbytes i{hr}
           (BArray2948.get8 srcp{hr}
              (W64.to_uint (W64.of_int i{hr})))); first smt().
  exact hframe.
auto => />.
qed.

lemma outside_frame_implies_stable_region
    (before after : global_mem_t)
    (write_base write_len base len : int) :
  byte_frame_outside before after write_base write_len =>
  ApiKeyMemoryBridge.disjoint_regions write_base write_len base len =>
  RawApiMuReachability.stable_region before after base len.
proof.
move=> hframe hdis.
rewrite /RawApiMuReachability.stable_region => i hi.
apply hframe.
move: hdis hi.
rewrite /ApiKeyMemoryBridge.disjoint_regions.
smt().
qed.

lemma stable_region_trans
    (before middle after : global_mem_t) (base len : int) :
  RawApiMuReachability.stable_region before middle base len =>
  RawApiMuReachability.stable_region middle after base len =>
  RawApiMuReachability.stable_region before after base len.
proof.
move=> hleft hright.
rewrite /RawApiMuReachability.stable_region => i hi.
rewrite (hright i hi).
exact (hleft i hi).
qed.

lemma sign_raw_trace_frames_reused_regions
    (mem0 : global_mem_t)
    (sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0 : int) :
  hoare [SignTrace.run :
    Glob.mem = mem0 /\ sigu = sigu0 /\ siglenu = siglenu0 /\
    preu = preu0 /\ prelen = prelen0 /\ mu = msgaddr0 /\ mlen = mlen0 /\
    ApiKeyMemoryBridge.valid_region_int sigu0 mode2_sigbytes /\
    output_disjoint_from_reused
      sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0
    ==>
    res = W64.zero /\
    reused_regions_stable
      mem0 Glob.mem vku0 sku0 preu0 prelen0 msgaddr0 mlen0 /\
    loadW64 Glob.mem siglenu0 = W64.of_int mode2_sigbytes].
proof.
proc.
seq 28 :
  (Glob.mem = mem0 /\ sigu = sigu0 /\ siglenu = siglenu0 /\
   ApiKeyMemoryBridge.valid_region_int sigu0 mode2_sigbytes /\
   output_disjoint_from_reused
     sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0).
+ wp.
  call (_ : true); first by auto.
  wp.
  call (_ : true); first by auto.
  call (_ : true); first by auto.
  auto.
+ wp.
  call (sign_output_copy_frames_outside mem0 sigu0).
  auto => />.
  move=> hsigu hlen hsum hsvk hssk hspre hsmsg
          hlvk hlsk hlpre hlmsg hsiglen heq mem hframe.
  split.
  + rewrite /reused_regions_stable.
    split.
    * apply (stable_region_trans mem0 mem
               (storeW64 mem siglenu0 (W64.of_int 1474))
               vku0 mode2_vkbytes).
      - apply (outside_frame_implies_stable_region
                 mem0 mem sigu0 mode2_sigbytes vku0 mode2_vkbytes);
          assumption.
      - apply stable_region_storeW64_disjoint; exact hlvk.
    split.
    * apply (stable_region_trans mem0 mem
               (storeW64 mem siglenu0 (W64.of_int 1474))
               sku0 mode2_skbytes).
      - apply (outside_frame_implies_stable_region
                 mem0 mem sigu0 mode2_sigbytes sku0 mode2_skbytes);
          assumption.
      - apply stable_region_storeW64_disjoint; exact hlsk.
    split.
    * apply (stable_region_trans mem0 mem
               (storeW64 mem siglenu0 (W64.of_int 1474))
               preu0 prelen0).
      - apply (outside_frame_implies_stable_region
                 mem0 mem sigu0 mode2_sigbytes preu0 prelen0);
          assumption.
      - apply stable_region_storeW64_disjoint; exact hlpre.
    * apply (stable_region_trans mem0 mem
               (storeW64 mem siglenu0 (W64.of_int 1474))
               msgaddr0 mlen0).
      - apply (outside_frame_implies_stable_region
                 mem0 mem sigu0 mode2_sigbytes msgaddr0 mlen0);
          assumption.
      - apply stable_region_storeW64_disjoint; exact hlmsg.
  + rewrite -heq.
    apply loadW64_storeW64_same.
qed.

(* The generated raw ABI and [SignRawApiMuTrace.run] have identical result
   and memory semantics.  Hence the frame proved above is a property of the
   actual ABI caller, not merely of the ghost-observing trace. *)
lemma sign_raw_api_frames_reused_regions
    (mem0 : global_mem_t)
    (sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0 : int) :
  hoare [Sign.cryptolab_haetae_mode2_signature_internal :
    Glob.mem = mem0 /\ sigu = sigu0 /\ siglenu = siglenu0 /\
    preu = preu0 /\ prelen = prelen0 /\ mu = msgaddr0 /\ mlen = mlen0 /\
    ApiKeyMemoryBridge.valid_region_int sigu0 mode2_sigbytes /\
    output_disjoint_from_reused
      sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0
    ==>
    res = W64.zero /\
    reused_regions_stable
      mem0 Glob.mem vku0 sku0 preu0 prelen0 msgaddr0 mlen0 /\
    loadW64 Glob.mem siglenu0 = W64.of_int mode2_sigbytes].
proof.
conseq RawApiCallerMuTrace.sign_raw_api_exact_mu_trace
  (sign_raw_trace_frames_reused_regions
     mem0 sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0) => //=.
move=> &1 hpre.
exists Glob.mem{1}
  (sigu{1}, siglenu{1}, mu{1}, mlen{1},
   preu{1}, prelen{1}, rndu{1}, sku{1}) => />.
qed.

lemma sign_raw_api_preserves_external_key_prefix
    (mem0 : global_mem_t)
    (sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0 : int) :
  hoare [Sign.cryptolab_haetae_mode2_signature_internal :
    Glob.mem = mem0 /\ sigu = sigu0 /\ siglenu = siglenu0 /\
    preu = preu0 /\ prelen = prelen0 /\ mu = msgaddr0 /\ mlen = mlen0 /\
    ApiKeyMemoryBridge.valid_region_int sigu0 mode2_sigbytes /\
    output_disjoint_from_reused
      sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0 /\
    RawApiMuReachability.external_key_prefix_match mem0 sku0 vku0
    ==>
    res = W64.zero /\
    RawApiMuReachability.external_key_prefix_match Glob.mem sku0 vku0].
proof.
conseq (sign_raw_api_frames_reused_regions
          mem0 sigu0 siglenu0 vku0 sku0 preu0 prelen0 msgaddr0 mlen0)
  => //=.
move=> &hr hpre result mem [hz [hstable hlen]].
split; first exact hz.
have hprefix :
    RawApiMuReachability.external_key_prefix_match mem0 sku0 vku0
  by move: hpre => />.
rewrite /reused_regions_stable in hstable.
case: hstable => hvk [hsk [hpre_stable hmsg_stable]].
have hsk_prefix :
    RawApiMuReachability.stable_region
      mem0 mem sku0 RawApiMuReachability.mode2_vkbytes.
+ rewrite /RawApiMuReachability.stable_region => i hi.
  apply hsk.
  move: hi.
  rewrite /RawApiMuReachability.mode2_vkbytes /mode2_skbytes.
  smt().
apply (RawApiMuReachability.external_prefix_survives_stability
         mem0 mem sku0 vku0 hprefix hsk_prefix hvk).
qed.

end RawApiSignOutputFrame.
