require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignMuHashTarget VerifyMuHashTarget.
require import ExtractedMuHashPrefix ExactMuTopControl.
require import RawApiMuReachability.

theory RegionLocalMuEquivalence.

module Sign = SignMuHashTarget.M.
module Verify = VerifyMuHashTarget.M.
module RawSign = RawSignApiTarget.M.
module RawVerify = RawVerifyApiTarget.M.
module SignCore = ExtractedMuHashPrefix.SignRawMuCore.
module VerifyCore = ExtractedMuHashPrefix.VerifyRawMuCore.
module SignTop = ExtractedMuHashPrefix.SignRawMuTop.
module VerifyTop = ExtractedMuHashPrefix.VerifyRawMuTop.

op mode2_vkbytes : int = ExtractedMuHashPrefix.mode2_vkbytes.

(* Byte equality only on the W64-addressed interval read by an absorb call. *)
op region_eq
    (mem1 mem2 : global_mem_t) (base len : W64.t) : bool =
  forall i, 0 <= i < W64.to_uint len =>
    loadW8 mem1 (W64.to_uint base + i) =
    loadW8 mem2 (W64.to_uint base + i).

op raw_mu_read_relation
    (sign_mem verify_mem : global_mem_t)
    (sign_sk : BArray2752.t) (vku preaddr prelen msgaddr mlen : W64.t) : bool =
  ExtractedMuHashPrefix.sk_memory_prefix sign_sk verify_mem vku /\
  region_eq sign_mem verify_mem preaddr prelen /\
  region_eq sign_mem verify_mem msgaddr mlen /\
  ExactMuTopControl.raw_prelen prelen /\
  ExactMuTopControl.valid_region preaddr prelen /\
  ExactMuTopControl.valid_region msgaddr mlen.

lemma region_eq_refl
    (mem : global_mem_t) (base len : W64.t) :
  region_eq mem mem base len.
proof.
rewrite /region_eq.
trivial.
qed.

lemma region_eq_head
    (mem1 mem2 : global_mem_t) (base len : W64.t) :
  len <> W64.zero =>
  region_eq mem1 mem2 base len =>
  loadW8 mem1 (W64.to_uint base) =
  loadW8 mem2 (W64.to_uint base).
proof.
move=> hlen hregion.
have hnonzero : W64.to_uint len <> 0.
+ rewrite -W64.to_uint0 -W64.to_uint_eq.
  exact hlen.
have hpos : 0 < W64.to_uint len by
  have := W64.to_uint_cmp len; smt().
have hbyte := hregion 0 _.
+ smt().
by rewrite !addr0 in hbyte.
qed.

lemma region_eq_tail
    (mem1 mem2 : global_mem_t) (base len : W64.t) :
  ExactMuTopControl.valid_region base len =>
  len <> W64.zero =>
  region_eq mem1 mem2 base len =>
  region_eq mem1 mem2
    (base + W64.of_int 1) (len - W64.of_int 1).
proof.
move=> hvalid hlen hregion.
have hnonzero : W64.to_uint len <> 0.
+ rewrite -W64.to_uint0 -W64.to_uint_eq.
  exact hlen.
have hpos : 1 <= W64.to_uint len by
  have := W64.to_uint_cmp len; smt().
have hule : W64.of_int 1 \ule len by
  rewrite W64.uleE W64.of_uintK /=; exact hpos.
have hlen_pred :
    W64.to_uint (len - W64.of_int 1) = W64.to_uint len - 1.
+ by rewrite W64.to_uintB 1:hule W64.of_uintK /=.
case: (W64.to_uint len = 1) => hunit.
+ have hlen_zero : W64.to_uint (len - W64.of_int 1) = 0 by smt().
  rewrite /region_eq hlen_zero.
  smt().
+ have hlen2 : 2 <= W64.to_uint len by smt().
have hbase_small : W64.to_uint base + 1 < W64.modulus.
+ move: hvalid.
  rewrite /ExactMuTopControl.valid_region.
  smt().
have hbase_succ :
    W64.to_uint (base + W64.of_int 1) = W64.to_uint base + 1.
+ by rewrite W64.to_uintD_small 1:hbase_small W64.of_uintK /=.
rewrite /region_eq hbase_succ hlen_pred => i hi.
have hbyte := hregion (i + 1) _.
+ smt().
by have -> : W64.to_uint base + 1 + i = W64.to_uint base + (i + 1) by ring.
qed.

lemma valid_region_tail (base len : W64.t) :
  ExactMuTopControl.valid_region base len =>
  len <> W64.zero =>
  ExactMuTopControl.valid_region
    (base + W64.of_int 1) (len - W64.of_int 1).
proof.
move=> hvalid hlen.
have hnonzero : W64.to_uint len <> 0.
+ rewrite -W64.to_uint0 -W64.to_uint_eq.
  exact hlen.
have hpos : 1 <= W64.to_uint len by
  have := W64.to_uint_cmp len; smt().
have hule : W64.of_int 1 \ule len by
  rewrite W64.uleE W64.of_uintK /=; exact hpos.
have hlen_pred :
    W64.to_uint (len - W64.of_int 1) = W64.to_uint len - 1.
+ by rewrite W64.to_uintB 1:hule W64.of_uintK /=.
case: (W64.to_uint len = 1) => hunit.
+ rewrite /ExactMuTopControl.valid_region.
  have hlen_zero : W64.to_uint (len - W64.of_int 1) = 0 by smt().
  rewrite hlen_zero.
  have hbound := W64.to_uint_cmp (base + W64.of_int 1).
  smt().
+ have hlen2 : 2 <= W64.to_uint len by smt().
have hbase_small : W64.to_uint base + 1 < W64.modulus.
+ move: hvalid.
  rewrite /ExactMuTopControl.valid_region.
  smt().
rewrite /ExactMuTopControl.valid_region.
rewrite W64.to_uintD_small 1:hbase_small W64.of_uintK /=.
rewrite hlen_pred.
move: hvalid.
rewrite /ExactMuTopControl.valid_region.
smt().
qed.

lemma sign_verify_absorb_addr_regionwise
    (mem1 mem2 : global_mem_t) :
  equiv [Sign._sf_shake256_absorb_addr ~
         Verify.__verify_shake256_absorb_raw :
    Glob.mem{1} = mem1 /\ Glob.mem{2} = mem2 /\
    ={sp_0, statep, inp, inlen} /\
    ExactMuTopControl.valid_region inp{1} inlen{1} /\
    region_eq mem1 mem2 inp{1} inlen{1}
    ==>
    ={res} /\ Glob.mem{1} = mem1 /\ Glob.mem{2} = mem2].
proof.
proc.
wp.
while
  (Glob.mem{1} = mem1 /\ Glob.mem{2} = mem2 /\
   ={sp_0, statep, inp, inlen, pos} /\
   ExactMuTopControl.valid_region inp{1} inlen{1} /\
   region_eq Glob.mem{1} Glob.mem{2} inp{1} inlen{1}).
+ sp.
  if.
  + auto.
  + wp.
    call (ExtractedMuHashPrefix.sign_verify_keccakf1600_from_same_state).
    auto => /> &1 &2 cur_len aux1 cur_inp aux2
                    hvalid_region hregion_eq hnz.
    have hbyte := region_eq_head Glob.mem{1} Glob.mem{2}
                    cur_inp cur_len hnz hregion_eq.
    have htail := region_eq_tail Glob.mem{1} Glob.mem{2}
                    cur_inp cur_len hvalid_region hnz hregion_eq.
    have hvalid_tail := valid_region_tail cur_inp cur_len
                          hvalid_region hnz.
    rewrite /protect_64 hbyte.
    trivial.
  + auto => /> &1 &2 cur_len aux1 cur_inp aux2
                  hvalid_region hregion_eq hnz.
    have hbyte := region_eq_head Glob.mem{1} Glob.mem{2}
                    cur_inp cur_len hnz hregion_eq.
    have htail := region_eq_tail Glob.mem{1} Glob.mem{2}
                    cur_inp cur_len hvalid_region hnz hregion_eq.
    have hvalid_tail := valid_region_tail cur_inp cur_len
                          hvalid_region hnz.
    rewrite hbyte.
    trivial.
wp.
skip => />.
qed.

(* The Sign-side SK absorber has no global-memory reads.  Consequently its
   memory need not equal the Verify-side memory that supplies the VK bytes. *)
lemma sign_absorb_sk_memory_independent :
  equiv [Sign._sf_shake256_absorb_sk ~ Sign._sf_shake256_absorb_sk :
    ={sp_0, statep, skp, inlen}
    ==>
    ={res}].
proof.
proc.
sim.
qed.

lemma sign_sk_verify_vk_absorb_mode2_regionwise
    (sk0 : BArray2752.t) (mem2 : global_mem_t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [Sign._sf_shake256_absorb_sk ~
         Verify.__verify_shake256_absorb_raw :
    Glob.mem{2} = mem2 /\
    ={sp_0, statep} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem2 /\
    inp{2} = base /\
    inlen{1} = W64.of_int mode2_vkbytes /\
    inlen{2} = W64.of_int mode2_vkbytes /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 mem2 base
    ==>
    ={res}].
proof.
move=> hbase.
transitivity Sign._sf_shake256_absorb_sk
  (={sp_0, statep, skp, inlen} ==> ={res})
  (={Glob.mem, sp_0, statep} /\
   skp{1} = sk0 /\ Glob.mem{2} = mem2 /\ inp{2} = base /\
   inlen{1} = W64.of_int mode2_vkbytes /\
   inlen{2} = W64.of_int mode2_vkbytes /\
   ExtractedMuHashPrefix.sk_memory_prefix sk0 mem2 base
   ==>
   ={res}).
+ move=> &1 &2 /> hsp hstate hsk hmem hinp.
  exists Glob.mem{2} (sp_0{1}, statep{1}, skp{1}, inlen{1}).
  auto.
+ move=> &1 &m &2 hleft hright.
  rewrite hleft.
  exact hright.
+ exact sign_absorb_sk_memory_independent.
+ rewrite /mode2_vkbytes in hbase.
  rewrite /mode2_vkbytes.
  conseq (ExtractedMuHashPrefix.sign_sk_verify_vk_absorb_mode2
           sk0 mem2 base hbase); auto.
qed.

lemma sign_verify_raw_mu_core_prefix_regionwise
    (sign_mem verify_mem : global_mem_t)
    (sk0 : BArray2752.t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [SignCore.run ~ VerifyCore.run :
    Glob.mem{1} = sign_mem /\ Glob.mem{2} = verify_mem /\
    ={sp_0, statep} /\
    skp{1} = sk0 /\ vkp{2} = base /\
    preaddr{1} = prep{2} /\ prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\ mlen{1} = mlen{2} /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 verify_mem base /\
    ExactMuTopControl.valid_region prep{2} prelen{2} /\
    ExactMuTopControl.valid_region mp{2} mlen{2} /\
    region_eq sign_mem verify_mem prep{2} prelen{2} /\
    region_eq sign_mem verify_mem mp{2} mlen{2}
    ==>
    ExtractedMuHashPrefix.mu32_prefix res{1} res{2}].
proof.
move=> hbase.
proc.
call ExtractedMuHashPrefix.sign_verify_final_squeeze_mu32_prefix.
call ExtractedMuHashPrefix.sign_verify_finalize_from_same_state.
call (sign_verify_absorb_addr_regionwise sign_mem verify_mem).
call (sign_verify_absorb_addr_regionwise sign_mem verify_mem).
call (sign_sk_verify_vk_absorb_mode2_regionwise
        sk0 verify_mem base hbase).
auto.
qed.

lemma sign_verify_raw_mu_top_wrappers_prefix_regionwise
    (sign_mem verify_mem : global_mem_t)
    (sk0 : BArray2752.t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [SignTop.run ~ VerifyTop.run :
    Glob.mem{1} = sign_mem /\ Glob.mem{2} = verify_mem /\
    skp{1} = sk0 /\ vkp{2} = base /\
    preaddr{1} = prep{2} /\ prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\ mlen{1} = mlen{2} /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 verify_mem base /\
    ExactMuTopControl.valid_region prep{2} prelen{2} /\
    ExactMuTopControl.valid_region mp{2} mlen{2} /\
    region_eq sign_mem verify_mem prep{2} prelen{2} /\
    region_eq sign_mem verify_mem mp{2} mlen{2}
    ==>
    ExtractedMuHashPrefix.mu32_prefix res{1} res{2}].
proof.
move=> hbase.
proc.
call (sign_verify_raw_mu_core_prefix_regionwise
        sign_mem verify_mem sk0 base hbase).
call ExtractedMuHashPrefix.sign_verify_keccak_init_from_same_state.
auto.
qed.

end RegionLocalMuEquivalence.
