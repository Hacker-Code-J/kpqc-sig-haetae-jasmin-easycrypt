require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignMuHashTarget VerifyMuHashTarget KeygenShakeStreamSpec.

theory ExtractedMuHashPrefix.

module Sign = SignMuHashTarget.M.
module Verify = VerifyMuHashTarget.M.

op mode2_vkbytes : int = 992.

op mu32_prefix (mu64 : BArray64.t) (mu32 : BArray32.t) : bool =
  forall i, 0 <= i < 32 =>
    BArray64.get8 mu64 i = BArray32.get8 mu32 i.

op sk_memory_prefix
    (sk : BArray2752.t) (mem : global_mem_t) (base : W64.t) : bool =
  forall i, 0 <= i < mode2_vkbytes =>
    BArray2752.get8 sk i = loadW8 mem (W64.to_uint base + i).

op state_prefix64
    (out : BArray64.t) (state : BArray200.t) (count : int) : bool =
  forall i, 0 <= i < count =>
    BArray64.get8 out i = BArray200.get8 state i.

op state_prefix32
    (out : BArray32.t) (state : BArray200.t) (count : int) : bool =
  forall i, 0 <= i < count =>
    BArray32.get8 out i = BArray200.get8 state i.

op dropped_word
    (state : BArray200.t) (lane count : int) (word : W64.t) : bool =
  word = KeygenShakeStreamSpec.drop_bytes
    (BArray200.get64 state lane) count.

lemma state_prefix64_zero out state :
  state_prefix64 out state 0.
proof. by rewrite /state_prefix64 => i /#. qed.

lemma state_prefix32_zero out state :
  state_prefix32 out state 0.
proof. by rewrite /state_prefix32 => i /#. qed.

lemma state_prefix64_set_word out state off :
  0 <= off =>
  off + 8 <= 64 =>
  state_prefix64 out state off =>
  state_prefix64
    (BArray64.set64d out off (BArray200.get64d state off))
    state (off + 8).
proof.
move=> hoff hcap hprefix.
rewrite /state_prefix64 in hprefix.
rewrite /state_prefix64 => i hi.
rewrite BArray64.get8_set64dE.
case: (off <= i < off + 8 /\ 0 <= i && i < BArray64.size) => hinside /=.
+ rewrite BArray200.get64d_byte 1:/#.
  rewrite hinside /=.
  have -> : off + (i - off) = i by smt().
  trivial.
+ rewrite hinside /=.
  have hiold : 0 <= i < off by smt().
  exact (hprefix i hiold).
qed.

lemma state_prefix32_set_next out state count :
  0 <= count < 32 =>
  state_prefix32 out state count =>
  state_prefix32
    (BArray32.set8 out count (BArray200.get8 state count))
    state (count + 1).
proof.
move=> hcount hprefix.
rewrite /state_prefix32 in hprefix.
rewrite /state_prefix32 => i hi.
rewrite BArray32.get_setE 1:/#.
case: (i = count) => [-> // | hne].
have hiold : 0 <= i < count by smt().
exact (hprefix i hiold).
qed.

lemma sign_verify_keccak_init_from_same_state :
  equiv [Sign._keccak_init_state ~ Verify._keccak_init_state :
    ={sp_0}
    ==>
    ={res}].
proof.
proc.
sim.
qed.

lemma sign_verify_keccakf1600_from_same_state :
  equiv [Sign._keccakf1600 ~ Verify._keccakf1600 :
    ={sp_0}
    ==>
    ={res}].
proof.
proc.
inline Sign.__keccakf1600_statepermute Verify.__keccakf1600_statepermute.
sim.
qed.

lemma sign_verify_finalize_from_same_state :
  equiv [Sign._sf_shake256_finalize ~ Verify.__poly_challenge_shake256_finalize :
    ={sp_0, statep}
    ==>
    ={res}].
proof.
proc.
auto => />.
qed.

lemma sign_verify_absorb_addr_from_same_state :
  equiv [Sign._sf_shake256_absorb_addr ~ Verify.__verify_shake256_absorb_raw :
    ={Glob.mem, sp_0, statep, inp, inlen}
    ==>
    ={res}].
proof.
proc.
wp.
while (={Glob.mem, sp_0, statep, inp, inlen, pos}).
+ sp.
  if.
  + auto.
  + wp.
    call (sign_verify_keccakf1600_from_same_state).
    auto.
  + auto.
wp.
skip => />.
qed.

lemma sign_sk_verify_vk_absorb_mode2
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [Sign._sf_shake256_absorb_sk ~ Verify.__verify_shake256_absorb_raw :
    ={sp_0, statep} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    inp{2} = base /\
    inlen{1} = W64.of_int mode2_vkbytes /\
    inlen{2} = W64.of_int mode2_vkbytes /\
    sk_memory_prefix sk0 mem0 base
    ==>
    ={res}].
proof.
move=> hbase.
proc.
wp.
while
  (sp_0{1} = sp_0{2} /\
   statep{1} = statep{2} /\
   pos{1} = pos{2} /\
   skp{1} = sk0 /\
   Glob.mem{2} = mem0 /\
   inlen{1} = W64.of_int mode2_vkbytes /\
   0 <= W64.to_uint i{1} <= mode2_vkbytes /\
   W64.to_uint inlen{2} = mode2_vkbytes - W64.to_uint i{1} /\
   W64.to_uint inp{2} = W64.to_uint base + W64.to_uint i{1} /\
   sk_memory_prefix sk0 mem0 base).
+ sp 11 12.
  if.
  + auto.
  + wp.
    call (sign_verify_keccakf1600_from_same_state).
    auto => /> &1 &2 hsp hst hpos hsk hmem hlen hi0 hi992 hrem hinp hprefix hguard.
    have hi : 0 <= W64.to_uint hmem < mode2_vkbytes.
    + move: hprefix.
      rewrite W64.ultE W64.of_uintK /= /mode2_vkbytes.
      smt(W64.to_uint_cmp).
    have hbyte := hinp (W64.to_uint hmem) hi.
    rewrite -hrem in hbyte.
    have hi_succ :
        W64.to_uint (hmem + W64.one) = W64.to_uint hmem + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hinp_succ :
        W64.to_uint (hpos + W64.one) = W64.to_uint hpos + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt().
    have hrem_pos : 1 <= W64.to_uint hsp by smt().
    have hrem_succ :
        W64.to_uint (hsp - W64.one) = W64.to_uint hsp - 1.
    + rewrite W64.to_uintB 1:/# W64.to_uint1.
      trivial.
    rewrite /protect_64 hbyte hi_succ hinp_succ hrem_succ.
    smt(W64.to_uint_cmp).
  + auto => /> &1 &2 hsp hst hpos hsk hmem hlen hi0 hi992 hrem hinp hprefix hguard.
    have hi : 0 <= W64.to_uint hmem < mode2_vkbytes.
    + move: hprefix.
      rewrite W64.ultE W64.of_uintK /= /mode2_vkbytes.
      smt(W64.to_uint_cmp).
    have hbyte := hinp (W64.to_uint hmem) hi.
    rewrite -hrem in hbyte.
    have hi_succ :
        W64.to_uint (hmem + W64.one) = W64.to_uint hmem + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hinp_succ :
        W64.to_uint (hpos + W64.one) = W64.to_uint hpos + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt().
    have hrem_pos : 1 <= W64.to_uint hsp by smt().
    have hrem_succ :
        W64.to_uint (hsp - W64.one) = W64.to_uint hsp - 1.
    + rewrite W64.to_uintB 1:/# W64.to_uint1.
      trivial.
    rewrite hbyte hi_succ hinp_succ hrem_succ.
    smt(W64.to_uint_cmp).
wp.
skip => />.
rewrite /protect_64 /mode2_vkbytes /=.
smt(W64.ultE W64.to_uint_cmp).
qed.

module SignFinalSqueeze = {
  proc run (outp : BArray64.t, sp_0 : BArray200.t) : BArray64.t = {
    sp_0 <@ Sign._keccakf1600(sp_0);
    (outp, sp_0) <@ Sign._sf_shake256_squeeze64(outp, sp_0);
    return outp;
  }
}.

module VerifyFinalSqueeze = {
  proc run (outp : BArray32.t, sp_0 : BArray200.t) : BArray32.t = {
    (outp, sp_0) <@ Verify.__poly_challenge_squeeze256_32(outp, sp_0);
    return outp;
  }
}.

lemma sign_verify_final_squeeze_mu32_prefix :
  equiv [SignFinalSqueeze.run ~ VerifyFinalSqueeze.run :
    ={sp_0}
    ==>
    mu32_prefix res{1} res{2}].
proof.
proc.
inline Sign._sf_shake256_squeeze64
       Verify.__poly_challenge_squeeze256_32.
seq 1 4 :
  (sp_0{1} = sp_00{2} /\ idx{2} = W64.zero).
+ sp 0 3.
  call (sign_verify_keccakf1600_from_same_state).
  auto.
sp 6 3.
wp.
seq 0 1 :
  (sp_00{1} = sp_00{2} /\
   i{1} = W64.zero /\
   state_prefix32 outp0{2} sp_00{2} 32).
+
while{2}
  (sp_00{1} = sp_00{2} /\
   state_prefix32 outp0{2} sp_00{2} (W64.to_uint i{2}) /\
   W64.to_uint idx{2} = W64.to_uint i{2} /\
   0 <= W64.to_uint i{2} <= 32 /\
   W64.to_uint i{2} %% 8 = 0)
  (32 - W64.to_uint i{2}).
+ move=> &1 z.
  sp 4.
  wp.
  while
    (sp_00{1} = sp_00 /\
     state_prefix32 outp0 sp_00
       (W64.to_uint i + W64.to_uint j) /\
     W64.to_uint idx =
       W64.to_uint i + W64.to_uint j /\
     W64.to_uint lane = W64.to_uint i %/ 8 /\
     dropped_word sp_00 (W64.to_uint lane) (W64.to_uint j) t /\
     0 <= W64.to_uint i < 32 /\
     W64.to_uint i %% 8 = 0 /\
     0 <= W64.to_uint j <= 8)
    (8 - W64.to_uint j).
  + move=> z0.
    auto => /> &hr hprefix hidx hlane hdrop
                       hi0 hi32 himod hj0 hj8 hguard.
    have hjlt : W64.to_uint j{hr} < 8.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /=.
      trivial.
    have hj_next :
        W64.to_uint (j{hr} + W64.one) = W64.to_uint j{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hidx_next :
        W64.to_uint (idx{hr} + W64.one) =
        W64.to_uint idx{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hlane25 : 0 <= W64.to_uint lane{hr} < 25 by smt().
    have hbytepos : 0 <= W64.to_uint j{hr} < 8 by smt().
    have hbyte :
        truncateu8 t{hr} =
        BArray200.get8 sp_00{1}
          (W64.to_uint i{hr} + W64.to_uint j{hr}).
    + rewrite /dropped_word in hdrop.
      rewrite hdrop.
      have hrl := KeygenShakeStreamSpec.rate_lane_byte_get8
        sp_00{1} (W64.to_uint lane{hr}) (W64.to_uint j{hr})
        hlane25 hbytepos.
      rewrite /KeygenShakeStreamSpec.rate_lane_byte in hrl.
      rewrite hrl.
      congr; smt(divz_eq).
    have hcount :
        0 <= W64.to_uint i{hr} + W64.to_uint j{hr} < 32 by smt().
    have hpnext :
        state_prefix32
          (BArray32.set8 outp0{hr} (W64.to_uint idx{hr})
             (truncateu8 t{hr}))
          sp_00{1}
          (W64.to_uint i{hr} + W64.to_uint j{hr} + 1).
    + rewrite hidx hbyte.
      apply state_prefix32_set_next.
      * exact hcount.
      * exact hprefix.
    have ht_next :
        t{hr} `>>` W8.of_int 8 =
        KeygenShakeStreamSpec.drop_bytes
          (BArray200.get64 sp_00{1} (W64.to_uint lane{hr}))
          (W64.to_uint j{hr} + 1).
    + rewrite /dropped_word in hdrop.
      rewrite hdrop KeygenShakeStreamSpec.drop_bytes_succ 1:/#.
      trivial.
    do split.
    + trivial.
    + rewrite hj_next.
      have -> : W64.to_uint i{hr} + (W64.to_uint j{hr} + 1) =
          W64.to_uint i{hr} + W64.to_uint j{hr} + 1 by ring.
      exact hpnext.
    + rewrite hidx_next hj_next hidx.
      ring.
    + smt(divz_eq).
    + rewrite /dropped_word hj_next.
    + smt().
    + smt().
  smt().
  auto => /> &hr hprefix hidx hi0 hi32 himod hguard.
  split.
  + split.
    + rewrite W64.shr_div_le 1:/# /=.
    split.
    + rewrite /dropped_word KeygenShakeStreamSpec.drop_bytes0.
      rewrite W64.shr_div_le 1:/# /=.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    exact hguard.
  move=> idx0 j0 outp0_0 t0.
  split.
  + move=> hp hidx0 hlane hdrop hi32' hj0 hj8 hvariant.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  move=> hjdone hp hidx0 hlane hdrop hi32' hj0 hj8.
  rewrite W64.ultE W64.of_uintK /= in hjdone.
  have hj : W64.to_uint j0 = 8 by smt(W64.to_uint_cmp).
  have hjword : j0 = W64.of_int 8.
  + by rewrite -(W64.to_uintK' j0) hj.
  subst j0.
  rewrite W64.to_uintD_small 1:/# /=.
  do split.
  + exact hp.
  + rewrite hidx0.
    ring.
  + smt(W64.to_uint_cmp).
  + smt(W64.to_uint_cmp).
  smt().
smt().
+ auto => />.
  move=> &2 outp0_R.
  split.
  + exact (state_prefix32_zero
      (SLH64.protect_ptr outp0_R W64.zero) sp_00{2}).
  move=> i_R idx_R outp0_R0.
  split.
  + move=> hsp hprefix hidx hi0 hi32 himod hvariant.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  move=> hdone hsp hprefix hidx hi0 hi32 himod.
  rewrite W64.ultE W64.of_uintK /= in hdone.
  have hiR : W64.to_uint i_R = 32 by smt(W64.to_uint_cmp).
  by rewrite -hiR.
+
while{1}
  (sp_00{1} = sp_00{2} /\
   state_prefix64 outp0{1} sp_00{1} (W64.to_uint i{1}) /\
   0 <= W64.to_uint i{1} <= 64 /\
   W64.to_uint i{1} %% 8 = 0)
  (64 - W64.to_uint i{1}).
+ auto => /> &hr hprefix hi0 hi64 himod hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  have hi8 := KeygenShakeStreamSpec.div8_split
    (W64.to_uint i{hr}) hi0 himod.
  have hinext :
      W64.to_uint (i{hr} + W64.of_int 8) = W64.to_uint i{hr} + 8.
  + rewrite W64.to_uintD_small 1:/# /=.
    trivial.
  have haddr :
      8 * W64.to_uint (i{hr} `>>` W8.of_int 3) = W64.to_uint i{hr}.
  + rewrite W64.shr_div_le 1:/# /=.
    smt().
  have hcap : W64.to_uint i{hr} + 8 <= 64 by smt().
  have hpnext := state_prefix64_set_word
    outp0{hr} sp_00{m} (W64.to_uint i{hr}) hi0 hcap hprefix.
  rewrite hinext haddr.
  do split.
  + exact hpnext.
  + smt().
  + smt().
  smt().
smt().
auto => />.
move=> &1 &2 hprefixR.
split.
+ trivial.
smt().
move=> i_L outp0_L.
split.
+ move=> hprefixL hi0 hi64 himod hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
+ move=> hdone hprefixL hi0 hi64 himod.
rewrite W64.ultE W64.of_uintK /= in hdone.
have hiL : W64.to_uint i_L = 64 by smt(W64.to_uint_cmp).
rewrite /mu32_prefix => k hk.
have hleft := hprefixL k _.
+ rewrite hiL.
  smt().
have hright := hprefixR k hk.
by rewrite hleft hright.
qed.

module SignRawMuCore = {
  proc run (mup : BArray64.t, skp : BArray2752.t,
            preaddr : W64.t, prelen : W64.t,
            maddr : W64.t, mlen : W64.t,
            sp_0 : BArray200.t, statep : BArray16.t) : BArray64.t = {
    (sp_0, statep) <@ Sign._sf_shake256_absorb_sk
      (sp_0, statep, skp, W64.of_int mode2_vkbytes);
    (sp_0, statep) <@ Sign._sf_shake256_absorb_addr
      (sp_0, statep, preaddr, prelen);
    (sp_0, statep) <@ Sign._sf_shake256_absorb_addr
      (sp_0, statep, maddr, mlen);
    sp_0 <@ Sign._sf_shake256_finalize(sp_0, statep);
    mup <@ SignFinalSqueeze.run(mup, sp_0);
    return mup;
  }
}.

module VerifyRawMuCore = {
  proc run (mup : BArray32.t, vkp : W64.t,
            prep : W64.t, prelen : W64.t,
            mp : W64.t, mlen : W64.t,
            sp_0 : BArray200.t, statep : BArray16.t) : BArray32.t = {
    (sp_0, statep) <@ Verify.__verify_shake256_absorb_raw
      (sp_0, statep, vkp, W64.of_int mode2_vkbytes);
    (sp_0, statep) <@ Verify.__verify_shake256_absorb_raw
      (sp_0, statep, prep, prelen);
    (sp_0, statep) <@ Verify.__verify_shake256_absorb_raw
      (sp_0, statep, mp, mlen);
    sp_0 <@ Verify.__poly_challenge_shake256_finalize(sp_0, statep);
    mup <@ VerifyFinalSqueeze.run(mup, sp_0);
    return mup;
  }
}.

lemma sign_verify_raw_mu_core_prefix
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [SignRawMuCore.run ~ VerifyRawMuCore.run :
    ={Glob.mem, sp_0, statep} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    vkp{2} = base /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    sk_memory_prefix sk0 mem0 base
    ==>
    mu32_prefix res{1} res{2}].
proof.
move=> hbase.
proc.
call sign_verify_final_squeeze_mu32_prefix.
call sign_verify_finalize_from_same_state.
call sign_verify_absorb_addr_from_same_state.
call sign_verify_absorb_addr_from_same_state.
call (sign_sk_verify_vk_absorb_mode2 sk0 mem0 base hbase).
auto.
qed.

module SignRawMuTop = {
  proc run (mup : BArray64.t, skp : BArray2752.t,
            preaddr : W64.t, prelen : W64.t,
            maddr : W64.t, mlen : W64.t) : BArray64.t = {
    var state : BArray200.t;
    var sp_0 : BArray200.t;
    var st : BArray16.t;
    var statep : BArray16.t;
    sp_0 <- witness;
    st <- witness;
    state <- witness;
    statep <- witness;
    sp_0 <- state;
    statep <- st;
    statep <- BArray16.set64 statep 0 W64.zero;
    statep <- BArray16.set64 statep 1 (W64.of_int 136);
    sp_0 <@ Sign._keccak_init_state(sp_0);
    mup <@ SignRawMuCore.run
      (mup, skp, preaddr, prelen, maddr, mlen, sp_0, statep);
    return mup;
  }
}.

module VerifyRawMuTop = {
  proc run (mup : BArray32.t, vkp : W64.t,
            prep : W64.t, prelen : W64.t,
            mp : W64.t, mlen : W64.t) : BArray32.t = {
    var state : BArray200.t;
    var sp_0 : BArray200.t;
    var st : BArray16.t;
    var statep : BArray16.t;
    sp_0 <- witness;
    st <- witness;
    state <- witness;
    statep <- witness;
    sp_0 <- state;
    statep <- st;
    statep <- BArray16.set64 statep 0 W64.zero;
    statep <- BArray16.set64 statep 1 (W64.of_int 136);
    sp_0 <@ Verify._keccak_init_state(sp_0);
    mup <@ VerifyRawMuCore.run
      (mup, vkp, prep, prelen, mp, mlen, sp_0, statep);
    return mup;
  }
}.

lemma sign_verify_raw_mu_top_wrappers_prefix
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [SignRawMuTop.run ~ VerifyRawMuTop.run :
    ={Glob.mem} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    vkp{2} = base /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    sk_memory_prefix sk0 mem0 base
    ==>
    mu32_prefix res{1} res{2}].
proof.
move=> hbase.
proc.
call (sign_verify_raw_mu_core_prefix sk0 mem0 base hbase).
call sign_verify_keccak_init_from_same_state.
auto.
qed.

end ExtractedMuHashPrefix.
