require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import BArray64 BArray200 BArray8192 Array25 ApiTarget
               SHAKEBlockSpec SHAKEBlockCorrectness SHAKEStreamSpec.
import SLH64.

theory SHAKESeedInitCorrectness.
module Signer = ApiTarget.M(ApiTarget.Syscall).
import SHAKEStreamSpec SHAKEBlockSpec.Word.

lemma keccak_init_zero :
  hoare [Signer._keccak_init_state : true ==>
    forall lane, 0 <= lane < 25 => BArray200.get64 res lane = W64.zero].
proof.
  proc.
  while ((forall lane, 0 <= lane < W64.to_uint i =>
      BArray200.get64 sp_0 lane = W64.zero) /\
    0 <= W64.to_uint i <= 25).
  + auto => /> &hr hprefix hlo hhi hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    split.
    + move=> lane hlane0 hlane1.
      rewrite BArray200.get_set64E 1:/# 1:/#.
      case (lane = W64.to_uint i{hr}) => [-> | hne]; first trivial.
      have -> /= : !(W64.to_uint i{hr} = lane) by smt().
      apply hprefix.
      rewrite W64.to_uintD_small 1:/# W64.to_uint1 in hlane1.
      smt().
    rewrite W64.to_uintD_small 1:/#.
    smt(W64.to_uint_cmp).
  auto => /> &hr.
  split; first by move=> lane hlo hlt; smt().
  move=> i0 state hdone hp hi0 hi25 lane hlo hlt.
  apply (hp lane).
  rewrite W64.ultE W64.of_uintK /= in hdone.
  smt().
qed.

lemma zero_state_seed_prefix (state : BArray200.t) (seed : BArray64.t) :
  (forall lane, 0 <= lane < 25 => BArray200.get64 state lane = W64.zero) =>
  state = shake_seed_prefix seed 0.
proof.
  move=> hz; apply BArray200.ext_eq => i hi.
  have hq : 0 <= i %/ 8 < 25 by smt(divz_cmp).
  rewrite (shake_state_byte state i hi) (state_of_barray_get state (i %/ 8) hq).
  rewrite (hz (i %/ 8) hq) W8u8.get_zero.
  by rewrite /shake_seed_prefix BArray200.initiE 1:hi /=; smt().
qed.

lemma seed_init_correct (seed0 : BArray64.t) (nonce0 : W64.t) :
  hoare [Signer._sf_shake256_init_seed64 : seedp = seed0 /\ nonce = nonce0 ==>
    res = shake_seed_state seed0 nonce0].
proof.
  proc; wp.
  while (0 <= k <= 2 /\ pos = W64.of_int (64 + k) /\
    n = SHAKEBlockSpec.drop_bytes nonce0 k /\
    sp_0 = shake_nonce_prefix seed0 nonce0 k).
  + auto => /> &hr hk0 hk2 hguard.
    have hstep := shake_nonce_prefix_step seed0 nonce0 k{hr} _; first smt().
    rewrite /shake_absorb_byte in hstep.
    rewrite SHAKEBlockSpec.drop_bytes_succ 1:/#.
    have hp : W64.of_int (64 + k{hr}) + W64.one =
      W64.of_int (64 + (k{hr} + 1)) by rewrite -W64.of_intD; congr; ring.
    smt().
  wp.
  while (seedp = seed0 /\ nonce = nonce0 /\ n = nonce0 /\
    0 <= W64.to_uint pos <= 64 /\
    sp_0 = shake_seed_prefix seed0 (W64.to_uint pos)).
  + auto => /> &hr hp0 hp64 hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    have hn : W64.to_uint (pos{hr} + W64.one) = W64.to_uint pos{hr} + 1 by
      rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    have hstep := shake_seed_prefix_step seed0 (W64.to_uint pos{hr}) _; first smt().
    rewrite W64.to_uintK /shake_absorb_byte in hstep.
    rewrite hn.
    smt().
  wp; call keccak_init_zero.
  auto => />.
  move=> state hzero.
  split.
  + exact (zero_state_seed_prefix state seed0 hzero).
  move=> pos hdone hp0 hp64.
  have hp : W64.to_uint pos = 64 by
    move: hdone; rewrite W64.ultE W64.of_uintK /=; smt().
  have hpword : pos = W64.of_int 64 by rewrite -hp W64.to_uintK.
  split.
  + by rewrite hp hpword shake_nonce_prefix0 SHAKEBlockSpec.drop_bytes0.
  move=> k hkdone hk0 hk2.
  have hk : k = 2 by smt().
  rewrite hk.
  have hpad := shake_pad_nonce_prefix seed0 nonce0.
  rewrite /shake_pad /= in hpad.
  exact hpad.
qed.

lemma keccak_init_ll : islossless Signer._keccak_init_state.
proof.
  proc.
  while (W64.to_uint i <= 25) (25 - W64.to_uint i).
  + move=> z; auto => /> &hr hi hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    smt().
  auto => /> i hi hv; rewrite W64.ultE W64.of_uintK /=; smt(W64.to_uint_cmp).
qed.

lemma seed_init_ll : islossless Signer._sf_shake256_init_seed64.
proof.
  proc; wp.
  while (0 <= k <= 2) (2 - k).
  + by move=> z; auto => />; smt().
  wp.
  while (W64.to_uint pos <= 64) (64 - W64.to_uint pos).
  + move=> z; auto => /> &hr hp hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  wp; call keccak_init_ll.
  auto => />; smt(W64.to_uint_cmp W64.ultE W64.of_uintK).
qed.

lemma seed_init_total (seed0 : BArray64.t) (nonce0 : W64.t) :
  phoare [Signer._sf_shake256_init_seed64 : seedp = seed0 /\ nonce = nonce0 ==>
    res = shake_seed_state seed0 nonce0] = 1%r.
proof. by conseq seed_init_ll (seed_init_correct seed0 nonce0). qed.

lemma seed_init_words_correct (seed0 : BArray64.t) (nonce0 : W64.t) :
  hoare [Signer._sf_shake256_init_seed64 : seedp = seed0 /\ nonce = nonce0 ==>
    word_state_of_barray res = shake_initial_words seed0 nonce0].
proof. by conseq (seed_init_correct seed0 nonce0) => />; rewrite /shake_initial_words. qed.

lemma shake_block_stream_correct
    (initial : word_state) (block : int) (out0 : BArray8192.t)
    (outoff0 : W64.t) (state0 : BArray200.t) :
  hoare [Signer.__sample_full_squeeze256 :
    outp = out0 /\ outoff = outoff0 /\ sp_0 = state0 /\
    0 <= block /\ word_state_of_barray state0 = shake_iterate initial block /\
    0 <= W64.to_uint outoff0 <= 8056 ==>
    (forall j, 0 <= j < 136 => BArray8192.get8 res.`1 (W64.to_uint outoff0 + j) =
      shake_stream_byte initial (136 * block + j)) /\
    SHAKEBlockSpec.rate_block_frame out0 res.`1 (W64.to_uint outoff0) 136 /\
    word_state_of_barray res.`2 = shake_iterate initial (block + 1)].
proof.
  conseq (SHAKEBlockCorrectness.squeeze256_word_correct out0 outoff0 state0) => />.
  + by move=> &hr hb hs ho0 ho; rewrite /BArray8192.size; smt().
  move=> &hr hb hs ho0 ho result hbytes hframe hword.
  have hnext : word_state_of_barray result.`2 = shake_iterate initial (block + 1).
  + by rewrite shake_iterateS 1:hb -hs; exact hword.
  split; last exact hnext.
  move=> j hj0 hj136.
  have hj : 0 <= j < 136 by smt().
  have h200 : 0 <= j < 200 by smt().
  rewrite (hbytes j hj) (shake_state_byte result.`2 j h200) hnext.
  by rewrite (shake_stream_block_byte initial block j hb hj).
qed.

lemma shake_block_stream_total
    (initial : word_state) (block : int) (out0 : BArray8192.t)
    (outoff0 : W64.t) (state0 : BArray200.t) :
  phoare [Signer.__sample_full_squeeze256 :
    outp = out0 /\ outoff = outoff0 /\ sp_0 = state0 /\
    0 <= block /\ word_state_of_barray state0 = shake_iterate initial block /\
    0 <= W64.to_uint outoff0 <= 8056 ==>
    (forall j, 0 <= j < 136 => BArray8192.get8 res.`1 (W64.to_uint outoff0 + j) =
      shake_stream_byte initial (136 * block + j)) /\
    SHAKEBlockSpec.rate_block_frame out0 res.`1 (W64.to_uint outoff0) 136 /\
    word_state_of_barray res.`2 = shake_iterate initial (block + 1)] = 1%r.
proof.
  by conseq SHAKEBlockCorrectness.squeeze256_ll
    (shake_block_stream_correct initial block out0 outoff0 state0).
qed.

end SHAKESeedInitCorrectness.
