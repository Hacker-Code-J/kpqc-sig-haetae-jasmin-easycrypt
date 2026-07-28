require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import
  KeygenSamplerCallersTarget
  KeygenSeedXofSpec KeygenShakeStreamSpec KeygenKeccak1600Spec
  HAETAE_FIPS202 HAETAE_Keccak1600
  TargetKeygenKeccak1600 TargetKeygenShakeStream.

theory TargetKeygenSeedXof.

op seed_zero_state : BArray200.t = BArray200.init_arr W8.zero.

lemma zero_lanes_seed_zero_state state :
  KeygenShakeStreamSpec.zero_lanes state =>
  state = seed_zero_state.
proof.
move=> hzero.
apply BArray200.ext_eq => i hi.
rewrite /seed_zero_state /BArray200.init_arr BArray200.initiE 1://.
exact (KeygenShakeStreamSpec.zero_lanes_get8 state i hzero hi).
qed.

lemma seed_pos_lane_word :
  W64.of_int 32 `>>` W8.of_int 3 = W64.of_int 4.
proof.
apply W64.to_uint_eq.
by rewrite W64.shr_div_le 1:/# !W64.of_uintK /=.
qed.

lemma seed_rate_lane_word :
  W64.of_int 136 `>>` W8.of_int 3 = W64.of_int 17.
proof.
apply W64.to_uint_eq.
by rewrite W64.shr_div_le 1:/# !W64.of_uintK /=.
qed.

lemma seed_final_lane_word :
  (W64.of_int 136 `>>` W8.of_int 3) - W64.one = W64.of_int 16.
proof.
rewrite seed_rate_lane_word.
apply W64.to_uint_eq.
have hle : W64.one \ule W64.of_int 17.
+ by rewrite W64.uleE W64.to_uint1 W64.of_uintK /=.
by rewrite W64.to_uintB 1:hle W64.to_uint1 !W64.of_uintK /=.
qed.

lemma seed_domain_shift_word :
  (((truncateu8 (W64.of_int 32) `&` W8.of_int 7) `<<` W8.of_int 3)
     `&` W8.of_int 63) = W8.zero.
proof.
apply W8.to_uint_eq.
rewrite (W8.to_uint_and_mod 6) 1:/#.
rewrite /(`<<`) W8.to_uint_shl 1:/#.
rewrite (W8.to_uint_and_mod 3) 1:/#.
by rewrite /truncateu8 W64.of_uintK !W8.of_uintK /=.
qed.

lemma keccak_finalize_seed32_correct (state0 : BArray200.t) :
  hoare [KeygenSamplerCallersTarget.M._keccak_finalize :
    sp_0 = state0 /\
    pos = W64.of_int 32 /\
    rate = W64.of_int 136 /\
    domain = W8.of_int 31
    ==>
    res = KeygenSeedXofSpec.seed_finalize state0].
proof.
proc.
auto => />.
rewrite /KeygenSeedXofSpec.seed_finalize
        /KeygenShakeStreamSpec.xor_lane_byte
        /KeygenShakeStreamSpec.xor_lane_byte.
rewrite seed_pos_lane_word seed_final_lane_word !W64.of_uintK /=.
rewrite KeygenShakeStreamSpec.finalize_padding_word.
rewrite seed_domain_shift_word.
have -> : 8 * 7 = 56 by ring.
trivial.
qed.

lemma seed_output_byte_word (state : BArray200.t) (idx : W64.t) :
  0 <= W64.to_uint idx < 128 =>
  truncateu8
    (BArray200.get64 state
       (W64.to_uint (idx `>>` W8.of_int 3))
     `>>`
       ((((truncateu8 idx) `&` W8.of_int 7) `<<` W8.of_int 3)
        `&` W8.of_int 63)) =
  BArray200.get8 state (W64.to_uint idx).
proof.
move=> hidx.
have hlane :
  W64.to_uint (idx `>>` W8.of_int 3) = W64.to_uint idx %/ 8.
+ by rewrite W64.shr_div_le 1:/# /=.
have hidxword : idx = W64.of_int (W64.to_uint idx).
+ by rewrite -(W64.to_uintK' idx).
rewrite hlane.
have hlane_bound : 0 <= W64.to_uint idx %/ 8 < 25.
+ apply divz_cmp => /#.
have hbyte_bound : 0 <= W64.to_uint idx %% 8 < 8 by smt(modz_cmp).
have hsplit :
  8 * (W64.to_uint idx %/ 8) + W64.to_uint idx %% 8 =
  W64.to_uint idx.
+ have hdiv := divz_eq (W64.to_uint idx) 8.
  smt().
have hshift_word :
  (((truncateu8 idx `&` W8.of_int 7) `<<` W8.of_int 3)
    `&` W8.of_int 63) =
  W8.of_int (8 * (W64.to_uint idx %% 8)).
+ apply W8.to_uint_eq.
  rewrite hidxword.
  rewrite (W8.to_uint_and_mod 6) 1:/#.
  rewrite /(`<<`) W8.to_uint_shl 1:/#.
  rewrite (W8.to_uint_and_mod 3) 1:/#.
  rewrite /truncateu8 W64.of_uintK
          (modz_small (W64.to_uint idx) W64.modulus) 1:/#.
  rewrite !W8.of_uintK.
  simplify.
  rewrite (modz_small (W64.to_uint idx) 256) 1:/#.
  have hidx8 : 0 <= W64.to_uint idx %% 8 < 8 by smt(modz_cmp).
  rewrite (modz_small (8 * (W64.to_uint idx %% 8)) 256) 1:/#.
  have -> : W64.to_uint idx %% 8 * 8 =
            8 * (W64.to_uint idx %% 8) by ring.
  rewrite (modz_small (8 * (W64.to_uint idx %% 8)) 256) 1:/#.
  rewrite (modz_small (8 * (W64.to_uint idx %% 8)) 64) 1:/#.
  ring.
rewrite hshift_word W64.shr_shrw 1:/#.
rewrite -KeygenShakeStreamSpec.drop_bytes_shrw 1:/#.
have hget := KeygenShakeStreamSpec.rate_lane_byte_get8
  state (W64.to_uint idx %/ 8) (W64.to_uint idx %% 8)
  hlane_bound hbyte_bound.
rewrite /KeygenShakeStreamSpec.rate_lane_byte in hget.
by rewrite hget hsplit.
qed.

lemma keccakf_seed_concrete_correct (seed0 : BArray32.t) :
  hoare [KeygenSamplerCallersTarget.M._keccakf1600 :
    sp_0 =
      KeygenSeedXofSpec.seed_finalize
        (KeygenSeedXofSpec.seed_absorb seed_zero_state seed0 32) /\
    KeygenShakeStreamSpec.zero_lanes seed_zero_state
    ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      KeygenSeedXofSpec.seed_permuted_state seed0].
proof.
conseq (TargetKeygenKeccak1600.keccakf1600_correct
  (KeygenSeedXofSpec.seed_finalize
    (KeygenSeedXofSpec.seed_absorb seed_zero_state seed0 32))).
+ move=> &hr [hstate hzero].
  exact hstate.
move=> &hr [hstate hzero] result hperm.
have hframe :
  KeygenSeedXofSpec.seed_framing
    (KeygenSeedXofSpec.seed_finalize
      (KeygenSeedXofSpec.seed_absorb seed_zero_state seed0 32))
    seed0.
+ rewrite /KeygenSeedXofSpec.seed_framing.
  exists seed_zero_state.
  split; first exact hzero.
  trivial.
have hpadded := KeygenSeedXofSpec.seed_framing_fips_state
  (KeygenSeedXofSpec.seed_finalize
    (KeygenSeedXofSpec.seed_absorb seed_zero_state seed0 32))
  seed0 hframe.
apply KeygenSeedXofSpec.seed_returned_state_bytes.
rewrite hperm.
rewrite KeygenShakeStreamSpec.state_of_barray_state_bytes_le.
by rewrite hpadded.
qed.

lemma kp_expand_seedbuf_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [KeygenSamplerCallersTarget.M._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.output_matches res seed0].
proof.
proc.
while (
  KeygenSeedXofSpec.output_state_prefix
    outp sp_0 (W64.to_uint idx) /\
  KeygenShakeStreamSpec.state_bytes_le sp_0 =
    KeygenSeedXofSpec.seed_permuted_state seed0 /\
  0 <= W64.to_uint idx <= 128).
+ auto => /> &hr hprefix hstate hidx0 hidx128 hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  have hbyte := seed_output_byte_word
    sp_0{hr} idx{hr} _.
  + smt(W64.to_uint_cmp).
  have hnext := KeygenSeedXofSpec.output_state_prefix_set_next
    outp{hr} sp_0{hr} (W64.to_uint idx{hr}) _ hprefix.
  + smt(W64.to_uint_cmp).
  have hnowrap :
    W64.to_uint idx{hr} + W64.to_uint W64.one < W64.modulus.
  + rewrite W64.to_uint1.
    smt(W64.to_uint_cmp).
  rewrite [W64.to_uint (idx{hr} + W64.one)]W64.to_uintD_small.
  + exact hnowrap.
  rewrite W64.to_uint1 hbyte.
  split.
  + exact hnext.
  split.
  + trivial.
  smt(W64.to_uint_cmp).
+ smt(W64.to_uint_cmp).
wp.
call (keccakf_seed_concrete_correct seed0).
wp.
call (keccak_finalize_seed32_correct
  (KeygenSeedXofSpec.seed_absorb seed_zero_state seed0 32)).
wp.
while (
  (exists initial,
     KeygenShakeStreamSpec.zero_lanes initial /\
     initial = seed_zero_state /\
     sp_0 = KeygenSeedXofSpec.seed_absorb
       initial seed0 (W64.to_uint pos)) /\
  seedp = seed0 /\
  0 <= W64.to_uint pos <= 32).
+ auto => /> &hr hzero hpos0 hpos32 hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  split.
  + exists seed_zero_state.
    split; first exact hzero.
    split; first trivial.
    have hnowrap :
      W64.to_uint pos{hr} + W64.to_uint W64.one < W64.modulus.
    + rewrite W64.to_uint1.
      smt(W64.to_uint_cmp).
    rewrite [W64.to_uint (pos{hr} + W64.one)]W64.to_uintD_small.
    + exact hnowrap.
    rewrite KeygenSeedXofSpec.seed_absorb_succ.
    + exact hpos0.
    rewrite /KeygenSeedXofSpec.seed_step
            /KeygenShakeStreamSpec.absorb_byte /=.
    trivial.
  have hnowrap2 :
    W64.to_uint pos{hr} + W64.to_uint W64.one < W64.modulus.
  + rewrite W64.to_uint1.
    smt(W64.to_uint_cmp).
  rewrite [W64.to_uint (pos{hr} + W64.one)]W64.to_uintD_small.
  + exact hnowrap2.
  smt(W64.to_uint_cmp).
wp.
call TargetKeygenShakeStream.keccak_init_state_zero.
auto => />.
move=> result hzero.
have hcanon := zero_lanes_seed_zero_state result hzero.
split.
+ exists seed_zero_state.
  split.
  + by rewrite -hcanon.
  split; first trivial.
  by rewrite KeygenSeedXofSpec.seed_absorb0 -hcanon.
move=> pos0 hposdone hzero0 hpos0 hpos32.
rewrite W64.ultE W64.of_uintK /= in hposdone.
have hpos : W64.to_uint pos0 = 32 by smt(W64.to_uint_cmp).
have hposword : pos0 = W64.of_int 32.
+ by rewrite -(W64.to_uintK' pos0) hpos.
do split.
+ trivial.
+ trivial.
trivial.
smt(W64.to_uint_cmp).
smt(W64.to_uint_cmp).
move=> _ _ result1 hstate1.
split.
+ exact (KeygenSeedXofSpec.output_state_prefix0 out0 result1).
move=> idx0 outp0 hdone hprefix hidx0 hidx128.
rewrite W64.ultE W64.of_uintK /= in hdone.
apply (KeygenSeedXofSpec.output_state_prefix_matches
  outp0 result1 seed0 hstate1).
have hidx : W64.to_uint idx0 = 128 by smt(W64.to_uint_cmp).
by rewrite -hidx.
qed.

lemma kp_expand_seedbuf_uniform_slice_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [KeygenSamplerCallersTarget.M._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.uniform_seed_slice_matches res seed0].
proof.
conseq (kp_expand_seedbuf_correct out0 seed0).
move=> &hr hpre result hmatch.
exact (KeygenSeedXofSpec.output_matches_uniform_slice
  result seed0 hmatch).
qed.

lemma kp_expand_seedbuf_eta_slice_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [KeygenSamplerCallersTarget.M._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.eta_seed_slice_matches res seed0].
proof.
conseq (kp_expand_seedbuf_correct out0 seed0).
move=> &hr hpre result hmatch.
exact (KeygenSeedXofSpec.output_matches_eta_slice
  result seed0 hmatch).
qed.

lemma kp_expand_seedbuf_key_slice_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [KeygenSamplerCallersTarget.M._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.key_seed_slice_matches res seed0].
proof.
conseq (kp_expand_seedbuf_correct out0 seed0).
move=> &hr hpre result hmatch.
exact (KeygenSeedXofSpec.output_matches_key_slice
  result seed0 hmatch).
qed.

end TargetKeygenSeedXof.
