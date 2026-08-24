require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget KeygenShakeStreamSpec
               HAETAE_Keccak1600
               TargetKeygenShakeStream TargetKeygenSeedXof
               VerifyChallengeM23SqueezeStreamPostFreeze
               VerifyChallengeM23StreamSamplerPostFreeze
               TranscriptBytes.

theory VerifyChallengeAbsorbStatePostFreeze.

module Verify = VerifyCoreTarget.M.
module Trace =
  VerifyChallengeM23StreamSamplerPostFreeze.ActualVerifyChallengeM23StreamTrace.

op shake256_rate : int = 136.
op mode2_highlen : int = 576.

op zero_state_bytes : int list = mkseq (fun _ => 0) 200.

op int_xor_byte (x y : int) : int =
  W8.to_uint (W8.of_int x `^` W8.of_int y).

op state_xor_byte (st : int list) (idx b : int) : int list =
  put st idx (int_xor_byte (nth 0 st idx) b).

op shake256_absorb_step
    (acc : int list * int) (b : int) : int list * int =
  let st1 = state_xor_byte acc.`1 acc.`2 b in
  if acc.`2 + 1 = shake256_rate
  then (HAETAE_Keccak1600.keccak_f1600_bytes st1, 0)
  else (st1, acc.`2 + 1).

op shake256_absorb_prefix
    (bytes : int list) (count : int) : int list * int =
  foldl shake256_absorb_step (zero_state_bytes, 0) (take count bytes).

op shake256_finalize_at (st : int list) (pos : int) : int list =
  state_xor_byte (state_xor_byte st pos 31) (shake256_rate - 1) 128.

op w8s_of_barray32 (bp : BArray32.t) : W8.t list =
  mkseq (fun i => BArray32.get8 bp i) 32.

op bytes_of_barray32 (bp : BArray32.t) : int list =
  map W8.to_uint (w8s_of_barray32 bp).

op mode2_highbits_w8s (bp : BArray1152.t) : W8.t list =
  mkseq (fun i => BArray1152.get8 bp i) mode2_highlen.

op mode2_highbits_bytes (bp : BArray1152.t) : int list =
  map W8.to_uint (mode2_highbits_w8s bp).

op mode2_verify_challenge_input_w8
    (highp : BArray1152.t) (lsbp mup : BArray32.t) : W8.t list =
  TranscriptBytes.verify_challenge_input
    (mode2_highbits_w8s highp)
    (w8s_of_barray32 lsbp)
    (w8s_of_barray32 mup).

op mode2_verify_challenge_input_bytes
    (highp : BArray1152.t) (lsbp mup : BArray32.t) : int list =
  map W8.to_uint (mode2_verify_challenge_input_w8 highp lsbp mup).

op mode2_verify_challenge_absorb_pair
    (highp : BArray1152.t) (lsbp mup : BArray32.t) : int list * int =
  shake256_absorb_prefix (mode2_verify_challenge_input_bytes highp lsbp mup)
    (mode2_highlen + 32 + 32).

op mode2_verify_challenge_absorb_state
    (highp : BArray1152.t) (lsbp mup : BArray32.t) : int list =
  shake256_finalize_at
    (mode2_verify_challenge_absorb_pair highp lsbp mup).`1
    (mode2_verify_challenge_absorb_pair highp lsbp mup).`2.

op mode2_state = mode2_verify_challenge_absorb_state.

lemma zero_state_bytes_size :
  size zero_state_bytes = 200.
proof. by rewrite /zero_state_bytes size_mkseq. qed.

lemma state_xor_byte_size st idx b :
  size (state_xor_byte st idx b) = size st.
proof. by rewrite /state_xor_byte size_put. qed.

lemma bytes_of_barray32E (bp : BArray32.t) :
  bytes_of_barray32 bp = mkseq (fun i => W8.to_uint (BArray32.get8 bp i)) 32.
proof. by rewrite /bytes_of_barray32 /w8s_of_barray32 map_mkseq. qed.

lemma mode2_highbits_bytesE (bp : BArray1152.t) :
  mode2_highbits_bytes bp =
    mkseq (fun i => W8.to_uint (BArray1152.get8 bp i)) mode2_highlen.
proof. by rewrite /mode2_highbits_bytes /mode2_highbits_w8s map_mkseq. qed.

lemma mode2_verify_challenge_input_bytesE
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  mode2_verify_challenge_input_bytes highp lsbp mup =
    mode2_highbits_bytes highp ++ bytes_of_barray32 lsbp ++
    bytes_of_barray32 mup.
proof.
rewrite /mode2_verify_challenge_input_bytes
        /mode2_verify_challenge_input_w8.
rewrite /TranscriptBytes.verify_challenge_input !map_cat.
by rewrite /mode2_highbits_bytes /mode2_highbits_w8s /bytes_of_barray32
           /w8s_of_barray32 !map_mkseq.
qed.

lemma bytes_of_barray32_size (bp : BArray32.t) :
  size (bytes_of_barray32 bp) = 32.
proof. by rewrite bytes_of_barray32E size_mkseq. qed.

lemma mode2_highbits_bytes_size (bp : BArray1152.t) :
  size (mode2_highbits_bytes bp) = mode2_highlen.
proof. by rewrite mode2_highbits_bytesE size_mkseq. qed.

lemma mode2_verify_challenge_input_bytes_size
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  size (mode2_verify_challenge_input_bytes highp lsbp mup) =
    mode2_highlen + 32 + 32.
proof.
by rewrite mode2_verify_challenge_input_bytesE !size_cat
           mode2_highbits_bytes_size !bytes_of_barray32_size.
qed.

lemma mode2_verify_challenge_input_high_nth
    (highp : BArray1152.t) (lsbp mup : BArray32.t) i :
  0 <= i < mode2_highlen =>
  nth 0 (mode2_verify_challenge_input_bytes highp lsbp mup) i =
    W8.to_uint (BArray1152.get8 highp i).
proof.
move=> hi.
rewrite mode2_verify_challenge_input_bytesE -catA nth_cat.
rewrite mode2_highbits_bytes_size.
have hil : i < mode2_highlen by smt().
rewrite hil /=.
by rewrite mode2_highbits_bytesE nth_mkseq 1:hi.
qed.

lemma mode2_verify_challenge_input_lsb_nth
    (highp : BArray1152.t) (lsbp mup : BArray32.t) i :
  0 <= i < 32 =>
  nth 0 (mode2_verify_challenge_input_bytes highp lsbp mup)
    (mode2_highlen + i) = W8.to_uint (BArray32.get8 lsbp i).
proof.
move=> hi.
rewrite mode2_verify_challenge_input_bytesE -catA nth_cat.
rewrite mode2_highbits_bytes_size.
have hhigh : !(mode2_highlen + i < mode2_highlen) by smt().
rewrite hhigh /= nth_cat bytes_of_barray32_size.
have hlsb : i < 32 by smt().
rewrite hlsb /=.
by rewrite bytes_of_barray32E nth_mkseq 1:hi.
qed.

lemma mode2_verify_challenge_input_mu_nth
    (highp : BArray1152.t) (lsbp mup : BArray32.t) i :
  0 <= i < 32 =>
  nth 0 (mode2_verify_challenge_input_bytes highp lsbp mup)
    (mode2_highlen + 32 + i) = W8.to_uint (BArray32.get8 mup i).
proof.
move=> hi.
rewrite mode2_verify_challenge_input_bytesE -catA nth_cat.
rewrite mode2_highbits_bytes_size.
have hhigh : !(mode2_highlen + 32 + i < mode2_highlen) by smt().
rewrite hhigh /= nth_cat bytes_of_barray32_size.
have hlsb : !(32 + i < 32) by smt().
rewrite hlsb /=.
by rewrite bytes_of_barray32E nth_mkseq 1:hi.
qed.

op absorb32_segment_matches
    (bytes : int list) (base : int) (inp : BArray32.t) : bool =
  forall i,
    0 <= i < 32 =>
    nth 0 bytes (base + i) = W8.to_uint (BArray32.get8 inp i).

lemma mode2_lsb_segment_matches
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  absorb32_segment_matches
    (mode2_verify_challenge_input_bytes highp lsbp mup)
    mode2_highlen lsbp.
proof.
rewrite /absorb32_segment_matches.
move=> i hi.
exact (mode2_verify_challenge_input_lsb_nth highp lsbp mup i hi).
qed.

lemma mode2_mu_segment_matches
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  absorb32_segment_matches
    (mode2_verify_challenge_input_bytes highp lsbp mup)
    (mode2_highlen + 32) mup.
proof.
rewrite /absorb32_segment_matches.
move=> i hi.
exact (mode2_verify_challenge_input_mu_nth highp lsbp mup i hi).
qed.

lemma shake256_absorb_prefix0 bytes :
  shake256_absorb_prefix bytes 0 = (zero_state_bytes, 0).
proof. by rewrite /shake256_absorb_prefix take0. qed.

lemma shake256_absorb_prefix_succ bytes count :
  0 <= count < size bytes =>
  shake256_absorb_prefix bytes (count + 1) =
    shake256_absorb_step (shake256_absorb_prefix bytes count)
      (nth 0 bytes count).
proof.
move=> hcount.
rewrite /shake256_absorb_prefix.
rewrite (take_nth 0 count bytes) 1:hcount foldl_rcons.
trivial.
qed.

lemma shake256_absorb_step_state_size (acc : int list * int) (b : int) :
  size acc.`1 = 200 =>
  size (shake256_absorb_step acc b).`1 = 200.
proof.
move=> hsize.
rewrite /shake256_absorb_step /=.
case (acc.`2 + 1 = shake256_rate) => _ /=.
+ by rewrite HAETAE_Keccak1600.keccak_f1600_bytes_size
           HAETAE_Keccak1600.keccak_state_bytesE.
by rewrite state_xor_byte_size.
qed.

lemma shake256_absorb_step_position (acc : int list * int) (b : int) :
  0 <= acc.`2 < shake256_rate =>
  (shake256_absorb_step acc b).`2 = (acc.`2 + 1) %% shake256_rate.
proof.
move=> hpos.
rewrite /shake256_absorb_step /=.
case (acc.`2 + 1 = shake256_rate) => hfull /=.
+ rewrite hfull /shake256_rate /=.
  trivial.
have hsmall : 0 <= acc.`2 + 1 < shake256_rate by smt().
by rewrite (modz_small (acc.`2 + 1) shake256_rate) 1:hsmall.
qed.

lemma shake256_absorb_prefix_state_size bytes count :
  0 <= count =>
  count <= size bytes =>
  size (shake256_absorb_prefix bytes count).`1 = 200.
proof.
move: count.
apply intind.
+ move=> _.
  by rewrite shake256_absorb_prefix0 zero_state_bytes_size.
move=> count hcount ih hcap.
rewrite shake256_absorb_prefix_succ 1:/#.
apply shake256_absorb_step_state_size.
apply ih.
smt().
qed.

lemma shake256_absorb_prefix_position (bytes : int list) (count : int) :
  0 <= count =>
  count <= size bytes =>
  (shake256_absorb_prefix bytes count).`2 = count %% shake256_rate.
proof.
move: count.
apply intind.
+ move=> _.
  by rewrite shake256_absorb_prefix0.
move=> count hcount ih hcap.
rewrite shake256_absorb_prefix_succ 1:/#.
have hipos := ih _.
+ smt().
have hpos :
    0 <= (shake256_absorb_prefix bytes count).`2 < shake256_rate.
+ rewrite hipos.
  apply modz_cmp.
  by rewrite /shake256_rate.
suff hstep :
    (shake256_absorb_step (shake256_absorb_prefix bytes count)
      (nth 0 bytes count)).`2 =
    ((shake256_absorb_prefix bytes count).`2 + 1) %% shake256_rate.
+ move: hstep hipos.
  smt(modzDml).
apply shake256_absorb_step_position.
rewrite hipos.
apply modz_cmp.
by rewrite /shake256_rate.
qed.

lemma mode2_absorb_position_high
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  (shake256_absorb_prefix
    (mode2_verify_challenge_input_bytes highp lsbp mup)
    mode2_highlen).`2 = 32.
proof.
rewrite shake256_absorb_prefix_position.
+ by rewrite /mode2_highlen.
+ rewrite mode2_verify_challenge_input_bytes_size.
  trivial.
by rewrite /mode2_highlen /shake256_rate /=.
qed.

lemma mode2_absorb_position_lsb
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  (shake256_absorb_prefix
    (mode2_verify_challenge_input_bytes highp lsbp mup)
    (mode2_highlen + 32)).`2 = 64.
proof.
rewrite shake256_absorb_prefix_position.
+ by rewrite /mode2_highlen.
+ rewrite mode2_verify_challenge_input_bytes_size.
  trivial.
by rewrite /mode2_highlen /shake256_rate /=.
qed.

lemma mode2_absorb_position_mu
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  (shake256_absorb_prefix
    (mode2_verify_challenge_input_bytes highp lsbp mup)
    (mode2_highlen + 32 + 32)).`2 = 96.
proof.
rewrite shake256_absorb_prefix_position.
+ by rewrite /mode2_highlen.
+ rewrite mode2_verify_challenge_input_bytes_size.
  trivial.
by rewrite /mode2_highlen /shake256_rate /=.
qed.

lemma mode2_absorb_high_pair_bridge
    (highp : BArray1152.t) (lsbp mup : BArray32.t)
    (spx : BArray200.t) (stp : BArray16.t) :
  (KeygenShakeStreamSpec.state_bytes_le spx,
   W64.to_uint (BArray16.get64 stp 0)) =
    shake256_absorb_prefix
      (mode2_verify_challenge_input_bytes highp lsbp mup) mode2_highlen =>
  BArray16.get64 stp 0 = W64.of_int 32 /\
  (KeygenShakeStreamSpec.state_bytes_le spx, 32) =
    shake256_absorb_prefix
      (mode2_verify_challenge_input_bytes highp lsbp mup) mode2_highlen.
proof.
move=> hpair.
have hpos : W64.to_uint (BArray16.get64 stp 0) = 32.
+ rewrite -(mode2_absorb_position_high highp lsbp mup).
  exact (congr1 snd _ _ hpair).
split.
+ apply W64.to_uint_eq.
  by rewrite hpos W64.of_uintK /=.
by move: hpair; rewrite hpos.
qed.

lemma mode2_absorb_lsb_pair_bridge
    (highp : BArray1152.t) (lsbp mup : BArray32.t)
    (spx : BArray200.t) (stp : BArray16.t) :
  (KeygenShakeStreamSpec.state_bytes_le spx,
   W64.to_uint (BArray16.get64 stp 0)) =
    shake256_absorb_prefix
      (mode2_verify_challenge_input_bytes highp lsbp mup)
      (mode2_highlen + 32) =>
  BArray16.get64 stp 0 = W64.of_int 64 /\
  (KeygenShakeStreamSpec.state_bytes_le spx, 64) =
    shake256_absorb_prefix
      (mode2_verify_challenge_input_bytes highp lsbp mup)
      (mode2_highlen + 32).
proof.
move=> hpair.
have hpos : W64.to_uint (BArray16.get64 stp 0) = 64.
+ rewrite -(mode2_absorb_position_lsb highp lsbp mup).
  exact (congr1 snd _ _ hpair).
split.
+ apply W64.to_uint_eq.
  by rewrite hpos W64.of_uintK /=.
by move: hpair; rewrite hpos.
qed.

lemma mode2_absorb_mu_pair_bridge
    (highp : BArray1152.t) (lsbp mup : BArray32.t)
    (spx : BArray200.t) (stp : BArray16.t) :
  (KeygenShakeStreamSpec.state_bytes_le spx,
   W64.to_uint (BArray16.get64 stp 0)) =
    shake256_absorb_prefix
      (mode2_verify_challenge_input_bytes highp lsbp mup)
      (mode2_highlen + 32 + 32) =>
  BArray16.get64 stp 0 = W64.of_int 96 /\
  (KeygenShakeStreamSpec.state_bytes_le spx, 96) =
    shake256_absorb_prefix
      (mode2_verify_challenge_input_bytes highp lsbp mup)
      (mode2_highlen + 32 + 32).
proof.
move=> hpair.
have hpos : W64.to_uint (BArray16.get64 stp 0) = 96.
+ rewrite -(mode2_absorb_position_mu highp lsbp mup).
  exact (congr1 snd _ _ hpair).
split.
+ apply W64.to_uint_eq.
  by rewrite hpos W64.of_uintK /=.
by move: hpair; rewrite hpos.
qed.

lemma int_xor_byteE x y :
  int_xor_byte x y = W8.to_uint (W8.of_int x `^` W8.of_int y).
proof. by rewrite /int_xor_byte. qed.

lemma state_xor_byte_nth st idx b i :
  0 <= idx < size st =>
  0 <= i < size st =>
  nth 0 (state_xor_byte st idx b) i =
    if i = idx then int_xor_byte (nth 0 st i) b else nth 0 st i.
proof.
move=> hidx hi.
rewrite /state_xor_byte nth_put 1:hidx.
case (idx = i) => hsame.
+ subst i. trivial.
by smt().
qed.

lemma state_bytes_le_absorb_byte
    (state : BArray200.t) (byte : W8.t) (pos : int) :
  0 <= pos < 200 =>
  KeygenShakeStreamSpec.state_bytes_le
    (KeygenShakeStreamSpec.absorb_byte state byte (W64.of_int pos)) =
  state_xor_byte
    (KeygenShakeStreamSpec.state_bytes_le state) pos (W8.to_uint byte).
proof.
move=> hpos.
apply (eq_from_nth 0).
+ rewrite KeygenShakeStreamSpec.state_bytes_le_size
          state_xor_byte_size
          KeygenShakeStreamSpec.state_bytes_le_size.
  trivial.
move=> i hi.
rewrite KeygenShakeStreamSpec.state_bytes_le_size in hi.
rewrite state_xor_byte_nth.
+ by rewrite KeygenShakeStreamSpec.state_bytes_le_size.
+ by rewrite KeygenShakeStreamSpec.state_bytes_le_size.
rewrite (KeygenShakeStreamSpec.state_bytes_le_nth
  (KeygenShakeStreamSpec.absorb_byte state byte (W64.of_int pos)) i hi).
rewrite (KeygenShakeStreamSpec.state_bytes_le_nth state i hi).
rewrite KeygenShakeStreamSpec.absorb_byte_at_int_get8 1:hpos 1:hi.
rewrite /int_xor_byte W8.to_uintK W8.to_uintK.
by case (i = pos).
qed.

lemma state_bytes_le_absorb_byte_word
    (state : BArray200.t) (byte : W8.t) (pos : W64.t) :
  W64.to_uint pos < 200 =>
  KeygenShakeStreamSpec.state_bytes_le
    (KeygenShakeStreamSpec.absorb_byte state byte pos) =
  state_xor_byte
    (KeygenShakeStreamSpec.state_bytes_le state)
    (W64.to_uint pos) (W8.to_uint byte).
proof.
move=> hpos.
have h := state_bytes_le_absorb_byte
  state byte (W64.to_uint pos) _.
+ smt(W64.to_uint_cmp).
by rewrite W64.to_uintK' in h.
qed.

lemma generated_absorb_byteE
    (state : BArray200.t) (byte : W8.t) (pos : W64.t) :
  BArray200.set64 state
    (W64.to_uint (pos `>>` (W8.of_int 3)))
    (BArray200.get64 state
       (W64.to_uint (pos `>>` (W8.of_int 3))) `^`
     ((zeroextu64 byte) `<<`
       (((((truncateu8 pos) `&` (W8.of_int 7))
            `<<` (W8.of_int 3)) `&` (W8.of_int 63))))) =
  KeygenShakeStreamSpec.absorb_byte state byte pos.
proof. by rewrite /KeygenShakeStreamSpec.absorb_byte /=. qed.

lemma generated_absorb_bytedE
    (state : BArray200.t) (byte : W8.t) (pos : W64.t) :
  BArray200.set64d state
    (8 * W64.to_uint (pos `>>` (W8.of_int 3)))
    (BArray200.get64d state
       (8 * W64.to_uint (pos `>>` (W8.of_int 3))) `^`
     ((zeroextu64 byte) `<<`
       (((((truncateu8 pos) `&` (W8.of_int 7))
            `<<` (W8.of_int 3)) `&` (W8.of_int 63))))) =
  KeygenShakeStreamSpec.absorb_byte state byte pos.
proof. by rewrite /KeygenShakeStreamSpec.absorb_byte /=. qed.

lemma zeroextu64_w8_31 :
  zeroextu64 (W8.of_int 31) = W64.of_int 31.
proof.
apply W64.to_uint_eq.
by rewrite W8u8.to_uint_zeroextu64 W8.of_uintK W64.of_uintK /=.
qed.

lemma generated_finalize_domainE
    (state : BArray200.t) (pos : W64.t) :
  BArray200.set64d state
    (8 * W64.to_uint (pos `>>` (W8.of_int 3)))
    (BArray200.get64d state
       (8 * W64.to_uint (pos `>>` (W8.of_int 3))) `^`
     ((W64.of_int 31) `<<`
       (((((truncateu8 pos) `&` (W8.of_int 7))
            `<<` (W8.of_int 3)) `&` (W8.of_int 63))))) =
  KeygenShakeStreamSpec.absorb_byte state (W8.of_int 31) pos.
proof.
rewrite -zeroextu64_w8_31.
exact (generated_absorb_bytedE state (W8.of_int 31) pos).
qed.

lemma generated_finalize_paddingE (state : BArray200.t) :
  BArray200.set64d state 128
    (BArray200.get64d state 128 `^`
      (W64.one `<<` (W8.of_int 63))) =
  KeygenShakeStreamSpec.absorb_byte
    state (W8.of_int 128) (W64.of_int 135).
proof.
rewrite /KeygenShakeStreamSpec.absorb_byte /=.
rewrite KeygenShakeStreamSpec.finalize_padding_word.
rewrite W64.shr_div_le 1:/# /=.
rewrite /truncateu8 W64.of_uintK /=.
have hshift :
  (((W8.of_int 135 `&` W8.of_int 7) `<<` W8.of_int 3)
     `&` W8.of_int 63) = W8.of_int 56.
+ apply W8.to_uint_eq.
  rewrite (W8.to_uint_and_mod 6) 1:/#.
  rewrite /(`<<`) W8.to_uint_shl 1:/#.
  rewrite (W8.to_uint_and_mod 3) 1:/#.
  rewrite !W8.of_uintK /=.
  trivial.
rewrite hshift.
trivial.
qed.

lemma verify_keccakf1600_state_bytes (sp0 : BArray200.t) :
  hoare [Verify._keccakf1600 :
    sp_0 = sp0 ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      HAETAE_Keccak1600.keccak_f1600_bytes
        (KeygenShakeStreamSpec.state_bytes_le sp0)].
proof.
conseq
  (VerifyChallengeM23SqueezeStreamPostFreeze.verify_keccakf1600_correct sp0).
move=> &hr hpre result hstate.
exact (KeygenShakeStreamSpec.state_bytes_le_keccak_step sp0 result hstate).
qed.

lemma verify_keccak_init_state_zero_lanes :
  hoare [Verify._keccak_init_state :
    true ==> KeygenShakeStreamSpec.zero_lanes res].
proof.
proc.
while
  ((forall lane,
      0 <= lane < W64.to_uint i =>
      BArray200.get64 sp_0 lane = W64.zero) /\
   0 <= W64.to_uint i <= 25).
+ auto => /> &hr hprefix hlo hhi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  split.
  + move=> lane hlane0 hlane1.
    rewrite BArray200.get_set64E 1:/# 1:/#.
    case (lane = W64.to_uint i{hr}) => [-> | hne].
    + trivial.
    have -> /= : !(W64.to_uint i{hr} = lane) by smt().
    apply hprefix.
    rewrite W64.to_uintD_small 1:/# in hlane1.
    rewrite W64.to_uint1 in hlane1.
    smt().
  rewrite W64.to_uintD_small 1:/#.
  smt(W64.to_uint_cmp).
wp.
skip => &hr _ /=.
split.
+ smt(W64.to_uint_cmp).
move=> i0 state hdone [hprefix hlo hhi].
rewrite /KeygenShakeStreamSpec.zero_lanes.
move=> hlane.
apply hprefix.
rewrite W64.ultE W64.of_uintK /= in hdone.
smt(W64.to_uint_cmp).
qed.

lemma verify_keccak_init_state_zero_bytes :
  hoare [Verify._keccak_init_state :
    true ==>
    KeygenShakeStreamSpec.state_bytes_le res = zero_state_bytes].
proof.
conseq verify_keccak_init_state_zero_lanes.
move=> &hr _ result hzero.
apply (eq_from_nth 0).
+ by rewrite KeygenShakeStreamSpec.state_bytes_le_size zero_state_bytes_size.
move=> i hi.
rewrite KeygenShakeStreamSpec.state_bytes_le_size in hi.
rewrite (KeygenShakeStreamSpec.state_bytes_le_nth result i hi).
rewrite /zero_state_bytes nth_mkseq 1:hi.
rewrite (KeygenShakeStreamSpec.zero_lanes_get8 result i hzero hi).
by rewrite W8.to_uint0.
qed.

lemma verify_absorb_buf_mode2
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t)
    (sp0 : BArray200.t) (stp0 : BArray16.t) :
  hoare [Verify.__verify_shake256_absorb_buf :
    sp_0 = sp0 /\ statep = stp0 /\ inp = high0 /\
    inlen = W64.of_int mode2_highlen /\
    KeygenShakeStreamSpec.state_bytes_le sp0 = zero_state_bytes /\
    BArray16.get64 stp0 0 = W64.zero
    ==>
    (KeygenShakeStreamSpec.state_bytes_le res.`1,
     W64.to_uint (BArray16.get64 res.`2 0)) =
      shake256_absorb_prefix
        (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
        mode2_highlen].
proof.
proc.
wp.
while
  (inp = high0 /\ inlen = W64.of_int mode2_highlen /\
   0 <= W64.to_uint i <= mode2_highlen /\
   0 <= W64.to_uint pos < shake256_rate /\
   (KeygenShakeStreamSpec.state_bytes_le sp_0, W64.to_uint pos) =
     shake256_absorb_prefix
       (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
       (W64.to_uint i)).
+ sp.
  if.
  + wp.
    exlim sp_0 => before_state.
    call (verify_keccakf1600_state_bytes before_state).
    auto => />.
    move=> &hr pos0 i0 sp00 hi0 hiend hp0 hplt hpair
            hguard hfull result hresult.
    rewrite /protect_64 /protect_ptr.
    have hilt : W64.to_uint i0 < mode2_highlen.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_highlen /=.
      smt(W64.to_uint_cmp).
    have hinext :
        W64.to_uint (i0 + W64.one) = W64.to_uint i0 + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hpos135 : W64.to_uint pos0 = shake256_rate - 1.
    + move: hfull.
      rewrite W64.to_uint_eq W64.to_uintD_small 1:/# W64.to_uint1
              W64.of_uintK /shake256_rate /=.
      smt().
    rewrite generated_absorb_bytedE in hresult.
    rewrite state_bytes_le_absorb_byte_word 1:/# in hresult.
    have hstate0 :
        KeygenShakeStreamSpec.state_bytes_le sp00 =
          (shake256_absorb_prefix
            (mode2_verify_challenge_input_bytes inp{hr} lsb0 mu0)
            (W64.to_uint i0)).`1 by
      exact (congr1 fst _ _ hpair).
    have hpos0 :
        W64.to_uint pos0 =
          (shake256_absorb_prefix
            (mode2_verify_challenge_input_bytes inp{hr} lsb0 mu0)
            (W64.to_uint i0)).`2 by
      exact (congr1 snd _ _ hpair).
    have hpnext := shake256_absorb_prefix_succ
      (mode2_verify_challenge_input_bytes inp{hr} lsb0 mu0)
      (W64.to_uint i0) _.
    + rewrite mode2_verify_challenge_input_bytes_size.
      smt(W64.to_uint_cmp).
    split.
    + smt(W64.to_uint_cmp).
    rewrite hinext hpnext /shake256_absorb_step /=.
    rewrite -hpos0 hpos135 /shake256_rate /=.
    rewrite -hstate0.
    have hibound : 0 <= W64.to_uint i0 < mode2_highlen by
      smt(W64.to_uint_cmp).
    rewrite (mode2_verify_challenge_input_high_nth
      inp{hr} lsb0 mu0 (W64.to_uint i0)) 1:hibound.
    move: hresult.
    rewrite hpos135.
    trivial.
  + skip => /> &hr pos0 i0 sp00 hi0 hiend hp0 hplt hpair
                    hguard hnotfull.
    have hilt : W64.to_uint i0 < mode2_highlen.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_highlen /=.
      smt(W64.to_uint_cmp).
    have hinext :
        W64.to_uint (i0 + W64.one) = W64.to_uint i0 + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hposnext :
        W64.to_uint (pos0 + W64.one) = W64.to_uint pos0 + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hnot136 : W64.to_uint pos0 + 1 <> shake256_rate.
    + move: hnotfull.
      rewrite W64.to_uint_eq W64.to_uintD_small 1:/# W64.to_uint1
              W64.of_uintK /shake256_rate /=.
      smt().
    have hbyte := mode2_verify_challenge_input_high_nth
      inp{hr} lsb0 mu0 (W64.to_uint i0) _.
    + smt(W64.to_uint_cmp).
    have hstate0 :
        KeygenShakeStreamSpec.state_bytes_le sp00 =
          (shake256_absorb_prefix
            (mode2_verify_challenge_input_bytes inp{hr} lsb0 mu0)
            (W64.to_uint i0)).`1 by
      exact (congr1 fst _ _ hpair).
    have hpos0 :
        W64.to_uint pos0 =
          (shake256_absorb_prefix
            (mode2_verify_challenge_input_bytes inp{hr} lsb0 mu0)
            (W64.to_uint i0)).`2 by
      exact (congr1 snd _ _ hpair).
    have hpnext := shake256_absorb_prefix_succ
      (mode2_verify_challenge_input_bytes inp{hr} lsb0 mu0)
      (W64.to_uint i0) _.
    + rewrite mode2_verify_challenge_input_bytes_size.
      smt(W64.to_uint_cmp).
    split.
    + rewrite hinext.
      smt(W64.to_uint_cmp).
    split.
    + rewrite hposnext.
      smt(W64.to_uint_cmp).
    rewrite hinext hposnext hpnext /shake256_absorb_step /=.
    rewrite -hpos0 hnot136 /=.
    rewrite -hstate0.
    rewrite generated_absorb_bytedE.
    rewrite state_bytes_le_absorb_byte_word 1:/#.
    rewrite hbyte.
    trivial.
wp.
auto => />.
move=> hzero hpos.
split.
+ split.
  + rewrite /protect_64 /protect_ptr hpos W64.to_uint0
            /shake256_rate /=.
    smt().
  rewrite /protect_64 /protect_ptr hpos W64.to_uint0
          hzero shake256_absorb_prefix0.
  trivial.
move=> i0 pos0 sp00 hdone hi0 hiend hp0 hplt hpair.
move: hdone hpair.
rewrite W64.ultE W64.of_uintK /mode2_highlen /=.
smt(W64.to_uint_cmp).
qed.

lemma verify_absorb_mu32_segment
    (bytes0 : int list) (inp0 : BArray32.t)
    (base start : int) (sp0 : BArray200.t) (stp0 : BArray16.t) :
  0 <= base =>
  base + 32 <= size bytes0 =>
  0 <= start =>
  start + 32 < shake256_rate =>
  hoare [Verify.__verify_shake256_absorb_mu32 :
    sp_0 = sp0 /\ statep = stp0 /\ inp = inp0 /\
    BArray16.get64 stp0 0 = W64.of_int start /\
    (KeygenShakeStreamSpec.state_bytes_le sp0, start) =
      shake256_absorb_prefix bytes0 base /\
    absorb32_segment_matches bytes0 base inp0
    ==>
    (KeygenShakeStreamSpec.state_bytes_le res.`1,
     W64.to_uint (BArray16.get64 res.`2 0)) =
      shake256_absorb_prefix bytes0 (base + 32)].
proof.
move=> hbase hcap hstart hfit.
proc.
wp.
while
  (inp = inp0 /\
   0 <= W64.to_uint i <= 32 /\
   W64.to_uint pos = start + W64.to_uint i /\
   (KeygenShakeStreamSpec.state_bytes_le sp_0, W64.to_uint pos) =
     shake256_absorb_prefix bytes0 (base + W64.to_uint i) /\
   absorb32_segment_matches bytes0 base inp0).
+ sp.
  skip => /> &hr pos0 i0 sp00 hi0 hi32 hpos hpair hmatches hguard.
  have hilt : W64.to_uint i0 < 32.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hinext :
      W64.to_uint (i0 + W64.one) = W64.to_uint i0 + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hposnext :
      W64.to_uint (pos0 + W64.one) = W64.to_uint pos0 + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hbyte := hmatches (W64.to_uint i0) _.
  + smt(W64.to_uint_cmp).
  have hstate0 :
      KeygenShakeStreamSpec.state_bytes_le sp00 =
        (shake256_absorb_prefix bytes0
          (base + W64.to_uint i0)).`1 by
    exact (congr1 fst _ _ hpair).
  have hpos0 :
      W64.to_uint pos0 =
        (shake256_absorb_prefix bytes0
          (base + W64.to_uint i0)).`2 by
    exact (congr1 snd _ _ hpair).
  have hpnext := shake256_absorb_prefix_succ bytes0
    (base + W64.to_uint i0) _.
  + smt(W64.to_uint_cmp).
  do split.
  + rewrite hinext.
    smt(W64.to_uint_cmp).
  + rewrite hinext.
    smt().
  + rewrite hinext hposnext.
    smt().
  rewrite hinext hposnext.
  have hassoc : base + (W64.to_uint i0 + 1) =
                base + W64.to_uint i0 + 1 by ring.
  rewrite hassoc.
  rewrite hpnext /shake256_absorb_step /=.
  have hnotfull : W64.to_uint pos0 + 1 <> shake256_rate by
    smt().
  rewrite -hpos0 hnotfull /=.
  rewrite -hstate0.
  rewrite generated_absorb_bytedE.
  rewrite state_bytes_le_absorb_byte_word 1:/#.
  rewrite -hbyte.
  trivial.
wp.
auto => />.
move=> hstpos hpair0 hmatches0.
split.
+ split.
  + rewrite /protect_64 /protect_ptr hstpos W64.of_uintK.
    rewrite (modz_small start W64.modulus) 1:/#.
    trivial.
  rewrite /protect_64 /protect_ptr hstpos W64.of_uintK.
  rewrite (modz_small start W64.modulus) 1:/#.
  exact hpair0.
move=> i0 pos0 sp00 hdone hinp hi0 hi32 hpos0 hpair.
move: hdone hpair.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma verify_absorb_mu32_mode2_lsb
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t)
    (sp0 : BArray200.t) (stp0 : BArray16.t) :
  hoare [Verify.__verify_shake256_absorb_mu32 :
    sp_0 = sp0 /\ statep = stp0 /\ inp = lsb0 /\
    BArray16.get64 stp0 0 = W64.of_int 32 /\
    (KeygenShakeStreamSpec.state_bytes_le sp0, 32) =
      shake256_absorb_prefix
        (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
        mode2_highlen /\
    absorb32_segment_matches
      (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
      mode2_highlen lsb0
    ==>
    (KeygenShakeStreamSpec.state_bytes_le res.`1,
     W64.to_uint (BArray16.get64 res.`2 0)) =
      shake256_absorb_prefix
        (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
        (mode2_highlen + 32)].
proof.
apply
  (verify_absorb_mu32_segment
    (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
    lsb0 mode2_highlen 32 sp0 stp0).
+ by rewrite /mode2_highlen.
+ rewrite mode2_verify_challenge_input_bytes_size /mode2_highlen.
  trivial.
+ trivial.
+ by rewrite /shake256_rate.
qed.

lemma verify_absorb_mu32_mode2_mu
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t)
    (sp0 : BArray200.t) (stp0 : BArray16.t) :
  hoare [Verify.__verify_shake256_absorb_mu32 :
    sp_0 = sp0 /\ statep = stp0 /\ inp = mu0 /\
    BArray16.get64 stp0 0 = W64.of_int 64 /\
    (KeygenShakeStreamSpec.state_bytes_le sp0, 64) =
      shake256_absorb_prefix
        (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
        (mode2_highlen + 32) /\
    absorb32_segment_matches
      (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
      (mode2_highlen + 32) mu0
    ==>
    (KeygenShakeStreamSpec.state_bytes_le res.`1,
     W64.to_uint (BArray16.get64 res.`2 0)) =
      shake256_absorb_prefix
        (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
        (mode2_highlen + 32 + 32)].
proof.
apply
  (verify_absorb_mu32_segment
    (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
    mu0 (mode2_highlen + 32) 64 sp0 stp0).
+ by rewrite /mode2_highlen.
+ rewrite mode2_verify_challenge_input_bytes_size /mode2_highlen.
  trivial.
+ trivial.
+ by rewrite /shake256_rate.
qed.

lemma verify_challenge_finalize_at
    (sp0 : BArray200.t) (stp0 : BArray16.t) (pos0 : int) :
  0 <= pos0 < shake256_rate =>
  hoare [Verify.__poly_challenge_shake256_finalize :
    sp_0 = sp0 /\ statep = stp0 /\
    BArray16.get64 stp0 0 = W64.of_int pos0
    ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      shake256_finalize_at
        (KeygenShakeStreamSpec.state_bytes_le sp0) pos0].
proof.
move=> hpos.
proc.
auto => />.
move=> hstpos.
rewrite /protect_64 /protect_ptr hstpos.
rewrite generated_finalize_paddingE generated_finalize_domainE.
rewrite state_bytes_le_absorb_byte_word 1:/#.
rewrite /shake256_finalize_at /shake256_rate
        W64.of_uintK !W8.of_uintK /=.
apply (congr1 (fun st => state_xor_byte st 135 128)).
rewrite state_bytes_le_absorb_byte.
+ move: hpos.
  rewrite /shake256_rate.
  smt().
by rewrite W8.of_uintK /=.
qed.

lemma verify_challenge_finalize_96
    (sp0 : BArray200.t) (stp0 : BArray16.t) :
  hoare [Verify.__poly_challenge_shake256_finalize :
    sp_0 = sp0 /\ statep = stp0 /\
    BArray16.get64 stp0 0 = W64.of_int 96
    ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      shake256_finalize_at
        (KeygenShakeStreamSpec.state_bytes_le sp0) 96].
proof.
apply (verify_challenge_finalize_at sp0 stp0 96).
by rewrite /shake256_rate.
qed.

(* Partial correctness only.  This identifies the padded pre-squeeze state of
   the generated mode-2 Verify transcript; it does not prove termination,
   distributional sampling claims, or equality with the paper challenge. *)
lemma verify_challenge_absorb_mode2_transcript_state
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t)
    (sp0 : BArray200.t) :
  hoare [Verify.__verify_challenge_absorb :
    sp_0 = sp0 /\ highp = high0 /\
    highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      mode2_verify_challenge_absorb_state high0 lsb0 mu0].
proof.
proc.
seq 6 :
  (highp = high0 /\ highlen = W64.of_int mode2_highlen /\
   lsbp = lsb0 /\ mup = mu0 /\
   KeygenShakeStreamSpec.state_bytes_le sp_0 = zero_state_bytes /\
   BArray16.get64 stp 0 = W64.zero).
+ wp.
  call verify_keccak_init_state_zero_bytes.
  auto => />.
seq 1 :
  (highp = high0 /\ highlen = W64.of_int mode2_highlen /\
   lsbp = lsb0 /\ mup = mu0 /\
   (KeygenShakeStreamSpec.state_bytes_le sp_0,
    W64.to_uint (BArray16.get64 stp 0)) =
      shake256_absorb_prefix
        (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
        mode2_highlen).
+ exlim sp_0 => before_high_state.
  exlim stp => before_high_pos.
  call (verify_absorb_buf_mode2
    high0 lsb0 mu0 before_high_state before_high_pos).
  auto => />.
seq 1 :
  (highp = high0 /\ highlen = W64.of_int mode2_highlen /\
   lsbp = lsb0 /\ mup = mu0 /\
   (KeygenShakeStreamSpec.state_bytes_le sp_0,
    W64.to_uint (BArray16.get64 stp 0)) =
      shake256_absorb_prefix
        (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
        (mode2_highlen + 32)).
+ exlim sp_0 => before_lsb_state.
  exlim stp => before_lsb_pos.
  call (verify_absorb_mu32_mode2_lsb
    high0 lsb0 mu0 before_lsb_state before_lsb_pos).
  auto => />.
  move=> hpair.
  have [hword hpair32] := mode2_absorb_high_pair_bridge
    high0 lsb0 mu0 before_lsb_state before_lsb_pos hpair.
  split; first exact hword.
  split; first exact hpair32.
  exact (mode2_lsb_segment_matches high0 lsb0 mu0).
seq 1 :
  ((KeygenShakeStreamSpec.state_bytes_le sp_0,
    W64.to_uint (BArray16.get64 stp 0)) =
      shake256_absorb_prefix
        (mode2_verify_challenge_input_bytes high0 lsb0 mu0)
        (mode2_highlen + 32 + 32)).
+ exlim sp_0 => before_mu_state.
  exlim stp => before_mu_pos.
  call (verify_absorb_mu32_mode2_mu
    high0 lsb0 mu0 before_mu_state before_mu_pos).
  auto => />.
  move=> hpair.
  have [hword hpair64] := mode2_absorb_lsb_pair_bridge
    high0 lsb0 mu0 before_mu_state before_mu_pos hpair.
  split; first exact hword.
  split; first exact hpair64.
  exact (mode2_mu_segment_matches high0 lsb0 mu0).
exlim sp_0 => before_finalize_state.
exlim stp => before_finalize_pos.
call (verify_challenge_finalize_96
  before_finalize_state before_finalize_pos).
auto => />.
move=> hpair.
have [hword hpair96] := mode2_absorb_mu_pair_bridge
  high0 lsb0 mu0 before_finalize_state before_finalize_pos hpair.
split; first exact hword.
move=> result hresult.
rewrite /mode2_verify_challenge_absorb_state
        /mode2_verify_challenge_absorb_pair.
rewrite mode2_absorb_position_mu.
have hstate := congr1 fst _ _ hpair96.
by rewrite -hstate.
qed.

lemma verify_challenge_m23_stream_trace_mode2_absorb
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [Trace.run :
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    Trace.observed_squeeze_initial = mode2_state high0 lsb0 mu0].
proof.
proc.
seq 18 :
  (Trace.observed_squeeze_initial = mode2_state high0 lsb0 mu0).
+ wp.
  call (verify_challenge_absorb_mode2_transcript_state
    high0 lsb0 mu0 witness).
  auto => />.
wp.
while (Trace.observed_squeeze_initial = mode2_state high0 lsb0 mu0).
+ wp.
  if.
  + wp.
    call (_ : true ==> true); first by auto.
    auto.
  + auto.
wp.
call (_ : true ==> true); first by auto.
wp.
call (_ : true ==> true); first by auto.
auto.
qed.

(* Partial correctness only.  These compositions remove the formerly opaque
   squeeze start state, but do not prove sampler termination, a distributional
   claim, or equality with the paper-level challenge abstraction. *)
lemma verify_challenge_m23_stream_trace_mode2_absorb_squeeze_replay
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [Trace.run :
    tau = W64.of_int
      VerifyChallengeM23StreamSamplerPostFreeze.mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    Trace.observed_squeeze_initial = mode2_state high0 lsb0 mu0 /\
    1 <= Trace.observed_loaded_blocks /\
    0 <= Trace.observed_final_pos <= 136 /\
    KeygenShakeStreamSpec.state_bytes_le Trace.observed_final_state =
      KeygenShakeStreamSpec.squeeze_state_iter
        Trace.observed_squeeze_initial Trace.observed_loaded_blocks /\
    Trace.observed_bytes =
      VerifyChallengeM23StreamSamplerPostFreeze.challenge_squeeze_consumed_prefix
          Trace.observed_squeeze_initial Trace.observed_loaded_blocks
          Trace.observed_final_pos /\
    VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_replay
      Trace.observed_init_cp Trace.observed_start_i Trace.observed_bytes =
      (Trace.observed_final_cp, Trace.observed_final_i) /\
    res = Trace.observed_final_cp /\
    Trace.observed_final_i =
      VerifyChallengeM23StreamSamplerPostFreeze.challenge_words].
proof.
conseq
  (verify_challenge_m23_stream_trace_mode2_absorb high0 lsb0 mu0)
  VerifyChallengeM23StreamSamplerPostFreeze.verify_challenge_m23_stream_trace_squeeze_replay;
  auto.
qed.

lemma verify_challenge_m23_stream_trace_mode2_concrete_squeeze_replay
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  hoare [Trace.run :
    tau = W64.of_int
      VerifyChallengeM23StreamSamplerPostFreeze.mode2_tau /\
    highp = high0 /\ highlen = W64.of_int mode2_highlen /\
    lsbp = lsb0 /\ mup = mu0
    ==>
    Trace.observed_squeeze_initial = mode2_state high0 lsb0 mu0 /\
    1 <= Trace.observed_loaded_blocks /\
    0 <= Trace.observed_final_pos <= 136 /\
    KeygenShakeStreamSpec.state_bytes_le Trace.observed_final_state =
      KeygenShakeStreamSpec.squeeze_state_iter
        (mode2_state high0 lsb0 mu0) Trace.observed_loaded_blocks /\
    Trace.observed_bytes =
      VerifyChallengeM23StreamSamplerPostFreeze.challenge_squeeze_consumed_prefix
          (mode2_state high0 lsb0 mu0) Trace.observed_loaded_blocks
          Trace.observed_final_pos /\
    VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_replay
      Trace.observed_init_cp Trace.observed_start_i Trace.observed_bytes =
      (Trace.observed_final_cp, Trace.observed_final_i) /\
    res = Trace.observed_final_cp /\
    Trace.observed_final_i =
      VerifyChallengeM23StreamSamplerPostFreeze.challenge_words].
proof.
conseq
  (verify_challenge_m23_stream_trace_mode2_absorb_squeeze_replay
    high0 lsb0 mu0).
+ auto.
qed.

lemma verify_challenge_m23_actual_mode2_concrete_squeeze_replay
    (high0 : BArray1152.t) (lsb0 mu0 : BArray32.t) :
  equiv [Verify.__verify_challenge_m23 ~ Trace.run :
    ={Glob.mem, cp, highp, highlen, lsbp, mup, tau} /\
    tau{1} = W64.of_int
      VerifyChallengeM23StreamSamplerPostFreeze.mode2_tau /\
    highp{1} = high0 /\ highlen{1} = W64.of_int mode2_highlen /\
    lsbp{1} = lsb0 /\ mup{1} = mu0
    ==>
    ={Glob.mem, res} /\
    Trace.observed_squeeze_initial{2} = mode2_state high0 lsb0 mu0 /\
    1 <= Trace.observed_loaded_blocks{2} /\
    0 <= Trace.observed_final_pos{2} <= 136 /\
    KeygenShakeStreamSpec.state_bytes_le Trace.observed_final_state{2} =
      KeygenShakeStreamSpec.squeeze_state_iter
        (mode2_state high0 lsb0 mu0) Trace.observed_loaded_blocks{2} /\
    Trace.observed_bytes{2} =
      VerifyChallengeM23StreamSamplerPostFreeze.challenge_squeeze_consumed_prefix
        (mode2_state high0 lsb0 mu0) Trace.observed_loaded_blocks{2}
        Trace.observed_final_pos{2} /\
    VerifyChallengeM23StreamSamplerPostFreeze.stream_sampler_replay
      Trace.observed_init_cp{2} Trace.observed_start_i{2}
      Trace.observed_bytes{2} =
      (Trace.observed_final_cp{2}, Trace.observed_final_i{2}) /\
    res{2} = Trace.observed_final_cp{2} /\
    Trace.observed_final_i{2} =
      VerifyChallengeM23StreamSamplerPostFreeze.challenge_words].
proof.
conseq
  VerifyChallengeM23StreamSamplerPostFreeze.verify_challenge_m23_exact_stream_trace
  (_ : true ==> true)
  (verify_challenge_m23_stream_trace_mode2_concrete_squeeze_replay
    high0 lsb0 mu0) => //=.
move=> &1 &2 [heq [htau [hhigh [hhighlen [hlsb hmu]]]]].
split; first exact heq.
move: heq htau hhigh hhighlen hlsb hmu.
smt().
qed.

end VerifyChallengeAbsorbStatePostFreeze.
