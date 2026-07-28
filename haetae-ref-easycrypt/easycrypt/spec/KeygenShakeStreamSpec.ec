require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import
  BArray128 BArray200 BArray1024
  HAETAE_Keccak1600 HAETAE_FIPS202 KeygenKeccak1600Spec.

theory KeygenShakeStreamSpec.

op zero_lanes (state : BArray200.t) : bool =
  forall lane,
    0 <= lane < 25 =>
    BArray200.get64 state lane = W64.zero.

op seed_byte64 (seed : BArray128.t) (seedoff : W64.t) (i : int) : W8.t =
  BArray128.get8 seed
    (W64.to_uint (seedoff + W64.of_int i)).

op absorb_byte
    (state : BArray200.t) (b : W8.t) (pos : W64.t) : BArray200.t =
  let lane = pos `>>` (W8.of_int 3) in
  let shift =
    ((truncateu8 pos) `&` (W8.of_int 7)) `<<` (W8.of_int 3) in
  let t =
    (zeroextu64 b) `<<` (shift `&` (W8.of_int 63)) in
  BArray200.set64 state (W64.to_uint lane)
    ((BArray200.get64 state (W64.to_uint lane)) `^` t).

op seed_step
    (seed : BArray128.t) (seedoff : W64.t)
    (state : BArray200.t) (i : int) : BArray200.t =
  absorb_byte state (seed_byte64 seed seedoff i) (W64.of_int i).

op seed_absorb
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff : W64.t) (count : int) : BArray200.t =
  foldl (seed_step seed seedoff) state (iota_ 0 count).

type nonce_acc = BArray200.t * W64.t * W64.t.

op nonce_step (acc : nonce_acc) (_ : int) : nonce_acc =
  (absorb_byte acc.`1 (truncateu8 acc.`2) acc.`3,
   acc.`2 `>>` (W8.of_int 8),
   acc.`3 + W64.one).

op nonce_run (acc : nonce_acc) (count : int) : nonce_acc =
  foldl nonce_step acc (iota_ 0 count).

op finalize_shake
    (state : BArray200.t) (domain_lane final_lane : int) : BArray200.t =
  let domain = (W64.of_int 31) `<<` (W8.of_int 16) in
  let state =
    BArray200.set64 state domain_lane
      ((BArray200.get64 state domain_lane) `^` domain) in
  let final = W64.one `<<` (W8.of_int 63) in
  BArray200.set64 state final_lane
    ((BArray200.get64 state final_lane) `^` final).

op finalize_shake128 (state : BArray200.t) : BArray200.t =
  finalize_shake state 4 20.

op finalize_shake256 (state : BArray200.t) : BArray200.t =
  finalize_shake state 8 16.

op shake_seedbuf_framing
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff nonce : W64.t) (seed_count domain_lane final_lane : int) : bool =
  exists initial,
    zero_lanes initial /\
    state =
      finalize_shake
        (nonce_run
          (seed_absorb initial seed seedoff seed_count,
           nonce, W64.of_int seed_count)
          2).`1
        domain_lane final_lane.

op shake128_seedbuf_framing
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff nonce : W64.t) : bool =
  shake_seedbuf_framing state seed seedoff nonce 32 4 20.

op shake256_seedbuf_framing
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff nonce : W64.t) : bool =
  shake_seedbuf_framing state seed seedoff nonce 64 8 16.

op drop_byte (w : W64.t) (_ : int) : W64.t =
  w `>>` (W8.of_int 8).

op drop_bytes (w : W64.t) (count : int) : W64.t =
  foldl drop_byte w (iota_ 0 count).

op rate_lane_byte
    (state : BArray200.t) (lane byte : int) : W8.t =
  truncateu8 (drop_bytes (BArray200.get64 state lane) byte).

op rate_prefix_matches
    (out : BArray1024.t) (outoff : int)
    (state : BArray200.t) (count : int) : bool =
  forall lane byte,
    0 <= lane =>
    0 <= byte < 8 =>
    8 * lane + byte < count =>
    BArray1024.get8 out (outoff + 8 * lane + byte) =
      rate_lane_byte state lane byte.

op rate_block_matches
    (out : BArray1024.t) (outoff : int)
    (state : BArray200.t) (rate : int) : bool =
  rate_prefix_matches out outoff state rate.

op rate_block_frame
    (before after : BArray1024.t) (outoff rate : int) : bool =
  forall byte_index,
    0 <= byte_index < BArray1024.size =>
    !(outoff <= byte_index < outoff + rate) =>
    BArray1024.get8 after byte_index =
      BArray1024.get8 before byte_index.

op state_bytes_le (state : BArray200.t) : int list =
  mkseq (fun i => W8.to_uint (BArray200.get8 state i)) 200.

op shake128_rate_bytes : int = 168.

op seed_nonce_input
    (seed : BArray128.t) (seedoff nonce : W64.t)
    (seed_count : int) : int list =
  mkseq
    (fun i =>
       if i < seed_count then
         W8.to_uint
           (BArray128.get8 seed (W64.to_uint seedoff + i))
       else if i = seed_count then
         W64.to_uint nonce %% 256
       else
         (W64.to_uint nonce %/ 256) %% 256)
    (seed_count + 2).

op shake128_seed_nonce_input
    (seed : BArray128.t) (seedoff nonce : W64.t) : int list =
  seed_nonce_input seed seedoff nonce 32.

op shake256_seed_nonce_input
    (seed : BArray128.t) (seedoff nonce : W64.t) : int list =
  seed_nonce_input seed seedoff nonce 64.

op shake128_absorb_once_short_block_byte
    (input : int list) (inlen i : int) : int =
  if 0 <= i /\ i < inlen then nth 0 input i
  else if i = inlen /\ i = shake128_rate_bytes - 1 then
    HAETAE_FIPS202.shake256_domain_separator +
    HAETAE_FIPS202.fips202_final_padding_byte
  else if i = inlen then
    HAETAE_FIPS202.shake256_domain_separator
  else if i = shake128_rate_bytes - 1 then
    HAETAE_FIPS202.fips202_final_padding_byte
  else 0.

op shake128_absorb_once_short_state
    (input : int list) (inlen : int) : int list =
  mkseq
    (fun i =>
       if i < shake128_rate_bytes then
         shake128_absorb_once_short_block_byte input inlen i
       else 0)
    200.

op shake128_absorb_once (input : int list) (inlen : int) : int list =
  HAETAE_Keccak1600.keccak_f1600_bytes
    (shake128_absorb_once_short_state input inlen).

op shake128_seed_nonce_padded_state
    (seed : BArray128.t) (seedoff nonce : W64.t) : int list =
  shake128_absorb_once_short_state
    (shake128_seed_nonce_input seed seedoff nonce) 34.

op shake256_seed_nonce_padded_state
    (seed : BArray128.t) (seedoff nonce : W64.t) : int list =
  HAETAE_FIPS202.shake256_absorb_once_short_state
    (shake256_seed_nonce_input seed seedoff nonce) 66.

op shake128_seed_nonce_state
    (seed : BArray128.t) (seedoff nonce : W64.t) : int list =
  shake128_absorb_once
    (shake128_seed_nonce_input seed seedoff nonce) 34.

op shake256_seed_nonce_state
    (seed : BArray128.t) (seedoff nonce : W64.t) : int list =
  HAETAE_FIPS202.shake256_absorb_once
    (shake256_seed_nonce_input seed seedoff nonce) 66.

op fips_rate_prefix_matches
    (out : BArray1024.t) (outoff : int)
    (bytes : int list) (count : int) : bool =
  forall i,
    0 <= i < count =>
    W8.to_uint (BArray1024.get8 out (outoff + i)) = nth 0 bytes i.

lemma state_bytes_le_size state : size (state_bytes_le state) = 200.
proof. by rewrite /state_bytes_le size_mkseq. qed.

lemma state_bytes_le_nth state i :
  0 <= i < 200 =>
  nth 0 (state_bytes_le state) i =
  W8.to_uint (BArray200.get8 state i).
proof. by move=> hi; rewrite /state_bytes_le nth_mkseq. qed.

lemma get64_bit_get8 state lane bit :
  0 <= lane < 25 =>
  0 <= bit < 64 =>
  (BArray200.get64 state lane).[bit] =
  (BArray200.get8 state (8 * lane + bit %/ 8)).[bit %% 8].
proof.
move=> hlane hbit.
rewrite W8u8.get_bits8 1:/#.
rewrite BArray200.get64d_byte 1:/#.
congr.
qed.

lemma state_of_barray_state_bytes_le state :
  KeygenKeccak1600Spec.state_of_barray state =
  HAETAE_Keccak1600.keccak_lanes_of_bytes (state_bytes_le state).
proof.
apply/(eq_from_nth HAETAE_Keccak1600.keccak_lane_zero).
+ by rewrite KeygenKeccak1600Spec.state_of_barray_size
             HAETAE_Keccak1600.keccak_lanes_of_bytes_size.
move=> lane.
rewrite KeygenKeccak1600Spec.state_of_barray_size
        HAETAE_Keccak1600.keccak_state_lanesE => hlane.
rewrite KeygenKeccak1600Spec.state_of_barray_laneE 1://.
apply/(eq_from_nth false).
+ rewrite KeygenKeccak1600Spec.lane_of_word_size.
  have hwf := HAETAE_Keccak1600.keccak_lanes_of_bytes_lane_wf
    (state_bytes_le state) lane hlane.
  rewrite /HAETAE_Keccak1600.keccak_lane_wf in hwf.
  by rewrite hwf.
move=> bit.
rewrite KeygenKeccak1600Spec.lane_of_word_size
        HAETAE_Keccak1600.keccak_lane_bitsE => hbit.
rewrite /KeygenKeccak1600Spec.lane_of_word nth_mkseq 1://.
rewrite /HAETAE_Keccak1600.keccak_lanes_of_bytes nth_mkseq 1://.
rewrite /HAETAE_Keccak1600.keccak_bytes_to_lane nth_mkseq 1://.
rewrite /HAETAE_Keccak1600.keccak_byte_bit
        /HAETAE_Keccak1600.keccak_byte_norm.
rewrite /= state_bytes_le_nth 1:/#.
have hpack := get64_bit_get8 state lane bit hlane hbit.
have hmod : 0 <= bit %% 8 < 8 by smt(modz_cmp).
have hword := W8.get_to_uint
  (BArray200.get8 state (8 * lane + bit %/ 8)) (bit %% 8).
have hbyte := W8.to_uint_cmp
  (BArray200.get8 state (8 * lane + bit %/ 8)).
rewrite hpack hword hmod /=.
by rewrite (modz_small (W8.to_uint
  (BArray200.get8 state (8 * lane + bit %/ 8))) 256) 1:/#.
qed.

lemma seed_absorb0 state seed seedoff :
  seed_absorb state seed seedoff 0 = state.
proof. by rewrite /seed_absorb iota0. qed.

lemma seed_absorb_succ state seed seedoff count :
  0 <= count =>
  seed_absorb state seed seedoff (count + 1) =
    seed_step seed seedoff
      (seed_absorb state seed seedoff count) count.
proof.
move=> hcount.
by rewrite /seed_absorb iotaSr 1:// foldl_rcons.
qed.

lemma nonce_run0 acc : nonce_run acc 0 = acc.
proof. by rewrite /nonce_run iota0. qed.

lemma nonce_run_succ acc count :
  0 <= count =>
  nonce_run acc (count + 1) = nonce_step (nonce_run acc count) count.
proof.
move=> hcount.
by rewrite /nonce_run iotaSr 1:// foldl_rcons.
qed.

lemma drop_bytes0 w : drop_bytes w 0 = w.
proof. by rewrite /drop_bytes iota0. qed.

lemma drop_bytes_succ w count :
  0 <= count =>
  drop_bytes w (count + 1) =
    drop_bytes w count `>>` (W8.of_int 8).
proof.
move=> hcount.
by rewrite /drop_bytes iotaSr 1:// foldl_rcons /drop_byte.
qed.

lemma rate_prefix_zero out outoff state :
  rate_prefix_matches out outoff state 0.
proof. by rewrite /rate_prefix_matches => lane byte /#. qed.

lemma rate_prefix_set_next out outoff state count lane byte :
  0 <= outoff =>
  count = 8 * lane + byte =>
  0 <= lane =>
  0 <= byte < 8 =>
  outoff + count < BArray1024.size =>
  rate_prefix_matches out outoff state count =>
  rate_prefix_matches
    (BArray1024.set8 out (outoff + count)
      (rate_lane_byte state lane byte))
    outoff state (count + 1).
proof.
rewrite /rate_prefix_matches.
move=> hoff hcount hlane hbyte hcap hprefix lane0 byte0
        hlane0 hbyte0 hlt.
case (8 * lane0 + byte0 = count) => heq.
+ have -> : lane0 = lane by smt().
  have -> : byte0 = byte by smt().
  rewrite BArray1024.set_eqiE 1:/# 1:/#.
  trivial.
rewrite BArray1024.set_neqiE 1:/#.
have hprev : 8 * lane0 + byte0 < count by smt().
exact (hprefix lane0 byte0 hlane0 hbyte0 hprev).
qed.

lemma div8_split i :
  0 <= i => i %% 8 = 0 => i = 8 * (i %/ 8).
proof.
move=> hi hmod.
have hdiv := divz_eq i 8.
smt().
qed.

lemma rate_prefix_set_cursor out outoff state i j :
  0 <= outoff =>
  0 <= i =>
  i %% 8 = 0 =>
  0 <= j < 8 =>
  outoff + (i + j) < BArray1024.size =>
  rate_prefix_matches out outoff state (i + j) =>
  rate_prefix_matches
    (BArray1024.set8 out (outoff + (i + j))
      (rate_lane_byte state (i %/ 8) j))
    outoff state (i + j + 1).
proof.
move=> hoff hi himod hj hcap hprefix.
apply (rate_prefix_set_next out outoff state (i + j) (i %/ 8) j).
+ exact hoff.
+ have hi8 := div8_split i hi himod.
  smt().
+ have hd : 0 < 8 by smt().
  have hdiv := divz_ge0 i 8 hd.
  smt().
+ exact hj.
+ exact hcap.
exact hprefix.
qed.

lemma rate_block_frame_refl out outoff rate :
  rate_block_frame out out outoff rate.
proof. by rewrite /rate_block_frame. qed.

lemma rate_block_frame_set_inside before current outoff rate count w :
  0 <= outoff =>
  0 <= count < rate =>
  outoff + rate <= BArray1024.size =>
  rate_block_frame before current outoff rate =>
  rate_block_frame before
    (BArray1024.set8 current (outoff + count) w) outoff rate.
proof.
rewrite /rate_block_frame.
move=> hoff hcount hcap hframe byte_index hindex hout.
rewrite BArray1024.set_neqiE 1:/#.
exact (hframe byte_index hindex hout).
qed.

lemma zeroextu64_w8_bit (b : W8.t) bit :
  (W8u8.zeroextu64 b).[bit] = (0 <= bit < 8 /\ b.[bit]).
proof.
case (0 <= bit < 64) => hbit.
+ rewrite W8u8.zeroextu64E W8u8.pack8wE 1://.
  have hq : 0 <= bit %/ 8 < 8 by apply divz_cmp => /#.
  rewrite W8u8.Pack.initiE 1:hq.
  case (bit %/ 8 = 0) => hbyte /=.
  + have hsmall : 0 <= bit < 8 by smt(divz_eq modz_cmp).
    have -> : bit %% 8 = bit by smt(divz_eq modz_cmp).
    by rewrite hsmall hbyte /=.
  have : 8 <= bit by smt(divz_eq modz_cmp).
  by smt().
rewrite W64.get_out 1://.
by smt().
qed.

lemma shifted_byte_bits8 (b : W8.t) byte target :
  0 <= byte < 8 =>
  0 <= target < 8 =>
  ((W8u8.zeroextu64 b) `<<` (W8.of_int (8 * byte))) \bits8 target =
  if target = byte then b else W8.zero.
proof.
move=> hbyte htarget.
apply W8.wordP => bit hbit.
rewrite W8u8.bits8iE 1://.
rewrite /(`<<`) W64.shlwE.
rewrite W8.of_uintK (modz_small (8 * byte) 256) 1:/# /=.
rewrite zeroextu64_w8_bit.
case (target = byte) => hsame /=.
+ have -> : target * 8 + bit - 8 * byte = bit by smt().
  have hpos : 0 <= target * 8 + bit < 64 by smt().
  by rewrite hpos hbit /=.
have hpos : 0 <= target * 8 + bit < 64 by smt().
have hout : !(0 <= target * 8 + bit - 8 * byte < 8) by smt().
by rewrite hpos hout /=.
qed.

lemma absorb_byte_at_int_get8
    (state : BArray200.t) (b : W8.t) p i :
  0 <= p < 200 =>
  0 <= i < 200 =>
  BArray200.get8 (absorb_byte state b (W64.of_int p)) i =
  if i = p then BArray200.get8 state i `^` b
  else BArray200.get8 state i.
proof.
move=> hp hi.
rewrite /absorb_byte /=.
rewrite W64.shr_div_le 1:/# /=.
rewrite W64.of_uintK (modz_small p W64.modulus) 1:/# /=.
rewrite BArray200.get8_set64dE.
have hshift :
  ((((truncateu8 (W64.of_int p)) `&` (W8.of_int 7))
      `<<` (W8.of_int 3)) `&` (W8.of_int 63)) =
  W8.of_int (8 * (p %% 8)).
+ apply W8.to_uint_eq.
  rewrite (W8.to_uint_and_mod 6) 1:/#.
  rewrite /(`<<`) W8.to_uint_shl 1:/#.
  rewrite (W8.to_uint_and_mod 3) 1:/#.
  rewrite /truncateu8 W64.of_uintK
          (modz_small p W64.modulus) 1:/#.
  rewrite !W8.of_uintK.
  simplify.
  rewrite (modz_small p 256) 1:/#.
  have hp8 : 0 <= p %% 8 < 8 by smt(modz_cmp).
  rewrite (modz_small (8 * (p %% 8)) 256) 1:/#.
  have -> : p %% 8 * 8 = 8 * (p %% 8) by ring.
  rewrite (modz_small (8 * (p %% 8)) 256) 1:/#.
  rewrite (modz_small (8 * (p %% 8)) 64) 1:/#.
  ring.
rewrite hshift.
case (8 * (p %/ 8) <= i < 8 * (p %/ 8) + 8) => hin /=.
+ rewrite hi /=.
  rewrite BArray200.get64d_byte 1:/#.
  have -> : 8 * (p %/ 8) + (i - 8 * (p %/ 8)) = i by ring.
  rewrite shifted_byte_bits8 1:/# 1:/#.
  have hpE : p = 8 * (p %/ 8) + p %% 8.
  + have hpdiv := divz_eq p 8.
    smt().
  case (i = p) => heq.
  + subst i.
    have -> : p - 8 * (p %/ 8) = p %% 8 by smt().
    trivial.
  have hne : i - 8 * (p %/ 8) <> p %% 8 by smt().
  rewrite hne /=.
  trivial.
have hpmod : 0 <= p %% 8 < 8 by smt(modz_cmp).
have hpdiv := divz_eq p 8.
have hne : i <> p by smt().
by rewrite hne.
qed.

lemma zero_lanes_get8 (state : BArray200.t) i :
  zero_lanes state =>
  0 <= i < 200 =>
  BArray200.get8 state i = W8.zero.
proof.
move=> hzero hi.
have hlane : 0 <= i %/ 8 < 25 by apply divz_cmp => /#.
have hbyte : 0 <= i %% 8 < 8 by smt(modz_cmp).
have hlanezero := hzero (i %/ 8) hlane.
have hget := BArray200.get64d_byte
  state (8 * (i %/ 8)) (i %% 8) hbyte.
have hiE : i = 8 * (i %/ 8) + i %% 8.
+ have hdiv := divz_eq i 8.
  smt().
rewrite hiE -hget hlanezero W8u8.get_zero.
trivial.
qed.

op seed_prefix
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff : W64.t) (count : int) : bool =
  forall i,
    0 <= i < 200 =>
    BArray200.get8 state i =
      if i < count then
        BArray128.get8 seed (W64.to_uint seedoff + i)
      else W8.zero.

lemma seed_prefix_step state seed seedoff count :
  0 <= count < 200 =>
  W64.to_uint seedoff + count < BArray128.size =>
  seed_prefix state seed seedoff count =>
  seed_prefix (seed_step seed seedoff state count)
    seed seedoff (count + 1).
proof.
rewrite /seed_prefix.
move=> hcount hcap hprefix i hi.
rewrite /seed_step absorb_byte_at_int_get8 1:// 1://.
case (i = count) => heq.
+ have hprev := hprefix i hi.
  rewrite hprev (_ : !(i < count)) 1:/# /=.
  rewrite (_ : i < count + 1) 1:/# /=.
  rewrite /seed_byte64.
  have hnowrap :
    W64.to_uint seedoff + W64.to_uint (W64.of_int count) <
      W64.modulus.
  + rewrite W64.of_uintK (modz_small count W64.modulus) 1:/#.
    smt(W64.to_uint_cmp).
  rewrite W64.to_uintD_small 1:hnowrap.
  rewrite W64.of_uintK (modz_small count W64.modulus) 1:/# /=.
  rewrite heq.
  trivial.
+ have hltE : (i < count + 1) = (i < count) by smt().
  rewrite hltE.
  exact (hprefix i hi).
qed.

lemma seed_absorb_prefix initial seed seedoff count :
  zero_lanes initial =>
  0 <= count =>
  W64.to_uint seedoff + count <= BArray128.size =>
  seed_prefix (seed_absorb initial seed seedoff count)
    seed seedoff count.
proof.
move=> hzero.
move: count.
apply intind.
+ move=> _.
  rewrite seed_absorb0 /seed_prefix.
  move=> i hi.
  rewrite (_ : !(i < 0)) 1:/# /=.
  exact (zero_lanes_get8 initial i hzero hi).
+ move=> count hcount ih hcap.
  rewrite /BArray128.size in hcap.
  have hseedoff : 0 <= W64.to_uint seedoff by smt(W64.to_uint_cmp).
  rewrite seed_absorb_succ 1://.
  apply seed_prefix_step.
  + smt().
  + smt().
  apply ih.
  smt().
qed.

op seed_nonce_prefix
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff nonce : W64.t) (count : int) : bool =
  forall i,
    0 <= i < 200 =>
    BArray200.get8 state i =
      if i < count then
        BArray128.get8 seed (W64.to_uint seedoff + i)
      else if i = count then truncateu8 nonce
      else if i = count + 1 then
        truncateu8 (nonce `>>` (W8.of_int 8))
      else W8.zero.

lemma nonce_run2_prefix state seed seedoff nonce count :
  0 <= count /\ count + 2 < 200 =>
  seed_prefix state seed seedoff count =>
  seed_nonce_prefix
    (nonce_run (state, nonce, W64.of_int count) 2).`1
    seed seedoff nonce count.
proof.
move=> hcount hprefix.
rewrite /nonce_run.
rewrite (iotaSr 0 1) 1:/# foldl_rcons.
rewrite (iotaSr 0 0) 1:/# foldl_rcons.
rewrite iota0 1:/# /=.
rewrite /nonce_step /=.
rewrite /nonce_step /=.
rewrite /seed_nonce_prefix.
move=> i hi.
rewrite absorb_byte_at_int_get8 1:/# 1://.
rewrite absorb_byte_at_int_get8 1:/# 1://.
case (i = count + 1) => hi1.
+ have hneq : i <> count by smt().
  rewrite hneq (_ : !(i < count)) 1:/# /=.
  rewrite hprefix 1:// (_ : !(i < count)) 1:/# /=.
  trivial.
case (i = count) => hi0.
+ rewrite (_ : !(i < count)) 1:/# /=.
  rewrite hprefix 1:// (_ : !(i < count)) 1:/# /=.
  trivial.
exact (hprefix i hi).
qed.

op xor_lane_byte
    (state : BArray200.t) (lane byte : int) (b : W8.t) : BArray200.t =
  BArray200.set64 state lane
    (BArray200.get64 state lane `^`
     ((W8u8.zeroextu64 b) `<<` (W8.of_int (8 * byte)))).

lemma finalize_domain_word :
  (W64.of_int 31) `<<` (W8.of_int 16) =
  (W8u8.zeroextu64 (W8.of_int 31)) `<<` (W8.of_int (8 * 2)).
proof.
have hbase : W64.of_int 31 = W8u8.zeroextu64 (W8.of_int 31).
+ apply W64.to_uint_eq.
  rewrite W8u8.to_uint_zeroextu64 W64.of_uintK W8.of_uintK /=.
  trivial.
rewrite hbase /=.
trivial.
qed.

lemma finalize_padding_word :
  W64.one `<<` (W8.of_int 63) =
  (W8u8.zeroextu64 (W8.of_int 128)) `<<` (W8.of_int (8 * 7)).
proof.
apply W64.to_uint_eq.
rewrite /(`<<`).
rewrite !W64.to_uint_shl; 1,2: smt(W8.to_uint_cmp).
rewrite W64.to_uint1 W8u8.to_uint_zeroextu64 !W8.of_uintK /=.
trivial.
qed.

lemma finalize_shake_as_lane_bytes state domain_lane final_lane :
  finalize_shake state domain_lane final_lane =
  xor_lane_byte
    (xor_lane_byte state domain_lane 2 (W8.of_int 31))
    final_lane 7 (W8.of_int 128).
proof.
rewrite /finalize_shake /xor_lane_byte /=
        finalize_domain_word finalize_padding_word.
trivial.
qed.

lemma xor_lane_byte_get8
    (state : BArray200.t) (b : W8.t) lane byte i :
  0 <= lane < 25 =>
  0 <= byte < 8 =>
  0 <= i < 200 =>
  BArray200.get8 (xor_lane_byte state lane byte b) i =
  if i = 8 * lane + byte then BArray200.get8 state i `^` b
  else BArray200.get8 state i.
proof.
move=> hlane hbyte hi.
rewrite /xor_lane_byte BArray200.get8_set64dE.
case (8 * lane <= i < 8 * lane + 8) => hin /=.
+ have htarget : 0 <= i - 8 * lane < 8 by smt().
  rewrite BArray200.get64d_byte 1://.
  rewrite shifted_byte_bits8 1:// 1://.
  smt().
smt().
qed.

op framed_seed_nonce_prefix
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff nonce : W64.t) (count rate : int) : bool =
  forall i,
    0 <= i < 200 =>
    BArray200.get8 state i =
      if i < count then
        BArray128.get8 seed (W64.to_uint seedoff + i)
      else if i = count then truncateu8 nonce
      else if i = count + 1 then
        truncateu8 (nonce `>>` (W8.of_int 8))
      else if i = count + 2 then W8.of_int 31
      else if i = rate - 1 then W8.of_int 128
      else W8.zero.

lemma finalize_seed_nonce_prefix
    state seed seedoff nonce count rate domain_lane final_lane :
  0 <= domain_lane < 25 =>
  0 <= final_lane < 25 =>
  0 <= count =>
  count + 2 < rate - 1 =>
  rate - 1 < 200 =>
  8 * domain_lane + 2 = count + 2 =>
  8 * final_lane + 7 = rate - 1 =>
  seed_nonce_prefix state seed seedoff nonce count =>
  framed_seed_nonce_prefix
    (finalize_shake state domain_lane final_lane)
    seed seedoff nonce count rate.
proof.
move=> hdomain hfinal hcount hsep hrate hdpos hfpos hprefix.
rewrite finalize_shake_as_lane_bytes.
rewrite /framed_seed_nonce_prefix.
move=> i hi.
rewrite xor_lane_byte_get8 1:hfinal 1:/# 1:hi.
rewrite xor_lane_byte_get8 1:hdomain 1:/# 1:hi.
case (i = rate - 1) => hirate.
+ have hfinalpos : i = 8 * final_lane + 7 by smt().
  have hdomainpos : i <> 8 * domain_lane + 2 by smt().
  have hnotdomain : i <> count + 2 by smt().
  have hiseed_r : !(i < count) by smt().
  have hinonce0_r : i <> count by smt().
  have hinonce1_r : i <> count + 1 by smt().
  have hp := hprefix i hi.
  rewrite hp hiseed_r hinonce0_r hinonce1_r hnotdomain /=.
  rewrite hdomainpos hfinalpos /=.
  trivial.
case (i = count + 2) => hidomain.
+ subst i.
  have hfinalpos : count + 2 <> 8 * final_lane + 7 by smt().
  have hiseed_d : !(count + 2 < count) by smt().
  have hinonce0_d : count + 2 <> count by smt().
  have hinonce1_d : count + 2 <> count + 1 by smt().
  have hp := hprefix (count + 2) hi.
  rewrite hp hiseed_d hinonce0_d hinonce1_d /=.
  rewrite hfinalpos hdpos /=.
  trivial.
have hfinalpos : i <> 8 * final_lane + 7 by smt().
have hdomainpos : i <> 8 * domain_lane + 2 by smt().
have hp := hprefix i hi.
rewrite hfinalpos hdomainpos hp.
case (i < count) => hiseed /=.
+ trivial.
case (i = count) => hinonce0 /=.
+ trivial.
case (i = count + 1) => hinonce1 /=.
+ trivial.
trivial.
qed.

lemma nonce_low_uint (nonce : W64.t) :
  W8.to_uint (truncateu8 nonce) = W64.to_uint nonce %% 256.
proof. by rewrite W8u8.to_uint_truncateu8. qed.

lemma nonce_high_uint (nonce : W64.t) :
  W8.to_uint (truncateu8 (nonce `>>` (W8.of_int 8))) =
  (W64.to_uint nonce %/ 256) %% 256.
proof.
rewrite W8u8.to_uint_truncateu8.
rewrite W64.shr_div_le 1:/# /=.
trivial.
qed.

lemma seed_nonce_input_nth seed seedoff nonce count i :
  0 <= count =>
  0 <= i < count + 2 =>
  nth 0 (seed_nonce_input seed seedoff nonce count) i =
  if i < count then
    W8.to_uint
      (BArray128.get8 seed (W64.to_uint seedoff + i))
  else if i = count then W64.to_uint nonce %% 256
  else (W64.to_uint nonce %/ 256) %% 256.
proof.
move=> hcount hi.
by rewrite /seed_nonce_input nth_mkseq 1:/#.
qed.

lemma shake128_framing_fips_state
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff nonce : W64.t) :
  W64.to_uint seedoff + 32 <= BArray128.size =>
  shake128_seedbuf_framing state seed seedoff nonce =>
  state_bytes_le state =
    shake128_seed_nonce_padded_state seed seedoff nonce.
proof.
move=> hcap.
rewrite /shake128_seedbuf_framing /shake_seedbuf_framing.
move=> [initial [hzero ->]].
have hseed :
  seed_prefix (seed_absorb initial seed seedoff 32)
    seed seedoff 32.
+ apply seed_absorb_prefix.
  + exact hzero.
  + smt().
  + exact hcap.
have hnonce :
  seed_nonce_prefix
    (nonce_run
      (seed_absorb initial seed seedoff 32,
       nonce, W64.of_int 32) 2).`1
    seed seedoff nonce 32.
+ apply nonce_run2_prefix.
  + smt().
  + exact hseed.
have hfinal :
  framed_seed_nonce_prefix
    (finalize_shake
      (nonce_run
        (seed_absorb initial seed seedoff 32,
         nonce, W64.of_int 32) 2).`1 4 20)
    seed seedoff nonce 32 168.
+ apply (finalize_seed_nonce_prefix
    (nonce_run
      (seed_absorb initial seed seedoff 32,
       nonce, W64.of_int 32) 2).`1
    seed seedoff nonce 32 168 4 20).
  + smt().
  + smt().
  + smt().
  + smt().
  + smt().
  + smt().
  + smt().
  + exact hnonce.
apply/(eq_from_nth 0).
+ rewrite state_bytes_le_size.
  by rewrite /shake128_seed_nonce_padded_state
             /shake128_absorb_once_short_state size_mkseq.
move=> i.
rewrite state_bytes_le_size => hi.
rewrite state_bytes_le_nth 1:hi.
rewrite /shake128_seed_nonce_padded_state
        /shake128_absorb_once_short_state
        nth_mkseq 1:hi
        /shake128_absorb_once_short_block_byte
        /shake128_rate_bytes.
have hf := hfinal i hi.
rewrite /framed_seed_nonce_prefix in hf.
rewrite hf.
case (i < 32) => hseed_i.
+ rewrite seed_nonce_input_nth 1:/# 1:/# /=.
  smt().
+ case (i = 32) => hnonce0.
  + subst i.
    by rewrite seed_nonce_input_nth 1:/# 1:/# /= nonce_low_uint.
  + case (i = 33) => hnonce1.
    + subst i.
      by rewrite seed_nonce_input_nth 1:/# 1:/# /= nonce_high_uint.
    + case (i = 34) => hdomain.
      + subst i.
        by rewrite /HAETAE_FIPS202.shake256_domain_separator /=.
      + case (i = 167) => hpadding.
        + subst i.
          by rewrite /HAETAE_FIPS202.fips202_final_padding_byte /=.
        + have hnotinput : !(0 <= i /\ i < 34) by smt().
          case (i < 168) => hirate /=.
          + rewrite hnonce1 hdomain hpadding hnotinput /=.
            trivial.
          + rewrite hnonce1 hdomain hpadding /=.
            trivial.
qed.

lemma shake256_framing_fips_state
    (state : BArray200.t) (seed : BArray128.t)
    (seedoff nonce : W64.t) :
  W64.to_uint seedoff + 64 <= BArray128.size =>
  shake256_seedbuf_framing state seed seedoff nonce =>
  state_bytes_le state =
    shake256_seed_nonce_padded_state seed seedoff nonce.
proof.
move=> hcap.
rewrite /shake256_seedbuf_framing /shake_seedbuf_framing.
move=> [initial [hzero ->]].
have hseed :
  seed_prefix (seed_absorb initial seed seedoff 64)
    seed seedoff 64.
+ apply seed_absorb_prefix.
  + exact hzero.
  + smt().
  + exact hcap.
have hnonce :
  seed_nonce_prefix
    (nonce_run
      (seed_absorb initial seed seedoff 64,
       nonce, W64.of_int 64) 2).`1
    seed seedoff nonce 64.
+ apply nonce_run2_prefix.
  + smt().
  + exact hseed.
have hfinal :
  framed_seed_nonce_prefix
    (finalize_shake
      (nonce_run
        (seed_absorb initial seed seedoff 64,
         nonce, W64.of_int 64) 2).`1 8 16)
    seed seedoff nonce 64 136.
+ apply (finalize_seed_nonce_prefix
    (nonce_run
      (seed_absorb initial seed seedoff 64,
       nonce, W64.of_int 64) 2).`1
    seed seedoff nonce 64 136 8 16).
  + smt().
  + smt().
  + smt().
  + smt().
  + smt().
  + smt().
  + smt().
  + exact hnonce.
apply/(eq_from_nth 0).
+ rewrite state_bytes_le_size.
  by rewrite /shake256_seed_nonce_padded_state
             /HAETAE_FIPS202.shake256_absorb_once_short_state
             /HAETAE_FIPS202.fips202_state_bytes size_mkseq.
move=> i.
rewrite state_bytes_le_size => hi.
rewrite state_bytes_le_nth 1:hi.
rewrite /shake256_seed_nonce_padded_state
        /HAETAE_FIPS202.shake256_absorb_once_short_state
        /HAETAE_FIPS202.fips202_state_bytes
        nth_mkseq 1:hi
        /HAETAE_FIPS202.shake256_absorb_once_short_block_byte
        /HAETAE_FIPS202.shake256_rate_bytes.
have hf := hfinal i hi.
rewrite /framed_seed_nonce_prefix in hf.
rewrite hf.
case (i < 64) => hseed_i.
+ rewrite seed_nonce_input_nth 1:/# 1:/# /=.
  smt().
+ case (i = 64) => hnonce0.
  + subst i.
    by rewrite seed_nonce_input_nth 1:/# 1:/# /= nonce_low_uint.
  + case (i = 65) => hnonce1.
    + subst i.
      by rewrite seed_nonce_input_nth 1:/# 1:/# /= nonce_high_uint.
    + case (i = 66) => hdomain.
      + subst i.
        by rewrite /HAETAE_FIPS202.shake256_domain_separator /=.
      + case (i = 135) => hpadding.
        + subst i.
          by rewrite /HAETAE_FIPS202.fips202_final_padding_byte /=.
        + have hnotinput : !(0 <= i /\ i < 66) by smt().
          case (i < 136) => hirate /=.
          + rewrite hnonce1 hdomain hpadding hnotinput /=.
            trivial.
          + rewrite hnonce1 hdomain hpadding /=.
            trivial.
qed.

lemma shake128_padding_positions seed seedoff nonce :
  nth 0 (shake128_seed_nonce_padded_state seed seedoff nonce) 34 = 31 /\
  nth 0 (shake128_seed_nonce_padded_state seed seedoff nonce) 167 = 128.
proof.
rewrite /shake128_seed_nonce_padded_state
        /shake128_absorb_once_short_state
        !nth_mkseq 1:/# 1:/# /=.
rewrite /shake128_absorb_once_short_block_byte
        /shake128_rate_bytes /=.
trivial.
qed.

lemma shake256_padding_positions seed seedoff nonce :
  nth 0 (shake256_seed_nonce_padded_state seed seedoff nonce) 66 = 31 /\
  nth 0 (shake256_seed_nonce_padded_state seed seedoff nonce) 135 = 128.
proof.
rewrite /shake256_seed_nonce_padded_state
        /HAETAE_FIPS202.shake256_absorb_once_short_state
        !nth_mkseq 1:/# 1:/# /=.
rewrite /HAETAE_FIPS202.shake256_absorb_once_short_block_byte /=.
trivial.
qed.

lemma w8_to_uint_bits (b : W8.t) :
  W8.to_uint b =
    (if b.[0] then 1 else 0) +
    (if b.[1] then 2 else 0) +
    (if b.[2] then 4 else 0) +
    (if b.[3] then 8 else 0) +
    (if b.[4] then 16 else 0) +
    (if b.[5] then 32 else 0) +
    (if b.[6] then 64 else 0) +
    (if b.[7] then 128 else 0).
proof.
rewrite W8.to_uintE /W8.w2bits /bs2int.
rewrite size_mkseq /max (_ : 0 < 8) 1:/# /=.
rewrite (_ : 8 = 7 + 1) 1:/# StdBigop.Bigint.BIA.big_int_recr 1:/#
        /= nth_mkseq 1:/#.
rewrite (_ : 7 = 6 + 1) 1:/# StdBigop.Bigint.BIA.big_int_recr 1:/#
        /= nth_mkseq 1:/#.
rewrite (_ : 6 = 5 + 1) 1:/# StdBigop.Bigint.BIA.big_int_recr 1:/#
        /= nth_mkseq 1:/#.
rewrite (_ : 5 = 4 + 1) 1:/# StdBigop.Bigint.BIA.big_int_recr 1:/#
        /= nth_mkseq 1:/#.
rewrite (_ : 4 = 3 + 1) 1:/# StdBigop.Bigint.BIA.big_int_recr 1:/#
        /= nth_mkseq 1:/#.
rewrite (_ : 3 = 2 + 1) 1:/# StdBigop.Bigint.BIA.big_int_recr 1:/#
        /= nth_mkseq 1:/#.
rewrite (_ : 2 = 1 + 1) 1:/# StdBigop.Bigint.BIA.big_int_recr 1:/#
        /= nth_mkseq 1:/#.
rewrite (_ : 1 = 0 + 1) 1:/# StdBigop.Bigint.BIA.big_int_recr 1:/#
        /= nth_mkseq 1:/#.
rewrite StdBigop.Bigint.BIA.big_geq 1:/# /= /b2i.
by case b.[0]; case b.[1]; case b.[2]; case b.[3];
   case b.[4]; case b.[5]; case b.[6]; case b.[7].
qed.

lemma lane_of_word_byte_le (w : W64.t) byte :
  0 <= byte < 8 =>
  HAETAE_Keccak1600.keccak_lane_to_byte
    (KeygenKeccak1600Spec.lane_of_word w) byte =
  W8.to_uint (w \bits8 byte).
proof.
move=> hbyte.
rewrite HAETAE_Keccak1600.keccak_lane_to_byte_bitsE.
rewrite !KeygenKeccak1600Spec.lane_of_word_bitE 1..8:/#.
rewrite w8_to_uint_bits.
rewrite !W8u8.bits8iE 1..8:/#.
rewrite HAETAE_Keccak1600.keccak_pow2_0E
        HAETAE_Keccak1600.keccak_pow2_1E
        HAETAE_Keccak1600.keccak_pow2_2E
        HAETAE_Keccak1600.keccak_pow2_3E
        HAETAE_Keccak1600.keccak_pow2_4E
        HAETAE_Keccak1600.keccak_pow2_5E
        HAETAE_Keccak1600.keccak_pow2_6E
        HAETAE_Keccak1600.keccak_pow2_7E.
have -> : 8 * byte = byte * 8 by ring.
ring.
qed.

lemma barray_get64_byte_le (a : BArray200.t) lane byte :
  0 <= lane < 25 =>
  0 <= byte < 8 =>
  BArray200.get64 a lane \bits8 byte =
  BArray200.get8 a (8 * lane + byte).
proof.
move=> hlane hbyte.
rewrite BArray200.get64dE.
rewrite W8u8.get_pack8.
+ by rewrite BArray200.size_sub.
by rewrite BArray200.nth_sub.
qed.

lemma state_bytes_le_of_lanes state :
  state_bytes_le state =
  HAETAE_Keccak1600.keccak_bytes_of_lanes
    (KeygenKeccak1600Spec.state_of_barray state).
proof.
apply/(eq_from_nth 0).
+ by rewrite state_bytes_le_size
             HAETAE_Keccak1600.keccak_bytes_of_lanes_size.
move=> i.
rewrite state_bytes_le_size => hi.
rewrite state_bytes_le_nth 1://.
rewrite HAETAE_Keccak1600.keccak_bytes_of_lanes_byteE 1://.
rewrite KeygenKeccak1600Spec.state_of_barray_laneE 1:/#.
rewrite lane_of_word_byte_le 1:/#.
rewrite barray_get64_byte_le 1:/# 1:/#.
congr; smt(divz_eq modz_cmp).
qed.

lemma drop_bytes_shrw w count :
  0 <= count =>
  drop_bytes w count = w `>>>` (8 * count).
proof.
move: count.
apply intind.
+ apply W64.wordP => bit hbit.
  rewrite /drop_bytes.
  rewrite iota0 1:/#.
  rewrite /=.
  by rewrite hbit /=.
+ move=> count hcount ih.
  rewrite /= in ih.
  rewrite /=.
  rewrite drop_bytes_succ 1:// ih.
  rewrite /(`>>`) W8.of_uintK /=.
  rewrite W64.shrw_add 1:/# 1:/#.
  congr; ring.
qed.

lemma rate_lane_byte_get8 state lane byte :
  0 <= lane < 25 =>
  0 <= byte < 8 =>
  rate_lane_byte state lane byte =
    BArray200.get8 state (8 * lane + byte).
proof.
move=> hlane hbyte.
rewrite /rate_lane_byte drop_bytes_shrw 1:/#.
rewrite -barray_get64_byte_le 1:// 1://.
apply W8.to_uint_eq.
rewrite to_uint_truncateu8 W64.to_uint_shr 1:/#.
rewrite W8u8.bits8_div 1:/# /=.
trivial.
qed.

lemma rate_block_matches_fips_prefix out outoff state bytes rate :
  0 <= rate <= 200 =>
  state_bytes_le state = bytes =>
  rate_block_matches out outoff state rate =>
  fips_rate_prefix_matches out outoff bytes rate.
proof.
move=> hrate_bound hstate hrate.
rewrite /rate_block_matches /rate_prefix_matches in hrate.
rewrite /fips_rate_prefix_matches.
move=> i hi.
have hlane : 0 <= i %/ 8 < 25 by apply divz_cmp => /#.
have hlane0 : 0 <= i %/ 8 by smt().
have hbyte : 0 <= i %% 8 < 8 by smt(modz_cmp).
have hsplit : 8 * (i %/ 8) + i %% 8 = i.
+ have hdiv := divz_eq i 8.
  smt().
have hbelow : 8 * (i %/ 8) + i %% 8 < rate by smt().
have hout := hrate (i %/ 8) (i %% 8) hlane0 hbyte hbelow.
have houti :
  BArray1024.get8 out (outoff + i) =
  rate_lane_byte state (i %/ 8) (i %% 8).
+ have hidx :
    outoff + 8 * (i %/ 8) + i %% 8 = outoff + i by smt().
  rewrite -hidx.
  exact hout.
rewrite -hstate state_bytes_le_nth 1:/#.
rewrite houti rate_lane_byte_get8 1:// 1:// hsplit.
trivial.
qed.

lemma shake128_rate_block_first_block
    out outoff state seed seedoff nonce :
  state_bytes_le state =
    shake128_seed_nonce_state seed seedoff nonce =>
  rate_block_matches out outoff state 168 =>
  fips_rate_prefix_matches out outoff
    (shake128_seed_nonce_state seed seedoff nonce) 168.
proof.
move=> hstate hmatches.
apply (rate_block_matches_fips_prefix out outoff state
  (shake128_seed_nonce_state seed seedoff nonce) 168).
+ smt().
+ exact hstate.
exact hmatches.
qed.

lemma shake256_rate_block_first_block
    out outoff state seed seedoff nonce :
  state_bytes_le state =
    shake256_seed_nonce_state seed seedoff nonce =>
  rate_block_matches out outoff state 136 =>
  fips_rate_prefix_matches out outoff
    (shake256_seed_nonce_state seed seedoff nonce) 136.
proof.
move=> hstate hmatches.
apply (rate_block_matches_fips_prefix out outoff state
  (shake256_seed_nonce_state seed seedoff nonce) 136).
+ smt().
+ exact hstate.
exact hmatches.
qed.

lemma shake128_returned_state_bytes state seed seedoff nonce :
  KeygenKeccak1600Spec.state_of_barray state =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (HAETAE_Keccak1600.keccak_lanes_of_bytes
        (shake128_seed_nonce_padded_state seed seedoff nonce)) =>
  state_bytes_le state =
    shake128_seed_nonce_state seed seedoff nonce.
proof.
move=> hstate.
rewrite state_bytes_le_of_lanes hstate.
rewrite /shake128_seed_nonce_state
        /shake128_absorb_once
        /shake128_seed_nonce_padded_state
        /HAETAE_Keccak1600.keccak_f1600_bytes.
trivial.
qed.

lemma shake256_returned_state_bytes state seed seedoff nonce :
  KeygenKeccak1600Spec.state_of_barray state =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (HAETAE_Keccak1600.keccak_lanes_of_bytes
        (shake256_seed_nonce_padded_state seed seedoff nonce)) =>
  state_bytes_le state =
    shake256_seed_nonce_state seed seedoff nonce.
proof.
move=> hstate.
rewrite state_bytes_le_of_lanes hstate.
rewrite /shake256_seed_nonce_state
        /HAETAE_FIPS202.shake256_absorb_once
        /HAETAE_FIPS202.fips202_keccak_f1600
        /shake256_seed_nonce_padded_state
        /HAETAE_Keccak1600.keccak_f1600_bytes.
trivial.
qed.

(* Multi-block squeeze model.  Block zero is produced by the first Keccak
   permutation of the framed absorb state; every later block applies one
   additional pinned [keccak_f1600_bytes] transition. *)

op squeeze_state_step (state : int list) (_ : int) : int list =
  HAETAE_Keccak1600.keccak_f1600_bytes state.

op squeeze_state_iter (state : int list) (blocks : int) : int list =
  foldl squeeze_state_step state (iota_ 0 blocks).

op squeeze_bytes_iter
    (state : int list) (rate blocks : int) : int list =
  mkseq
    (fun i =>
       nth 0 (squeeze_state_iter state (i %/ rate + 1)) (i %% rate))
    (blocks * rate).

op squeeze_blocks_matches
    (out : BArray1024.t) (outoff : int)
    (state : int list) (rate blocks : int) : bool =
  forall block byte,
    0 <= block < blocks =>
    0 <= byte < rate =>
    W8.to_uint
      (BArray1024.get8 out (outoff + block * rate + byte)) =
    nth 0 (squeeze_state_iter state (block + 1)) byte.

op squeeze_region_frame
    (before after : BArray1024.t) (outoff rate blocks : int) : bool =
  forall byte_index,
    0 <= byte_index < BArray1024.size =>
    !(outoff <= byte_index < outoff + blocks * rate) =>
    BArray1024.get8 after byte_index =
      BArray1024.get8 before byte_index.

op shake128_squeeze_bytes (state : int list) (blocks : int) : int list =
  squeeze_bytes_iter state 168 blocks.

op shake128_squeeze_block (state : int list) (block : int) : int list =
  mkseq
    (fun i => nth 0 (squeeze_state_iter state (block + 1)) i)
    168.

op shake256_squeeze_bytes (state : int list) (blocks : int) : int list =
  squeeze_bytes_iter state 136 blocks.

op shake256_squeeze_block (state : int list) (block : int) : int list =
  mkseq
    (fun i => nth 0 (squeeze_state_iter state (block + 1)) i)
    136.

lemma squeeze_state_iter0 state :
  squeeze_state_iter state 0 = state.
proof. by rewrite /squeeze_state_iter iota0. qed.

lemma squeeze_state_iter_succ state blocks :
  0 <= blocks =>
  squeeze_state_iter state (blocks + 1) =
    HAETAE_Keccak1600.keccak_f1600_bytes
      (squeeze_state_iter state blocks).
proof.
move=> hblocks.
by rewrite /squeeze_state_iter iotaSr 1:// foldl_rcons
           /squeeze_state_step.
qed.

lemma squeeze_bytes_iter0 state rate :
  squeeze_bytes_iter state rate 0 = [].
proof. by rewrite /squeeze_bytes_iter /= mkseq0. qed.

lemma squeeze_bytes_iter_size state rate blocks :
  0 <= rate =>
  0 <= blocks =>
  size (squeeze_bytes_iter state rate blocks) = blocks * rate.
proof.
move=> hrate hblocks.
rewrite /squeeze_bytes_iter size_mkseq /max.
smt().
qed.

lemma shake128_squeeze_block_size state block :
  size (shake128_squeeze_block state block) = 168.
proof. by rewrite /shake128_squeeze_block size_mkseq. qed.

lemma fips_rate_prefix_matches_shake128_block
    out outoff state block :
  fips_rate_prefix_matches out outoff
    (squeeze_state_iter state (block + 1)) 168 =>
  fips_rate_prefix_matches out outoff
    (shake128_squeeze_block state block) 168.
proof.
rewrite /fips_rate_prefix_matches /shake128_squeeze_block.
move=> hprefix i hi.
by rewrite nth_mkseq 1://; apply hprefix.
qed.

lemma shake128_squeeze_bytes_succ state blocks :
  0 <= blocks =>
  shake128_squeeze_bytes state (blocks + 1) =
    shake128_squeeze_bytes state blocks ++
    shake128_squeeze_block state blocks.
proof.
move=> hblocks.
rewrite /shake128_squeeze_bytes /squeeze_bytes_iter
        /shake128_squeeze_block.
have -> : (blocks + 1) * 168 = blocks * 168 + 168 by ring.
rewrite mkseq_add 1:/# 1:/#.
congr.
apply eq_in_mkseq => i hi /=.
by rewrite divzMDl 1:/# divz_small 1:/#
           modzMDl modz_small 1:/#.
qed.

lemma shake256_squeeze_block_size state block :
  size (shake256_squeeze_block state block) = 136.
proof. by rewrite /shake256_squeeze_block size_mkseq. qed.

lemma fips_rate_prefix_matches_shake256_block
    out outoff state block :
  fips_rate_prefix_matches out outoff
    (squeeze_state_iter state (block + 1)) 136 =>
  fips_rate_prefix_matches out outoff
    (shake256_squeeze_block state block) 136.
proof.
rewrite /fips_rate_prefix_matches /shake256_squeeze_block.
move=> hprefix i hi.
by rewrite nth_mkseq 1://; apply hprefix.
qed.

lemma shake256_squeeze_bytes_succ state blocks :
  0 <= blocks =>
  shake256_squeeze_bytes state (blocks + 1) =
    shake256_squeeze_bytes state blocks ++
    shake256_squeeze_block state blocks.
proof.
move=> hblocks.
rewrite /shake256_squeeze_bytes /squeeze_bytes_iter
        /shake256_squeeze_block.
have -> : (blocks + 1) * 136 = blocks * 136 + 136 by ring.
rewrite mkseq_add 1:/# 1:/#.
congr.
apply eq_in_mkseq => i hi /=.
by rewrite divzMDl 1:/# divz_small 1:/#
           modzMDl modz_small 1:/#.
qed.

lemma squeeze_bytes_iter_nth state rate blocks i :
  0 < rate =>
  0 <= blocks =>
  0 <= i < blocks * rate =>
  nth 0 (squeeze_bytes_iter state rate blocks) i =
    nth 0 (squeeze_state_iter state (i %/ rate + 1)) (i %% rate).
proof.
move=> hrate hblocks hi.
by rewrite /squeeze_bytes_iter nth_mkseq 1://.
qed.

lemma state_bytes_le_keccak_step before after :
  KeygenKeccak1600Spec.state_of_barray after =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray before) =>
  state_bytes_le after =
    HAETAE_Keccak1600.keccak_f1600_bytes (state_bytes_le before).
proof.
move=> hstate.
rewrite state_bytes_le_of_lanes hstate
        /HAETAE_Keccak1600.keccak_f1600_bytes.
by rewrite state_of_barray_state_bytes_le.
qed.

lemma squeeze_state_iter_barray_step initial before after blocks :
  0 <= blocks =>
  state_bytes_le before = squeeze_state_iter initial blocks =>
  KeygenKeccak1600Spec.state_of_barray after =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray before) =>
  state_bytes_le after = squeeze_state_iter initial (blocks + 1).
proof.
move=> hblocks hbefore hstate.
rewrite squeeze_state_iter_succ 1:// -hbefore.
exact (state_bytes_le_keccak_step before after hstate).
qed.

lemma squeeze_blocks_matches0 out outoff state rate :
  squeeze_blocks_matches out outoff state rate 0.
proof. by rewrite /squeeze_blocks_matches => block byte /#. qed.

lemma squeeze_region_frame0 out outoff rate :
  squeeze_region_frame out out outoff rate 0.
proof. by rewrite /squeeze_region_frame. qed.

lemma squeeze_blocks_matches_step
    before after outoff state rate blocks :
  0 <= outoff =>
  0 <= blocks =>
  0 < rate =>
  outoff + (blocks + 1) * rate <= BArray1024.size =>
  squeeze_blocks_matches before outoff state rate blocks =>
  fips_rate_prefix_matches after (outoff + blocks * rate)
    (squeeze_state_iter state (blocks + 1)) rate =>
  rate_block_frame before after (outoff + blocks * rate) rate =>
  squeeze_blocks_matches after outoff state rate (blocks + 1).
proof.
move=> hoff hblocks hrate hcap hmatches hprefix hframe.
rewrite /squeeze_blocks_matches in hmatches.
rewrite /squeeze_blocks_matches.
rewrite /fips_rate_prefix_matches in hprefix.
rewrite /rate_block_frame in hframe.
move=> block byte hblock hbyte.
case (block < blocks) => hprev.
+ have hmatch := hmatches block byte _ hbyte; first smt().
  have hindex :
    0 <= outoff + block * rate + byte < BArray1024.size by smt().
  have houtside :
    !(outoff + blocks * rate <= outoff + block * rate + byte <
      outoff + blocks * rate + rate) by smt().
  have hsame := hframe
    (outoff + block * rate + byte) hindex houtside.
  by rewrite hsame.
have -> : block = blocks by smt().
exact (hprefix byte hbyte).
qed.

lemma squeeze_region_frame_step
    original before after outoff rate blocks :
  0 <= outoff =>
  0 <= blocks =>
  0 < rate =>
  outoff + (blocks + 1) * rate <= BArray1024.size =>
  squeeze_region_frame original before outoff rate blocks =>
  rate_block_frame before after (outoff + blocks * rate) rate =>
  squeeze_region_frame original after outoff rate (blocks + 1).
proof.
rewrite /squeeze_region_frame /rate_block_frame.
move=> hoff hblocks hrate hcap hregion hframe byte_index hindex houtside.
have houtside_block :
  !(outoff + blocks * rate <= byte_index <
    outoff + blocks * rate + rate) by smt().
have houtside_region :
  !(outoff <= byte_index < outoff + blocks * rate) by smt().
rewrite (hframe byte_index hindex houtside_block).
exact (hregion byte_index hindex houtside_region).
qed.

lemma squeeze_blocks_induction_step
    original before after outoff state rate blocks :
  0 <= outoff =>
  0 <= blocks =>
  0 < rate =>
  outoff + (blocks + 1) * rate <= BArray1024.size =>
  squeeze_blocks_matches before outoff state rate blocks =>
  squeeze_region_frame original before outoff rate blocks =>
  fips_rate_prefix_matches after (outoff + blocks * rate)
    (squeeze_state_iter state (blocks + 1)) rate =>
  rate_block_frame before after (outoff + blocks * rate) rate =>
  squeeze_blocks_matches after outoff state rate (blocks + 1) /\
  squeeze_region_frame original after outoff rate (blocks + 1).
proof.
move=> hoff hblocks hrate hcap hmatches hregion hprefix hframe.
split.
+ exact (squeeze_blocks_matches_step before after outoff state rate blocks
    hoff hblocks hrate hcap hmatches hprefix hframe).
exact (squeeze_region_frame_step original before after outoff rate blocks
  hoff hblocks hrate hcap hregion hframe).
qed.

lemma squeeze_blocks_matches_fips out outoff state rate blocks :
  0 <= blocks =>
  0 < rate =>
  squeeze_blocks_matches out outoff state rate blocks =>
  fips_rate_prefix_matches out outoff
    (squeeze_bytes_iter state rate blocks) (blocks * rate).
proof.
move=> hblocks hrate hmatches.
rewrite /squeeze_blocks_matches in hmatches.
rewrite /fips_rate_prefix_matches.
move=> i hi.
rewrite squeeze_bytes_iter_nth 1:// 1:// 1://.
have hblock : 0 <= i %/ rate < blocks.
+ apply divz_cmp => /#.
have hbyte : 0 <= i %% rate < rate by apply modz_cmp => /#.
have hmatch := hmatches (i %/ rate) (i %% rate) hblock hbyte.
have hsplit := divz_eq i rate.
have hindex :
  outoff + (i %/ rate) * rate + i %% rate = outoff + i by smt().
rewrite -hindex.
exact hmatch.
qed.

lemma shake128_squeeze_blocks_fips out outoff state blocks :
  0 <= blocks =>
  squeeze_blocks_matches out outoff state 168 blocks =>
  fips_rate_prefix_matches out outoff
    (shake128_squeeze_bytes state blocks) (blocks * 168).
proof.
move=> hblocks hmatches.
rewrite /shake128_squeeze_bytes.
apply (squeeze_blocks_matches_fips out outoff state 168 blocks).
+ exact hblocks.
+ smt().
exact hmatches.
qed.

lemma shake256_squeeze_blocks_fips out outoff state blocks :
  0 <= blocks =>
  squeeze_blocks_matches out outoff state 136 blocks =>
  fips_rate_prefix_matches out outoff
    (shake256_squeeze_bytes state blocks) (blocks * 136).
proof.
move=> hblocks hmatches.
rewrite /shake256_squeeze_bytes.
apply (squeeze_blocks_matches_fips out outoff state 136 blocks).
+ exact hblocks.
+ smt().
exact hmatches.
qed.

end KeygenShakeStreamSpec.
