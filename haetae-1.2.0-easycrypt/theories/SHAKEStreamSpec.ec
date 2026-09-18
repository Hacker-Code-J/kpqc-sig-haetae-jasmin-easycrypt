require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import BArray64 BArray200 BArray8192 Array25 SHAKEBlockSpec.

(* A concrete word-based SHAKE stream. This specifies the current 64-byte
   seed / 16-bit nonce encoding and padding, without claiming a separate
   equivalence to an external bit-oriented FIPS specification. *)
theory SHAKEStreamSpec.
import SHAKEBlockSpec.Word.

op shake_nonce_byte (nonce : W64.t) (i : int) : W8.t =
  truncateu8 (nonce `>>>` (8 * i)).

op shake_seed_state (seed : BArray64.t) (nonce : W64.t) : BArray200.t =
  BArray200.init (fun i =>
    if i < 64 then BArray64.get8 seed i
    else if i < 66 then shake_nonce_byte nonce (i - 64)
    else if i = 66 then W8.of_int 31
    else if i = 135 then W8.of_int 128
    else W8.zero).

op shake_initial_words (seed : BArray64.t) (nonce : W64.t) : word_state =
  word_state_of_barray (shake_seed_state seed nonce).

op shake_iterate (initial : word_state) (blocks : int) : word_state =
  foldl (fun state (_ : int) => keccak_f1600 state) initial (iota_ 0 blocks).

op shake_stream_byte (initial : word_state) (j : int) : W8.t =
  (shake_iterate initial (j %/ 136 + 1)).[(j %% 136) %/ 8]
    \bits8 ((j %% 136) %% 8).

lemma shake_iterate0 initial : shake_iterate initial 0 = initial.
proof. by rewrite /shake_iterate iota0. qed.

lemma shake_iterateS initial n : 0 <= n =>
  shake_iterate initial (n + 1) = keccak_f1600 (shake_iterate initial n).
proof. by move=> hn; rewrite /shake_iterate iotaSr 1:hn foldl_rcons. qed.

lemma shake_iterate_add initial n m : 0 <= n => 0 <= m =>
  shake_iterate initial (n + m) = shake_iterate (shake_iterate initial n) m.
proof.
  move=> hn; move: m; apply intind.
  + by rewrite /= shake_iterate0.
  move=> m hm ih.
  rewrite /= in ih; rewrite /=.
  have -> : n + (m + 1) = (n + m) + 1 by ring.
  by rewrite !shake_iterateS 1..2:/# ih.
qed.

lemma shake_stream_block_byte initial block j :
  0 <= block => 0 <= j < 136 =>
  shake_stream_byte initial (136 * block + j) =
    (shake_iterate initial (block + 1)).[j %/ 8] \bits8 (j %% 8).
proof.
  move=> hb hj.
  have hd : (136 * block + j) %/ 136 = block by rewrite divz_eqP //; smt().
  have hm : (136 * block + j) %% 136 = j by
    rewrite (mulzC 136 block) modzMDl modz_small; smt().
  by rewrite /shake_stream_byte hd hm.
qed.

lemma shake_state_byte (state : BArray200.t) j : 0 <= j < 200 =>
  BArray200.get8 state j =
    (word_state_of_barray state).[j %/ 8] \bits8 (j %% 8).
proof.
  move=> hj.
  have hq : 0 <= j %/ 8 < 25 by smt(divz_cmp).
  have hr : 0 <= j %% 8 < 8 by smt(modz_cmp).
  have h := SHAKEBlockSpec.barray_get64_byte_le state (j %/ 8) (j %% 8) hq hr.
  rewrite state_of_barray_get 1:hq.
  smt(divz_eq).
qed.

lemma shake_words_injective (a b : BArray200.t) :
  word_state_of_barray a = word_state_of_barray b => a = b.
proof.
  move=> h; apply BArray200.ext_eq => i hi.
  by rewrite !shake_state_byte 1..2:hi h.
qed.

lemma shake_seed_state_get seed nonce i : 0 <= i < 200 =>
  BArray200.get8 (shake_seed_state seed nonce) i =
    if i < 64 then BArray64.get8 seed i
    else if i < 66 then shake_nonce_byte nonce (i - 64)
    else if i = 66 then W8.of_int 31
    else if i = 135 then W8.of_int 128
    else W8.zero.
proof. by move=> hi; rewrite /shake_seed_state BArray200.initiE. qed.

op shake_seed_prefix (seed : BArray64.t) (count : int) : BArray200.t =
  BArray200.init (fun i => if i < count then BArray64.get8 seed i else W8.zero).

op shake_nonce_prefix (seed : BArray64.t) (nonce : W64.t) (count : int) : BArray200.t =
  BArray200.init (fun i => if i < 64 then BArray64.get8 seed i
    else if i < 64 + count then shake_nonce_byte nonce (i - 64) else W8.zero).

op shake_absorb_byte (state : BArray200.t) (b : W8.t) (pos : W64.t) : BArray200.t =
  let lane = pos `>>` (W8.of_int 3) in
  let shift = ((truncateu8 pos) `&` (W8.of_int 7)) `<<` (W8.of_int 3) in
  let t = (zeroextu64 b) `<<` (shift `&` (W8.of_int 63)) in
  BArray200.set64 state (W64.to_uint lane)
    (BArray200.get64 state (W64.to_uint lane) `^` t).

op shake_pad (state : BArray200.t) : BArray200.t =
  let state = BArray200.set64 state 8
    (BArray200.get64 state 8 `^` ((W64.of_int 31) `<<` W8.of_int 16)) in
  BArray200.set64 state 16
    (BArray200.get64 state 16 `^` (W64.one `<<` W8.of_int 63)).

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

lemma shake_absorb_byte_get8
    (state : BArray200.t) (b : W8.t) p i :
  0 <= p < 200 =>
  0 <= i < 200 =>
  BArray200.get8 (shake_absorb_byte state b (W64.of_int p)) i =
  if i = p then BArray200.get8 state i `^` b
  else BArray200.get8 state i.
proof.
move=> hp hi.
rewrite /shake_absorb_byte /=.
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


lemma shake_seed_prefix_step seed p : 0 <= p < 64 =>
  shake_absorb_byte (shake_seed_prefix seed p) (BArray64.get8 seed p) (W64.of_int p) =
    shake_seed_prefix seed (p + 1).
proof.
  move=> hp; apply BArray200.ext_eq => i hi.
  rewrite shake_absorb_byte_get8 1:/# 1:hi.
  rewrite /shake_seed_prefix !BArray200.initiE 1..2:hi.
  case (i = p) => heq; smt(W8.xor0w).
qed.

lemma shake_nonce_prefix0 seed nonce :
  shake_nonce_prefix seed nonce 0 = shake_seed_prefix seed 64.
proof.
  apply BArray200.ext_eq => i hi.
  by rewrite /shake_nonce_prefix /shake_seed_prefix !BArray200.initiE 1..2:hi; smt().
qed.

lemma shake_nonce_prefix_step seed nonce k : 0 <= k < 2 =>
  shake_absorb_byte (shake_nonce_prefix seed nonce k)
    (truncateu8 (SHAKEBlockSpec.drop_bytes nonce k)) (W64.of_int (64 + k)) =
      shake_nonce_prefix seed nonce (k + 1).
proof.
  move=> hk; apply BArray200.ext_eq => i hi.
  rewrite shake_absorb_byte_get8 1:/# 1:hi.
  rewrite /shake_nonce_prefix !BArray200.initiE 1..2:hi.
  rewrite SHAKEBlockSpec.drop_bytes_shrw 1:/#.
  rewrite /shake_nonce_byte.
  case (i = 64 + k) => heq; smt(W8.xor0w).
qed.

lemma shake_absorb_byte_word (state : BArray200.t) (b : W8.t) p :
  0 <= p < 200 =>
  shake_absorb_byte state b (W64.of_int p) =
    BArray200.set64 state (p %/ 8)
      (BArray200.get64 state (p %/ 8) `^`
        ((zeroextu64 b) `<<` W8.of_int (8 * (p %% 8)))).
proof.
  move=> hp; rewrite /shake_absorb_byte /=.
  rewrite W64.shr_div_le 1:/# /=.
  rewrite W64.of_uintK (modz_small p W64.modulus) 1:/# /=.
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
by rewrite hshift.
qed.

lemma shake_domain_word :
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

lemma shake_padding_word :
  W64.one `<<` (W8.of_int 63) =
  (W8u8.zeroextu64 (W8.of_int 128)) `<<` (W8.of_int (8 * 7)).
proof.
apply W64.to_uint_eq.
rewrite /(`<<`).
rewrite !W64.to_uint_shl; 1,2: smt(W8.to_uint_cmp).
rewrite W64.to_uint1 W8u8.to_uint_zeroextu64 !W8.of_uintK /=.
trivial.
qed.

lemma shake_pad_absorb state :
  shake_pad state = shake_absorb_byte
    (shake_absorb_byte state (W8.of_int 31) (W64.of_int 66))
    (W8.of_int 128) (W64.of_int 135).
proof.
  have h66 : 0 <= 66 < 200 by trivial.
  have h135 : 0 <= 135 < 200 by trivial.
  rewrite (shake_absorb_byte_word _ _ 135 h135).
  rewrite !(shake_absorb_byte_word _ _ 66 h66).
  by rewrite /shake_pad /= shake_domain_word shake_padding_word.
qed.

lemma shake_pad_nonce_prefix seed nonce :
  shake_pad (shake_nonce_prefix seed nonce 2) = shake_seed_state seed nonce.
proof.
  apply BArray200.ext_eq => i hi.
  rewrite shake_pad_absorb !shake_absorb_byte_get8 1..4:/#.
  rewrite /shake_nonce_prefix BArray200.initiE 1:hi shake_seed_state_get 1:hi.
  smt(W8.xor0w).
qed.

end SHAKEStreamSpec.
