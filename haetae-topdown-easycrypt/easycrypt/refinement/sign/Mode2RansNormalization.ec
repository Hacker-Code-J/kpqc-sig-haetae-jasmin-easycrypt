require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2HbzCodecSpec Mode2RansByteStack.

theory Mode2RansNormalization.

import Mode2HbzCodecSpec Mode2RansByteStack.

op append_word_byte (x : W32.t) (b : W8.t) : W32.t =
  (x `<<` W8.of_int 8) `|` zeroextu32 b.

lemma encoder_shift8_uint (x : W32.t) :
  W32.to_uint (x `>>` W8.of_int 8) = W32.to_uint x %/ 256.
proof.
rewrite W32.shr_div W8.of_uintK /=.
trivial.
qed.

lemma encoder_low_byte_uint (x : W32.t) :
  W8.to_uint (truncateu8 x) = W32.to_uint x %% 256.
proof.
rewrite W4u8.to_uint_truncateu8.
trivial.
qed.

lemma shifted_word_disjoint_byte (x : W32.t) (b : W8.t) :
  (x `<<` W8.of_int 8) `&` zeroextu32 b = W32.zero.
proof.
apply W32.wordP => bit hbit.
rewrite W32.andwE /(`<<`) W32.shlwE.
rewrite W8.of_uintK /= W4u8.zeroextu32_bit.
smt().
qed.

lemma decoder_append_word_uint (x : W32.t) (b : W8.t) :
  W32.to_uint x < 16777216 =>
  W32.to_uint (append_word_byte x b) =
    256 * W32.to_uint x + W8.to_uint b.
proof.
move=> hx.
rewrite /append_word_byte W32.to_uint_orw_disjoint.
+ exact (shifted_word_disjoint_byte x b).
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
rewrite W4u8.to_uint_zeroextu32.
rewrite modz_small.
+ have hxu := W32.to_uint_cmp x.
  smt().
+ ring.
qed.

lemma decoder_append_encoder_byte (x : W32.t) :
  append_word_byte (x `>>` W8.of_int 8) (truncateu8 x) = x.
proof.
apply W32.to_uint_eq.
rewrite decoder_append_word_uint.
+ rewrite encoder_shift8_uint.
  have hx := W32.to_uint_cmp x.
  have hdiv := divz_eq (W32.to_uint x) 256.
  have hmod := modz_cmp (W32.to_uint x) 256 _; first smt().
  smt().
rewrite encoder_shift8_uint encoder_low_byte_uint.
have hdiv := divz_eq (W32.to_uint x) 256.
smt().
qed.

lemma encoder_two_byte_decoder_order (x : W32.t) :
  append_word_byte
    (append_word_byte
      ((x `>>` W8.of_int 8) `>>` W8.of_int 8)
      (truncateu8 (x `>>` W8.of_int 8)))
    (truncateu8 x) = x.
proof.
rewrite decoder_append_encoder_byte.
exact (decoder_append_encoder_byte x).
qed.

lemma cursor_decrement_no_underflow (off : W64.t) :
  0 < W64.to_uint off =>
  W64.to_uint (off - W64.one) = W64.to_uint off - 1.
proof.
move=> hoff.
rewrite W64.to_uintB.
+ rewrite W64.uleE W64.to_uint1.
  smt().
rewrite W64.to_uint1.
trivial.
qed.

lemma cursor_two_decrements_no_underflow (off : W64.t) :
  2 <= W64.to_uint off =>
  W64.to_uint ((off - W64.one) - W64.one) = W64.to_uint off - 2.
proof.
move=> hoff.
have h1 := cursor_decrement_no_underflow off _; first smt().
have hpos : 0 < W64.to_uint (off - W64.one).
+ rewrite h1; smt().
have h2 := cursor_decrement_no_underflow (off - W64.one) hpos.
rewrite h2 h1.
ring.
qed.

lemma normalization_word_preconditions_satisfiable :
  exists x,
    rans_initial_state <= W32.to_uint x < 2147483648.
proof.
exists (W32.of_int rans_initial_state).
rewrite W32.to_uint_small.
+ rewrite /rans_initial_state; smt().
rewrite /rans_initial_state; smt().
qed.

end Mode2RansNormalization.
