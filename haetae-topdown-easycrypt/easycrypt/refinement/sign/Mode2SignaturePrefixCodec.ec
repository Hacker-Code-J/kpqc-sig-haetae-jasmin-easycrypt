require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignaturePackMode2Target SignatureUnpackMode2Target.

theory Mode2SignaturePrefixCodec.

module Pack = SignaturePackMode2Target.M.
module Unpack = SignatureUnpackMode2Target.M.

op mode2_sigbytes : int = 1474.
op mode2_lcount : int = 4.
op challenge_bytes : int = 32.
op challenge_words : int = 256.
op low_words : int = 1024.
op prefix_bytes : int = challenge_bytes + low_words.

op bitword (b : bool) : W32.t =
  if b then W32.one else W32.zero.

op sign_extend_byte (b : W8.t) : W32.t =
  ((zeroextu32 b) `<<` (W8.of_int 24)) `|>>` (W8.of_int 24).

op canonical_challenge (cp : BArray1024.t) : bool =
  forall i, 0 <= i < challenge_words =>
    0 <= W32.to_uint (BArray1024.get32 cp i) <= 1 /\
    BArray1024.get32 cp i =
      bitword (BArray1024.get32 cp i).[0].

op canonical_signed_low (low : BArray8192.t) : bool =
  forall i, 0 <= i < low_words =>
    -128 <= W32.to_sint (BArray8192.get32 low i) < 128 /\
    BArray8192.get32 low i =
      sign_extend_byte (truncateu8 (BArray8192.get32 low i)).

op challenge_prefix_eq
    (left right : BArray1024.t) : bool =
  forall i, 0 <= i < challenge_words =>
    BArray1024.get32 left i = BArray1024.get32 right i.

op low_mode2_eq (left right : BArray8192.t) : bool =
  forall i, 0 <= i < low_words =>
    BArray8192.get32 left i = BArray8192.get32 right i.

op challenge_source
    (cp : BArray1024.t) (byte bit : int) : bool =
  (BArray1024.get32 cp (8 * byte + bit)).[0].

op packed_challenge_prefix
    (sig : BArray2948.t) (cp : BArray1024.t) (bytes : int) : bool =
  forall byte bit,
    0 <= byte < bytes => 0 <= bit < 8 =>
    (BArray2948.get8 sig byte).[bit] = challenge_source cp byte bit.

op packed_low_prefix
    (sig : BArray2948.t) (low : BArray8192.t) (words : int) : bool =
  forall i, 0 <= i < words =>
    BArray2948.get8 sig (challenge_bytes + i) =
      truncateu8 (BArray8192.get32 low i).

op decoded_challenge_prefix
    (outp inp : BArray1024.t) (words : int) : bool =
  forall i, 0 <= i < words =>
    BArray1024.get32 outp i = bitword (BArray1024.get32 inp i).[0].

op decoded_low_prefix
    (outp inp : BArray8192.t) (words : int) : bool =
  forall i, 0 <= i < words =>
    BArray8192.get32 outp i =
      sign_extend_byte (truncateu8 (BArray8192.get32 inp i)).

op signature_tail_frame
    (before after : BArray2948.t) : bool =
  forall i, mode2_sigbytes <= i < 2948 =>
    BArray2948.get8 after i = BArray2948.get8 before i.

op zero_sig_prefix (sig : BArray2948.t) (n : int) : bool =
  forall i, 0 <= i < n => BArray2948.get8 sig i = W8.zero.

op low_tail_frame
    (before after : BArray8192.t) : bool =
  forall i, low_words <= i < 2048 =>
    BArray8192.get32 after i = BArray8192.get32 before i.

op partial_word
    (out : W32.t) (source : int -> bool) (upto : int) : bool =
  forall bit, 0 <= bit < 8 =>
    out.[bit] = (bit < upto /\ source bit).

lemma signature_tail_frame_refl (sig : BArray2948.t) :
  signature_tail_frame sig sig.
proof. rewrite /signature_tail_frame; trivial. qed.

lemma signature_tail_frame_set_before
    (before after : BArray2948.t) (idx : int) (value : W8.t) :
  0 <= idx < mode2_sigbytes =>
  signature_tail_frame before after =>
  signature_tail_frame before (BArray2948.set8 after idx value).
proof.
move=> hidx hframe.
rewrite /signature_tail_frame => i hi.
rewrite BArray2948.get_setE 1:/#.
rewrite ifF 1:/#.
apply hframe; exact hi.
qed.

lemma bitword_bit (b : bool) (bit : int) :
  0 <= bit < 32 => (bitword b).[bit] = (bit = 0 /\ b).
proof.
move=> hbit.
case b => hb.
+ rewrite /bitword /= W32.nth_one; trivial.
+ rewrite /bitword /=; trivial.
qed.

lemma and_one_is_bitword (w : W32.t) :
  w `&` W32.one = bitword w.[0].
proof.
apply W32.ext_eq => k hk.
rewrite W32.andwE W32.nth_one (bitword_bit w.[0] k hk).
smt().
qed.

lemma decode_w8_bit (b : W8.t) (j : int) :
  0 <= j < 8 =>
  ((zeroextu32 b) `>>` (W8.of_int j)) `&` W32.one = bitword b.[j].
proof.
move=> hj.
apply W32.ext_eq => k hk.
rewrite W32.andwE /(`>>`) W32.shrwE W8.of_uintK /=.
rewrite W4u8.zeroextu32_bit W32.nth_one
        (bitword_bit b.[j] k hk).
rewrite (modz_small j 256) 1:/#.
smt().
qed.

lemma shifted_bitword_bit
    (source : int -> bool) (j bit : int) :
  0 <= j < 8 => 0 <= bit < 8 =>
  (bitword (source j) `<<` W8.of_int j).[bit] =
    (bit = j /\ source j).
proof.
move=> hj hbit.
rewrite /(`<<`) W32.shlwE W8.of_uintK
        (modz_small j 256) 1:/# /bitword.
case (source j) => hs.
+ rewrite W32.nth_one; smt().
+ rewrite W32.zerowE; smt().
qed.

lemma partial_word_zero (source : int -> bool) :
  partial_word W32.zero source 0.
proof.
rewrite /partial_word => bit hbit.
rewrite W32.zerowE.
smt().
qed.

lemma partial_word_step
    (out : W32.t) (source : int -> bool) (j : int) :
  0 <= j < 8 =>
  partial_word out source j =>
  partial_word
    (out `|` (bitword (source j) `<<` W8.of_int j)) source (j + 1).
proof.
move=> hj hp.
rewrite /partial_word => bit hbit.
rewrite W32.orwE
        (shifted_bitword_bit source j bit hj hbit)
        (hp bit hbit).
smt().
qed.

lemma mask255_low_bit (bit : int) :
  0 <= bit < 8 => (W32.of_int 255).[bit].
proof.
move=> hbit.
rewrite W32.get_to_uint W32.of_uintK /=
        (modz_small 255 W32.modulus) 1:/#.
have hcases :
    bit = 0 \/ bit = 1 \/ bit = 2 \/ bit = 3 \/
    bit = 4 \/ bit = 5 \/ bit = 6 \/ bit = 7 by smt().
elim hcases => h0; first by subst bit; trivial.
elim h0 => h1; first by subst bit; trivial.
elim h1 => h2; first by subst bit; trivial.
elim h2 => h3; first by subst bit; trivial.
elim h3 => h4; first by subst bit; trivial.
elim h4 => h5; first by subst bit; trivial.
elim h5 => h6; by subst bit; trivial.
qed.

lemma truncateu8_bit (w : W32.t) (bit : int) :
  0 <= bit < 8 => (truncateu8 w).[bit] = w.[bit].
proof.
move=> hbit.
have heq :
    (zeroextu32 (truncateu8 w)).[bit] =
    (w `&` W32.of_int W8.max_uint).[bit]
  by rewrite W4u8.zeroext_truncateu8_and.
move: heq.
have hmax : W8.max_uint = 255 by trivial.
rewrite hmax W4u8.zeroextu32_bit W32.andwE
        (mask255_low_bit bit hbit) hbit /=.
trivial.
qed.

lemma packed_challenge_prefix_zero sig cp :
  packed_challenge_prefix sig cp 0.
proof. rewrite /packed_challenge_prefix; smt(). qed.

lemma packed_challenge_prefix_step sig cp byte out :
  0 <= byte < challenge_bytes =>
  packed_challenge_prefix sig cp byte =>
  partial_word out (challenge_source cp byte) 8 =>
  packed_challenge_prefix
    (BArray2948.set8 sig byte (truncateu8 out)) cp (byte + 1).
proof.
move=> hbyte hp hw.
rewrite /packed_challenge_prefix => current bit hcurrent hbit.
rewrite BArray2948.get_setE 1:/#.
case (current = byte) => heq.
+ subst current.
  rewrite /= (truncateu8_bit out bit hbit) (hw bit hbit).
  smt().
+ apply hp; smt().
qed.

lemma prefix_index_disjoint byte upto idx :
  0 <= byte < upto => upto <= challenge_bytes =>
  challenge_bytes <= idx => byte <> idx.
proof. smt(). qed.

lemma index_before_next_if_neq k current :
  0 <= k => k < current + 1 => k <> current => k < current.
proof. smt(). qed.

lemma bounded_index_before_next_if_neq k current :
  0 <= k < current + 1 => k <> current => 0 <= k < current.
proof. smt(). qed.

lemma low_prior_index_from_actual
    k current next actual :
  0 <= k < next =>
  next = current + 1 =>
  actual = challenge_bytes + current =>
  challenge_bytes + k <> actual =>
  0 <= k < current.
proof. smt(). qed.

lemma packed_challenge_prefix_set_after sig cp upto idx value :
  0 <= idx < 2948 =>
  0 <= upto <= challenge_bytes =>
  challenge_bytes <= idx =>
  packed_challenge_prefix sig cp upto =>
  packed_challenge_prefix (BArray2948.set8 sig idx value) cp upto.
proof.
move=> hidxbounds [hupto0 huptole] hidx hp.
rewrite /packed_challenge_prefix => byte bit hbyte hbit.
rewrite BArray2948.get_setE 1:hidxbounds.
case (byte = idx) => hsame.
+ have hneq : byte <> idx.
  + exact (prefix_index_disjoint byte upto idx hbyte huptole hidx).
  smt().
+ exact (hp byte bit hbyte hbit).
qed.

lemma packed_low_prefix_zero sig low :
  packed_low_prefix sig low 0.
proof. rewrite /packed_low_prefix; smt(). qed.

lemma packed_low_prefix_step sig low words :
  0 <= words < low_words =>
  packed_low_prefix sig low words =>
  packed_low_prefix
    (BArray2948.set8 sig (challenge_bytes + words)
       (truncateu8 (BArray8192.get32 low words)))
    low (words + 1).
proof.
move=> hwords hp.
rewrite /packed_low_prefix => i hi.
rewrite BArray2948.get_setE 1:/#.
case (i = words) => heq.
+ subst i; trivial.
+ rewrite ifF 1:/#.
  apply hp; smt().
qed.

lemma packed_low_prefix_step_at sig low words idx :
  idx = challenge_bytes + words =>
  0 <= words < low_words =>
  packed_low_prefix sig low words =>
  packed_low_prefix
    (BArray2948.set8 sig idx
       (truncateu8 (BArray8192.get32 low words)))
    low (words + 1).
proof.
move=> -> hwords hp.
exact (packed_low_prefix_step sig low words hwords hp).
qed.

lemma zero_sig_prefix_zero sig :
  zero_sig_prefix sig 0.
proof. rewrite /zero_sig_prefix; smt(). qed.

lemma zero_sig_prefix_step sig n :
  0 <= n < mode2_sigbytes =>
  zero_sig_prefix sig n =>
  zero_sig_prefix (BArray2948.set8 sig n W8.zero) (n + 1).
proof.
move=> hn hp.
rewrite /zero_sig_prefix => i hi.
rewrite BArray2948.get_setE 1:/#.
case (i = n) => heq.
+ subst i; trivial.
+ apply hp; smt().
qed.

lemma decoded_challenge_prefix_zero outp inp :
  decoded_challenge_prefix outp inp 0.
proof. rewrite /decoded_challenge_prefix; smt(). qed.

lemma decoded_challenge_prefix_step outp inp words :
  0 <= words < challenge_words =>
  decoded_challenge_prefix outp inp words =>
  decoded_challenge_prefix
    (BArray1024.set32 outp words
       (bitword (BArray1024.get32 inp words).[0]))
    inp (words + 1).
proof.
move=> hwords hp.
rewrite /decoded_challenge_prefix => i hi.
rewrite /decoded_challenge_prefix in hp.
rewrite BArray1024.get_set32E 1:/# 1:/#.
case (i = words) => heq.
+ by subst i.
+ by rewrite ifF 1:/#; apply hp; smt().
qed.

lemma decoded_low_prefix_zero outp inp :
  decoded_low_prefix outp inp 0.
proof. rewrite /decoded_low_prefix; smt(). qed.

lemma decoded_low_prefix_step outp inp words :
  0 <= words < low_words =>
  decoded_low_prefix outp inp words =>
  decoded_low_prefix
    (BArray8192.set32 outp words
       (sign_extend_byte (truncateu8 (BArray8192.get32 inp words))))
    inp (words + 1).
proof.
move=> hwords hp.
rewrite /decoded_low_prefix => i hi.
rewrite /decoded_low_prefix in hp.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = words) => heq.
+ by subst i.
+ by rewrite ifF 1:/#; apply hp; smt().
qed.

lemma decoded_challenge_prefix_canonical_eq outp inp :
  canonical_challenge inp =>
  decoded_challenge_prefix outp inp challenge_words =>
  challenge_prefix_eq outp inp.
proof.
move=> hcanon hdec.
rewrite /challenge_prefix_eq => i hi.
have hbit := hcanon i hi.
rewrite /decoded_challenge_prefix in hdec.
have hres := hdec i hi.
rewrite /canonical_challenge in hcanon.
move: hbit.
rewrite /bitword.
smt().
qed.

lemma decoded_low_prefix_canonical_eq outp inp :
  canonical_signed_low inp =>
  decoded_low_prefix outp inp low_words =>
  low_mode2_eq outp inp.
proof.
move=> hcanon hdec.
rewrite /low_mode2_eq => i hi.
have hbit := hcanon i hi.
rewrite /decoded_low_prefix in hdec.
have hres := hdec i hi.
rewrite /canonical_signed_low in hcanon.
move: hbit.
rewrite /sign_extend_byte.
smt().
qed.

lemma zero_challenge_get32 (i : int) :
  0 <= i < challenge_words =>
  BArray1024.get32 (BArray1024.init (fun _ => W8.zero)) i = W32.zero.
proof.
move=> hi.
apply W32.ext_eq => bit hbit.
rewrite W4u8.get_bits8 1:hbit.
rewrite BArray1024.get32d_byte 1:/#.
rewrite BArray1024.initiE 1:/# W8.zerowE W32.zerowE.
trivial.
qed.

lemma zero_low_get32 (i : int) :
  0 <= i < 2048 =>
  BArray8192.get32 (BArray8192.init (fun _ => W8.zero)) i = W32.zero.
proof.
move=> hi.
apply W32.ext_eq => bit hbit.
rewrite W4u8.get_bits8 1:hbit.
rewrite BArray8192.get32d_byte 1:/#.
rewrite BArray8192.initiE 1:/# W8.zerowE W32.zerowE.
trivial.
qed.

lemma sign_extend_zero : sign_extend_byte W8.zero = W32.zero.
proof.
apply W32.ext_eq => bit hbit.
rewrite /sign_extend_byte /(`|>>`) W32.sarE W32.initiE 1:hbit /=.
rewrite /(`<<`) W32.shlwE.
rewrite W4u8.zeroextu32_bit.
trivial.
qed.

lemma truncateu8_zero : truncateu8 W32.zero = W8.zero.
proof.
rewrite /W4u8.truncateu8 W32.to_uint0.
trivial.
qed.

lemma prefix_codec_preconditions_satisfiable :
  exists cp low,
    canonical_challenge cp /\ canonical_signed_low low.
proof.
exists (BArray1024.init (fun _ => W8.zero))
       (BArray8192.init (fun _ => W8.zero)).
split.
+ rewrite /canonical_challenge => i hi.
  rewrite (zero_challenge_get32 i hi)
          W32.to_uint0 /bitword W32.zerowE /=.
  trivial.
+ rewrite /canonical_signed_low => i hi.
  rewrite (zero_low_get32 i) 1:/# W32.to_sintE W32.to_uint0 /=.
  rewrite truncateu8_zero sign_extend_zero.
  smt().
qed.

end Mode2SignaturePrefixCodec.
