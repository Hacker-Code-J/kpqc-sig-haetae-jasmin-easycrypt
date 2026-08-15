require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignatureUnpackMode2Target.
require import Mode2SignaturePrefixCodec.
require import Mode2VerifyPrepareNorm.

theory VerifySignaturePrefixCanonicalPostFreeze.

import Mode2SignaturePrefixCodec.

module Unpack = SignatureUnpackMode2Target.M.

op unpacked_challenge_prefix
    (cp : BArray1024.t) (sig : BArray2948.t) (words : int) : bool =
  forall i, 0 <= i < words =>
    BArray1024.get32 cp i =
      Mode2VerifyPrepareNorm.bitword
        ((BArray2948.get8 sig (i %/ 8)).[i %% 8]).

op unpacked_low_prefix
    (low : BArray8192.t) (sig : BArray2948.t) (words : int) : bool =
  forall i, 0 <= i < words =>
    BArray8192.get32 low i =
      Mode2VerifyPrepareNorm.sign_extend_byte
        (BArray2948.get8 sig (challenge_bytes + i)).

lemma bitword_canonical (b : bool) :
  0 <= W32.to_uint (Mode2VerifyPrepareNorm.bitword b) <= 1 /\
  Mode2VerifyPrepareNorm.bitword b =
    Mode2VerifyPrepareNorm.bitword
      (Mode2VerifyPrepareNorm.bitword b).[0].
proof.
case b.
+ rewrite /Mode2VerifyPrepareNorm.bitword W32.to_uint1 /= W32.nth_one.
  smt().
+ rewrite /Mode2VerifyPrepareNorm.bitword W32.to_uint0 /= W32.zerowE.
  smt().
qed.

lemma sign_extend_byte_low_bit (b : W8.t) (bit : int) :
  0 <= bit < 8 =>
  (Mode2VerifyPrepareNorm.sign_extend_byte b).[bit] = b.[bit].
proof.
move=> hbit.
have -> :
    Mode2VerifyPrepareNorm.sign_extend_byte b =
    Mode2SignaturePrefixCodec.sign_extend_byte b.
+ by rewrite /Mode2VerifyPrepareNorm.sign_extend_byte
            /Mode2SignaturePrefixCodec.sign_extend_byte.
rewrite /Mode2SignaturePrefixCodec.sign_extend_byte
        /W32.(`|>>`) W32.sarE /=.
rewrite W32.initiE 1:/# /=.
have -> : min 31 (bit + 24) = bit + 24 by smt().
rewrite /W32.(`<<`) W32.shlwE /=.
rewrite W4u8.zeroextu32_bit 1:/#.
qed.

lemma truncateu8_sign_extend_byte (b : W8.t) :
  truncateu8 (Mode2VerifyPrepareNorm.sign_extend_byte b) = b.
proof.
apply W8.ext_eq => bit hbit.
rewrite Mode2SignaturePrefixCodec.truncateu8_bit 1:hbit.
rewrite sign_extend_byte_low_bit 1:hbit.
trivial.
qed.

op byte_sign_mask : W32.t =
  W32.onew `<<` W8.of_int 8.

lemma byte_top_bitE (b : W8.t) :
  b.[7] = (128 <= W8.to_uint b).
proof.
rewrite W8.get_to_uint /=.
have hb := W8.to_uint_cmp b.
smt().
qed.

lemma byte_sign_mask_disjoint (b : W8.t) :
  zeroextu32 b `&` byte_sign_mask = W32.zero.
proof.
apply W32.ext_eq => bit hbit.
rewrite W32.andwE W4u8.zeroextu32_bit.
rewrite /byte_sign_mask /W32.(`<<`) W32.shlwE W32.onewE W32.zerowE.
smt().
qed.

lemma byte_sign_mask_uint :
  W32.to_uint byte_sign_mask = W32.modulus - 256.
proof.
rewrite /byte_sign_mask /W32.(`<<`) W32.to_uint_shl 1:/#.
rewrite W32.to_uint_onew /=.
trivial.
qed.

lemma sign_extended_byte_mask_uint (b : W8.t) :
  W32.to_uint (zeroextu32 b `|` byte_sign_mask) =
    W8.to_uint b + (W32.modulus - 256).
proof.
rewrite W32.to_uint_orw_disjoint.
+ exact (byte_sign_mask_disjoint b).
rewrite W4u8.to_uint_zeroextu32 byte_sign_mask_uint.
trivial.
qed.

lemma sign_extend_byte_mask (b : W8.t) :
  Mode2VerifyPrepareNorm.sign_extend_byte b =
    zeroextu32 b `|` (if b.[7] then byte_sign_mask else W32.zero).
proof.
apply W32.ext_eq => bit hbit.
rewrite /Mode2VerifyPrepareNorm.sign_extend_byte
        /W32.(`|>>`) W32.sarE W32.initiE 1:hbit /=.
rewrite /W32.(`<<`) !W32.shlwE /=.
rewrite W4u8.zeroextu32_bit.
  case (b.[7]) => hb7 /=.
+ rewrite /byte_sign_mask /W32.(`<<`) W32.shlwE W32.onewE.
  case (bit < 8) => hsmall.
- have -> : min 31 (bit + 24) = bit + 24 by smt().
    smt().
- have -> : min 31 (bit + 24) = 31 by smt().
    smt().
+ case (bit < 8) => hsmall.
- have -> : min 31 (bit + 24) = bit + 24 by smt().
    smt().
- have -> : min 31 (bit + 24) = 31 by smt().
    smt().
qed.

lemma sign_extend_byte_sint_high (b : W8.t) :
  128 <= W8.to_uint b =>
  W32.to_sint (Mode2VerifyPrepareNorm.sign_extend_byte b) =
    W8.to_uint b - 256.
proof.
move=> hsign.
have hb7 : b.[7] by rewrite byte_top_bitE hsign.
rewrite sign_extend_byte_mask hb7 /= W32.to_sintE /W32.smod.
rewrite sign_extended_byte_mask_uint.
smt(W8.to_uint_cmp).
qed.

lemma sign_extend_byte_sint_low (b : W8.t) :
  W8.to_uint b < 128 =>
  W32.to_sint (Mode2VerifyPrepareNorm.sign_extend_byte b) = W8.to_uint b.
proof.
move=> hsign.
have hb7 : !b.[7] by rewrite byte_top_bitE; smt().
rewrite sign_extend_byte_mask hb7 /= W32.to_sintE
        /W32.smod W4u8.to_uint_zeroextu32.
smt(W8.to_uint_cmp).
qed.

lemma sign_extend_byte_canonical (b : W8.t) :
  -128 <= W32.to_sint (Mode2VerifyPrepareNorm.sign_extend_byte b) < 128 /\
  Mode2VerifyPrepareNorm.sign_extend_byte b =
    Mode2VerifyPrepareNorm.sign_extend_byte
      (truncateu8 (Mode2VerifyPrepareNorm.sign_extend_byte b)).
proof.
split; last by rewrite truncateu8_sign_extend_byte.
have hb := W8.to_uint_cmp b.
case (128 <= W8.to_uint b) => hsign.
+ have hs := sign_extend_byte_sint_high b hsign.
  smt().
+ have hs : W32.to_sint (Mode2VerifyPrepareNorm.sign_extend_byte b) =
              W8.to_uint b.
  + apply sign_extend_byte_sint_low.
    smt().
  smt().
qed.

lemma unpacked_challenge_prefix_zero cp sig :
  unpacked_challenge_prefix cp sig 0.
proof. rewrite /unpacked_challenge_prefix; smt(). qed.

lemma unpacked_challenge_prefix_step cp sig words bit :
  0 <= words < challenge_words =>
  unpacked_challenge_prefix cp sig words =>
  bit = Mode2VerifyPrepareNorm.bitword
          ((BArray2948.get8 sig (words %/ 8)).[words %% 8]) =>
  unpacked_challenge_prefix
    (BArray1024.set32 cp words bit) sig (words + 1).
proof.
move=> hwords hprefix ->.
rewrite /unpacked_challenge_prefix => i hi.
rewrite BArray1024.get_set32E 1:/# 1:/#.
case (i = words) => heq.
+ by subst i.
+ by rewrite ifF 1:/#; apply hprefix; smt().
qed.

lemma unpacked_low_prefix_zero low sig :
  unpacked_low_prefix low sig 0.
proof. rewrite /unpacked_low_prefix; smt(). qed.

lemma unpacked_low_prefix_step low sig words :
  0 <= words < low_words =>
  unpacked_low_prefix low sig words =>
  unpacked_low_prefix
    (BArray8192.set32 low words
      (Mode2VerifyPrepareNorm.sign_extend_byte
        (BArray2948.get8 sig (challenge_bytes + words))))
    sig (words + 1).
proof.
move=> hwords hprefix.
rewrite /unpacked_low_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = words) => heq.
+ by subst i.
+ by rewrite ifF 1:/#; apply hprefix; smt().
qed.

lemma unpacked_challenge_prefix_canonical cp sig :
  unpacked_challenge_prefix cp sig challenge_words =>
  Mode2VerifyPrepareNorm.canonical_challenge cp.
proof.
move=> hprefix.
rewrite /Mode2VerifyPrepareNorm.canonical_challenge => i hi.
rewrite hprefix 1:hi.
exact (bitword_canonical _).
qed.

lemma unpacked_low_prefix_canonical low sig :
  unpacked_low_prefix low sig low_words =>
  Mode2VerifyPrepareNorm.canonical_signed_low low.
proof.
move=> hprefix.
rewrite /Mode2VerifyPrepareNorm.canonical_signed_low => i hi.
rewrite hprefix 1:hi.
exact (sign_extend_byte_canonical _).
qed.

lemma unpack_sig_prefix_mode2_canonical
    (cp0 : BArray1024.t)
    (low0 : BArray8192.t)
    (sig0 : BArray2948.t) :
  hoare [Unpack._unpack_sig_prefix :
    cp = cp0 /\ lowp = low0 /\ sigp = sig0 /\
    lcount = W64.of_int mode2_lcount
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res.`1 /\
    Mode2VerifyPrepareNorm.canonical_signed_low res.`2].
proof.
proc.
while
  (lcount = W64.of_int mode2_lcount /\
   off = W64.of_int challenge_bytes /\
   total = W64.of_int low_words /\
   unpacked_challenge_prefix cp sigp challenge_words /\
   0 <= W64.to_uint i <= low_words /\
   unpacked_low_prefix lowp sigp (W64.to_uint i)).
+ auto => /> &hr hcprefix hi0 hile hlowprefix hguard.
   have hilt : W64.to_uint i{hr} < low_words.
   + move: hguard.
     rewrite W64.ultE W64.of_uintK /=.
     smt(W64.to_uint_cmp).
   have hidx :
       W64.to_uint (W64.of_int challenge_bytes + i{hr}) =
       challenge_bytes + W64.to_uint i{hr}.
   + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
     trivial.
   have hi_next :
       W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
   + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
     trivial.
   split; first by rewrite hi_next; smt(W64.to_uint_cmp).
   rewrite hidx hi_next.
   apply unpacked_low_prefix_step; first by smt().
   exact hlowprefix.
+ auto => />.
   move=> &hr [hlcount [hoff [htotal hcprefix]]].
   move=> cp1 hloop /=.
   rewrite hcprefix W64.of_intM /=.
   move: hloop => [[hchallenge hlowzero] hcont].
   split.
   + rewrite /challenge_bytes /low_words /mode2_lcount /=.
     split; first exact hchallenge.
     exact hlowzero.
   + move=> i0 lowp0 hdone
             [heqoff [heqtotal [hchallenge0
               [[hi0 hile] hlow0]]]].
     apply (hcont i0 lowp0 hdone).
     + exact heqoff.
     + exact heqtotal.
     + exact hchallenge0.
     + exact hi0.
     + exact hile.
     + exact hlow0.
while
  (lowp = low0 /\
   lcount = W64.of_int mode2_lcount /\
   0 <= W64.to_uint i <= challenge_bytes /\
   unpacked_challenge_prefix cp sigp (8 * W64.to_uint i)).
+ wp.
   while
     (lowp = low0 /\
      lcount = W64.of_int mode2_lcount /\
      0 <= W64.to_uint i < challenge_bytes /\
      b = zeroextu32 (BArray2948.get8 sigp (W64.to_uint i)) /\
      0 <= j <= 8 /\
      unpacked_challenge_prefix cp sigp (8 * W64.to_uint i + j)).
   - auto => /> &hr hi0 hilt hj0 hjle hprefix.
      move=> hloop.
      have hjlt : j{hr} < 8 by exact hloop.
      have hidx :
          W64.to_uint
            (W64.of_int 8 * i{hr} + W64.of_int j{hr}) =
          8 * W64.to_uint i{hr} + j{hr}.
      + rewrite W64.to_uintD_small 1:/#.
        rewrite W64.to_uintM_small 1:/# !W64.of_uintK /=.
        smt(W64.to_uint_cmp).
      have hbit :
          (((zeroextu32 (BArray2948.get8 sigp{hr} (W64.to_uint i{hr})))
             `>>` (W8.of_int j{hr})) `&` W32.one) =
          bitword ((BArray2948.get8 sigp{hr} (W64.to_uint i{hr})).[j{hr}]).
      + apply Mode2SignaturePrefixCodec.decode_w8_bit.
        smt(W64.to_uint_cmp).
      split.
      + split; smt().
      + have hwords_next :
            8 * W64.to_uint i{hr} + (j{hr} + 1) =
            (8 * W64.to_uint i{hr} + j{hr}) + 1 by ring.
        have hword_div :
            (8 * W64.to_uint i{hr} + j{hr}) %/ 8 =
            W64.to_uint i{hr}.
        + have -> :
              8 * W64.to_uint i{hr} + j{hr} =
              j{hr} + W64.to_uint i{hr} * 8 by ring.
          rewrite divzMDr 1:/# divz_small 1:/#.
          ring.
        have hword_mod :
            (8 * W64.to_uint i{hr} + j{hr}) %% 8 = j{hr}.
        + have -> :
              8 * W64.to_uint i{hr} + j{hr} =
              j{hr} + W64.to_uint i{hr} * 8 by ring.
          rewrite modzMDr modz_small 1:/#.
          trivial.
        rewrite hidx hbit hwords_next.
        apply unpacked_challenge_prefix_step; first by smt().
        + exact hprefix.
        + by rewrite hword_div hword_mod.
   - auto => />.
      move=> &hr hi0 hile hprefix hguard.
      have hilt : W64.to_uint i{hr} < challenge_bytes.
      + move: hguard.
        rewrite W64.ultE W64.of_uintK /=.
        smt(W64.to_uint_cmp).
      split; first exact hilt.
      move=> cp1 j0 hjdone hilt0 hj0 hjle hprefix1.
      have hj_eq : j0 = 8 by smt().
      have hi_next :
          W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
      + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      split.
      + rewrite hi_next.
        split; smt(W64.to_uint_cmp).
      + rewrite hi_next.
        have hcount :
            8 * (W64.to_uint i{hr} + 1) =
            8 * W64.to_uint i{hr} + 8 by ring.
        rewrite hcount.
        have -> :
            8 * W64.to_uint i{hr} + 8 =
            8 * W64.to_uint i{hr} + j0 by smt().
        exact hprefix1.
+ auto => />.
   split.
- apply unpacked_challenge_prefix_zero.
- move=> cp1 i0 hdone hi0 hile hprefix.
     move: hdone.
     rewrite W64.ultE W64.of_uintK /challenge_bytes /=.
     move=> hdone_int.
     have hi_done : W64.to_uint i0 = challenge_bytes.
     + rewrite /challenge_bytes.
       smt(W64.to_uint_cmp).
     have hwords_done :
         8 * W64.to_uint i0 = challenge_words.
     + rewrite hi_done /challenge_bytes /challenge_words.
       trivial.
     split.
     + split.
       - rewrite -hwords_done.
         exact hprefix.
       - apply unpacked_low_prefix_zero.
     + move=> i1 lowp1 hdone heqoff hchallenge
              hi1 hile1 hlowprefix1.
       have hieq : W64.to_uint i1 = low_words.
       - move: hdone.
         rewrite W64.ultE W64.of_uintK /mode2_lcount /low_words /=.
         smt(W64.to_uint_cmp).
       split.
       - exact (unpacked_challenge_prefix_canonical _ _ hchallenge).
       - apply (unpacked_low_prefix_canonical lowp1 sig0).
         rewrite -hieq.
         exact hlowprefix1.
qed.

lemma unpack_sig_full_mode2_canonical
    (cp0 : BArray1024.t)
    (low0 : BArray8192.t)
    (hbz0 h0 : BArray8192.t)
    (bad0 : BArray8.t)
    (sig0 : BArray2948.t)
    (h_symbolw0 : BArray2048.t)
    (h_dsymsw0 : BArray528.t)
    (hb_symbolw0 : BArray2048.t)
    (hb_dsymsw0 : BArray528.t) :
  hoare [Unpack._unpack_sig_full :
    cp = cp0 /\ lowp = low0 /\ hbzp = hbz0 /\ hp = h0 /\ badp = bad0 /\
    sigp = sig0 /\
    h_symbolwp = h_symbolw0 /\ h_dsymswp = h_dsymsw0 /\
    hb_symbolwp = hb_symbolw0 /\ hb_dsymswp = hb_dsymsw0 /\
    lcount_i = mode2_lcount
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res.`1 /\
    Mode2VerifyPrepareNorm.canonical_signed_low res.`2].
proof.
proc.
seq 11 :
  (Mode2VerifyPrepareNorm.canonical_challenge cp /\
   Mode2VerifyPrepareNorm.canonical_signed_low lowp).
+ call (unpack_sig_prefix_mode2_canonical cp0 low0 sig0).
   auto.
+ seq 25 :
    (Mode2VerifyPrepareNorm.canonical_challenge cp /\
     Mode2VerifyPrepareNorm.canonical_signed_low lowp).
  + wp.
    call (_ : true); first by auto.
    auto.
  if.
  + seq 12 :
      (Mode2VerifyPrepareNorm.canonical_challenge cp /\
       Mode2VerifyPrepareNorm.canonical_signed_low lowp).
    + wp.
      call (_ : true); first by auto.
      wp.
      call (_ : true); first by auto.
      wp.
      call (_ : true); first by auto.
      auto.
    if.
    + wp.
      call (_ : true); first by auto.
      auto.
    + auto.
  + auto.
qed.

end VerifySignaturePrefixCanonicalPostFreeze.
