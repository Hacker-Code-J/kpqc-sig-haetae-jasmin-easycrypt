require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignatureUnpackMode2Target.
require import Mode2HbzCodecSpec Mode2VerifyPrepareNorm.

theory VerifyHbzDecodeCanonicalPostFreeze.

import Mode2HbzCodecSpec.

module Unpack = SignatureUnpackMode2Target.M.

op mode2_symbol_prefix_bound
    (symsp : BArray2048.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    W8.to_uint (BArray2048.get8 symsp i) < mode2_hbz_alphabet.

op canonical_hbz_prefix
    (hbz : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    -mode2_hbz_offset <= W32.to_sint (BArray8192.get32 hbz i) <
      mode2_hbz_alphabet - mode2_hbz_offset.

lemma mode2_symbol_prefix_bound_zero symsp :
  mode2_symbol_prefix_bound symsp 0.
proof. rewrite /mode2_symbol_prefix_bound; smt(). qed.

lemma canonical_hbz_prefix_zero hbz :
  canonical_hbz_prefix hbz 0.
proof. rewrite /canonical_hbz_prefix; smt(). qed.

lemma mode2_symbol_prefix_bound_step symsp n s :
  0 <= n < mode2_hbz_count =>
  mode2_symbol_prefix_bound symsp n =>
  W8.to_uint s < mode2_hbz_alphabet =>
  mode2_symbol_prefix_bound (BArray2048.set8 symsp n s) (n + 1).
proof.
move=> hn hprefix hs.
rewrite /mode2_symbol_prefix_bound => i hi.
rewrite BArray2048.get_setE 1:/#.
case (i = n) => heq.
+ by subst i.
+ apply hprefix; smt().
qed.

lemma canonical_hbz_prefix_step hbz n w :
  0 <= n < mode2_hbz_count =>
  canonical_hbz_prefix hbz n =>
  -mode2_hbz_offset <= W32.to_sint w <
    mode2_hbz_alphabet - mode2_hbz_offset =>
  canonical_hbz_prefix (BArray8192.set32 hbz n w) (n + 1).
proof.
move=> hn hprefix hw.
rewrite /canonical_hbz_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ by rewrite ifF 1:/#; apply hprefix; smt().
qed.

lemma mode2_symbol_byte_decodes_canonical (s : W8.t) :
  W8.to_uint s < mode2_hbz_alphabet =>
  -mode2_hbz_offset <=
    W32.to_sint (zeroextu32 s - W32.of_int mode2_hbz_offset) <
    mode2_hbz_alphabet - mode2_hbz_offset.
proof.
move=> hs.
have hsmall :
    W32.min_sint <=
      W32.to_sint (zeroextu32 s) -
      W32.to_sint (W32.of_int mode2_hbz_offset) <=
    W32.max_sint.
+ rewrite zeroextu32_word W32.to_sintK_small /= 1:/#.
   rewrite W32.to_sintK_small /= 1:/#.
   smt(W8.to_uint_cmp).
rewrite W32.to_sintB_small 1:hsmall.
rewrite zeroextu32_word W32.to_sintK_small /= 1:/#.
rewrite W32.to_sintK_small /= 1:/#.
smt(W8.to_uint_cmp).
qed.

lemma canonical_hbz_prefix_implies_verify hbz n :
  n = mode2_hbz_count =>
  canonical_hbz_prefix hbz n =>
  Mode2VerifyPrepareNorm.canonical_hbz_mode2 hbz.
proof.
move=> -> hprefix.
rewrite /Mode2VerifyPrepareNorm.canonical_hbz_mode2 /canonical_hbz_prefix.
move=> i hi.
apply hprefix.
rewrite /Mode2VerifyPrepareNorm.low_words in hi.
exact hi.
qed.

lemma decode_hb_z1_apply_mode2_symbol_prefix_canonical
    (hbz0 : BArray8192.t) (symsp0 : BArray2048.t) :
  hoare [Unpack._decode_hb_z1_apply :
    hp = hbz0 /\
    symsp = symsp0 /\
    count = W64.of_int mode2_hbz_count /\
    offset = W64.of_int mode2_hbz_offset /\
    mode2_symbol_prefix_bound symsp0 mode2_hbz_count
    ==>
    canonical_hbz_prefix res mode2_hbz_count /\
    Mode2VerifyPrepareNorm.coeff_tail_frame hbz0 res mode2_hbz_count].
proof.
proc.
while
  (symsp = symsp0 /\
   count = W64.of_int mode2_hbz_count /\
   offset = W64.of_int mode2_hbz_offset /\
   off32 = W32.of_int mode2_hbz_offset /\
   mode2_symbol_prefix_bound symsp0 mode2_hbz_count /\
   0 <= W64.to_uint i <= mode2_hbz_count /\
   canonical_hbz_prefix hp (W64.to_uint i) /\
   Mode2VerifyPrepareNorm.coeff_tail_frame hbz0 hp mode2_hbz_count).
+ auto => /> &hr hprefix hi0 hile hcanon hframe hguard.
   have hilt : W64.to_uint i{hr} < mode2_hbz_count.
   + move: hguard.
     rewrite W64.ultE W64.of_uintK /=.
     smt(W64.to_uint_cmp).
  have hs :
      W8.to_uint (BArray2048.get8 symsp0 (W64.to_uint i{hr})) <
      mode2_hbz_alphabet.
  + rewrite /mode2_symbol_prefix_bound in hprefix.
    apply hprefix; smt().
   have hw :
       -mode2_hbz_offset <=
         W32.to_sint
           (zeroextu32 (BArray2048.get8 symsp0 (W64.to_uint i{hr})) -
            W32.of_int mode2_hbz_offset) <
         mode2_hbz_alphabet - mode2_hbz_offset.
   + exact (mode2_symbol_byte_decodes_canonical
       (BArray2048.get8 symsp0 (W64.to_uint i{hr})) hs).
   have hi_next :
       W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
   + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
     trivial.
  split; first by rewrite hi_next; smt(W64.to_uint_cmp).
   split.
   + rewrite hi_next.
     apply canonical_hbz_prefix_step; first by smt().
     exact hcanon.
     exact hw.
   + apply Mode2HbzCodecSpec.coeff_tail_frame_set_before; first by smt().
     exact hframe.
+ auto => />.
move=> &hr.
split.
+ apply canonical_hbz_prefix_zero.
+ move=> hp1 i1 hdone _ hi0 hile hcanon hframe.
  have hieq : W64.to_uint i1 = mode2_hbz_count.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  rewrite -hieq.
  exact hcanon.
qed.

end VerifyHbzDecodeCanonicalPostFreeze.
