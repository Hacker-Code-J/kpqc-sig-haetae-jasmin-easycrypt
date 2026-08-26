require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2VerifyPrepareNorm
               VerifySignaturePrefixCanonicalPostFreeze
               RawSignApiTarget.

theory Mode2DecomposeZ1CanonicalPostFreeze.

module Sign = RawSignApiTarget.M.

(* Actual-word and loop partial correctness only.  This file proves that the
   Mode-2 z1 decomposition emits canonical signed-byte low words for every
   terminating call; it makes no signer-acceptance or distribution claim. *)

op center_word (b : W8.t) : W32.t =
  W32.of_int 128 - zeroextu32 b - W32.one.

op low_word (b : W8.t) : W32.t =
  zeroextu32 b -
    ((center_word b `|>>` W8.of_int 31) `&` W32.of_int 256).

lemma center_word_uint_low (b : W8.t) :
  W8.to_uint b < 128 =>
  W32.to_uint (center_word b) = 127 - W8.to_uint b.
proof.
move=> hb.
have -> : center_word b = W32.of_int (127 - W8.to_uint b).
+ rewrite /center_word.
  have -> : zeroextu32 b = W32.of_int (W8.to_uint b).
  + apply W32.to_uint_eq.
    rewrite W4u8.to_uint_zeroextu32 W32.of_uintK /=.
    have hbcmp := W8.to_uint_cmp b.
    by rewrite modz_small 1:/#.
  ring.
rewrite W32.to_uint_small; smt(W8.to_uint_cmp).
qed.

lemma center_word_uint_high (b : W8.t) :
  128 <= W8.to_uint b =>
  W32.to_uint (center_word b) =
    W32.modulus + 127 - W8.to_uint b.
proof.
move=> hb.
have -> : center_word b = W32.of_int (127 - W8.to_uint b).
+ rewrite /center_word.
  have -> : zeroextu32 b = W32.of_int (W8.to_uint b).
  + apply W32.to_uint_eq.
    rewrite W4u8.to_uint_zeroextu32 W32.of_uintK /=.
    have hbcmp := W8.to_uint_cmp b.
    by rewrite modz_small 1:/#.
  ring.
rewrite W32.of_uintK /=.
have hcmp := W8.to_uint_cmp b.
smt(@IntDiv).
qed.

lemma center_word_top_low (b : W8.t) :
  W8.to_uint b < 128 => !(center_word b).[31].
proof.
move=> hb.
rewrite W32.get_to_uint center_word_uint_low 1:hb /=.
smt(@IntDiv W8.to_uint_cmp).
qed.

lemma center_word_top_high (b : W8.t) :
  128 <= W8.to_uint b => (center_word b).[31].
proof.
move=> hb.
rewrite W32.get_to_uint center_word_uint_high 1:hb /=.
smt(@IntDiv W8.to_uint_cmp).
qed.

lemma sar31_zero (w : W32.t) :
  !w.[31] => w `|>>` W8.of_int 31 = W32.zero.
proof.
move=> htop.
apply W32.ext_eq => i hi.
rewrite /W32.(`|>>`) W32.sarE W32.initiE 1:hi W32.zerowE /=.
have -> : min 31 (i + 31) = 31 by smt().
smt().
qed.

lemma sar31_ones (w : W32.t) :
  w.[31] => w `|>>` W8.of_int 31 = W32.of_int (-1).
proof.
move=> htop.
apply W32.ext_eq => i hi.
rewrite /W32.(`|>>`) W32.sarE W32.initiE 1:hi /=.
have -> : min 31 (i + 31) = 31 by smt().
have -> : W32.of_int (-1) = W32.onew by rewrite /W32.onew.
rewrite W32.onewE.
by rewrite htop hi.
qed.

lemma byte_sub_mod (u : int) :
  128 <= u < 256 =>
  (u - 256) %% W32.modulus = u + (W32.modulus - 256).
proof.
move=> hu.
have -> : u - 256 = (u + (W32.modulus - 256)) + (-1) * W32.modulus
  by ring.
rewrite modzMDr modz_small; smt().
qed.

lemma low_word_low (b : W8.t) :
  W8.to_uint b < 128 =>
  low_word b = Mode2VerifyPrepareNorm.sign_extend_byte b.
proof.
move=> hblow.
have hsar : center_word b `|>>` W8.of_int 31 = W32.zero by
  apply sar31_zero; exact (center_word_top_low b hblow).
rewrite /low_word hsar W32.and0w.
have -> : zeroextu32 b - W32.zero = zeroextu32 b by ring.
have hnot : !(128 <= W8.to_uint b) by smt().
have hright : Mode2VerifyPrepareNorm.sign_extend_byte b = zeroextu32 b.
+ move: (VerifySignaturePrefixCanonicalPostFreeze.sign_extend_byte_mask b).
  rewrite VerifySignaturePrefixCanonicalPostFreeze.byte_top_bitE hnot /=.
  trivial.
rewrite hright.
trivial.
qed.

lemma low_wordE (b : W8.t) :
  low_word b = Mode2VerifyPrepareNorm.sign_extend_byte b.
proof.
case (128 <= W8.to_uint b) => hb.
+ rewrite /low_word sar31_ones 1:(center_word_top_high b hb).
  have -> : W32.of_int (-1) = W32.onew by rewrite /W32.onew.
  rewrite W32.andwC W32.andw1.
  rewrite VerifySignaturePrefixCanonicalPostFreeze.sign_extend_byte_mask
          VerifySignaturePrefixCanonicalPostFreeze.byte_top_bitE hb /=.
  have -> :
      zeroextu32 b - W32.of_int 256 =
      W32.of_int (W8.to_uint b - 256).
  + have -> : zeroextu32 b = W32.of_int (W8.to_uint b).
    + apply W32.to_uint_eq.
      rewrite W4u8.to_uint_zeroextu32 W32.of_uintK /=.
      have hbcmp := W8.to_uint_cmp b.
      by rewrite modz_small 1:/#.
    ring.
  apply W32.to_uint_eq.
  rewrite W32.of_uintK byte_sub_mod 1:/#.
  rewrite VerifySignaturePrefixCanonicalPostFreeze.sign_extended_byte_mask_uint.
  ring.
+ apply low_word_low.
  smt().
qed.

op decompose_low_word (a : W32.t) : W32.t =
  let lb = a `&` W32.of_int 255 in
  let center = W32.of_int 128 - lb - W32.one in
  lb - ((center `|>>` W8.of_int 31) `&` W32.of_int 256).

lemma decompose_low_wordE (a : W32.t) :
  decompose_low_word a =
  Mode2VerifyPrepareNorm.sign_extend_byte (truncateu8 a).
proof.
have hmask :
    a `&` W32.of_int 255 = zeroextu32 (truncateu8 a) by
  rewrite W4u8.zeroext_truncateu8_and.
rewrite /decompose_low_word hmask.
exact (low_wordE (truncateu8 a)).
qed.

op decompose_low_prefix
    (outp inp : BArray8192.t) (words : int) : bool =
  forall i, 0 <= i < words =>
    BArray8192.get32 outp i =
      Mode2VerifyPrepareNorm.sign_extend_byte
        (truncateu8 (BArray8192.get32 inp i)).

lemma decompose_low_prefix_zero outp inp :
  decompose_low_prefix outp inp 0.
proof. rewrite /decompose_low_prefix; smt(). qed.

lemma decompose_low_prefix_step outp inp words :
  0 <= words < 2048 =>
  decompose_low_prefix outp inp words =>
  decompose_low_prefix
    (BArray8192.set32 outp words
      (decompose_low_word (BArray8192.get32 inp words)))
    inp (words + 1).
proof.
move=> hwords hprefix.
rewrite /decompose_low_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = words) => heq.
+ subst i.
  exact (decompose_low_wordE (BArray8192.get32 inp words)).
+ rewrite ifF 1:/#.
  apply hprefix; smt().
qed.

lemma decompose_low_prefix_canonical outp inp :
  decompose_low_prefix outp inp 1024 =>
  Mode2VerifyPrepareNorm.canonical_signed_low outp.
proof.
move=> hprefix.
rewrite /Mode2VerifyPrepareNorm.canonical_signed_low => i hi.
rewrite hprefix 1:hi.
exact
  (VerifySignaturePrefixCanonicalPostFreeze.sign_extend_byte_canonical
    (truncateu8 (BArray8192.get32 inp i))).
qed.

lemma raw_polyvec_decompose_z1_mode2_canonical_low
    (ap0 : BArray8192.t) :
  hoare [Sign._polyvec_decompose_z1 :
    ap = ap0 /\ count = W64.of_int 1024
    ==>
    Mode2VerifyPrepareNorm.canonical_signed_low res.`1].
proof.
proc.
while
  (ap = ap0 /\ count = W64.of_int 1024 /\
   0 <= W64.to_uint i <= 1024 /\
   decompose_low_prefix lowp ap0 (W64.to_uint i)).
+ auto => /> &hr hi0 hile hprefix hguard.
  have hilt : W64.to_uint i{hr} < 1024.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hinext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  split.
  + rewrite hinext; smt(W64.to_uint_cmp).
  rewrite hinext.
  have hword :=
    decompose_low_wordE
      (BArray8192.get32 ap0 (W64.to_uint i{hr})).
  rewrite /decompose_low_word in hword.
  rewrite /decompose_low_prefix => j hj.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (j = W64.to_uint i{hr}) => heq.
  + subst j.
    exact hword.
  + rewrite ifF 1:/#.
    apply hprefix; smt().
auto => />.
move=> &hr.
split.
+ apply decompose_low_prefix_zero.
+ move=> final_i final_low hdone hi0 hile hprefix.
  have hieq : W64.to_uint final_i = 1024.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  apply (decompose_low_prefix_canonical final_low ap0).
  rewrite -hieq.
  exact hprefix.
qed.

end Mode2DecomposeZ1CanonicalPostFreeze.
