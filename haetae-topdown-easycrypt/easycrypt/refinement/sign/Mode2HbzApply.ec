require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import HbzApplyTarget Mode2HbzCodecSpec.

theory Mode2HbzApply.

import Mode2HbzCodecSpec.

module Apply = HbzApplyTarget.M.

lemma decode_hb_z1_apply_core_mode2_correct
    (decoded0 original0 : BArray8192.t) :
  hoare [Apply._decode_hb_z1_apply :
    hp = decoded0 /\
    count = W64.of_int mode2_hbz_count /\
    offset = W64.of_int mode2_hbz_offset /\
    canonical_hbz_mode2 original0 /\
    prepared_hbz_prefix symsp original0 mode2_hbz_count
    ==>
    decoded_hbz_prefix res original0 mode2_hbz_count /\
    coeff_tail_frame decoded0 res mode2_hbz_count].
proof.
proc.
while
  (count = W64.of_int mode2_hbz_count /\
   offset = W64.of_int mode2_hbz_offset /\
   off32 = W32.of_int mode2_hbz_offset /\
   canonical_hbz_mode2 original0 /\
   prepared_hbz_prefix symsp original0 mode2_hbz_count /\
   0 <= W64.to_uint i <= mode2_hbz_count /\
   decoded_hbz_prefix hp original0 (W64.to_uint i) /\
   coeff_tail_frame decoded0 hp mode2_hbz_count).
+ auto => /> &hr hcanon hsymbols hi0 hile hdecoded hframe hguard.
  have hilt : W64.to_uint i{hr} < mode2_hbz_count.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hword :
      -mode2_hbz_offset <=
        W32.to_sint
          (BArray8192.get32 original0 (W64.to_uint i{hr})) <
      mode2_hbz_alphabet - mode2_hbz_offset.
  + rewrite /canonical_hbz_mode2 in hcanon.
    apply hcanon; smt().
  have hsym :
      BArray2048.get8 symsp{hr} (W64.to_uint i{hr}) =
      hbz_symbol_word
        (BArray8192.get32 original0 (W64.to_uint i{hr})).
  + rewrite /prepared_hbz_prefix in hsymbols.
    apply hsymbols; smt().
  have hinverse := hbz_apply_symbol_inverse
    (BArray8192.get32 original0 (W64.to_uint i{hr})) hword.
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  rewrite /mode2_hbz_offset in hinverse.
  rewrite hsym hinverse.
  split; first by rewrite hi_next; smt(W64.to_uint_cmp).
  split.
  + rewrite hi_next.
    apply decoded_hbz_prefix_step; first by smt().
    exact hdecoded.
  + apply coeff_tail_frame_set_before; first by smt().
    exact hframe.
auto => />.
move=> &hr hcanon hsymbols.
split.
+ apply decoded_hbz_prefix_zero.
+ move=> hp1 i1 hdone _ hi0 hile hdecoded hframe.
  have hieq : W64.to_uint i1 = mode2_hbz_count.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  rewrite -hieq.
  exact hdecoded.
qed.

lemma decode_hb_z1_apply_mode2_correct
    (decoded0 original0 : BArray8192.t) :
  hoare [Apply.decode_hb_z1_apply_jazz :
    hp = decoded0 /\
    count = W64.of_int mode2_hbz_count /\
    offset = W64.of_int mode2_hbz_offset /\
    canonical_hbz_mode2 original0 /\
    prepared_hbz_prefix symsp original0 mode2_hbz_count
    ==>
    decoded_hbz_prefix res original0 mode2_hbz_count /\
    coeff_tail_frame decoded0 res mode2_hbz_count].
proof.
proc.
call (decode_hb_z1_apply_core_mode2_correct
        decoded0 original0).
auto.
qed.

end Mode2HbzApply.
