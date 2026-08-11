require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import HbzPrepareTarget Mode2HbzCodecSpec.

theory Mode2HbzPrepare.

import Mode2HbzCodecSpec.

module Prepare = HbzPrepareTarget.M.

lemma encode_hb_z1_prepare_core_mode2_correct
    (symbols0 : BArray2048.t)
    (bad0 : BArray8.t)
    (hbz0 : BArray8192.t) :
  hoare [Prepare._encode_hb_z1_prepare :
    symsp = symbols0 /\ badp = bad0 /\ hp = hbz0 /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset /\
    canonical_hbz_mode2 hbz0
    ==>
    BArray8.get64 res.`2 0 = W64.zero /\
    prepared_hbz_prefix res.`1 hbz0 mode2_hbz_count /\
    byte_tail_frame symbols0 res.`1 mode2_hbz_count].
proof.
proc.
wp.
while
  (hp = hbz0 /\
   count = W64.of_int mode2_hbz_count /\
   mhb = W64.of_int mode2_hbz_alphabet /\
   offset = W64.of_int mode2_hbz_offset /\
   canonical_hbz_mode2 hbz0 /\
   bad = W64.zero /\
   0 <= W64.to_uint i <= mode2_hbz_count /\
   prepared_hbz_prefix symsp hbz0 (W64.to_uint i) /\
   byte_tail_frame symbols0 symsp mode2_hbz_count).
+ auto => /> &hr hcanon hi0 hile hprefix hframe hguard.
  have hilt : W64.to_uint i{hr} < mode2_hbz_count.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hword :
      -mode2_hbz_offset <=
        W32.to_sint (BArray8192.get32 hbz0 (W64.to_uint i{hr})) <
      mode2_hbz_alphabet - mode2_hbz_offset.
  + rewrite /canonical_hbz_mode2 in hcanon.
    apply hcanon; smt().
  have hneg := hbz_prepare_neg_zero
    (BArray8192.get32 hbz0 (W64.to_uint i{hr})) hword.
  have hlt := hbz_prepare_tmp_lt_alphabet
    (BArray8192.get32 hbz0 (W64.to_uint i{hr})) hword.
  have hsymbol := hbz_prepare_truncate_symbol
    (BArray8192.get32 hbz0 (W64.to_uint i{hr})) hword.
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  rewrite hneg hlt hsymbol.
  rewrite /protect_64 /=.
  split; first by rewrite hi_next; smt(W64.to_uint_cmp).
  split.
  + rewrite hi_next.
    rewrite /prepared_hbz_prefix => k hk.
    rewrite BArray2048.get_setE 1:/#.
    case (k = W64.to_uint i{hr}) => heq.
    * by subst k.
    * rewrite /prepared_hbz_prefix in hprefix.
      apply hprefix; smt().
  + apply byte_tail_frame_set_before; first by smt().
    exact hframe.
auto => />.
move=> hcanon.
split.
+ apply prepared_hbz_prefix_zero.
+ move=> i1 symsp1 hdone _ _ _ hi0 hile hprefix hframe.
  have hieq : W64.to_uint i1 = mode2_hbz_count.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  rewrite -hieq.
  exact hprefix.
qed.

lemma encode_hb_z1_prepare_mode2_correct
    (symbols0 : BArray2048.t)
    (bad0 : BArray8.t)
    (hbz0 : BArray8192.t) :
  hoare [Prepare.encode_hb_z1_prepare_jazz :
    symsp = symbols0 /\ badp = bad0 /\ hp = hbz0 /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset /\
    canonical_hbz_mode2 hbz0
    ==>
    BArray8.get64 res.`2 0 = W64.zero /\
    prepared_hbz_prefix res.`1 hbz0 mode2_hbz_count /\
    byte_tail_frame symbols0 res.`1 mode2_hbz_count].
proof.
proc.
call (encode_hb_z1_prepare_core_mode2_correct symbols0 bad0 hbz0).
auto.
qed.

end Mode2HbzPrepare.
