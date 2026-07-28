require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenMode2ParentTarget
               KeygenM23MatrixSpec KeygenM23FinalizeSpec.

theory TargetKeygenM23Finalize.

module Parent = KeygenMode2ParentTarget.M.

lemma freeze_word_correct (a0 : W32.t) :
  hoare [Parent.__freeze :
    a = a0
    ==>
    res = KeygenM23FinalizeSpec.freeze_word a0].
proof.
proc.
auto => />.
qed.

lemma freeze_word_ll :
  islossless Parent.__freeze.
proof.
proc.
islossless.
qed.

lemma keypair_finalize_m23_mode2_correct
    (bp0 s2p0 ap0 : BArray8192.t) :
  hoare [Parent._keypair_finalize_m23 :
    bp = bp0 /\ s2p = s2p0 /\ ap = ap0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_b_words_i
    ==>
    KeygenM23FinalizeSpec.finalize_output
      bp0 s2p0 ap0 res.`1 res.`2].
proof.
proc.
while
  (ap = ap0 /\
   count = W64.of_int KeygenM23MatrixSpec.mode2_b_words_i /\
   KeygenM23FinalizeSpec.finalize_prefix
     bp0 s2p0 ap0 bp s2p (W64.to_uint i)).
+ wp; ecall (freeze_word_correct b).
  auto => /> &hr hi0 hle hbp hs2 hbpframe hs2frame hguard.
  have hprefix :
      KeygenM23FinalizeSpec.finalize_prefix
        bp0 s2p0 ap0 bp{hr} s2p{hr} (W64.to_uint i{hr}).
  + rewrite /KeygenM23FinalizeSpec.finalize_prefix.
    smt().
  have hilt :
      W64.to_uint i{hr} <
        KeygenM23MatrixSpec.mode2_b_words_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i /=.
    trivial.
  have hstep :=
    KeygenM23FinalizeSpec.finalize_prefix_step
      bp0 s2p0 ap0 bp{hr} s2p{hr} (W64.to_uint i{hr})
      hprefix hilt.
  have hsucc :
      W64.to_uint (i{hr} + W64.one) =
        W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  have hiarray :
      0 <= W64.to_uint i{hr} <
        KeygenM23MatrixSpec.array_words_i.
  + move: hilt.
    rewrite /KeygenM23MatrixSpec.array_words_i
            /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i
            /BArray8192.size /=.
    smt().
  have hiframe :
      W64.to_uint i{hr} <= W64.to_uint i{hr} <
        KeygenM23MatrixSpec.array_words_i by smt().
  have hbcur :
      BArray8192.get32 bp{hr} (W64.to_uint i{hr}) =
      BArray8192.get32 bp0 (W64.to_uint i{hr}).
  + move: hbpframe.
    rewrite /KeygenM23MatrixSpec.word_tail_frame.
    move=> hframe.
    exact (hframe (W64.to_uint i{hr}) hiframe).
  have hs2cur :
      BArray8192.get32 s2p{hr} (W64.to_uint i{hr}) =
      BArray8192.get32 s2p0 (W64.to_uint i{hr}).
  + move: hs2frame.
    rewrite /KeygenM23MatrixSpec.word_tail_frame.
    move=> hframe.
    exact (hframe (W64.to_uint i{hr}) hiframe).
  rewrite hsucc hbcur hs2cur.
  rewrite /KeygenM23FinalizeSpec.finalize_prefix
          /KeygenM23FinalizeSpec.finalize_b_word
          /KeygenM23FinalizeSpec.finalize_s2_word
          /KeygenM23FinalizeSpec.frozen_sum_word
          /KeygenM23FinalizeSpec.egen_high_word
          /KeygenM23FinalizeSpec.egen_low_word in hstep.
  rewrite /= in hstep.
  move: hstep =>
    [hbound [hbpnext [hs2next [hbpnextframe hs2nextframe]]]].
  split.
  + split.
    + smt().
    + move=> _.
      smt().
  split.
  + move=> j hj0 hjlt.
    apply hbpnext.
    smt().
  split.
  + move=> j hj0 hjlt.
    apply hs2next.
    smt().
  split.
  + exact hbpnextframe.
  + exact hs2nextframe.
auto => />.
split.
+ split; smt().
+ move=> bp1 i0 s2p1 hdone hi0 hle
         hbpfin hs2fin hbpfinframe hs2finframe.
  have hieq :
      W64.to_uint i0 = KeygenM23MatrixSpec.mode2_b_words_i.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i /=.
    smt().
  rewrite -hieq.
  split.
  + move=> j hj0 hjlt.
    apply hbpfin.
    smt().
  split.
  + move=> j hj0 hjlt.
    apply hs2fin.
    smt().
  split.
  + exact hbpfinframe.
  + exact hs2finframe.
qed.

lemma keypair_finalize_m23_ll :
  islossless Parent._keypair_finalize_m23.
proof.
proc.
while (W64.to_uint i <= W64.to_uint count)
      (W64.to_uint count - W64.to_uint i).
+ move=> z.
  wp.
  call freeze_word_ll.
  auto => /> &hr hi hguard.
  rewrite W64.ultE in hguard.
  have hcount := W64.to_uint_cmp count{hr}.
  move: hcount => [_ hcount].
  have hsmall :
      W64.to_uint i{hr} + W64.to_uint W64.one < W64.modulus.
  + rewrite W64.to_uint1 ltzE.
    apply (lez_trans (W64.to_uint count{hr} + 1)).
    + rewrite lez_add2r -ltzE.
      exact hguard.
    + by rewrite -ltzE.
  rewrite W64.to_uintD_small 1:hsmall W64.to_uint1.
  split.
  + by rewrite -ltzE.
  + rewrite ltzE.
    have hident :
        W64.to_uint count{hr} - (W64.to_uint i{hr} + 1) + 1 =
        W64.to_uint count{hr} - W64.to_uint i{hr} by ring.
    by rewrite hident.
auto => />.
move=> &hr.
split.
+ have hcount := W64.to_uint_cmp count{hr}.
  by move: hcount => [hcount _].
+ move=> i0 hle hvariant.
  move: hvariant; rewrite subz_le0 => hge.
  by rewrite W64.ultE ltzNge hge.
qed.

lemma keypair_finalize_m23_mode2_ll
    (bp0 s2p0 ap0 : BArray8192.t) :
  phoare [Parent._keypair_finalize_m23 :
    bp = bp0 /\ s2p = s2p0 /\ ap = ap0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_b_words_i
    ==> true] = 1%r.
proof.
conseq keypair_finalize_m23_ll => //=.
qed.

end TargetKeygenM23Finalize.
