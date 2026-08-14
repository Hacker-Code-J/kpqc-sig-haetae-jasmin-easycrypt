require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8192 BArray32768 Fq KeygenM23ArithmeticSpec
  KeygenM23MatrixSpec VerifyUnpackV3AssemblyPostFreeze
  VerifyUnpackV3NttBound17PostFreeze
  VerifyUnpackV3NttTightBoundPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3MatrixProfilePostFreeze.

op unpack_matrix_firstcol_bound25 (mat : BArray32768.t) : bool =
  forall i, 0 <= i < mode2_vec_words =>
    Fq.bw32
      (BArray32768.get32 mat (firstcol_slot_idx i)) 25.

op unpack_matrix_firstcol_bound20 (mat : BArray32768.t) : bool =
  forall i, 0 <= i < mode2_vec_words =>
    Fq.bw32
      (BArray32768.get32 mat (firstcol_slot_idx i)) 20.

op unpack_matrix_nonfirst_bound17 (mat : BArray32768.t) : bool =
  forall i, 0 <= i < mode2_doubled_words =>
    Fq.bw32
      (BArray32768.get32 mat (double_slot_idx i)) 17.

op verify_unpack_mode2_matrix_repr_bound25_17
    (mat : BArray32768.t) : bool =
  unpack_matrix_firstcol_bound25 mat /\
  unpack_matrix_nonfirst_bound17 mat.

op verify_unpack_mode2_matrix_repr_bound20_17
    (mat : BArray32768.t) : bool =
  unpack_matrix_firstcol_bound20 mat /\
  unpack_matrix_nonfirst_bound17 mat.

lemma verify_unpack_mode2_matrix_repr_bound20_17_get
    (mat : BArray32768.t) row col j :
  verify_unpack_mode2_matrix_repr_bound20_17 mat =>
  0 <= row < mode2_rows =>
  0 <= col < mode2_cols =>
  0 <= j < poly_words =>
  Fq.bw32 (BArray32768.get32 mat (mat_idx row col j))
    (if col = 0 then 20 else 17).
proof.
move=> [hfirst hnonfirst] hrow hcol hj.
case (col = 0) => hcol0.
+ subst col.
  have hi : 0 <= vec_idx row j < mode2_vec_words.
  + rewrite /vec_idx /mode2_vec_words /mode2_rows /poly_words.
    smt().
  have hslot := firstcol_slot_idxE row j hrow hj.
  rewrite -hslot.
  exact (hfirst (vec_idx row j) hi).
+ have hcol1 : 1 <= col < mode2_cols by smt().
  have hi :
      0 <= row * 768 + (col - 1) * 256 + j < mode2_doubled_words.
  + rewrite /mode2_doubled_words /mode2_rows /mode2_cols /poly_words.
    smt().
  have hslot := double_slot_idxE row col j hrow hcol1 hj.
  rewrite -hslot.
  exact (hnonfirst (row * 768 + (col - 1) * 256 + j) hi).
qed.

lemma verify_unpack_mode2_matrix_repr_bound25_17_get
    (mat : BArray32768.t) row col j :
  verify_unpack_mode2_matrix_repr_bound25_17 mat =>
  0 <= row < mode2_rows =>
  0 <= col < mode2_cols =>
  0 <= j < poly_words =>
  Fq.bw32 (BArray32768.get32 mat (mat_idx row col j))
    (if col = 0 then 25 else 17).
proof.
move=> [hfirst hnonfirst] hrow hcol hj.
case (col = 0) => hcol0.
+ subst col.
  have hi : 0 <= vec_idx row j < mode2_vec_words.
  + rewrite /vec_idx /mode2_vec_words /mode2_rows /poly_words.
    smt().
  have hslot := firstcol_slot_idxE row j hrow hj.
  rewrite -hslot.
  exact (hfirst (vec_idx row j) hi).
+ have hcol1 : 1 <= col < mode2_cols by smt().
  have hi :
      0 <= row * 768 + (col - 1) * 256 + j < mode2_doubled_words.
  + rewrite /mode2_doubled_words /mode2_rows /mode2_cols /poly_words.
    smt().
  have hslot := double_slot_idxE row col j hrow hcol1 hj.
  rewrite -hslot.
  exact (hnonfirst (row * 768 + (col - 1) * 256 + j) hi).
qed.

lemma ntt_bound25_to_firstcol_bound25
    (vec : BArray8192.t) (mat : BArray32768.t)
    (p0 p1 : Rq.poly) :
  VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
    vec p0 p1 =>
  mat_firstcol_install_prefix vec mat mode2_vec_words =>
  unpack_matrix_firstcol_bound25 mat.
proof.
rewrite
  /VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
  /KeygenM23ArithmeticSpec.wide_slice_repr_bound
  /KeygenM23ArithmeticSpec.wide_slice_bound.
move=> [[_ hbound0] [_ hbound1]] hinstall.
rewrite /unpack_matrix_firstcol_bound25 => i hi.
rewrite (hinstall i hi).
case (i < KeygenM23MatrixSpec.poly_words_i) => hfirst.
+ have hj : 0 <= i < KeygenM23MatrixSpec.poly_words_i by smt().
  have h := hbound0 i hj.
  by rewrite add0z in h.
+ have hj :
      0 <= i - KeygenM23MatrixSpec.poly_words_i <
        KeygenM23MatrixSpec.poly_words_i.
  + move: hi hfirst.
    rewrite /mode2_vec_words /mode2_rows /poly_words
            /KeygenM23MatrixSpec.poly_words_i.
    smt().
  have h := hbound1 (i - KeygenM23MatrixSpec.poly_words_i) hj.
  have <- :
      KeygenM23MatrixSpec.poly_words_i +
        (i - KeygenM23MatrixSpec.poly_words_i) = i by smt().
  exact h.
qed.

lemma ntt_bound20_to_firstcol_bound20
    (vec : BArray8192.t) (mat : BArray32768.t) :
  VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_output_bound20
    vec =>
  mat_firstcol_install_prefix vec mat mode2_vec_words =>
  unpack_matrix_firstcol_bound20 mat.
proof.
move=> hntt hinstall.
rewrite /unpack_matrix_firstcol_bound20 => i hi.
rewrite (hinstall i hi).
apply hntt.
move: hi.
rewrite
  /VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_words
  /VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_polys
  /mode2_vec_words /mode2_rows /poly_words
  /KeygenM23MatrixSpec.poly_words_i.
by smt().
qed.

lemma install_preserves_nonfirst_bound17
    (before after : BArray32768.t) :
  unpack_matrix_nonfirst_bound17 before =>
  mat_firstcol_install_frame before after mode2_vec_words =>
  unpack_matrix_nonfirst_bound17 after.
proof.
move=> hbound hframe.
rewrite /unpack_matrix_nonfirst_bound17 => n hn.
have hidx := double_slot_idx_bound n hn.
have hsame :
    BArray32768.get32 after (double_slot_idx n) =
    BArray32768.get32 before (double_slot_idx n).
+ apply hframe.
  + move: hidx; rewrite /BArray32768.size; smt().
  + move=> i hi.
    have hneq := firstcol_slot_idx_neq_double_slot i n hi hn.
    smt().
rewrite hsame.
exact (hbound n hn).
qed.

lemma verify_unpack_mode2_matrix_repr_bound25_17_of_install
    (vec : BArray8192.t) (before after : BArray32768.t)
    (p0 p1 : Rq.poly) :
  unpack_matrix_nonfirst_bound17 before =>
  VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
    vec p0 p1 =>
  mat_firstcol_install_prefix vec after mode2_vec_words =>
  mat_firstcol_install_frame before after mode2_vec_words =>
  verify_unpack_mode2_matrix_repr_bound25_17 after.
proof.
move=> hnonfirst hntt hprefix hframe.
split.
+ exact (ntt_bound25_to_firstcol_bound25 vec after p0 p1 hntt hprefix).
+ exact (install_preserves_nonfirst_bound17 before after hnonfirst hframe).
qed.

lemma verify_unpack_mode2_matrix_repr_bound20_17_of_install
    (vec : BArray8192.t) (before after : BArray32768.t) :
  unpack_matrix_nonfirst_bound17 before =>
  VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_output_bound20
    vec =>
  mat_firstcol_install_prefix vec after mode2_vec_words =>
  mat_firstcol_install_frame before after mode2_vec_words =>
  verify_unpack_mode2_matrix_repr_bound20_17 after.
proof.
move=> hnonfirst hntt hprefix hframe.
split.
+ exact (ntt_bound20_to_firstcol_bound20 vec after hntt hprefix).
+ exact (install_preserves_nonfirst_bound17 before after hnonfirst hframe).
qed.

lemma verify_unpack_mode2_matrix_repr_bound20_17_weaken
    (mat : BArray32768.t) :
  verify_unpack_mode2_matrix_repr_bound20_17 mat =>
  verify_unpack_mode2_matrix_repr_bound25_17 mat.
proof.
move=> [hfirst hnonfirst].
split.
+ rewrite /unpack_matrix_firstcol_bound25 => i hi.
  have h := hfirst i hi.
  move: h.
  rewrite /Fq.bw32.
  smt().
+ exact hnonfirst.
qed.

end VerifyUnpackV3MatrixProfilePostFreeze.
