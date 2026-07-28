require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenMode2ParentTarget
               KeygenM23MatrixSpec KeygenM23ArithmeticSpec
               NTT_Fq NTTFullSpec
               TargetKeygenM23Matrix
               TargetKeygenM23WideNTT
               TargetKeygenM23Pointwise
               TargetKeygenM23WideInvNTT.

theory TargetKeygenM23Arithmetic.

module Parent = KeygenMode2ParentTarget.M.

lemma kp_m23_matrix_mode2_arithmetic_correct
    (bp0 s1hat0 : BArray8192.t)
    (ap0 : BArray32768.t)
    (s1p0 : BArray8192.t)
    (p0 p1 p2 : Rq.poly) :
  hoare [Parent._kp_m23_matrix :
    bp = bp0 /\ s1hatp = s1hat0 /\
    ap = ap0 /\ s1p = s1p0 /\
    rows = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    cols = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 ap0 /\
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16
      s1p0 p0 p1 p2
    ==>
    KeygenM23ArithmeticSpec.mode2_output_repr_bound16
      res.`1 ap0 p0 p1 p2 /\
    KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
      res.`2 p0 p1 p2 /\
    KeygenM23MatrixSpec.word_tail_frame
      bp0 res.`1 KeygenM23MatrixSpec.mode2_b_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      s1hat0 res.`2 KeygenM23MatrixSpec.mode2_s1_words_i].
proof.
proc.
seq 3 :
  (bp = bp0 /\ ap = ap0 /\ s1p = s1p0 /\
   rows = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
   cols = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
   KeygenM23ArithmeticSpec.matrix_active_bound16 ap0 /\
   KeygenM23ArithmeticSpec.mode2_input_repr_bound16
     s1hatp p0 p1 p2 /\
   KeygenM23MatrixSpec.word_tail_frame
     s1hat0 s1hatp KeygenM23MatrixSpec.mode2_s1_words_i).
  + call
    (TargetKeygenM23Matrix.kp_copy_vec_mode2_correct
       s1hat0 s1p0).
  auto => />.
  move=> _ hbound0 hbound1 hbound2 _ result hprefix _.
  have hin :
      KeygenM23ArithmeticSpec.mode2_input_repr_bound16
        s1p0
        (KeygenM23ArithmeticSpec.wide_poly s1p0 0)
        (KeygenM23ArithmeticSpec.wide_poly
          s1p0 KeygenM23MatrixSpec.poly_words_i)
        (KeygenM23ArithmeticSpec.wide_poly
          s1p0 (2 * KeygenM23MatrixSpec.poly_words_i)).
  + rewrite /KeygenM23ArithmeticSpec.mode2_input_repr_bound16
            /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
    by do split.
  have hprefix' :
      KeygenM23MatrixSpec.word_prefix_eq
        s1p0 result KeygenM23MatrixSpec.mode2_s1_words_i.
  + move: hprefix.
    rewrite /KeygenM23MatrixSpec.word_prefix_eq.
    move=> hp i hi.
    by rewrite hp.
  have hout :=
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16_prefix_eq
      s1p0 result
      (KeygenM23ArithmeticSpec.wide_poly s1p0 0)
      (KeygenM23ArithmeticSpec.wide_poly
        s1p0 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        s1p0 (2 * KeygenM23MatrixSpec.poly_words_i))
      hprefix' hin.
  exact hout.
exlim s1hatp => copied.
seq 1 :
  (bp = bp0 /\ ap = ap0 /\ s1p = s1p0 /\
   rows = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
   cols = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
   KeygenM23ArithmeticSpec.matrix_active_bound16 ap0 /\
   KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
     s1hatp p0 p1 p2 /\
   KeygenM23MatrixSpec.word_tail_frame
     s1hat0 s1hatp KeygenM23MatrixSpec.mode2_s1_words_i).
  + call
    (TargetKeygenM23WideNTT.parent_polyvec_ntt_mode2_correct
       copied p0 p1 p2).
  auto => />.
  move=> _ _ _ _ hcopy result _ _ _ _ _ _ hntt.
  exact
    (KeygenM23MatrixSpec.word_tail_frame_trans
       s1hat0 copied result KeygenM23MatrixSpec.mode2_s1_words_i
       hcopy hntt).
exlim s1hatp => transformed.
seq 10 :
  (ap = ap0 /\ s1hatp = transformed /\
   rows = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
   KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
     transformed p0 p1 p2 /\
   KeygenM23ArithmeticSpec.mode2_pointwise_repr_bound18
     bp ap0 transformed /\
   KeygenM23MatrixSpec.word_tail_frame
     bp0 bp KeygenM23MatrixSpec.mode2_b_words_i /\
   KeygenM23MatrixSpec.word_tail_frame
     s1hat0 transformed KeygenM23MatrixSpec.mode2_s1_words_i).
+ wp.
  call
    (TargetKeygenM23Pointwise.polymat_pointwise_mode2_repr_bound18_frame
       bp0 ap0 transformed p0 p1 p2).
  wp.
  auto => />;
    rewrite /SLH64.protect_64 /SLH64.protect_ptr.
exlim bp => pointwise.
call
  (TargetKeygenM23WideInvNTT.polyvec_invntt_mode2_pointwise_correct18
     pointwise ap0 transformed).
auto => />.
move=> hntt0 hnttb0 hntt1 hnttb1 hntt2 hnttb2
        _ _ _ _ hbp hs1 result
        hout0 houtb0 hout1 houtb1 hinv.
have hntt :
    KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
      transformed p0 p1 p2.
+ rewrite /KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
          /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  by do split.
have hinvrows :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      result 0
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (KeygenM23ArithmeticSpec.pointwise_row_words
              ap0 transformed 0))) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      result KeygenM23MatrixSpec.poly_words_i
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (KeygenM23ArithmeticSpec.pointwise_row_words
              ap0 transformed 1))) 16.
+ rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  by do split.
have houtput :=
  KeygenM23ArithmeticSpec.mode2_output_words_ntt
    result ap0 transformed p0 p1 p2 hntt hinvrows.
split.
+ move: houtput.
  rewrite /KeygenM23ArithmeticSpec.mode2_output_repr_bound16
          /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  by move=> [[heq0 _] [heq1 _]].
exact
  (KeygenM23MatrixSpec.word_tail_frame_trans
     bp0 pointwise result KeygenM23MatrixSpec.mode2_b_words_i
     hbp hinv).
qed.

end TargetKeygenM23Arithmetic.
