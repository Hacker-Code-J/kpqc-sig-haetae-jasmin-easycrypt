require import AllCore IntDiv List Ring.

require import Array256 BArray8192 BArray32768
               Rq NTT_Fq NTTFullSpec
               NTTRowProductSpec NTTFullSpectralAction
               KeygenM23MatrixSpec
               KeygenM23ArithmeticSpec
               Mode2KeygenCoreEquation.

theory Mode2KeygenNttMulBridge.

op mode2_vector (p0 p1 p2 : Rq.poly) (col : int) : Rq.poly =
  if col = 0 then p0 else if col = 1 then p1 else p2.

op mode2_matrix_hat (m : BArray32768.t) (row col : int) : Rq.poly =
  KeygenM23ArithmeticSpec.matrix_poly m row col.

op mode2_row_product
    (m : BArray32768.t) (p0 p1 p2 : Rq.poly) (row : int) : Rq.poly =
  NTTRowProductSpec.coefficient_row_product 3
    (fun r col => NTTFullSpec.full_invntt (mode2_matrix_hat m r col))
    (mode2_vector p0 p1 p2) row.

lemma pointwise_row_ntt_shared m p0 p1 p2 row :
  KeygenM23ArithmeticSpec.pointwise_row_ntt m p0 p1 p2 row =
  NTTRowProductSpec.pointwise_row 3
    (mode2_matrix_hat m) (mode2_vector p0 p1 p2) row.
proof.
apply Array256.ext_eq => j hj.
rewrite /KeygenM23ArithmeticSpec.pointwise_row_ntt
        Array256.initiE 1:/#.
rewrite NTTRowProductSpec.pointwise_row_get 1:hj.
rewrite /Rq.BigDom.BAdd.big /range /= filter_predT foldr_map.
rewrite /mode2_matrix_hat /mode2_vector /=.
rewrite (@iotaS 0 2) 1:/# /=
        (@iotaS 1 1) 1:/# /=
        (@iotaS 2 0) 1:/# /=
        (@iota0 3 0) 1:/# /=.
ring.
qed.

lemma keygen_mode2_row_product m p0 p1 p2 row :
  KeygenM23ArithmeticSpec.output_row m p0 p1 p2 row =
  mode2_row_product m p0 p1 p2 row.
proof.
rewrite /KeygenM23ArithmeticSpec.output_row
        pointwise_row_ntt_shared /mode2_row_product.
exact (NTTFullSpectralAction.full_ntt_montgomery_row_product
  3 (mode2_matrix_hat m) (mode2_vector p0 p1 p2) row).
qed.

lemma output_row_from_mode2_ntt_words
    (m : BArray32768.t) (v : BArray8192.t)
    (p0 p1 p2 : Rq.poly) (row : int) :
  KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24 v p0 p1 p2 =>
  KeygenM23ArithmeticSpec.output_row m p0 p1 p2 row =
    NTT_Fq.array256_mont
      (NTTFullSpec.full_invntt
        (KeygenM23ArithmeticSpec.pointwise_row_words m v row)).
proof.
move=> hntt.
rewrite /KeygenM23ArithmeticSpec.output_row.
have -> :=
  KeygenM23ArithmeticSpec.pointwise_row_words_ntt
    m v p0 p1 p2 row hntt.
trivial.
qed.

lemma output_row_repr_from_mode2_ntt_words
    (b v : BArray8192.t) (m : BArray32768.t)
    (p0 p1 p2 : Rq.poly) (row base : int) :
  KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24 v p0 p1 p2 =>
  KeygenM23ArithmeticSpec.wide_slice_repr_bound b base
    (NTT_Fq.array256_mont
      (NTTFullSpec.full_invntt
        (KeygenM23ArithmeticSpec.pointwise_row_words m v row))) 16 =>
  KeygenM23ArithmeticSpec.wide_slice_repr_bound b base
    (KeygenM23ArithmeticSpec.output_row m p0 p1 p2 row) 16.
proof.
move=> hntt hrepr.
rewrite (output_row_from_mode2_ntt_words m v p0 p1 p2 row hntt).
exact hrepr.
qed.

lemma actual_m23_matrix_snapshot_rows_explicit
    (bp0 s1hat0 s10 s20 avec0 : BArray8192.t)
    (mat0 : BArray32768.t)
    (p0 p1 p2 : Rq.poly) :
  hoare [Mode2KeygenCoreEquation.ActualM23MatrixFinalizeSnapshot.run :
    bp = bp0 /\ s1hatp = s1hat0 /\
    mat = mat0 /\ s1 = s10 /\ s2 = s20 /\ avec = avec0 /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 mat0 /\
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16
      s10 p0 p1 p2 /\
    Mode2KeygenCoreEquation.centered_s2_active s20 /\
    Mode2KeygenCoreEquation.canonical_a_active avec0
    ==>
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`1 0
      (NTT_Fq.array256_mont
        (NTTFullSpec.full_invntt
          (KeygenM23ArithmeticSpec.pointwise_row_words
            mat0 res.`2 0))) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`1 KeygenM23MatrixSpec.poly_words_i
      (NTT_Fq.array256_mont
        (NTTFullSpec.full_invntt
          (KeygenM23ArithmeticSpec.pointwise_row_words
            mat0 res.`2 1))) 16].
proof.
conseq
  (Mode2KeygenCoreEquation.actual_m23_matrix_finalize_semantic_snapshot
    bp0 s1hat0 s10 s20 avec0 mat0 p0 p1 p2) => //=.
move=> &m _ result hpost.
move: hpost =>
  [hout [hntt _]].
move: hout.
rewrite /KeygenM23ArithmeticSpec.mode2_output_repr_bound16.
move=> [hrow0 hrow1].
split.
+ move: hrow0.
  rewrite (output_row_from_mode2_ntt_words
    mat0 result.`2 p0 p1 p2 0 hntt).
  trivial.
move: hrow1.
rewrite (output_row_from_mode2_ntt_words
  mat0 result.`2 p0 p1 p2 1 hntt).
trivial.
qed.

lemma actual_m23_matrix_snapshot_rows_row_product
    (bp0 s1hat0 s10 s20 avec0 : BArray8192.t)
    (mat0 : BArray32768.t)
    (p0 p1 p2 : Rq.poly) :
  hoare [Mode2KeygenCoreEquation.ActualM23MatrixFinalizeSnapshot.run :
    bp = bp0 /\ s1hatp = s1hat0 /\
    mat = mat0 /\ s1 = s10 /\ s2 = s20 /\ avec = avec0 /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 mat0 /\
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16
      s10 p0 p1 p2 /\
    Mode2KeygenCoreEquation.centered_s2_active s20 /\
    Mode2KeygenCoreEquation.canonical_a_active avec0
    ==>
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`1 0 (mode2_row_product mat0 p0 p1 p2 0) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`1 KeygenM23MatrixSpec.poly_words_i
      (mode2_row_product mat0 p0 p1 p2 1) 16].
proof.
conseq
  (Mode2KeygenCoreEquation.actual_m23_matrix_finalize_semantic_snapshot
    bp0 s1hat0 s10 s20 avec0 mat0 p0 p1 p2) => //=.
move=> &m _ result hpost.
move: hpost => [hout _].
move: hout.
rewrite /KeygenM23ArithmeticSpec.mode2_output_repr_bound16.
move=> [hrow0 hrow1].
split.
+ by move: hrow0; rewrite keygen_mode2_row_product.
by move: hrow1; rewrite keygen_mode2_row_product.
qed.

end Mode2KeygenNttMulBridge.
