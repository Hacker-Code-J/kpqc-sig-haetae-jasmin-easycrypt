require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray8192 BArray32768
               Fq Rq
               KeygenMode2ParentTarget
               KeygenM23MatrixSpec KeygenM23ArithmeticSpec
               KeygenM23FinalizeSpec KeygenM23FinalizeSemantics
               KeygenM23FinalizeArraySemantics
               KeygenM23FinalizeHAETAEBridge
               TargetKeygenM23Arithmetic TargetKeygenM23Finalize
               Mode2KeygenSnapshotAlgebra.

theory Mode2KeygenCoreEquation.

module Parent = KeygenMode2ParentTarget.M.

op centered_s2_active (s2 : BArray8192.t) : bool =
  forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    -1 <= W32.to_sint (BArray8192.get32 s2 i) <= 1.

op canonical_a_active (a : BArray8192.t) : bool =
  forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    W32.to_uint (BArray8192.get32 a i) <
      KeygenM23FinalizeSemantics.q.

lemma mode2_output_repr_bound16_word
    (bp : BArray8192.t)
    (mat : BArray32768.t)
    (p0 p1 p2 : Rq.poly) i :
  KeygenM23ArithmeticSpec.mode2_output_repr_bound16
    bp mat p0 p1 p2 =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  Fq.bw32 (BArray8192.get32 bp i) 16.
proof.
move=> hout hi.
move: hout.
rewrite /KeygenM23ArithmeticSpec.mode2_output_repr_bound16
        /KeygenM23ArithmeticSpec.wide_slice_repr_bound
        /KeygenM23ArithmeticSpec.wide_slice_bound.
move=> [[_ hb0] [_ hb1]].
case (i < KeygenM23MatrixSpec.poly_words_i).
+ move=> hi0.
  have h := hb0 i _.
  + smt().
  by move: h; rewrite add0z.
+ move=> hi0.
  have hj :
      0 <= i - KeygenM23MatrixSpec.poly_words_i <
        KeygenM23MatrixSpec.poly_words_i.
  + move: hi hi0.
    rewrite /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i.
    smt().
  have h := hb1 (i - KeygenM23MatrixSpec.poly_words_i) hj.
  have heq :
      KeygenM23MatrixSpec.poly_words_i +
        (i - KeygenM23MatrixSpec.poly_words_i) = i by ring.
  by move: h; rewrite heq.
qed.

lemma finalize_reachable_inputs_from_matrix_output
    (bp s2 a : BArray8192.t)
    (mat : BArray32768.t)
    (p0 p1 p2 : Rq.poly) :
  KeygenM23ArithmeticSpec.mode2_output_repr_bound16
    bp mat p0 p1 p2 =>
  centered_s2_active s2 =>
  canonical_a_active a =>
  KeygenM23FinalizeArraySemantics.finalize_reachable_inputs
    bp s2 a.
proof.
move=> hbp hs2 ha.
rewrite /KeygenM23FinalizeArraySemantics.finalize_reachable_inputs.
move=> i hi.
rewrite /KeygenM23FinalizeArraySemantics.reachable_word_inputs.
split.
+ exact (mode2_output_repr_bound16_word bp mat p0 p1 p2 i hbp hi).
split.
+ exact (hs2 i hi).
+ exact (ha i hi).
qed.

op actual_snapshot_mod2q_zero
    (pre_bp s2 a b1 adjusted : BArray8192.t) : bool =
  forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (2 * (W32.to_uint (BArray8192.get32 a i) -
              2 * W32.to_uint (BArray8192.get32 b1 i)) +
       2 * W32.to_sint (BArray8192.get32 pre_bp i) +
       2 * W32.to_sint (BArray8192.get32 adjusted i))
      0.

op actual_snapshot_low_high_decomposition
    (pre_bp s2 a b1 adjusted : BArray8192.t) : bool =
  forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    let r = KeygenM23FinalizeArraySemantics.raw_residue
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 s2 i)
      (BArray8192.get32 a i) in
    let b0 = KeygenM23FinalizeSemantics.vk_low_int r in
    r = 2 * W32.to_uint (BArray8192.get32 b1 i) + b0 /\
    -1 <= b0 <= 1 /\
    W32.to_sint (BArray8192.get32 adjusted i) =
      W32.to_sint (BArray8192.get32 s2 i) - b0.

lemma finalize_semantic_output_low_high_decomposition
    (pre_bp s2 a b1 adjusted : BArray8192.t) :
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    pre_bp s2 a b1 adjusted =>
  actual_snapshot_low_high_decomposition pre_bp s2 a b1 adjusted.
proof.
rewrite /KeygenM23FinalizeArraySemantics.finalize_semantic_output.
move=> [hwords _].
rewrite /actual_snapshot_low_high_decomposition => i hi /=.
have [hb1 hadjusted] := hwords i hi.
have hrange :
    0 <= KeygenM23FinalizeArraySemantics.raw_residue
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 s2 i)
      (BArray8192.get32 a i) < Mode2KeygenSnapshotAlgebra.q.
+ rewrite /KeygenM23FinalizeArraySemantics.raw_residue
          /Mode2KeygenSnapshotAlgebra.q.
  apply modz_cmp.
  by rewrite /KeygenM23FinalizeSemantics.q.
have hdecompose :=
  Mode2KeygenSnapshotAlgebra.snapshot_residue_exact_low_high
    (KeygenM23FinalizeArraySemantics.raw_residue
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 s2 i)
      (BArray8192.get32 a i)) hrange.
move: hdecompose => [hdecompose [hlow _]].
rewrite /Mode2KeygenSnapshotAlgebra.snapshot_high
        /Mode2KeygenSnapshotAlgebra.snapshot_low in hdecompose.
rewrite /Mode2KeygenSnapshotAlgebra.snapshot_low in hlow.
rewrite hb1.
split; first exact hdecompose.
split; first exact hlow.
exact hadjusted.
qed.

lemma finalize_semantic_output_snapshot_mod2q_zero
    (pre_bp s2 a b1 adjusted : BArray8192.t) :
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    pre_bp s2 a b1 adjusted =>
  actual_snapshot_mod2q_zero pre_bp s2 a b1 adjusted.
proof.
rewrite /KeygenM23FinalizeArraySemantics.finalize_semantic_output.
move=> [hwords _].
rewrite /actual_snapshot_mod2q_zero => i hi.
have [hb1 hadjusted] := hwords i hi.
have halgebra :=
  Mode2KeygenSnapshotAlgebra.snapshot_expression_from_product_congruent_mod_2q
    (W32.to_sint (BArray8192.get32 pre_bp i))
    (W32.to_sint (BArray8192.get32 s2 i))
    (W32.to_uint (BArray8192.get32 a i))
    0.
rewrite hb1 hadjusted.
move: halgebra.
rewrite /Mode2KeygenSnapshotAlgebra.snapshot_expression_from_product
        /Mode2KeygenSnapshotAlgebra.residue_high_from_product
        /Mode2KeygenSnapshotAlgebra.residue_low_from_product
        /Mode2KeygenSnapshotAlgebra.snapshot_high
        /Mode2KeygenSnapshotAlgebra.snapshot_low
        Mode2KeygenSnapshotAlgebra.array_raw_residue_matches_from_product.
trivial.
qed.

module ActualM23MatrixFinalizeSnapshot = {
  proc run
      (bp : BArray8192.t, s1hatp : BArray8192.t,
       mat : BArray32768.t, s1 : BArray8192.t,
       s2 : BArray8192.t, avec : BArray8192.t)
      : BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8192.t = {
    var pre_bp : BArray8192.t;

    (bp, s1hatp) <@ Parent._kp_m23_matrix
      (bp, s1hatp, mat, s1,
       W64.of_int KeygenM23MatrixSpec.mode2_rows_i,
       W64.of_int KeygenM23MatrixSpec.mode2_cols_i);
    pre_bp <- bp;
    (bp, s2) <@ Parent._keypair_finalize_m23
      (bp, s2, avec,
       W64.of_int KeygenM23MatrixSpec.mode2_b_words_i);
    return (pre_bp, s1hatp, bp, s2);
  }
}.

lemma actual_m23_matrix_finalize_snapshot
    (bp0 s1hat0 s10 s20 avec0 : BArray8192.t)
    (mat0 : BArray32768.t)
    (p0 p1 p2 : Rq.poly) :
  hoare [ActualM23MatrixFinalizeSnapshot.run :
    bp = bp0 /\ s1hatp = s1hat0 /\
    mat = mat0 /\ s1 = s10 /\ s2 = s20 /\ avec = avec0 /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 mat0 /\
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16
      s10 p0 p1 p2 /\
    centered_s2_active s20 /\
    canonical_a_active avec0
    ==>
    KeygenM23ArithmeticSpec.mode2_output_repr_bound16
      res.`1 mat0 p0 p1 p2 /\
    KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
      res.`2 p0 p1 p2 /\
    KeygenM23FinalizeSpec.finalize_output
      res.`1 s20 avec0 res.`3 res.`4 /\
    KeygenM23MatrixSpec.word_tail_frame
      bp0 res.`1 KeygenM23MatrixSpec.mode2_b_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      s1hat0 res.`2 KeygenM23MatrixSpec.mode2_s1_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      s20 res.`4 KeygenM23MatrixSpec.mode2_b_words_i].
proof.
proc.
seq 1 :
  (s2 = s20 /\ avec = avec0 /\
   KeygenM23ArithmeticSpec.mode2_output_repr_bound16
     bp mat0 p0 p1 p2 /\
   KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
     s1hatp p0 p1 p2 /\
   KeygenM23MatrixSpec.word_tail_frame
     bp0 bp KeygenM23MatrixSpec.mode2_b_words_i /\
   KeygenM23MatrixSpec.word_tail_frame
     s1hat0 s1hatp KeygenM23MatrixSpec.mode2_s1_words_i /\
   centered_s2_active s20 /\
   canonical_a_active avec0).
+ call
    (TargetKeygenM23Arithmetic.kp_m23_matrix_mode2_arithmetic_correct
      bp0 s1hat0 mat0 s10 p0 p1 p2).
  auto => />.
exlim bp => pre_bp0.
call
  (TargetKeygenM23Finalize.keypair_finalize_m23_mode2_correct
    pre_bp0 s20 avec0).
auto => />.
qed.

lemma actual_m23_matrix_finalize_semantic_snapshot
    (bp0 s1hat0 s10 s20 avec0 : BArray8192.t)
    (mat0 : BArray32768.t)
    (p0 p1 p2 : Rq.poly) :
  hoare [ActualM23MatrixFinalizeSnapshot.run :
    bp = bp0 /\ s1hatp = s1hat0 /\
    mat = mat0 /\ s1 = s10 /\ s2 = s20 /\ avec = avec0 /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 mat0 /\
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16
      s10 p0 p1 p2 /\
    centered_s2_active s20 /\
    canonical_a_active avec0
    ==>
    KeygenM23ArithmeticSpec.mode2_output_repr_bound16
      res.`1 mat0 p0 p1 p2 /\
    KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
      res.`2 p0 p1 p2 /\
    KeygenM23FinalizeSpec.finalize_output
      res.`1 s20 avec0 res.`3 res.`4 /\
    KeygenM23FinalizeArraySemantics.finalize_semantic_output
      res.`1 s20 avec0 res.`3 res.`4 /\
    actual_snapshot_low_high_decomposition
      res.`1 s20 avec0 res.`3 res.`4 /\
    KeygenM23FinalizeHAETAEBridge.finalize_haetae_semantic_output
      res.`1 s20 avec0 res.`3 res.`4 /\
    actual_snapshot_mod2q_zero
      res.`1 s20 avec0 res.`3 res.`4 /\
    KeygenM23MatrixSpec.word_tail_frame
      bp0 res.`1 KeygenM23MatrixSpec.mode2_b_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      bp0 res.`3 KeygenM23MatrixSpec.mode2_b_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      s1hat0 res.`2 KeygenM23MatrixSpec.mode2_s1_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      s20 res.`4 KeygenM23MatrixSpec.mode2_b_words_i].
proof.
conseq
  (actual_m23_matrix_finalize_snapshot
    bp0 s1hat0 s10 s20 avec0 mat0 p0 p1 p2) => //=.
move=> &m hpre result hpost.
move: hpre =>
  [_ [_ [_ [_ [_ [_ [_ [_ [hcenter hcanonical]]]]]]]]].
move: hpost =>
  [hout [hntt [hfinal [hpreframe [hhatframe hs2frame]]]]].
have hreachable :=
  finalize_reachable_inputs_from_matrix_output
    result.`1 s20 avec0 mat0 p0 p1 p2
    hout hcenter hcanonical.
have hsemantic :=
  KeygenM23FinalizeArraySemantics.finalize_output_semantics
    result.`1 s20 avec0 result.`3 result.`4
    hreachable hfinal.
have hhaetae :=
  KeygenM23FinalizeHAETAEBridge.finalize_semantic_output_haetae
    result.`1 s20 avec0 result.`3 result.`4 hsemantic.
have hdecomposition :=
  finalize_semantic_output_low_high_decomposition
    result.`1 s20 avec0 result.`3 result.`4 hsemantic.
have hmod2q :=
  finalize_semantic_output_snapshot_mod2q_zero
    result.`1 s20 avec0 result.`3 result.`4 hsemantic.
have hfinalframe :
    KeygenM23MatrixSpec.word_tail_frame
      result.`1 result.`3 KeygenM23MatrixSpec.mode2_b_words_i.
+ move: hsemantic.
  rewrite /KeygenM23FinalizeArraySemantics.finalize_semantic_output.
  by move=> [_ [h _]].
have hcomposedframe :=
  KeygenM23MatrixSpec.word_tail_frame_trans
    bp0 result.`1 result.`3 KeygenM23MatrixSpec.mode2_b_words_i
    hpreframe hfinalframe.
split; first exact hout.
split; first exact hntt.
split; first exact hfinal.
split; first exact hsemantic.
split; first exact hdecomposition.
split; first exact hhaetae.
split; first exact hmod2q.
split; first exact hpreframe.
split; first exact hcomposedframe.
split; first exact hhatframe.
exact hs2frame.
qed.

end Mode2KeygenCoreEquation.
