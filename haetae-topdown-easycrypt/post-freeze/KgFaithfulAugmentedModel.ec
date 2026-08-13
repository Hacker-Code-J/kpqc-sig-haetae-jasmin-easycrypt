require import AllCore IntDiv List Ring.

from Jasmin require import JModel_x86.

require import Array256 BArray32 BArray128 BArray8192 BArray32768.
require import Fq GFq Rq NTT_Fq NTTFullSpec.
require import HAETAE_Params HAETAE_Algebra.
require import KeygenM23MatrixSpec KeygenM23ArithmeticSpec.
require import KeygenM23FinalizeSemantics.
require import Mode2KeygenSnapshotAlgebra Mode2KeygenCoreEquation
               Mode2KeygenNttMulBridge.
require import TargetKeygenM23FinalizeComposition
               TargetKeygenM23FinalizeSemanticComposition.
require import KgActualAvecQjSemantics KgActualAvecQjComposition.
require import RqHAETAEBridge.

theory KgFaithfulAugmentedModel.

import Zq.

op ring_one_coeff (coeff : int) : int =
  if coeff = 0 then 1 else 0.

(* j=(1,0)^T: only row zero's constant coefficient is one. *)
op faithful_j_coeff (row coeff : int) : int =
  if row = 0 /\ coeff = 0 then 1 else 0.

op faithful_qj_coeff (row coeff : int) : int =
  KeygenM23FinalizeSemantics.q * faithful_j_coeff row coeff.

lemma faithful_qj_coeffE row coeff :
  faithful_qj_coeff row coeff =
  KgActualAvecQjSemantics.paper_qj_coeff row coeff.
proof.
by rewrite /faithful_qj_coeff /faithful_j_coeff
           /KgActualAvecQjSemantics.paper_qj_coeff
           /KgActualAvecQjSemantics.paper_j_coeff.
qed.

op two_i2_coeff (row idcol coeff : int) : int =
  2 * (if row = idcol /\ coeff = 0 then 1 else 0).

op faithful_head_coeff
    (a b1 : int -> int -> int) row coeff : int =
  2 * (a row coeff - 2 * b1 row coeff) +
  faithful_qj_coeff row coeff.

op faithful_generated_matrix_coeff
    (agen : int -> int -> int -> int) row col coeff : int =
  if 0 <= col < 3 then 2 * agen row col coeff else 0.

op faithful_identity_matrix_coeff row col coeff : int =
  if col = 0 then two_i2_coeff row 0 coeff
  else if col = 1 then two_i2_coeff row 1 coeff
  else 0.

op faithful_augmented_matrix_coeff
    (agen : int -> int -> int -> int)
    (a b1 : int -> int -> int) row col coeff : int =
  if col = 0 then faithful_head_coeff a b1 row coeff
  else if 1 <= col < 4 then
    faithful_generated_matrix_coeff agen row (col - 1) coeff
  else if 4 <= col < 6 then
    faithful_identity_matrix_coeff row (col - 4) coeff
  else 0.

op faithful_augmented_secret_coeff
    (sgen : int -> int -> int)
    (eadj : int -> int -> int) col coeff : int =
  if col = 0 then ring_one_coeff coeff
  else if 1 <= col < 4 then sgen (col - 1) coeff
  else if 4 <= col < 6 then eadj (col - 4) coeff
  else 0.

(* The width-6 carrier exposes the paper-faithful block structure explicitly.
   Because ring multiplication is not coefficientwise, the middle 2x3 block is
   consumed through a supplied generated-product coefficient. *)
op faithful_augmented_As_coeff
    (a b1 : int -> int -> int)
    (generated eadj : int -> int -> int)
    row coeff : int =
  faithful_head_coeff a b1 row coeff +
  2 * generated row coeff +
  2 * eadj row coeff.

lemma congruent_mod_2q_add x1 y1 x2 y2 :
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q x1 y1 =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q x2 y2 =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q (x1 + x2) (y1 + y2).
proof.
rewrite /Mode2KeygenSnapshotAlgebra.congruent_mod_2q.
move=> h1 h2.
have hdiv1 := divz_eq (x1 - y1) Mode2KeygenSnapshotAlgebra.q2.
have hdiv2 := divz_eq (x2 - y2) Mode2KeygenSnapshotAlgebra.q2.
move: h1 h2 hdiv1 hdiv2.
smt().
qed.

lemma congruent_mod_2q_trans x y z :
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q x y =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q y z =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q x z.
proof.
rewrite /Mode2KeygenSnapshotAlgebra.congruent_mod_2q.
move=> hxy hyz.
have hdiv1 := divz_eq (x - y) Mode2KeygenSnapshotAlgebra.q2.
have hdiv2 := divz_eq (y - z) Mode2KeygenSnapshotAlgebra.q2.
move: hxy hyz hdiv1 hdiv2.
smt().
qed.

lemma faithful_augmented_As_qj_of_generated_zero
    (a b1 generated eadj : int -> int -> int) row coeff :
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (2 * (a row coeff - 2 * b1 row coeff) +
     2 * generated row coeff +
     2 * eadj row coeff)
    0 =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (faithful_augmented_As_coeff a b1 generated eadj row coeff)
    (faithful_qj_coeff row coeff).
proof.
rewrite /faithful_augmented_As_coeff /faithful_head_coeff.
rewrite /Mode2KeygenSnapshotAlgebra.congruent_mod_2q.
move=> hzero.
move: hzero.
smt(divz_eq).
qed.

op actual_array_coeff
    (arr : BArray8192.t) (row coeff : int) : int =
  W32.to_uint (BArray8192.get32 arr (row * 256 + coeff)).

op actual_centered_coeff
    (arr : BArray8192.t) (row coeff : int) : int =
  W32.to_sint (BArray8192.get32 arr (row * 256 + coeff)).

lemma actual_snapshot_paper_qj_to_faithful_augmented
    (pre_bp sampled_s2 a b1 adjusted : BArray8192.t)
    row coeff :
  KgActualAvecQjComposition.actual_snapshot_paper_qj
    pre_bp sampled_s2 a b1 adjusted =>
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (faithful_augmented_As_coeff
      (actual_array_coeff a)
      (actual_array_coeff b1)
      (actual_centered_coeff pre_bp)
      (actual_centered_coeff adjusted)
      row coeff)
    (faithful_qj_coeff row coeff).
proof.
move=> hactual hrow hcoeff.
have hqj := hactual row coeff hrow hcoeff.
move: hqj.
rewrite /KgActualAvecQjComposition.actual_snapshot_paper_qj.
rewrite /faithful_augmented_As_coeff /faithful_head_coeff.
rewrite /actual_array_coeff /actual_centered_coeff.
trivial.
qed.

lemma checked_mode2_parent_m23_finalize_faithful_augmented
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [
    TargetKeygenM23FinalizeComposition.CheckedMode2ParentM23Finalize.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0
    ==>
    KgActualAvecQjComposition.actual_paper_mode2_a res.`3 res.`1 /\
    (forall row coeff,
      0 <= row < 2 =>
      0 <= coeff < 256 =>
      Mode2KeygenSnapshotAlgebra.congruent_mod_2q
        (faithful_augmented_As_coeff
          (actual_array_coeff res.`3)
          (actual_array_coeff res.`9)
          (actual_centered_coeff res.`7)
          (actual_centered_coeff res.`10)
          row coeff)
        (faithful_qj_coeff row coeff))].
proof.
conseq
  (KgActualAvecQjComposition.checked_mode2_parent_m23_finalize_actual_avec_qj
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result [ha hqj].
split; first exact ha.
move=> row coeff hrow hcoeff.
exact
  (actual_snapshot_paper_qj_to_faithful_augmented
    result.`7 result.`5 result.`3 result.`9 result.`10
    row coeff hqj hrow hcoeff).
qed.

lemma double_congruent_mod_2q_of_incoeff_eq (x y : int) :
  incoeff x = incoeff y =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q (2 * x) (2 * y).
proof.
move=> hxy.
have hmodq : (x - y) %% KeygenM23FinalizeSemantics.q = 0.
+ move: hxy.
   rewrite -eq_incoeff /GFq.q /KeygenM23FinalizeSemantics.q /=.
   smt(divz_eq).
have hdiv := divz_eq (x - y) KeygenM23FinalizeSemantics.q.
rewrite /Mode2KeygenSnapshotAlgebra.congruent_mod_2q
        /Mode2KeygenSnapshotAlgebra.q2
        /Mode2KeygenSnapshotAlgebra.q.
move: hmodq hdiv.
smt().
qed.

lemma generated_product_coeff_from_rq_repr
    (pre_bp : BArray8192.t) row coeff
    (row_product : Rq.poly)
    (hprod : HAETAE_Algebra.poly) :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    pre_bp (row * 256) row_product 16 =>
  RqHAETAEBridge.rq_poly_repr row_product hprod =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (2 * HAETAE_Algebra.poly_coeff hprod coeff)
    (2 * W32.to_sint (BArray8192.get32 pre_bp (row * 256 + coeff))).
proof.
move=> hrow hcoeff [hrepr hbound] hrq.
have hcoeff256 : 0 <= coeff < KeygenM23MatrixSpec.poly_words_i.
+ move: hcoeff.
   rewrite /KeygenM23MatrixSpec.poly_words_i.
   smt().
have hrqcoeff :=
  RqHAETAEBridge.rq_poly_repr_coeff
    row_product hprod coeff hrq _.
+ move: hcoeff.
   rewrite /HAETAE_Params.n.
   smt().
have hwide :
    row_product.[coeff] =
    NTT_Fq.word_to_coeff
      (BArray8192.get32 pre_bp (row * 256 + coeff)).
+ rewrite hrepr.
   exact
     (KeygenM23ArithmeticSpec.wide_poly_get
       pre_bp (row * 256) coeff hcoeff256).
have hword :
    NTT_Fq.word_to_coeff
      (BArray8192.get32 pre_bp (row * 256 + coeff)) =
    incoeff (W32.to_sint (BArray8192.get32 pre_bp (row * 256 + coeff))).
+ by rewrite /NTT_Fq.word_to_coeff.
have hincoeff :
    incoeff (HAETAE_Algebra.poly_coeff hprod coeff) =
    incoeff (W32.to_sint (BArray8192.get32 pre_bp (row * 256 + coeff))).
+ rewrite hrqcoeff hwide hword.
   trivial.
exact (double_congruent_mod_2q_of_incoeff_eq
  (HAETAE_Algebra.poly_coeff hprod coeff)
  (W32.to_sint (BArray8192.get32 pre_bp (row * 256 + coeff)))
  hincoeff).
qed.

lemma faithful_augmented_As_qj_from_generated_repr
    (pre_bp sampled_s2 a b1 adjusted : BArray8192.t)
    row coeff
    (row_product : Rq.poly)
    (hprod : HAETAE_Algebra.poly) :
  KgActualAvecQjComposition.actual_snapshot_paper_qj
    pre_bp sampled_s2 a b1 adjusted =>
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    pre_bp (row * 256) row_product 16 =>
  RqHAETAEBridge.rq_poly_repr row_product hprod =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (faithful_head_coeff
      (actual_array_coeff a)
      (actual_array_coeff b1)
      row coeff +
     2 * HAETAE_Algebra.poly_coeff hprod coeff +
     2 * actual_centered_coeff adjusted row coeff)
    (faithful_qj_coeff row coeff).
proof.
move=> hactual hrow hcoeff hrepr hrq.
have hbase :=
  actual_snapshot_paper_qj_to_faithful_augmented
    pre_bp sampled_s2 a b1 adjusted row coeff
    hactual hrow hcoeff.
have hgen :=
  generated_product_coeff_from_rq_repr
    pre_bp row coeff row_product hprod
    hrow hcoeff hrepr hrq.
rewrite /faithful_augmented_As_coeff in hbase.
have hreflex :
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * actual_centered_coeff adjusted row coeff)
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * actual_centered_coeff adjusted row coeff).
+ rewrite /Mode2KeygenSnapshotAlgebra.congruent_mod_2q.
  smt().
have hgen_with_context :=
  congruent_mod_2q_add
    (2 * HAETAE_Algebra.poly_coeff hprod coeff)
    (2 * actual_centered_coeff pre_bp row coeff)
    (faithful_head_coeff
      (actual_array_coeff a)
      (actual_array_coeff b1)
      row coeff +
     2 * actual_centered_coeff adjusted row coeff)
    (faithful_head_coeff
      (actual_array_coeff a)
      (actual_array_coeff b1)
      row coeff +
     2 * actual_centered_coeff adjusted row coeff)
    hgen hreflex.
have hsum :
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * HAETAE_Algebra.poly_coeff hprod coeff +
       2 * actual_centered_coeff adjusted row coeff)
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * actual_centered_coeff pre_bp row coeff +
       2 * actual_centered_coeff adjusted row coeff).
+ have hleft :
      faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
      2 * HAETAE_Algebra.poly_coeff hprod coeff +
      2 * actual_centered_coeff adjusted row coeff =
      2 * HAETAE_Algebra.poly_coeff hprod coeff +
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * actual_centered_coeff adjusted row coeff) by ring.
  have hright :
      faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
      2 * actual_centered_coeff pre_bp row coeff +
      2 * actual_centered_coeff adjusted row coeff =
      2 * actual_centered_coeff pre_bp row coeff +
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * actual_centered_coeff adjusted row coeff) by ring.
  rewrite hleft hright.
  exact hgen_with_context.
exact (congruent_mod_2q_trans _ _ _ hsum hbase).
qed.

op rq_as_haetae_poly (p : Rq.poly) : HAETAE_Algebra.poly =
  mkseq (fun i => asint p.[i]) HAETAE_Params.n.

lemma rq_as_haetae_poly_repr (p : Rq.poly) :
  RqHAETAEBridge.rq_poly_repr p (rq_as_haetae_poly p).
proof.
split.
+ by rewrite /HAETAE_Algebra.poly_wf /rq_as_haetae_poly
             size_mkseq /HAETAE_Params.n.
move=> i hi.
rewrite /rq_as_haetae_poly /HAETAE_Algebra.poly_coeff
        nth_mkseq 1:hi.
exact (asintK p.[i]).
qed.

op actual_generated_row_product
    (mat : BArray32768.t) (sgen : BArray8192.t) row : Rq.poly =
  Mode2KeygenNttMulBridge.mode2_row_product mat
    (KeygenM23ArithmeticSpec.wide_poly sgen 0)
    (KeygenM23ArithmeticSpec.wide_poly
      sgen KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      sgen (2 * KeygenM23MatrixSpec.poly_words_i))
    row.

op actual_generated_haetae_product
    (mat : BArray32768.t) (sgen : BArray8192.t) row :
    HAETAE_Algebra.poly =
  rq_as_haetae_poly (actual_generated_row_product mat sgen row).

op actual_generated_matrix_poly
    (mat : BArray32768.t) row col : HAETAE_Algebra.poly =
  rq_as_haetae_poly
    (NTTFullSpec.full_invntt
      (KeygenM23ArithmeticSpec.matrix_poly mat row col)).

op actual_generated_secret_poly
    (sgen : BArray8192.t) col : HAETAE_Algebra.poly =
  rq_as_haetae_poly
    (KeygenM23ArithmeticSpec.wide_poly
      sgen (col * KeygenM23MatrixSpec.poly_words_i)).

op faithful_middle_matrix_poly
    (a : int -> int -> int -> int) row midcol : HAETAE_Algebra.poly =
  mkseq (fun i => (a row (midcol + 1) i) %/ 2) HAETAE_Params.n.

op faithful_middle_secret_poly
    (s : int -> int -> int) midcol : HAETAE_Algebra.poly =
  mkseq (fun i => s (midcol + 1) i) HAETAE_Params.n.

op faithful_generated_block_dot
    (a : int -> int -> int -> int)
    (s : int -> int -> int)
    row : HAETAE_Algebra.poly =
  HAETAE_Algebra.poly_dot
    [faithful_middle_matrix_poly a row 0;
     faithful_middle_matrix_poly a row 1;
     faithful_middle_matrix_poly a row 2]
    [faithful_middle_secret_poly s 0;
     faithful_middle_secret_poly s 1;
     faithful_middle_secret_poly s 2].

op actual_faithful_augmented_matrix
    (mat : BArray32768.t) (a b1 : BArray8192.t)
    row col coeff : int =
  if col = 0 then
    faithful_head_coeff (actual_array_coeff a) (actual_array_coeff b1)
      row coeff
  else if 1 <= col < 4 then
    2 * HAETAE_Algebra.poly_coeff
          (actual_generated_matrix_poly mat row (col - 1)) coeff
  else if col = 4 then two_i2_coeff row 0 coeff
  else if col = 5 then two_i2_coeff row 1 coeff
  else 0.

op actual_faithful_augmented_secret
    (sgen adjusted : BArray8192.t) col coeff : int =
  if col = 0 then ring_one_coeff coeff
  else if 1 <= col < 4 then
    HAETAE_Algebra.poly_coeff
      (actual_generated_secret_poly sgen (col - 1)) coeff
  else if col = 4 then actual_centered_coeff adjusted 0 coeff
  else if col = 5 then actual_centered_coeff adjusted 1 coeff
  else 0.

op faithful_augmented_matrix_vector_product_coeff
    (a : int -> int -> int -> int)
    (s : int -> int -> int)
    row coeff : int =
  a row 0 coeff * s 0 0 +
  2 * HAETAE_Algebra.poly_coeff
        (faithful_generated_block_dot a s row) coeff +
  a row 4 0 * s 4 coeff +
  a row 5 0 * s 5 coeff.

lemma actual_faithful_augmented_productE
    (mat : BArray32768.t)
    (sgen a b1 adjusted : BArray8192.t) row coeff :
  0 <= row < 2 =>
  faithful_augmented_matrix_vector_product_coeff
    (actual_faithful_augmented_matrix mat a b1)
    (actual_faithful_augmented_secret sgen adjusted)
    row coeff =
  faithful_head_coeff (actual_array_coeff a) (actual_array_coeff b1)
    row coeff +
  2 * HAETAE_Algebra.poly_coeff
        (faithful_generated_block_dot
          (actual_faithful_augmented_matrix mat a b1)
          (actual_faithful_augmented_secret sgen adjusted)
          row)
        coeff +
  2 * actual_centered_coeff adjusted row coeff.
proof.
move=> hrow.
rewrite /faithful_augmented_matrix_vector_product_coeff
        /actual_faithful_augmented_matrix
        /actual_faithful_augmented_secret.
have [-> | ->] : row = 0 \/ row = 1 by smt().
+ rewrite /=.
   trivial.
rewrite /=.
trivial.
qed.

lemma faithful_generated_row_product_haetae_dot
    (mat : BArray32768.t)
    (sgen a b1 adjusted : BArray8192.t) row :
  0 <= row < 2 =>
  RqHAETAEBridge.rq_poly_repr
    (actual_generated_row_product mat sgen row)
    (faithful_generated_block_dot
      (actual_faithful_augmented_matrix mat a b1)
      (actual_faithful_augmented_secret sgen adjusted)
      row).
proof.
move=> hrow.
rewrite /faithful_generated_block_dot.
apply
  (Mode2KeygenNttMulBridge.mode2_row_product_haetae_dot
    mat
    (KeygenM23ArithmeticSpec.wide_poly sgen 0)
    (KeygenM23ArithmeticSpec.wide_poly
      sgen KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      sgen (2 * KeygenM23MatrixSpec.poly_words_i))
    row
    (faithful_middle_matrix_poly
      (actual_faithful_augmented_matrix mat a b1) row 0)
    (faithful_middle_matrix_poly
      (actual_faithful_augmented_matrix mat a b1) row 1)
    (faithful_middle_matrix_poly
      (actual_faithful_augmented_matrix mat a b1) row 2)
    (faithful_middle_secret_poly
      (actual_faithful_augmented_secret sgen adjusted) 0)
    (faithful_middle_secret_poly
      (actual_faithful_augmented_secret sgen adjusted) 1)
    (faithful_middle_secret_poly
      (actual_faithful_augmented_secret sgen adjusted) 2)) => //.
+ split.
   + by rewrite /HAETAE_Algebra.poly_wf /faithful_middle_matrix_poly size_mkseq.
   move=> i hi.
   rewrite /faithful_middle_matrix_poly /actual_faithful_augmented_matrix
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   rewrite /actual_generated_matrix_poly /rq_as_haetae_poly
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   have -> :
       (2 *
        asint
          (NTTFullSpec.full_invntt
            (KeygenM23ArithmeticSpec.matrix_poly mat row 0)).[i]) %/ 2 =
       asint
         (NTTFullSpec.full_invntt
           (KeygenM23ArithmeticSpec.matrix_poly mat row 0)).[i] by smt().
   exact (asintK
     (NTTFullSpec.full_invntt
       (KeygenM23ArithmeticSpec.matrix_poly mat row 0)).[i]).
+ split.
   + by rewrite /HAETAE_Algebra.poly_wf /faithful_middle_matrix_poly size_mkseq.
   move=> i hi.
   rewrite /faithful_middle_matrix_poly /actual_faithful_augmented_matrix
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   rewrite /actual_generated_matrix_poly /rq_as_haetae_poly
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   have -> :
       (2 *
        asint
          (NTTFullSpec.full_invntt
            (KeygenM23ArithmeticSpec.matrix_poly mat row 1)).[i]) %/ 2 =
       asint
         (NTTFullSpec.full_invntt
           (KeygenM23ArithmeticSpec.matrix_poly mat row 1)).[i] by smt().
   exact (asintK
     (NTTFullSpec.full_invntt
       (KeygenM23ArithmeticSpec.matrix_poly mat row 1)).[i]).
+ split.
   + by rewrite /HAETAE_Algebra.poly_wf /faithful_middle_matrix_poly size_mkseq.
   move=> i hi.
   rewrite /faithful_middle_matrix_poly /actual_faithful_augmented_matrix
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   rewrite /actual_generated_matrix_poly /rq_as_haetae_poly
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   have -> :
       (2 *
        asint
          (NTTFullSpec.full_invntt
            (KeygenM23ArithmeticSpec.matrix_poly mat row 2)).[i]) %/ 2 =
       asint
         (NTTFullSpec.full_invntt
           (KeygenM23ArithmeticSpec.matrix_poly mat row 2)).[i] by smt().
   exact (asintK
     (NTTFullSpec.full_invntt
       (KeygenM23ArithmeticSpec.matrix_poly mat row 2)).[i]).
+ split.
   + by rewrite /HAETAE_Algebra.poly_wf /faithful_middle_secret_poly size_mkseq.
   move=> i hi.
   rewrite /faithful_middle_secret_poly /actual_faithful_augmented_secret
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   rewrite /actual_generated_secret_poly /rq_as_haetae_poly
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   exact (asintK (KeygenM23ArithmeticSpec.wide_poly sgen 0).[i]).
+ split.
   + by rewrite /HAETAE_Algebra.poly_wf /faithful_middle_secret_poly size_mkseq.
   move=> i hi.
   rewrite /faithful_middle_secret_poly /actual_faithful_augmented_secret
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   rewrite /actual_generated_secret_poly /rq_as_haetae_poly
           /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
   exact
     (asintK
       (KeygenM23ArithmeticSpec.wide_poly
         sgen KeygenM23MatrixSpec.poly_words_i).[i]).
split.
+ by rewrite /HAETAE_Algebra.poly_wf /faithful_middle_secret_poly size_mkseq.
move=> i hi.
rewrite /faithful_middle_secret_poly /actual_faithful_augmented_secret
        /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
rewrite /actual_generated_secret_poly /rq_as_haetae_poly
        /HAETAE_Algebra.poly_coeff nth_mkseq 1:hi /=.
exact
  (asintK
    (KeygenM23ArithmeticSpec.wide_poly
      sgen (2 * KeygenM23MatrixSpec.poly_words_i)).[i]).
qed.

lemma faithful_augmented_product_qj_from_generated_dot
    (pre_bp sampled_s2 : BArray8192.t)
    (mat : BArray32768.t)
    (sgen a b1 adjusted : BArray8192.t)
    row coeff :
  KgActualAvecQjComposition.actual_snapshot_paper_qj
    pre_bp sampled_s2 a b1 adjusted =>
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    pre_bp (row * 256) (actual_generated_row_product mat sgen row) 16 =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (faithful_augmented_matrix_vector_product_coeff
      (actual_faithful_augmented_matrix mat a b1)
      (actual_faithful_augmented_secret sgen adjusted)
      row coeff)
    (faithful_qj_coeff row coeff).
proof.
move=> hactual hrow hcoeff hrepr.
have hbase :=
  actual_snapshot_paper_qj_to_faithful_augmented
    pre_bp sampled_s2 a b1 adjusted row coeff
    hactual hrow hcoeff.
have hgen :=
  generated_product_coeff_from_rq_repr
    pre_bp row coeff
    (actual_generated_row_product mat sgen row)
    (faithful_generated_block_dot
      (actual_faithful_augmented_matrix mat a b1)
      (actual_faithful_augmented_secret sgen adjusted)
      row)
    hrow hcoeff hrepr
    (faithful_generated_row_product_haetae_dot
      mat sgen a b1 adjusted row hrow).
rewrite (actual_faithful_augmented_productE
  mat sgen a b1 adjusted row coeff hrow).
have hreflex :
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * actual_centered_coeff adjusted row coeff)
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * actual_centered_coeff adjusted row coeff).
+ rewrite /Mode2KeygenSnapshotAlgebra.congruent_mod_2q.
   smt().
have hgen_with_context :=
  congruent_mod_2q_add
    (2 * HAETAE_Algebra.poly_coeff
      (faithful_generated_block_dot
        (actual_faithful_augmented_matrix mat a b1)
        (actual_faithful_augmented_secret sgen adjusted)
        row)
      coeff)
    (2 * actual_centered_coeff pre_bp row coeff)
    (faithful_head_coeff
      (actual_array_coeff a)
      (actual_array_coeff b1)
      row coeff +
     2 * actual_centered_coeff adjusted row coeff)
    (faithful_head_coeff
      (actual_array_coeff a)
      (actual_array_coeff b1)
      row coeff +
     2 * actual_centered_coeff adjusted row coeff)
    hgen hreflex.
have hsum :
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (faithful_head_coeff
       (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * HAETAE_Algebra.poly_coeff
         (faithful_generated_block_dot
           (actual_faithful_augmented_matrix mat a b1)
           (actual_faithful_augmented_secret sgen adjusted)
           row)
         coeff +
       2 * actual_centered_coeff adjusted row coeff)
      (faithful_head_coeff
        (actual_array_coeff a)
        (actual_array_coeff b1)
        row coeff +
       2 * actual_centered_coeff pre_bp row coeff +
       2 * actual_centered_coeff adjusted row coeff).
+ have hleft :
       faithful_head_coeff
         (actual_array_coeff a)
         (actual_array_coeff b1)
         row coeff +
       2 * HAETAE_Algebra.poly_coeff
         (faithful_generated_block_dot
           (actual_faithful_augmented_matrix mat a b1)
           (actual_faithful_augmented_secret sgen adjusted)
           row)
         coeff +
       2 * actual_centered_coeff adjusted row coeff =
       2 * HAETAE_Algebra.poly_coeff
         (faithful_generated_block_dot
           (actual_faithful_augmented_matrix mat a b1)
           (actual_faithful_augmented_secret sgen adjusted)
           row)
         coeff +
       (faithful_head_coeff
         (actual_array_coeff a)
         (actual_array_coeff b1)
         row coeff +
        2 * actual_centered_coeff adjusted row coeff) by ring.
   have hright :
       faithful_head_coeff
         (actual_array_coeff a)
         (actual_array_coeff b1)
         row coeff +
       2 * actual_centered_coeff pre_bp row coeff +
       2 * actual_centered_coeff adjusted row coeff =
       2 * actual_centered_coeff pre_bp row coeff +
       (faithful_head_coeff
         (actual_array_coeff a)
         (actual_array_coeff b1)
         row coeff +
        2 * actual_centered_coeff adjusted row coeff) by ring.
   rewrite hleft hright.
   exact hgen_with_context.
exact (congruent_mod_2q_trans _ _ _ hsum hbase).
qed.

lemma mode2_m23_facts_generated_row_product
    (mat : BArray32768.t)
    (sgen pre_bp s1hatp bp0 s1hat0 : BArray8192.t) row :
  TargetKeygenM23FinalizeComposition.mode2_m23_facts
    mat sgen pre_bp s1hatp bp0 s1hat0 =>
  0 <= row < 2 =>
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    pre_bp (row * 256) (actual_generated_row_product mat sgen row) 16.
proof.
rewrite /TargetKeygenM23FinalizeComposition.mode2_m23_facts.
move=> [_ [_ [hout _]]] hrow.
rewrite /KeygenM23ArithmeticSpec.mode2_output_repr_bound16 in hout.
case: (row = 0) => hrow0.
+ have -> : row = 0 by exact hrow0.
  move: hout => [h0 _].
  have h0rp :
      KeygenM23ArithmeticSpec.wide_slice_repr_bound
        pre_bp 0 (actual_generated_row_product mat sgen 0) 16.
  + rewrite /actual_generated_row_product.
    move: h0.
    rewrite Mode2KeygenNttMulBridge.keygen_mode2_row_product.
    trivial.
  move: h0rp.
  by rewrite /=.
have -> : row = 1 by smt().
move: hout => [_ h1].
have h1rp :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      pre_bp KeygenM23MatrixSpec.poly_words_i
      (actual_generated_row_product mat sgen 1) 16.
+ rewrite /actual_generated_row_product.
  move: h1.
  rewrite Mode2KeygenNttMulBridge.keygen_mode2_row_product.
  trivial.
move: h1rp.
by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
qed.

lemma checked_mode2_parent_m23_finalize_faithful_augmented_paper_as_qj
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [
    TargetKeygenM23FinalizeComposition.CheckedMode2ParentM23Finalize.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0
    ==>
    KgActualAvecQjComposition.actual_paper_mode2_a res.`3 res.`1 /\
    (forall row coeff,
      0 <= row < 2 =>
      0 <= coeff < 256 =>
      Mode2KeygenSnapshotAlgebra.congruent_mod_2q
        (faithful_augmented_matrix_vector_product_coeff
          (actual_faithful_augmented_matrix res.`2 res.`3 res.`9)
          (actual_faithful_augmented_secret res.`4 res.`10)
          row coeff)
        (faithful_qj_coeff row coeff))].
proof.
conseq
  (TargetKeygenM23FinalizeSemanticComposition.checked_mode2_parent_m23_finalize_semantic_correct
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result [hsampler [hm23 [_ hsemantic]]].
have ha :=
  KgActualAvecQjComposition.mode2_sampler_facts_actual_paper_a
    result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
    mat0 avec0 s10 s20 raw_seed0 hsampler.
have hzero :=
  Mode2KeygenCoreEquation.finalize_semantic_output_snapshot_mod2q_zero
    result.`7 result.`5 result.`3 result.`9 result.`10 hsemantic.
have hqj :=
  KgActualAvecQjComposition.actual_snapshot_zero_adds_paper_qj
    result.`7 result.`5 result.`3 result.`9 result.`10 hzero.
split; first exact ha.
move=> row coeff hrow hcoeff.
exact
  (faithful_augmented_product_qj_from_generated_dot
    result.`7 result.`5 result.`2 result.`4 result.`3 result.`9 result.`10
    row coeff hqj hrow hcoeff
    (mode2_m23_facts_generated_row_product
      result.`2 result.`4 result.`7 result.`8 bp0 s1hat0 row
      hm23 hrow)).
qed.

end KgFaithfulAugmentedModel.
