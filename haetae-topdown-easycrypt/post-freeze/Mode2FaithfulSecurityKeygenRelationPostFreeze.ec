require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra.
require import Mode2KeygenSnapshotAlgebra.
require import TargetKeygenM23FinalizeComposition.
require import KgFaithfulAugmentedModel
               Mode2FaithfulSecurityExpandVecAPostFreeze
               Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.

theory Mode2FaithfulSecurityKeygenRelationPostFreeze.

import HAETAE_Params.

(* These finite lists are raw coefficient carriers for the faithful 2-by-6
   augmented matrix and six-polynomial secret; they do not assert a native
   HAETAE matrix-product interpretation. *)
op faithful_augmented_matrix_poly
    (mcoeff : int -> int -> int -> int) row col : HAETAE_Algebra.poly =
  mkseq (fun coeff => mcoeff row col coeff) HAETAE_Params.n.

op faithful_augmented_secret_poly
    (scoeff : int -> int -> int) col : HAETAE_Algebra.poly =
  mkseq (fun coeff => scoeff col coeff) HAETAE_Params.n.

op faithful_augmented_matrix
    (mcoeff : int -> int -> int -> int) : HAETAE_Algebra.matrix =
  mkseq (fun row => mkseq (faithful_augmented_matrix_poly mcoeff row) 6) 2.

op faithful_augmented_secret
    (scoeff : int -> int -> int) : HAETAE_Algebra.poly list =
  mkseq (faithful_augmented_secret_poly scoeff) 6.

op faithful_augmented_row_wf (row : HAETAE_Algebra.poly list) : bool =
  size row = 6 /\ all HAETAE_Algebra.poly_wf row.

op faithful_augmented_matrix_wf (augA : HAETAE_Algebra.matrix) : bool =
  size augA = 2 /\ all faithful_augmented_row_wf augA.

op faithful_augmented_secret_wf (augS : HAETAE_Algebra.poly list) : bool =
  size augS = 6 /\ all HAETAE_Algebra.poly_wf augS.

lemma faithful_augmented_matrix_poly_wf mcoeff row col :
  HAETAE_Algebra.poly_wf
    (faithful_augmented_matrix_poly mcoeff row col).
proof.
by rewrite /faithful_augmented_matrix_poly
           /HAETAE_Algebra.poly_wf size_mkseq /HAETAE_Params.n.
qed.

lemma faithful_augmented_secret_poly_wf scoeff col :
  HAETAE_Algebra.poly_wf
    (faithful_augmented_secret_poly scoeff col).
proof.
by rewrite /faithful_augmented_secret_poly
           /HAETAE_Algebra.poly_wf size_mkseq /HAETAE_Params.n.
qed.

lemma faithful_augmented_matrix_poly_coeffE
    mcoeff row col coeff :
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (faithful_augmented_matrix_poly mcoeff row col) coeff =
  mcoeff row col coeff.
proof.
move=> hcoeff.
rewrite /faithful_augmented_matrix_poly /HAETAE_Algebra.poly_coeff.
rewrite nth_mkseq; first trivial.
by move: hcoeff; rewrite /HAETAE_Params.n.
qed.

lemma faithful_augmented_secret_poly_coeffE
    scoeff col coeff :
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (faithful_augmented_secret_poly scoeff col) coeff =
  scoeff col coeff.
proof.
move=> hcoeff.
rewrite /faithful_augmented_secret_poly /HAETAE_Algebra.poly_coeff.
rewrite nth_mkseq; first trivial.
by move: hcoeff; rewrite /HAETAE_Params.n.
qed.

lemma faithful_augmented_matrix_wf_packaged mcoeff :
  faithful_augmented_matrix_wf (faithful_augmented_matrix mcoeff).
proof.
rewrite /faithful_augmented_matrix_wf /faithful_augmented_matrix size_mkseq.
split; first done.
apply/List.allP=> row.
move=> /mkseqP [i [hi ->]].
rewrite /faithful_augmented_row_wf size_mkseq.
split; first done.
apply/List.allP=> p.
move=> /mkseqP [j [hj ->]].
exact (faithful_augmented_matrix_poly_wf mcoeff i j).
qed.

lemma faithful_augmented_secret_wf_packaged scoeff :
  faithful_augmented_secret_wf (faithful_augmented_secret scoeff).
proof.
rewrite /faithful_augmented_secret_wf /faithful_augmented_secret size_mkseq.
split; first done.
apply/List.allP=> p.
move=> /mkseqP [i [hi ->]].
exact (faithful_augmented_secret_poly_wf scoeff i).
qed.

lemma faithful_augmented_matrix_coeffE
    mcoeff row col coeff :
  0 <= row < 2 =>
  0 <= col < 6 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] (faithful_augmented_matrix mcoeff) row) col)
    coeff =
  mcoeff row col coeff.
proof.
move=> hrow hcol hcoeff.
rewrite /faithful_augmented_matrix.
rewrite nth_mkseq 1:hrow.
rewrite nth_mkseq 1:hcol.
exact (faithful_augmented_matrix_poly_coeffE
  mcoeff row col coeff hcoeff).
qed.

lemma faithful_augmented_secret_coeffE
    scoeff col coeff :
  0 <= col < 6 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (faithful_augmented_secret scoeff) col)
    coeff =
  scoeff col coeff.
proof.
move=> hcol hcoeff.
rewrite /faithful_augmented_secret.
rewrite nth_mkseq 1:hcol.
exact (faithful_augmented_secret_poly_coeffE scoeff col coeff hcoeff).
qed.

op faithful_packaged_middle_matrix_poly
    (augA : HAETAE_Algebra.matrix) row midcol : HAETAE_Algebra.poly =
  mkseq
    (fun coeff =>
      HAETAE_Algebra.poly_coeff
        (nth HAETAE_Algebra.poly_zero
          (nth [] augA row) (midcol + 1))
        coeff %/ 2)
    HAETAE_Params.n.

op faithful_packaged_middle_secret_poly
    (augS : HAETAE_Algebra.poly list) midcol : HAETAE_Algebra.poly =
  nth HAETAE_Algebra.poly_zero augS (midcol + 1).

op faithful_packaged_generated_block_dot
    (augA : HAETAE_Algebra.matrix)
    (augS : HAETAE_Algebra.poly list)
    row : HAETAE_Algebra.poly =
  HAETAE_Algebra.poly_dot
    [faithful_packaged_middle_matrix_poly augA row 0;
     faithful_packaged_middle_matrix_poly augA row 1;
     faithful_packaged_middle_matrix_poly augA row 2]
    [faithful_packaged_middle_secret_poly augS 0;
     faithful_packaged_middle_secret_poly augS 1;
     faithful_packaged_middle_secret_poly augS 2].

(* Keep the outer augmented product over integers.  Replacing it with the
   native matrix-vector operation would reduce modulo q before the doubled
   middle block and auxiliary q-multiple terms reach the final mod-2q test. *)
op faithful_packaged_matrix_vector_product_coeff
    (augA : HAETAE_Algebra.matrix)
    (augS : HAETAE_Algebra.poly list)
    row coeff : int =
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] augA row) 0)
    coeff *
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero augS 0) 0 +
  2 * HAETAE_Algebra.poly_coeff
        (faithful_packaged_generated_block_dot augA augS row)
        coeff +
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] augA row) 4)
    0 *
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero augS 4)
    coeff +
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] augA row) 5)
    0 *
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero augS 5)
    coeff.

lemma int_div2_congr x y : x = y => x %/ 2 = y %/ 2.
proof. by move=> ->. qed.

lemma faithful_packaged_middle_matrix_polyE
    mcoeff row midcol :
  0 <= row < 2 =>
  0 <= midcol < 3 =>
  faithful_packaged_middle_matrix_poly
    (faithful_augmented_matrix mcoeff) row midcol =
  KgFaithfulAugmentedModel.faithful_middle_matrix_poly
    mcoeff row midcol.
proof.
move=> hrow hmid.
apply/(eq_from_nth 0).
+ rewrite /faithful_packaged_middle_matrix_poly
           /KgFaithfulAugmentedModel.faithful_middle_matrix_poly
           !size_mkseq.
  trivial.
move=> coeff.
rewrite /faithful_packaged_middle_matrix_poly
        /KgFaithfulAugmentedModel.faithful_middle_matrix_poly
        !size_mkseq => hcoeff.
rewrite !nth_mkseq 1:hcoeff.
+ exact hrow.
+ have hcol : 0 <= midcol + 1 < 6 by move: hmid; smt().
  exact hcol.
+ have hcoeff' : 0 <= coeff < HAETAE_Params.n by
    move: hcoeff; rewrite /HAETAE_Params.n; smt().
  exact hcoeff'.
+ have hcoeff' : 0 <= coeff < 256 by
    move: hcoeff; rewrite /HAETAE_Params.n; smt().
  have heq :
      HAETAE_Algebra.poly_coeff
        (faithful_augmented_matrix_poly mcoeff row (midcol + 1))
        coeff =
      mcoeff row (midcol + 1) coeff.
  + exact (faithful_augmented_matrix_poly_coeffE
      mcoeff row (midcol + 1) coeff hcoeff').
  exact (int_div2_congr _ _ heq).
qed.

lemma faithful_packaged_middle_secret_polyE scoeff midcol :
  0 <= midcol < 3 =>
  faithful_packaged_middle_secret_poly
    (faithful_augmented_secret scoeff) midcol =
  KgFaithfulAugmentedModel.faithful_middle_secret_poly
    scoeff midcol.
proof.
move=> hmid.
rewrite /faithful_packaged_middle_secret_poly
        /KgFaithfulAugmentedModel.faithful_middle_secret_poly
        /faithful_augmented_secret.
rewrite nth_mkseq 1:/#.
trivial.
qed.

lemma faithful_packaged_generated_block_dotE mcoeff scoeff row :
  0 <= row < 2 =>
  faithful_packaged_generated_block_dot
    (faithful_augmented_matrix mcoeff)
    (faithful_augmented_secret scoeff)
    row =
  KgFaithfulAugmentedModel.faithful_generated_block_dot
    mcoeff scoeff row.
proof.
move=> hrow.
have hmid0 : 0 <= 0 < 3 by trivial.
have hmid1 : 0 <= 1 < 3 by trivial.
have hmid2 : 0 <= 2 < 3 by trivial.
have hm0 :=
  faithful_packaged_middle_matrix_polyE mcoeff row 0 hrow hmid0.
have hm1 :=
  faithful_packaged_middle_matrix_polyE mcoeff row 1 hrow hmid1.
have hm2 :=
  faithful_packaged_middle_matrix_polyE mcoeff row 2 hrow hmid2.
have hs0 := faithful_packaged_middle_secret_polyE scoeff 0 hmid0.
have hs1 := faithful_packaged_middle_secret_polyE scoeff 1 hmid1.
have hs2 := faithful_packaged_middle_secret_polyE scoeff 2 hmid2.
rewrite /faithful_packaged_generated_block_dot
        /KgFaithfulAugmentedModel.faithful_generated_block_dot.
congr.
+ by rewrite hm0 hm1 hm2.
+ by rewrite hs0 hs1 hs2.
qed.

lemma faithful_packaged_matrix_vector_product_coeffE
    mcoeff scoeff row coeff :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  faithful_packaged_matrix_vector_product_coeff
    (faithful_augmented_matrix mcoeff)
    (faithful_augmented_secret scoeff)
    row coeff =
  KgFaithfulAugmentedModel.faithful_augmented_matrix_vector_product_coeff
    mcoeff scoeff row coeff.
proof.
move=> hrow hcoeff.
rewrite /faithful_packaged_matrix_vector_product_coeff
        /KgFaithfulAugmentedModel.faithful_augmented_matrix_vector_product_coeff.
rewrite (faithful_augmented_matrix_coeffE mcoeff row 0 coeff) 1:hrow 1:/# 1:hcoeff.
rewrite (faithful_augmented_secret_coeffE scoeff 0 0) 1:/# 1:/#.
rewrite (faithful_augmented_matrix_coeffE mcoeff row 4 0) 1:hrow 1:/# 1:/#.
rewrite (faithful_augmented_secret_coeffE scoeff 4 coeff) 1:/# 1:hcoeff.
rewrite (faithful_augmented_matrix_coeffE mcoeff row 5 0) 1:hrow 1:/# 1:/#.
rewrite (faithful_augmented_secret_coeffE scoeff 5 coeff) 1:/# 1:hcoeff.
by rewrite faithful_packaged_generated_block_dotE 1:hrow.
qed.

lemma faithful_packaged_matrix_vector_product_qj
    mcoeff scoeff row coeff :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (KgFaithfulAugmentedModel.faithful_augmented_matrix_vector_product_coeff
      mcoeff scoeff row coeff)
    (KgFaithfulAugmentedModel.faithful_qj_coeff row coeff) =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (faithful_packaged_matrix_vector_product_coeff
      (faithful_augmented_matrix mcoeff)
      (faithful_augmented_secret scoeff)
      row coeff)
    (KgFaithfulAugmentedModel.faithful_qj_coeff row coeff).
proof.
move=> hrow hcoeff hqj.
rewrite (faithful_packaged_matrix_vector_product_coeffE
  mcoeff scoeff row coeff hrow hcoeff).
exact hqj.
qed.

(* This is the security-facing, BArray-free boundary.  Concrete buffers occur
   only in the representation theorem below, where the checked parent supplies
   witnesses for these finite mathematical objects.  No totality, uniqueness,
   sampler-distribution, or synthetic public-rounding-vector identification is
   claimed here. *)
op faithful_mode2_keygen_relation
    (sd : HAETAE_Algebra.seed)
    (a : HAETAE_Algebra.polyveck)
    (augA : HAETAE_Algebra.matrix)
    (augS : HAETAE_Algebra.poly list) : bool =
  Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
    .faithful_mode2_expandveca_security_row_global sd a /\
  HAETAE_Algebra.polyveck_coeffs_q_bound Mode2 a /\
  faithful_augmented_matrix_wf augA /\
  faithful_augmented_secret_wf augS /\
  forall row coeff,
    0 <= row < 2 =>
    0 <= coeff < 256 =>
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (faithful_packaged_matrix_vector_product_coeff
        augA augS row coeff)
      (KgFaithfulAugmentedModel.faithful_qj_coeff row coeff).

lemma checked_mode2_parent_m23_finalize_faithful_mode2_keygen_relation
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
    exists sd a augA augS,
      faithful_mode2_keygen_relation sd a augA augS /\
      sd =
        Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
          .raw_security_seed raw_seed0 /\
      a =
        Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
          res.`3 /\
      augA =
        faithful_augmented_matrix
          (KgFaithfulAugmentedModel.actual_faithful_augmented_matrix
            res.`2 res.`3 res.`9) /\
      augS =
        faithful_augmented_secret
          (KgFaithfulAugmentedModel.actual_faithful_augmented_secret
            res.`4 res.`10)].
proof.
conseq
  (Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
    .checked_mode2_parent_m23_finalize_expandveca_security_seed_row_global_paper_as_qj
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result [hseed [hrow_global [hqbound hqj]]].
exists
  (Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
    .raw_security_seed raw_seed0).
exists
  (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
    result.`3).
exists
  (faithful_augmented_matrix
    (KgFaithfulAugmentedModel.actual_faithful_augmented_matrix
      result.`2 result.`3 result.`9)).
exists
  (faithful_augmented_secret
    (KgFaithfulAugmentedModel.actual_faithful_augmented_secret
      result.`4 result.`10)).
split.
+ split; first exact hrow_global.
   split; first exact hqbound.
   split.
   + exact
       (faithful_augmented_matrix_wf_packaged
         (KgFaithfulAugmentedModel.actual_faithful_augmented_matrix
           result.`2 result.`3 result.`9)).
   split.
   + exact
       (faithful_augmented_secret_wf_packaged
         (KgFaithfulAugmentedModel.actual_faithful_augmented_secret
           result.`4 result.`10)).
   move=> row coeff hrow hcoeff.
   exact
     (faithful_packaged_matrix_vector_product_qj
       (KgFaithfulAugmentedModel.actual_faithful_augmented_matrix
         result.`2 result.`3 result.`9)
       (KgFaithfulAugmentedModel.actual_faithful_augmented_secret
         result.`4 result.`10)
       row coeff hrow hcoeff
       (hqj row coeff hrow hcoeff)).
move: hseed.
rewrite
  /Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
    .faithful_mode2_expandveca_security_seed.
move=> [hsd _].
split; first exact hsd.
split; first done.
split; first done.
done.
qed.

end Mode2FaithfulSecurityKeygenRelationPostFreeze.
