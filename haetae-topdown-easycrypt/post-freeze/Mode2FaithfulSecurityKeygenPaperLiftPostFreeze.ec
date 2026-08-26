require import AllCore List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra.
require import Mode2KeygenSnapshotAlgebra.
require import TargetKeygenM23FinalizeComposition.
require import KgFaithfulAugmentedModel
               Mode2FaithfulSecurityExpandVecAPostFreeze
               Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
               Mode2FaithfulSecurityKeygenRelationPostFreeze.

theory Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.

import HAETAE_Params.

(* The paper-generated block has exactly three columns.  It is represented by
   explicit length-3 lists rather than HAETAE_Algebra.polyvecl, whose Mode-2
   width is four because it includes the verification head column. *)
op coeff_poly (f : int -> int) : HAETAE_Algebra.poly =
  mkseq f HAETAE_Params.n.

op coeff_polyveck2 (f : int -> int -> int) : HAETAE_Algebra.polyveck =
  mkseq (fun row => coeff_poly (f row)) 2.

op polyveck_coeff
    (xs : HAETAE_Algebra.polyveck) row coeff : int =
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero xs row)
    coeff.

op matrix23_coeff
    (xs : HAETAE_Algebra.matrix) row col coeff : int =
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] xs row) col)
    coeff.

op polylist3_coeff
    (xs : HAETAE_Algebra.poly list) col coeff : int =
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero xs col)
    coeff.

op faithful_Agen_wf (agen : HAETAE_Algebra.matrix) : bool =
  size agen = 2 /\
  all (fun row => size row = 3 /\ all HAETAE_Algebra.poly_wf row) agen.

op faithful_sgen_wf (sgen : HAETAE_Algebra.poly list) : bool =
  size sgen = 3 /\ all HAETAE_Algebra.poly_wf sgen.

lemma coeff_poly_wf f :
  HAETAE_Algebra.poly_wf (coeff_poly f).
proof.
by rewrite /coeff_poly /HAETAE_Algebra.poly_wf size_mkseq /HAETAE_Params.n.
qed.

lemma coeff_poly_coeffE f coeff :
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff (coeff_poly f) coeff = f coeff.
proof.
move=> hcoeff.
rewrite /coeff_poly /HAETAE_Algebra.poly_coeff nth_mkseq; first trivial.
by move: hcoeff; rewrite /HAETAE_Params.n.
qed.

lemma coeff_polyveck2_wf f :
  HAETAE_Algebra.polyveck_wf Mode2 (coeff_polyveck2 f).
proof.
rewrite /HAETAE_Algebra.polyveck_wf /coeff_polyveck2 size_mkseq.
split; first by rewrite /mode_k.
apply/List.allP=> p /mkseqP [row [hrow ->]].
exact (coeff_poly_wf (f row)).
qed.

lemma coeff_polyveck2_coeffE f row coeff :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero (coeff_polyveck2 f) row)
    coeff = f row coeff.
proof.
move=> hrow hcoeff.
rewrite /coeff_polyveck2 nth_mkseq 1:hrow.
exact (coeff_poly_coeffE (f row) coeff hcoeff).
qed.

lemma faithful_augmented_matrix_ext f g :
  (forall row col coeff,
    0 <= row < 2 =>
    0 <= col < 6 =>
    0 <= coeff < 256 =>
    f row col coeff = g row col coeff) =>
  Mode2FaithfulSecurityKeygenRelationPostFreeze.faithful_augmented_matrix f =
  Mode2FaithfulSecurityKeygenRelationPostFreeze.faithful_augmented_matrix g.
proof.
move=> hfg.
rewrite /Mode2FaithfulSecurityKeygenRelationPostFreeze
          .faithful_augmented_matrix.
apply eq_in_mkseq=> row hrow /=.
apply eq_in_mkseq=> col hcol /=.
rewrite /Mode2FaithfulSecurityKeygenRelationPostFreeze
          .faithful_augmented_matrix_poly.
apply eq_in_mkseq=> coeff hcoeff /=.
exact (hfg row col coeff hrow hcol hcoeff).
qed.

lemma faithful_augmented_secret_ext f g :
  (forall col coeff,
    0 <= col < 6 =>
    0 <= coeff < 256 =>
    f col coeff = g col coeff) =>
  Mode2FaithfulSecurityKeygenRelationPostFreeze.faithful_augmented_secret f =
  Mode2FaithfulSecurityKeygenRelationPostFreeze.faithful_augmented_secret g.
proof.
move=> hfg.
rewrite /Mode2FaithfulSecurityKeygenRelationPostFreeze
          .faithful_augmented_secret.
apply eq_in_mkseq=> col hcol /=.
rewrite /Mode2FaithfulSecurityKeygenRelationPostFreeze
          .faithful_augmented_secret_poly.
apply eq_in_mkseq=> coeff hcoeff /=.
exact (hfg col coeff hcol hcoeff).
qed.

op faithful_kg3_matrix
    (a b1 : HAETAE_Algebra.polyveck)
    (Agen : HAETAE_Algebra.matrix) : HAETAE_Algebra.matrix =
  Mode2FaithfulSecurityKeygenRelationPostFreeze.faithful_augmented_matrix
    (KgFaithfulAugmentedModel.faithful_augmented_matrix_coeff
      (matrix23_coeff Agen)
      (polyveck_coeff a)
      (polyveck_coeff b1)).

op faithful_kg4_secret
    (sgen : HAETAE_Algebra.poly list)
    (eadj : HAETAE_Algebra.polyveck) : HAETAE_Algebra.poly list =
  Mode2FaithfulSecurityKeygenRelationPostFreeze.faithful_augmented_secret
    (KgFaithfulAugmentedModel.faithful_augmented_secret_coeff
      (polylist3_coeff sgen)
      (polyveck_coeff eadj)).

(* KG-3 and KG-4 are exposed coefficientwise without using the native
   Mode-2 matrix product, whose width and modulus are different. *)
lemma faithful_kg3_matrix_coeffE a b1 Agen row col coeff :
  0 <= row < 2 =>
  0 <= col < 6 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] (faithful_kg3_matrix a b1 Agen) row) col)
    coeff =
  KgFaithfulAugmentedModel.faithful_augmented_matrix_coeff
    (matrix23_coeff Agen) (polyveck_coeff a) (polyveck_coeff b1)
    row col coeff.
proof.
move=> hrow hcol hcoeff.
rewrite /faithful_kg3_matrix.
exact
  (Mode2FaithfulSecurityKeygenRelationPostFreeze
    .faithful_augmented_matrix_coeffE
    (KgFaithfulAugmentedModel.faithful_augmented_matrix_coeff
      (matrix23_coeff Agen) (polyveck_coeff a) (polyveck_coeff b1))
    row col coeff hrow hcol hcoeff).
qed.

lemma faithful_kg3_headE a b1 Agen row coeff :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] (faithful_kg3_matrix a b1 Agen) row) 0)
    coeff =
  KgFaithfulAugmentedModel.faithful_head_coeff
    (polyveck_coeff a) (polyveck_coeff b1) row coeff.
proof.
move=> hrow hcoeff.
rewrite (faithful_kg3_matrix_coeffE a b1 Agen row 0 coeff)
  1:hrow 1:/# 1:hcoeff.
by rewrite /KgFaithfulAugmentedModel.faithful_augmented_matrix_coeff.
qed.

lemma faithful_kg3_middleE a b1 Agen row col coeff :
  0 <= row < 2 =>
  0 <= col < 3 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] (faithful_kg3_matrix a b1 Agen) row) (col + 1))
    coeff =
  2 * matrix23_coeff Agen row col coeff.
proof.
move=> hrow hcol hcoeff.
have haugcol : 0 <= col + 1 < 6 by move: hcol; smt().
rewrite (faithful_kg3_matrix_coeffE a b1 Agen row (col + 1) coeff)
  1:hrow 1:haugcol 1:hcoeff.
rewrite /KgFaithfulAugmentedModel.faithful_augmented_matrix_coeff
        /KgFaithfulAugmentedModel.faithful_generated_matrix_coeff.
have hmid : 1 <= col + 1 < 4 by move: hcol; smt().
have hzero : col + 1 <> 0 by move: hcol; smt().
have hgen : 0 <= col + 1 - 1 < 3 by move: hcol; smt().
have heq : col + 1 - 1 = col by ring.
by rewrite hzero hmid hgen heq.
qed.

lemma faithful_kg3_tailE a b1 Agen row col coeff :
  0 <= row < 2 =>
  0 <= col < 2 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (nth [] (faithful_kg3_matrix a b1 Agen) row) (col + 4))
    coeff =
  KgFaithfulAugmentedModel.two_i2_coeff row col coeff.
proof.
move=> hrow hcol hcoeff.
have haugcol : 0 <= col + 4 < 6 by move: hcol; smt().
rewrite (faithful_kg3_matrix_coeffE a b1 Agen row (col + 4) coeff)
  1:hrow 1:haugcol 1:hcoeff.
rewrite /KgFaithfulAugmentedModel.faithful_augmented_matrix_coeff
        /KgFaithfulAugmentedModel.faithful_identity_matrix_coeff.
have htail : 4 <= col + 4 < 6 by move: hcol; smt().
rewrite htail /=.
have [-> | ->] : col = 0 \/ col = 1 by smt().
+ trivial.
trivial.
qed.

lemma faithful_kg4_secret_coeffE sgen eadj col coeff :
  0 <= col < 6 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero (faithful_kg4_secret sgen eadj) col)
    coeff =
  KgFaithfulAugmentedModel.faithful_augmented_secret_coeff
    (polylist3_coeff sgen) (polyveck_coeff eadj) col coeff.
proof.
move=> hcol hcoeff.
rewrite /faithful_kg4_secret.
exact
  (Mode2FaithfulSecurityKeygenRelationPostFreeze
    .faithful_augmented_secret_coeffE
    (KgFaithfulAugmentedModel.faithful_augmented_secret_coeff
      (polylist3_coeff sgen) (polyveck_coeff eadj))
    col coeff hcol hcoeff).
qed.

lemma faithful_kg4_unitE sgen eadj coeff :
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero (faithful_kg4_secret sgen eadj) 0)
    coeff =
  KgFaithfulAugmentedModel.ring_one_coeff coeff.
proof.
move=> hcoeff.
rewrite (faithful_kg4_secret_coeffE sgen eadj 0 coeff) 1:/# 1:hcoeff.
by rewrite /KgFaithfulAugmentedModel.faithful_augmented_secret_coeff.
qed.

lemma faithful_kg4_sgenE sgen eadj col coeff :
  0 <= col < 3 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (faithful_kg4_secret sgen eadj) (col + 1))
    coeff =
  polylist3_coeff sgen col coeff.
proof.
move=> hcol hcoeff.
have hscol : 0 <= col + 1 < 6 by move: hcol; smt().
rewrite (faithful_kg4_secret_coeffE sgen eadj (col + 1) coeff)
  1:hscol 1:hcoeff.
rewrite /KgFaithfulAugmentedModel.faithful_augmented_secret_coeff.
have hmid : 1 <= col + 1 < 4 by move: hcol; smt().
have hzero : col + 1 <> 0 by move: hcol; smt().
have heq : col + 1 - 1 = col by ring.
by rewrite hzero hmid heq.
qed.

lemma faithful_kg4_eadjE sgen eadj row coeff :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (faithful_kg4_secret sgen eadj) (row + 4))
    coeff =
  polyveck_coeff eadj row coeff.
proof.
move=> hrow hcoeff.
have hscol : 0 <= row + 4 < 6 by move: hrow; smt().
rewrite (faithful_kg4_secret_coeffE sgen eadj (row + 4) coeff)
  1:hscol 1:hcoeff.
rewrite /KgFaithfulAugmentedModel.faithful_augmented_secret_coeff.
have htail : 4 <= row + 4 < 6 by move: hrow; smt().
rewrite htail /=.
have [-> | ->] : row = 0 \/ row = 1 by smt().
+ trivial.
trivial.
qed.

(* Concrete buffers occur only in these representation adapters and the final
   checked-parent theorem.  The named paper relation below is BArray-free. *)
op actual_Agen
    (mat : BArray32768.t) : HAETAE_Algebra.matrix =
  mkseq
    (fun row =>
      mkseq
        (KgFaithfulAugmentedModel.actual_generated_matrix_poly mat row)
        3)
    2.

op actual_sgen
    (sgen : BArray8192.t) : HAETAE_Algebra.poly list =
  mkseq (KgFaithfulAugmentedModel.actual_generated_secret_poly sgen) 3.

op actual_eadj
    (adjusted : BArray8192.t) : HAETAE_Algebra.polyveck =
  coeff_polyveck2 (KgFaithfulAugmentedModel.actual_centered_coeff adjusted).

lemma actual_generated_matrix_poly_wf mat row col :
  HAETAE_Algebra.poly_wf
    (KgFaithfulAugmentedModel.actual_generated_matrix_poly mat row col).
proof.
rewrite /KgFaithfulAugmentedModel.actual_generated_matrix_poly
        /KgFaithfulAugmentedModel.rq_as_haetae_poly
        /HAETAE_Algebra.poly_wf size_mkseq /HAETAE_Params.n.
trivial.
qed.

lemma actual_generated_secret_poly_wf sgen col :
  HAETAE_Algebra.poly_wf
    (KgFaithfulAugmentedModel.actual_generated_secret_poly sgen col).
proof.
rewrite /KgFaithfulAugmentedModel.actual_generated_secret_poly
        /KgFaithfulAugmentedModel.rq_as_haetae_poly
        /HAETAE_Algebra.poly_wf size_mkseq /HAETAE_Params.n.
trivial.
qed.

lemma actual_Agen_wf mat :
  faithful_Agen_wf (actual_Agen mat).
proof.
rewrite /faithful_Agen_wf /actual_Agen size_mkseq.
split; first done.
apply/List.allP=> row /mkseqP [i [hi ->]].
rewrite /= size_mkseq.
split; first done.
apply/List.allP=> p /mkseqP [j [hj ->]].
exact (actual_generated_matrix_poly_wf mat i j).
qed.

lemma actual_Agen_coeffE mat row col coeff :
  0 <= row < 2 =>
  0 <= col < 3 =>
  0 <= coeff < 256 =>
  matrix23_coeff (actual_Agen mat) row col coeff =
  HAETAE_Algebra.poly_coeff
    (KgFaithfulAugmentedModel.actual_generated_matrix_poly mat row col)
    coeff.
proof.
move=> hrow hcol hcoeff.
rewrite /matrix23_coeff /actual_Agen nth_mkseq 1:hrow.
rewrite nth_mkseq 1:hcol.
trivial.
qed.

lemma actual_sgen_wf sgen :
  faithful_sgen_wf (actual_sgen sgen).
proof.
rewrite /faithful_sgen_wf /actual_sgen size_mkseq.
split; first done.
apply/List.allP=> p /mkseqP [i [hi ->]].
exact (actual_generated_secret_poly_wf sgen i).
qed.

lemma actual_sgen_coeffE sgen col coeff :
  0 <= col < 3 =>
  0 <= coeff < 256 =>
  polylist3_coeff (actual_sgen sgen) col coeff =
  HAETAE_Algebra.poly_coeff
    (KgFaithfulAugmentedModel.actual_generated_secret_poly sgen col)
    coeff.
proof.
move=> hcol hcoeff.
rewrite /polylist3_coeff /actual_sgen nth_mkseq 1:hcol.
trivial.
qed.

lemma actual_eadj_wf adjusted :
  HAETAE_Algebra.polyveck_wf Mode2 (actual_eadj adjusted).
proof.
exact (coeff_polyveck2_wf (KgFaithfulAugmentedModel.actual_centered_coeff adjusted)).
qed.

lemma actual_eadj_coeffE adjusted row coeff :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  polyveck_coeff (actual_eadj adjusted) row coeff =
  KgFaithfulAugmentedModel.actual_centered_coeff adjusted row coeff.
proof.
move=> hrow hcoeff.
exact (coeff_polyveck2_coeffE
  (KgFaithfulAugmentedModel.actual_centered_coeff adjusted)
  row coeff hrow hcoeff).
qed.

lemma actual_faithful_kg3_matrixE mat avec b1 :
  faithful_kg3_matrix
    (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca avec)
    (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca b1)
    (actual_Agen mat) =
  Mode2FaithfulSecurityKeygenRelationPostFreeze.faithful_augmented_matrix
    (KgFaithfulAugmentedModel.actual_faithful_augmented_matrix
      mat avec b1).
proof.
apply
  (faithful_augmented_matrix_ext
    (KgFaithfulAugmentedModel.faithful_augmented_matrix_coeff
      (matrix23_coeff (actual_Agen mat))
      (polyveck_coeff
        (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca avec))
      (polyveck_coeff
        (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca b1)))
    (KgFaithfulAugmentedModel.actual_faithful_augmented_matrix
      mat avec b1)).
move=> row col coeff hrow hcol hcoeff.
rewrite /KgFaithfulAugmentedModel.actual_faithful_augmented_matrix
        /KgFaithfulAugmentedModel.faithful_augmented_matrix_coeff.
case (col = 0)=> h0.
+ rewrite /polyveck_coeff
           /KgFaithfulAugmentedModel.faithful_head_coeff.
   rewrite
     (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca_coeffE
       avec row coeff hrow hcoeff).
   rewrite
     (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca_coeffE
       b1 row coeff hrow hcoeff).
   by rewrite /KgFaithfulAugmentedModel.actual_array_coeff.
case (1 <= col < 4)=> hmid.
+ have hcol3 : 0 <= col - 1 < 3 by move: hmid; smt().
   rewrite /KgFaithfulAugmentedModel.faithful_generated_matrix_coeff hcol3.
   rewrite (actual_Agen_coeffE mat row (col - 1) coeff hrow hcol3 hcoeff).
   trivial.
have htail : 4 <= col < 6 by move: hcol h0 hmid; smt().
have [-> | ->] : col = 4 \/ col = 5 by move: htail; smt().
+ trivial.
trivial.
qed.

lemma actual_faithful_kg4_secretE sgen adjusted :
  faithful_kg4_secret (actual_sgen sgen) (actual_eadj adjusted) =
  Mode2FaithfulSecurityKeygenRelationPostFreeze.faithful_augmented_secret
    (KgFaithfulAugmentedModel.actual_faithful_augmented_secret
      sgen adjusted).
proof.
apply
  (faithful_augmented_secret_ext
    (KgFaithfulAugmentedModel.faithful_augmented_secret_coeff
      (polylist3_coeff (actual_sgen sgen))
      (polyveck_coeff (actual_eadj adjusted)))
    (KgFaithfulAugmentedModel.actual_faithful_augmented_secret
      sgen adjusted)).
move=> col coeff hcol hcoeff.
rewrite /KgFaithfulAugmentedModel.faithful_augmented_secret_coeff
        /KgFaithfulAugmentedModel.actual_faithful_augmented_secret.
case (col = 0)=> h0.
+ trivial.
case (1 <= col < 4)=> hscol.
+ have hcol3 : 0 <= col - 1 < 3 by move: hscol; smt().
   rewrite (actual_sgen_coeffE sgen (col - 1) coeff hcol3 hcoeff).
   trivial.
have htail : 4 <= col < 6 by move: hcol h0 hscol; smt().
have [-> | ->] : col = 4 \/ col = 5 by move: htail; smt().
+ rewrite (actual_eadj_coeffE adjusted 0 coeff) 1:/# 1:hcoeff.
   trivial.
rewrite (actual_eadj_coeffE adjusted 1 coeff) 1:/# 1:hcoeff.
trivial.
qed.

(* This BArray-free boundary is still a partial, execution-witnessed relation.
   It claims neither sampler termination or distribution, uniqueness, full
   KeyGen equivalence, nor equality with public_rounding_vector_seed. *)
op faithful_mode2_keygen_paper_lift
    (sd : HAETAE_Algebra.seed)
    (a b1 : HAETAE_Algebra.polyveck)
    (Agen : HAETAE_Algebra.matrix)
    (sgen : HAETAE_Algebra.poly list)
    (eadj : HAETAE_Algebra.polyveck) : bool =
  HAETAE_Algebra.polyveck_wf Mode2 a /\
  HAETAE_Algebra.polyveck_wf Mode2 b1 /\
  faithful_Agen_wf Agen /\
  faithful_sgen_wf sgen /\
  HAETAE_Algebra.polyveck_wf Mode2 eadj /\
  Mode2FaithfulSecurityKeygenRelationPostFreeze
    .faithful_mode2_keygen_relation
    sd a
    (faithful_kg3_matrix a b1 Agen)
    (faithful_kg4_secret sgen eadj).

lemma faithful_mode2_keygen_paper_lift_as_qj
    sd a b1 Agen sgen eadj :
  faithful_mode2_keygen_paper_lift sd a b1 Agen sgen eadj =>
  forall row coeff,
    0 <= row < 2 =>
    0 <= coeff < 256 =>
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (Mode2FaithfulSecurityKeygenRelationPostFreeze
        .faithful_packaged_matrix_vector_product_coeff
        (faithful_kg3_matrix a b1 Agen)
        (faithful_kg4_secret sgen eadj)
        row coeff)
      (KgFaithfulAugmentedModel.faithful_qj_coeff row coeff).
proof.
rewrite /faithful_mode2_keygen_paper_lift
        /Mode2FaithfulSecurityKeygenRelationPostFreeze
          .faithful_mode2_keygen_relation.
move=> [_ [_ [_ [_ [_ [_ [_ [_ [_ hqj]]]]]]]]].
exact hqj.
qed.

lemma faithful_mode2_keygen_relation_a_wf sd a augA augS :
  Mode2FaithfulSecurityKeygenRelationPostFreeze
    .faithful_mode2_keygen_relation sd a augA augS =>
  HAETAE_Algebra.polyveck_wf Mode2 a.
proof.
rewrite /Mode2FaithfulSecurityKeygenRelationPostFreeze
          .faithful_mode2_keygen_relation.
rewrite /Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
          .faithful_mode2_expandveca_security_row_global.
move=> [[_ [hawf _]] _].
exact hawf.
qed.

lemma checked_mode2_parent_m23_finalize_faithful_mode2_keygen_paper_lift
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
    exists sd a b1 Agen sgen eadj,
      faithful_mode2_keygen_paper_lift sd a b1 Agen sgen eadj /\
      sd =
        Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
          .raw_security_seed raw_seed0 /\
      a =
        Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
          res.`3 /\
      b1 =
        Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
          res.`9 /\
      Agen = actual_Agen res.`2 /\
      sgen = actual_sgen res.`4 /\
      eadj = actual_eadj res.`10].
proof.
conseq
  (Mode2FaithfulSecurityKeygenRelationPostFreeze
    .checked_mode2_parent_m23_finalize_faithful_mode2_keygen_relation
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result
  [sd a augA augS [hrel [hsd [ha [haugA haugS]]]]].
exists sd.
exists a.
exists
  (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
    result.`9).
exists (actual_Agen result.`2).
exists (actual_sgen result.`4).
exists (actual_eadj result.`10).
split.
+ split.
   + exact
       (faithful_mode2_keygen_relation_a_wf sd a augA augS hrel).
   split.
   + exact
       (Mode2FaithfulSecurityExpandVecAPostFreeze
         .actual_mode2_expandveca_wf result.`9).
   split.
   + exact (actual_Agen_wf result.`2).
   split.
   + exact (actual_sgen_wf result.`4).
   split.
   + exact (actual_eadj_wf result.`10).
   have hrel_actual :
       Mode2FaithfulSecurityKeygenRelationPostFreeze
         .faithful_mode2_keygen_relation
         sd
         (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
           result.`3)
         augA augS.
   + move: hrel.
     by rewrite ha.
   rewrite ha.
   rewrite actual_faithful_kg3_matrixE -haugA.
   rewrite actual_faithful_kg4_secretE -haugS.
   exact hrel_actual.
split; first exact hsd.
split; first exact ha.
split; first done.
split; first done.
split; first done.
done.
qed.

end Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.
