require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra.
require import KeygenUniformXofLeafSpec KeygenSamplerCallersSpec.
require import KeygenM23FinalizeSemantics.
require import Mode2KeygenSnapshotAlgebra.
require import TargetKeygenM23FinalizeComposition.
require import KgActualAvecQjSemantics
               KgActualAvecQjComposition
               KgFaithfulAugmentedModel.

theory Mode2FaithfulSecurityExpandVecAPostFreeze.

import HAETAE_Params.

(* This adapter reifies a realized, terminating Mode-2 sampler output as a
   security-side polyveck.  The seed relation remains existential on purpose:
   it does not define a total seed-to-polyveck function or claim sampler
   termination, uniqueness, or distributional equivalence.  It also does not
   identify the BArray128 seed carrier with HAETAE_Algebra.seed. *)

lemma mode2_kE : mode_k Mode2 = 2.
proof. by []. qed.

op actual_mode2_expandveca_poly
    (avec : BArray8192.t) (row : int) : HAETAE_Algebra.poly =
  mkseq
    (fun coeff =>
      W32.to_uint (BArray8192.get32 avec (row * 256 + coeff)))
    HAETAE_Params.n.

op actual_mode2_expandveca
    (avec : BArray8192.t) : HAETAE_Algebra.polyveck =
  mkseq (actual_mode2_expandveca_poly avec) 2.

lemma actual_mode2_expandveca_poly_coeffE
    (avec : BArray8192.t) row coeff :
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (actual_mode2_expandveca_poly avec row) coeff =
  W32.to_uint (BArray8192.get32 avec (row * 256 + coeff)).
proof.
move=> hcoeff.
rewrite /actual_mode2_expandveca_poly /HAETAE_Algebra.poly_coeff.
rewrite nth_mkseq; first trivial.
by move: hcoeff; rewrite /HAETAE_Params.n.
qed.

lemma actual_mode2_expandveca_nth
    (avec : BArray8192.t) row :
  0 <= row < 2 =>
  nth HAETAE_Algebra.poly_zero (actual_mode2_expandveca avec) row =
  actual_mode2_expandveca_poly avec row.
proof.
move=> hrow.
rewrite /actual_mode2_expandveca nth_mkseq; first trivial.
by move: hrow.
qed.

lemma actual_mode2_expandveca_coeffE
    (avec : BArray8192.t) row coeff :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero (actual_mode2_expandveca avec) row)
    coeff =
  W32.to_uint (BArray8192.get32 avec (row * 256 + coeff)).
proof.
move=> hrow hcoeff.
rewrite (actual_mode2_expandveca_nth avec row hrow).
exact (actual_mode2_expandveca_poly_coeffE avec row coeff hcoeff).
qed.

lemma actual_mode2_expandveca_wf (avec : BArray8192.t) :
  HAETAE_Algebra.polyveck_wf Mode2 (actual_mode2_expandveca avec).
proof.
rewrite /HAETAE_Algebra.polyveck_wf /actual_mode2_expandveca size_mkseq.
split; first by rewrite /mode_k.
apply/List.allP=> p /mkseqP [row [hrow ->]].
by rewrite /HAETAE_Algebra.poly_wf /actual_mode2_expandveca_poly
           size_mkseq /HAETAE_Params.n.
qed.

lemma paper_mode2_a_coeff_lt_q
    (seed : BArray128.t) row coeff value :
  KgActualAvecQjSemantics.paper_mode2_a_coeff seed row coeff value =>
  0 <= coeff < 256 =>
  value < KeygenM23FinalizeSemantics.q.
proof.
move=> hpaper hcoeff.
case: hpaper => blocks pairs [hblocks [hpairs [hsize ->]]].
have hi :
    0 <= coeff <
    size
      (KeygenSamplerCallersSpec.caller_uniform_values
        seed
        (KeygenSamplerCallersSpec.vector_nonce_word
          KeygenSamplerCallersSpec.mode2_k_i
          KeygenSamplerCallersSpec.mode2_m_i row)
        blocks pairs).
+ move: hcoeff hsize.
   rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i.
   smt().
have hlt :=
  KeygenSamplerCallersSpec.caller_uniform_values_lt
    seed
    (KeygenSamplerCallersSpec.vector_nonce_word
      KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i row)
    blocks pairs coeff hi.
move: hlt.
by rewrite /KeygenUniformXofLeafSpec.uniform_q_i
           /KeygenM23FinalizeSemantics.q.
qed.

lemma actual_mode2_expandveca_coeffs_q_bound_of_actual_paper_mode2_a
    (avec : BArray8192.t) (seed : BArray128.t) :
  KgActualAvecQjComposition.actual_paper_mode2_a avec seed =>
  HAETAE_Algebra.polyveck_coeffs_q_bound Mode2
    (actual_mode2_expandveca avec).
proof.
move=> hpaper.
rewrite /HAETAE_Algebra.polyveck_coeffs_q_bound.
move=> row hrow.
rewrite /HAETAE_Algebra.poly_coeffs_q_bound.
move=> coeff hcoeff.
have hrow2 : 0 <= row < 2.
+ move: hrow.
   by rewrite mode2_kE.
have hcoeff256 : 0 <= coeff < 256.
+ move: hcoeff.
   by rewrite /HAETAE_Params.n.
have hpapercoeff :=
  hpaper row coeff hrow2 hcoeff256.
rewrite /HAETAE_Algebra.coeff_q_bound.
rewrite (actual_mode2_expandveca_coeffE avec row coeff hrow2 hcoeff256).
split.
+ by smt(W32.to_uint_cmp).
have hlt := paper_mode2_a_coeff_lt_q
  seed row coeff
  (W32.to_uint (BArray8192.get32 avec (row * 256 + coeff)))
  hpapercoeff hcoeff256.
move: hlt.
by rewrite /KeygenM23FinalizeSemantics.q /HAETAE_Params.q.
qed.

op faithful_mode2_expandveca
    (seed : BArray128.t) (a : HAETAE_Algebra.polyveck) : bool =
  HAETAE_Algebra.polyveck_wf Mode2 a /\
  forall row coeff,
    0 <= row < 2 =>
    0 <= coeff < 256 =>
    KgActualAvecQjSemantics.paper_mode2_a_coeff
      seed row coeff
      (HAETAE_Algebra.poly_coeff
        (nth HAETAE_Algebra.poly_zero a row) coeff).

lemma actual_mode2_expandveca_faithful_of_actual_paper_mode2_a
    (avec : BArray8192.t) (seed : BArray128.t) :
  KgActualAvecQjComposition.actual_paper_mode2_a avec seed =>
  faithful_mode2_expandveca seed (actual_mode2_expandveca avec).
proof.
move=> hpaper.
split; first exact (actual_mode2_expandveca_wf avec).
move=> row coeff hrow hcoeff.
rewrite (actual_mode2_expandveca_coeffE avec row coeff hrow hcoeff).
rewrite /KgActualAvecQjComposition.actual_paper_mode2_a in hpaper.
exact (hpaper row coeff hrow hcoeff).
qed.

lemma checked_mode2_parent_m23_finalize_expandveca_faithful_paper_as_qj
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
    faithful_mode2_expandveca res.`1 (actual_mode2_expandveca res.`3) /\
    HAETAE_Algebra.polyveck_coeffs_q_bound Mode2
      (actual_mode2_expandveca res.`3) /\
    (forall row coeff,
      0 <= row < 2 =>
      0 <= coeff < 256 =>
      Mode2KeygenSnapshotAlgebra.congruent_mod_2q
        (KgFaithfulAugmentedModel.faithful_augmented_matrix_vector_product_coeff
          (KgFaithfulAugmentedModel.actual_faithful_augmented_matrix
            res.`2 res.`3 res.`9)
          (KgFaithfulAugmentedModel.actual_faithful_augmented_secret
            res.`4 res.`10)
          row coeff)
        (KgFaithfulAugmentedModel.faithful_qj_coeff row coeff))].
proof.
conseq
  (KgFaithfulAugmentedModel.checked_mode2_parent_m23_finalize_faithful_augmented_paper_as_qj
     seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result [hpaper harith].
split.
+ exact
    (actual_mode2_expandveca_faithful_of_actual_paper_mode2_a
      result.`3 result.`1 hpaper).
split.
+ exact
    (actual_mode2_expandveca_coeffs_q_bound_of_actual_paper_mode2_a
      result.`3 result.`1 hpaper).
exact harith.
qed.

end Mode2FaithfulSecurityExpandVecAPostFreeze.
