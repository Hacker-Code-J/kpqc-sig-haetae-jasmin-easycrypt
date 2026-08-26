require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra.
require import KeygenUniformXofLeafSpec KeygenSamplerCallersSpec.
require import Mode2KeygenSnapshotAlgebra Mode2KeygenCoreEquation.
require import TargetKeygenM23FinalizeComposition
               TargetKeygenM23FinalizeSemanticComposition.
require import KgActualAvecQjComposition
               KgFaithfulAugmentedModel
               Mode2FaithfulSecurityExpandVecAPostFreeze.

theory Mode2FaithfulSecurityExpandVecARowWitnessPostFreeze.

import HAETAE_Params.

(* Stronger than the coefficientwise paper predicate: each row carries one
   shared finite sampler witness whose accepted list has length 256 and
   matches all 256 coefficients of the adapted security polyveck.  This stays
   intentionally existential and relational; it does not totalize the seed,
   assert sampler termination in general, claim uniqueness of witnesses, or
   upgrade to any distributional statement.  The two rows may use different
   witnesses, and BArray128 is not identified with HAETAE_Algebra.seed. *)
op faithful_mode2_expandveca_row_global
    (seed : BArray128.t) (a : HAETAE_Algebra.polyveck) : bool =
  HAETAE_Algebra.polyveck_wf Mode2 a /\
  forall row,
    0 <= row < 2 =>
    exists blocks pairs,
      4 <= blocks /\
      0 <= pairs <=
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
      size (KeygenSamplerCallersSpec.caller_uniform_values
        seed
        (KeygenSamplerCallersSpec.vector_nonce_word
          KeygenSamplerCallersSpec.mode2_k_i
          KeygenSamplerCallersSpec.mode2_m_i row)
        blocks pairs) = 256 /\
      forall coeff,
        0 <= coeff < 256 =>
        HAETAE_Algebra.poly_coeff
          (nth HAETAE_Algebra.poly_zero a row) coeff =
        nth 0
          (KeygenSamplerCallersSpec.caller_uniform_values
            seed
            (KeygenSamplerCallersSpec.vector_nonce_word
              KeygenSamplerCallersSpec.mode2_k_i
              KeygenSamplerCallersSpec.mode2_m_i row)
            blocks pairs)
          coeff.

lemma actual_mode2_expandveca_row_global_of_uniform_vector_stream8192
    (avec : BArray8192.t) (seed : BArray128.t) :
  KeygenSamplerCallersSpec.uniform_vector_stream8192
    avec seed
    KeygenSamplerCallersSpec.mode2_k_i
    KeygenSamplerCallersSpec.mode2_m_i
    KeygenSamplerCallersSpec.mode2_k_i =>
  faithful_mode2_expandveca_row_global
    seed
    (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca avec).
proof.
move=> hstream.
split.
+ exact
    (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca_wf
      avec).
move=> row hrow.
rewrite /KeygenSamplerCallersSpec.uniform_vector_stream8192 in hstream.
have hrow2 : 0 <= row < KeygenSamplerCallersSpec.mode2_k_i.
+ exact hrow.
have hrow_stream := hstream row hrow2.
case: hrow_stream => blocks pairs [hblocks [hpairs [hsize hdecoded]]].
exists blocks pairs.
split; first exact hblocks.
split; first exact hpairs.
split.
+ move: hsize.
   by rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i.
move=> coeff hcoeff.
rewrite
  (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca_coeffE
    avec row coeff hrow hcoeff).
rewrite /KeygenUniformXofLeafSpec.decoded_prefix8192 in hdecoded.
have hdecoded_coeff := hdecoded coeff _.
+ move: hcoeff hsize.
   rewrite /KeygenSamplerCallersSpec.uniform_vector_words_i
           /KeygenUniformXofLeafSpec.uniform_poly_words_i.
   smt().
move: hdecoded_coeff.
rewrite /KeygenSamplerCallersSpec.uniform_vector_words_i
        /KeygenUniformXofLeafSpec.uniform_poly_words_i.
trivial.
qed.

lemma actual_mode2_expandveca_row_global_of_mode2_sampler_facts
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2 counter mat0 avec0 s10 s20 raw_seed0 =>
  faithful_mode2_expandveca_row_global
    seedbuf
    (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca avec).
proof.
move=> hf.
have hstream :
    KeygenSamplerCallersSpec.uniform_vector_stream8192
      avec seedbuf 2 3 2.
+ move: hf.
   rewrite /TargetKeygenM23FinalizeComposition.mode2_sampler_facts
           /KeygenSamplerCallersSpec.mode2_k_i
           /KeygenSamplerCallersSpec.mode2_m_i.
   smt().
exact
  (actual_mode2_expandveca_row_global_of_uniform_vector_stream8192
    avec seedbuf hstream).
qed.

lemma faithful_mode2_expandveca_of_row_global
    (seed : BArray128.t) (a : HAETAE_Algebra.polyveck) :
  faithful_mode2_expandveca_row_global seed a =>
  Mode2FaithfulSecurityExpandVecAPostFreeze.faithful_mode2_expandveca
    seed a.
proof.
move=> [hwf hrow_global].
split; first exact hwf.
move=> row coeff hrow hcoeff.
case: (hrow_global row hrow) =>
  blocks pairs [hblocks [hpairs [hsize hall]]].
exists blocks pairs.
split; first exact hblocks.
split; first exact hpairs.
split; first exact hsize.
exact (hall coeff hcoeff).
qed.

lemma checked_mode2_parent_m23_finalize_expandveca_row_global_paper_as_qj
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
    faithful_mode2_expandveca_row_global
      res.`1
      (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
        res.`3) /\
    HAETAE_Algebra.polyveck_coeffs_q_bound Mode2
      (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
        res.`3) /\
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
  (TargetKeygenM23FinalizeSemanticComposition.checked_mode2_parent_m23_finalize_semantic_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result [hsampler [hm23 [_ hsemantic]]].
have hrow_global :=
  actual_mode2_expandveca_row_global_of_mode2_sampler_facts
    result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
    mat0 avec0 s10 s20 raw_seed0 hsampler.
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
split; first exact hrow_global.
split.
+ exact
    (Mode2FaithfulSecurityExpandVecAPostFreeze
      .actual_mode2_expandveca_coeffs_q_bound_of_actual_paper_mode2_a
      result.`3 result.`1 ha).
move=> row coeff hrow hcoeff.
exact
  (KgFaithfulAugmentedModel.faithful_augmented_product_qj_from_generated_dot
    result.`7 result.`5 result.`2 result.`4 result.`3 result.`9 result.`10
    row coeff hqj hrow hcoeff
    (KgFaithfulAugmentedModel.mode2_m23_facts_generated_row_product
      result.`2 result.`4 result.`7 result.`8 bp0 s1hat0 row
      hm23 hrow)).
qed.

end Mode2FaithfulSecurityExpandVecARowWitnessPostFreeze.
