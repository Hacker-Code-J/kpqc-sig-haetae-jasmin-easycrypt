require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra.
require import KeygenSeedXofSpec KeygenShakeStreamSpec
               KeygenUniformXofLeafSpec KeygenSamplerCallersSpec.
require import Mode2KeygenSnapshotAlgebra Mode2KeygenCoreEquation.
require import TargetKeygenM23FinalizeComposition
               TargetKeygenM23FinalizeSemanticComposition.
require import KgActualAvecQjComposition KgFaithfulAugmentedModel.
require import Mode2FaithfulSecurityExpandVecAPostFreeze
               Mode2FaithfulSecurityExpandVecARowWitnessPostFreeze.

theory Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.

import HAETAE_Params.

(* This bridge keeps the seed relation intentionally partial and existential.
   It does not totalize ExpandVec_a as a function of the implementation seed
   buffer, prove sampler termination in general, or identify [a] with the
   synthetic public_rounding_vector_seed.  It does identify the raw BArray32
   bytes with one explicit security seed list and its derived rhoprime slice. *)

op raw_security_seed (raw_seed : BArray32.t) : HAETAE_Algebra.seed =
  KeygenSeedXofSpec.seed_input_bytes raw_seed.

op actual_uniform_seed (seedbuf : BArray128.t) : HAETAE_Algebra.seed =
  mkseq (fun i => W8.to_uint (BArray128.get8 seedbuf i)) 32.

op security_expandveca_seed (sd : HAETAE_Algebra.seed) : HAETAE_Algebra.seed =
  HAETAE_Algebra.haetae_keygen_rhoprime sd.

op faithful_mode2_expandveca_security_seed
    (seedbuf : BArray128.t) (raw_seed : BArray32.t)
    (sd : HAETAE_Algebra.seed) : bool =
  sd = raw_security_seed raw_seed /\
  actual_uniform_seed seedbuf = security_expandveca_seed sd.

lemma raw_security_seed_size raw_seed :
  size (raw_security_seed raw_seed) = seedbytes.
proof.
by rewrite /raw_security_seed KeygenSeedXofSpec.seed_input_bytes_size /seedbytes.
qed.

lemma actual_uniform_seed_size seedbuf :
  size (actual_uniform_seed seedbuf) = seedbytes.
proof. by rewrite /actual_uniform_seed size_mkseq /seedbytes. qed.

lemma actual_uniform_seed_nth seedbuf i :
  0 <= i < seedbytes =>
  nth 0 (actual_uniform_seed seedbuf) i =
    W8.to_uint (BArray128.get8 seedbuf i).
proof.
move=> hi.
by rewrite /actual_uniform_seed /seedbytes nth_mkseq.
qed.

lemma haetae_reference_keygen_xof_input_raw_seedE raw_seed :
  HAETAE_Algebra.haetae_reference_keygen_xof_input
    (raw_security_seed raw_seed) =
  KeygenSeedXofSpec.seed_input_bytes raw_seed.
proof.
apply/(eq_from_nth 0).
+ rewrite HAETAE_Algebra.haetae_reference_keygen_xof_input_size.
  by rewrite /HAETAE_Algebra.haetae_reference_keygen_xof_absorb_bytes
             /seedbytes KeygenSeedXofSpec.seed_input_bytes_size.
move=> i.
rewrite HAETAE_Algebra.haetae_reference_keygen_xof_input_size
        /HAETAE_Algebra.haetae_reference_keygen_xof_absorb_bytes
        /seedbytes => hi.
rewrite /HAETAE_Algebra.haetae_reference_keygen_xof_input
        /HAETAE_Algebra.haetae_seed_slice nth_mkseq 1:/#
        /HAETAE_Algebra.haetae_reference_keygen_seedbuf_after_memcpy
        /HAETAE_Algebra.haetae_reference_keygen_seedbuf_bytes
        /HAETAE_Params.seedbytes /HAETAE_Params.crhbytes
        nth_mkseq 1:/#
        /raw_security_seed /KeygenSeedXofSpec.seed_input_bytes /=.
+ have hi128 : 0 <= i < 128 by smt().
  rewrite nth_mkseq 1:hi128 /=.
  rewrite (_ : i < 32) 1:/# /=.
  by rewrite nth_mkseq 1:hi.
qed.

lemma haetae_reference_keygen_xof256_seedbuf_raw_seedE raw_seed :
  HAETAE_Algebra.haetae_reference_keygen_xof256_seedbuf
    (raw_security_seed raw_seed) =
  KeygenSeedXofSpec.seed_output_bytes raw_seed.
proof.
rewrite /HAETAE_Algebra.haetae_reference_keygen_xof256_seedbuf
        HAETAE_Algebra.haetae_keygen_xof_seedbuf_shake256E.
rewrite haetae_reference_keygen_xof_input_raw_seedE.
rewrite /HAETAE_Algebra.haetae_shake256_bytes /KeygenSeedXofSpec.seed_output_bytes.
by rewrite KeygenSeedXofSpec.seed_input_bytes_size.
qed.

lemma security_expandveca_seed_outputE raw_seed :
  security_expandveca_seed (raw_security_seed raw_seed) =
  HAETAE_Algebra.haetae_keygen_seedbuf_rhoprime
    (KeygenSeedXofSpec.seed_output_bytes raw_seed).
proof.
rewrite /security_expandveca_seed HAETAE_Algebra.haetae_keygen_rhoprime_ref_sliceE.
by rewrite haetae_reference_keygen_xof256_seedbuf_raw_seedE.
qed.

lemma uniform_seed_slice_matches_security_seed
    (seedbuf : BArray128.t) (raw_seed : BArray32.t) :
  KeygenSeedXofSpec.uniform_seed_slice_matches seedbuf raw_seed =>
  actual_uniform_seed seedbuf =
    security_expandveca_seed (raw_security_seed raw_seed).
proof.
move=> hslice.
rewrite /security_expandveca_seed
        /HAETAE_Algebra.haetae_keygen_rhoprime
        haetae_reference_keygen_xof256_seedbuf_raw_seedE.
apply/(eq_from_nth 0).
+ rewrite actual_uniform_seed_size
          HAETAE_Algebra.haetae_keygen_seedbuf_rhoprime_size.
  trivial.
move=> i.
rewrite actual_uniform_seed_size => hi.
rewrite actual_uniform_seed_nth 1:hi.
rewrite /HAETAE_Algebra.haetae_keygen_seedbuf_rhoprime
        /HAETAE_Algebra.haetae_seed_slice nth_mkseq 1:/#
        /HAETAE_Algebra.haetae_keygen_rhoprime_offset /=.
rewrite /KeygenSeedXofSpec.uniform_seed_slice_matches
        /KeygenSeedXofSpec.output_slice_matches in hslice.
exact (hslice i _).
qed.

lemma mode2_sampler_facts_security_seed
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2 counter mat0 avec0 s10 s20 raw_seed0 =>
  faithful_mode2_expandveca_security_seed
    seedbuf raw_seed0 (raw_security_seed raw_seed0).
proof.
move=> hfacts.
rewrite /faithful_mode2_expandveca_security_seed.
split; first by [].
move: hfacts.
rewrite /TargetKeygenM23FinalizeComposition.mode2_sampler_facts.
move=> [_ [hslice _]].
exact (uniform_seed_slice_matches_security_seed seedbuf raw_seed0 hslice).
qed.

op security_seed_nonce_input
    (sd : HAETAE_Algebra.seed) (nonce : W64.t) : int list =
  mkseq
    (fun i =>
       if i < seedbytes then
         nth 0 (security_expandveca_seed sd) i
       else if i = seedbytes then
         W64.to_uint nonce %% 256
       else
         (W64.to_uint nonce %/ 256) %% 256)
    (seedbytes + 2).

op security_mode2_xof_bytes
    (sd : HAETAE_Algebra.seed) (row blocks : int) : int list =
  KeygenShakeStreamSpec.shake128_squeeze_bytes
    (KeygenShakeStreamSpec.shake128_absorb_once_short_state
      (security_seed_nonce_input sd
        (KeygenSamplerCallersSpec.vector_nonce_word
          KeygenSamplerCallersSpec.mode2_k_i
          KeygenSamplerCallersSpec.mode2_m_i row))
      34)
    blocks.

op security_mode2_accepted_values
    (sd : HAETAE_Algebra.seed) (row blocks pairs : int) : int list =
  KeygenUniformXofLeafSpec.uniform_accepted
    (security_mode2_xof_bytes sd row blocks) pairs.

lemma security_seed_nonce_input_size sd nonce :
  size (security_seed_nonce_input sd nonce) = 34.
proof. by rewrite /security_seed_nonce_input /seedbytes size_mkseq. qed.

lemma actual_shake128_seed_nonce_inputE
    (seedbuf : BArray128.t)
    (raw_seed : BArray32.t)
    (sd : HAETAE_Algebra.seed)
    (nonce : W64.t) :
  faithful_mode2_expandveca_security_seed seedbuf raw_seed sd =>
  KeygenShakeStreamSpec.shake128_seed_nonce_input
    seedbuf (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i) nonce =
  security_seed_nonce_input sd nonce.
proof.
rewrite /faithful_mode2_expandveca_security_seed.
move=> [_ hseed].
rewrite /security_seed_nonce_input -hseed.
apply/(eq_from_nth 0).
+ rewrite /KeygenShakeStreamSpec.shake128_seed_nonce_input
           /KeygenShakeStreamSpec.seed_nonce_input
           /seedbytes !size_mkseq.
  trivial.
move=> i.
rewrite /KeygenShakeStreamSpec.shake128_seed_nonce_input
        /seedbytes
        !size_mkseq => hi.
rewrite KeygenShakeStreamSpec.seed_nonce_input_nth 1:/# 1:/#.
rewrite nth_mkseq 1:/#.
case (i < 32) => hseed_i.
+ rewrite /KeygenSamplerCallersSpec.uniform_seed_offset_i /=.
  rewrite actual_uniform_seed_nth 1:/#.
  by rewrite hseed_i.
by rewrite hseed_i.
qed.

lemma caller_uniform_values_securityE
    (seedbuf : BArray128.t)
    (raw_seed : BArray32.t)
    (sd : HAETAE_Algebra.seed)
    row blocks pairs :
  faithful_mode2_expandveca_security_seed seedbuf raw_seed sd =>
  KeygenSamplerCallersSpec.caller_uniform_values
    seedbuf
    (KeygenSamplerCallersSpec.vector_nonce_word
      KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i row)
    blocks pairs =
  security_mode2_accepted_values sd row blocks pairs.
proof.
move=> hseed.
rewrite /KeygenSamplerCallersSpec.caller_uniform_values
        /security_mode2_accepted_values
        /security_mode2_xof_bytes
        /KeygenShakeStreamSpec.shake128_seed_nonce_padded_state.
rewrite (actual_shake128_seed_nonce_inputE
          seedbuf raw_seed sd
          (KeygenSamplerCallersSpec.vector_nonce_word
            KeygenSamplerCallersSpec.mode2_k_i
            KeygenSamplerCallersSpec.mode2_m_i row) hseed).
done.
qed.

op faithful_mode2_expandveca_security_row_global
    (sd : HAETAE_Algebra.seed) (a : HAETAE_Algebra.polyveck) : bool =
  size sd = seedbytes /\
  HAETAE_Algebra.polyveck_wf Mode2 a /\
  forall row,
    0 <= row < 2 =>
    exists blocks pairs,
      4 <= blocks /\
      0 <= pairs <=
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
      size (security_mode2_accepted_values sd row blocks pairs) = 256 /\
      forall coeff,
        0 <= coeff < 256 =>
        HAETAE_Algebra.poly_coeff
          (nth HAETAE_Algebra.poly_zero a row) coeff =
        nth 0 (security_mode2_accepted_values sd row blocks pairs) coeff.

lemma faithful_mode2_expandveca_security_row_global_of_actual
    (seedbuf : BArray128.t)
    (raw_seed : BArray32.t)
    (sd : HAETAE_Algebra.seed)
    (a : HAETAE_Algebra.polyveck) :
  faithful_mode2_expandveca_security_seed seedbuf raw_seed sd =>
  Mode2FaithfulSecurityExpandVecARowWitnessPostFreeze
    .faithful_mode2_expandveca_row_global seedbuf a =>
  faithful_mode2_expandveca_security_row_global sd a.
proof.
move=> hseed [hwf hrows].
have hsdsize : size sd = seedbytes.
+ move: hseed.
  rewrite /faithful_mode2_expandveca_security_seed.
  move=> [-> _].
  exact (raw_security_seed_size raw_seed).
split; first exact hsdsize.
split; first exact hwf.
move=> row hrow.
case: (hrows row hrow) => blocks pairs [hblocks [hpairs [hsize hall]]].
exists blocks pairs.
split; first exact hblocks.
split; first exact hpairs.
split.
+ move: hsize.
   by rewrite (caller_uniform_values_securityE
                seedbuf raw_seed sd row blocks pairs hseed).
move=> coeff hcoeff.
move: (hall coeff hcoeff).
by rewrite (caller_uniform_values_securityE
              seedbuf raw_seed sd row blocks pairs hseed).
qed.

lemma checked_mode2_parent_m23_finalize_expandveca_security_seed_row_global_paper_as_qj
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
    faithful_mode2_expandveca_security_seed
      res.`1 raw_seed0 (raw_security_seed raw_seed0) /\
    faithful_mode2_expandveca_security_row_global
        (raw_security_seed raw_seed0)
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
have hseed :
    faithful_mode2_expandveca_security_seed
      result.`1 raw_seed0 (raw_security_seed raw_seed0).
+ exact
    (mode2_sampler_facts_security_seed
      result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
      mat0 avec0 s10 s20 raw_seed0 hsampler).
have hrow_actual :=
  Mode2FaithfulSecurityExpandVecARowWitnessPostFreeze
    .actual_mode2_expandveca_row_global_of_mode2_sampler_facts
      result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
      mat0 avec0 s10 s20 raw_seed0 hsampler.
have hrow_security :=
  faithful_mode2_expandveca_security_row_global_of_actual
    result.`1 raw_seed0 (raw_security_seed raw_seed0)
    (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
      result.`3)
    hseed hrow_actual.
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
split; first exact hseed.
split; first exact hrow_security.
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

end Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.
