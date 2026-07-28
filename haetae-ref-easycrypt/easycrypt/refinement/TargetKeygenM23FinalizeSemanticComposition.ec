require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768
               Fq KeygenM23MatrixSpec KeygenM23ArithmeticSpec
               KeygenSamplerCallersSpec KeygenEtaSamplerSpec
               KeygenUniformXofLeafSpec
               KeygenM23FinalizeSpec KeygenM23FinalizeSemantics
               KeygenM23FinalizeArraySemantics
               KeygenM23FinalizeHAETAEBridge
               TargetKeygenM23FinalizeComposition.

theory TargetKeygenM23FinalizeSemanticComposition.

lemma mode2_m23_facts_word_bound16
    (mat : BArray32768.t)
    (s1 bp s1hatp bp0 s1hat0 : BArray8192.t) i :
  TargetKeygenM23FinalizeComposition.mode2_m23_facts
    mat s1 bp s1hatp bp0 s1hat0 =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  Fq.bw32 (BArray8192.get32 bp i) 16.
proof.
move=> hf hi.
have hout :
    KeygenM23ArithmeticSpec.mode2_output_repr_bound16
      bp mat
      (KeygenM23ArithmeticSpec.wide_poly s1 0)
      (KeygenM23ArithmeticSpec.wide_poly
        s1 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        s1 (2 * KeygenM23MatrixSpec.poly_words_i)).
+ move: hf.
  rewrite /TargetKeygenM23FinalizeComposition.mode2_m23_facts.
  smt().
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

lemma mode2_sampler_facts_s2_centered
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t) i :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2 counter mat0 avec0 s10 s20 raw_seed0 =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  -1 <= W32.to_sint (BArray8192.get32 s2 i) <= 1.
proof.
move=> hf hi.
have hc :
    KeygenSamplerCallersSpec.eta_vector_centered8192
      s2 KeygenSamplerCallersSpec.mode2_k_i.
+ move: hf.
  rewrite /TargetKeygenM23FinalizeComposition.mode2_sampler_facts.
  smt().
rewrite /KeygenSamplerCallersSpec.eta_vector_centered8192
        /KeygenSamplerCallersSpec.eta_vector_words_i
        /KeygenSamplerCallersSpec.mode2_k_i
        /KeygenEtaSamplerSpec.centered_interval8192
        /KeygenEtaSamplerSpec.eta_poly_words_i /= in hc.
apply (hc i).
move: hi.
rewrite /KeygenM23MatrixSpec.mode2_b_words_i
        /KeygenM23MatrixSpec.mode2_rows_i
        /KeygenM23MatrixSpec.poly_words_i.
smt().
qed.

lemma mode2_sampler_facts_avec_bounded
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t) i :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2 counter mat0 avec0 s10 s20 raw_seed0 =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  W32.to_uint (BArray8192.get32 avec i) <
    KeygenM23FinalizeSemantics.q.
proof.
move=> hf hi.
have hu :
    KeygenSamplerCallersSpec.uniform_vector_range8192
      avec KeygenSamplerCallersSpec.mode2_k_i.
+ move: hf.
  rewrite /TargetKeygenM23FinalizeComposition.mode2_sampler_facts.
  smt().
rewrite /KeygenSamplerCallersSpec.uniform_vector_range8192 in hu.
case (i < KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ move=> hi0.
  have hslot := hu 0 _.
  + rewrite /KeygenSamplerCallersSpec.mode2_k_i.
    smt().
  rewrite /KeygenUniformXofLeafSpec.bounded_prefix8192
          /KeygenSamplerCallersSpec.uniform_vector_words_i in hslot.
  have h := hslot i _.
  + rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i in hi0.
    smt().
  move: h.
  rewrite /KeygenM23FinalizeSemantics.q
          /KeygenUniformXofLeafSpec.uniform_q_i /=.
  done.
+ move=> hi0.
  have hslot := hu 1 _.
  + rewrite /KeygenSamplerCallersSpec.mode2_k_i.
    smt().
  rewrite /KeygenUniformXofLeafSpec.bounded_prefix8192
          /KeygenSamplerCallersSpec.uniform_vector_words_i in hslot.
  have hj :
      0 <= i - KeygenUniformXofLeafSpec.uniform_poly_words_i <
        KeygenUniformXofLeafSpec.uniform_poly_words_i.
  + move: hi hi0.
    rewrite /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i
            /KeygenUniformXofLeafSpec.uniform_poly_words_i.
    smt().
  have h := hslot
    (i - KeygenUniformXofLeafSpec.uniform_poly_words_i) hj.
  move: h.
  rewrite /KeygenSamplerCallersSpec.uniform_vector_words_i
          /KeygenUniformXofLeafSpec.uniform_poly_words_i
          /KeygenM23FinalizeSemantics.q
          /KeygenUniformXofLeafSpec.uniform_q_i /=.
  done.
qed.

lemma checked_mode2_parent_m23_finalize_semantic_correct
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
    TargetKeygenM23FinalizeComposition.mode2_sampler_facts
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      mat0 avec0 s10 s20 raw_seed0 /\
    TargetKeygenM23FinalizeComposition.mode2_m23_facts
      res.`2 res.`4 res.`7 res.`8 bp0 s1hat0 /\
    KeygenM23FinalizeSpec.finalize_output
      res.`7 res.`5 res.`3 res.`9 res.`10 /\
    KeygenM23FinalizeArraySemantics.finalize_semantic_output
      res.`7 res.`5 res.`3 res.`9 res.`10].
proof.
conseq
  (TargetKeygenM23FinalizeComposition.checked_mode2_parent_m23_finalize_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr hpre result [hsampler [hm23 hfinal]].
split.
+ exact hsampler.
split.
+ exact hm23.
split.
+ exact hfinal.
apply KeygenM23FinalizeArraySemantics.finalize_output_semantics.
+ rewrite /KeygenM23FinalizeArraySemantics.finalize_reachable_inputs.
  move=> i hi.
  rewrite /KeygenM23FinalizeArraySemantics.reachable_word_inputs.
  split.
  + exact
      (mode2_m23_facts_word_bound16
        result.`2 result.`4 result.`7 result.`8 bp0 s1hat0 i
        hm23 hi).
  split.
  + exact
      (mode2_sampler_facts_s2_centered
        result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
        mat0 avec0 s10 s20 raw_seed0 i hsampler hi).
  + exact
      (mode2_sampler_facts_avec_bounded
        result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
        mat0 avec0 s10 s20 raw_seed0 i hsampler hi).
+ exact hfinal.
qed.

lemma checked_mode2_parent_m23_finalize_haetae_correct
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
    TargetKeygenM23FinalizeComposition.mode2_sampler_facts
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      mat0 avec0 s10 s20 raw_seed0 /\
    TargetKeygenM23FinalizeComposition.mode2_m23_facts
      res.`2 res.`4 res.`7 res.`8 bp0 s1hat0 /\
    KeygenM23FinalizeSpec.finalize_output
      res.`7 res.`5 res.`3 res.`9 res.`10 /\
    KeygenM23FinalizeArraySemantics.finalize_semantic_output
      res.`7 res.`5 res.`3 res.`9 res.`10 /\
    KeygenM23FinalizeHAETAEBridge.finalize_haetae_semantic_output
      res.`7 res.`5 res.`3 res.`9 res.`10].
proof.
conseq
  (checked_mode2_parent_m23_finalize_semantic_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr hpre result
  [hsampler [hm23 [hfinal hsemantic]]].
split.
+ exact hsampler.
split.
+ exact hm23.
split.
+ exact hfinal.
split.
+ exact hsemantic.
apply KeygenM23FinalizeHAETAEBridge.finalize_semantic_output_haetae.
exact hsemantic.
qed.

end TargetKeygenM23FinalizeSemanticComposition.
