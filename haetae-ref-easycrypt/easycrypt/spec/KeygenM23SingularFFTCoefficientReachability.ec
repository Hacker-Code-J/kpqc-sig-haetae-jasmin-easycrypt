require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

require import
  BArray32 BArray128 BArray1024 BArray2048 BArray8192 BArray32768
  SBArray8192_1024.
require import
  KeygenEtaSamplerSpec
  KeygenSamplerCallersSpec
  KeygenM23MatrixSpec
  KeygenM23FinalizeSemantics
  KeygenM23FinalizeArraySemantics
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTScheduleBounds
  KeygenM23SingularFFTGlobalTrace
  KeygenMode2ParentTarget
  TargetKeygenM23FinalizeComposition
  TargetKeygenM23Singular.

theory KeygenM23SingularFFTCoefficientReachability.

op mode2_fft_inputs_bound2
    (s1 s2 : BArray8192.t) : bool =
  forall slot,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    KeygenM23SingularFFTInitBridge.fft_coefficient_bound
      (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot) 2.

lemma mode2_s1_slice_get32
    (s1 s2 : BArray8192.t) (slot i : int) :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  0 <= i < KeygenM23SingularSpec.singular_words_i =>
  BArray1024.get32
    (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot) i =
  BArray8192.get32 s1
    (slot * KeygenM23SingularSpec.singular_words_i + i).
proof.
move=> hslot hi.
rewrite (TargetKeygenM23Singular.mode2_slice_s1E s1 s2 slot hslot).
rewrite SBArray8192_1024.get32d_get_sub 1:/#.
by congr; ring.
qed.

lemma mode2_s2_slice_get32
    (s1 s2 : BArray8192.t) (slot i : int) :
  KeygenM23SingularFFTSpec.mode2_s1_count_i <= slot <
    KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= i < KeygenM23SingularSpec.singular_words_i =>
  BArray1024.get32
    (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot) i =
  BArray8192.get32 s2
    ((slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
      KeygenM23SingularSpec.singular_words_i + i).
proof.
move=> hslot hi.
rewrite (TargetKeygenM23Singular.mode2_slice_s2E s1 s2 slot hslot).
rewrite SBArray8192_1024.get32d_get_sub 1:/#.
by congr; ring.
qed.

lemma mode2_s1_slot_coefficient_bound2
    (s1 s2 : BArray8192.t) (slot : int) :
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s1 KeygenSamplerCallersSpec.mode2_m_i =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  KeygenM23SingularFFTInitBridge.fft_coefficient_bound
    (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot) 2.
proof.
move=> hs1 hslot.
rewrite /KeygenM23SingularFFTInitBridge.fft_coefficient_bound.
move=> i hi.
rewrite mode2_s1_slice_get32 1:hslot 1:hi.
rewrite /KeygenSamplerCallersSpec.eta_vector_centered8192
        /KeygenEtaSamplerSpec.centered_interval8192 in hs1.
have hidx :
    0 <= slot * KeygenM23SingularSpec.singular_words_i + i <
      KeygenSamplerCallersSpec.eta_vector_words_i
        KeygenSamplerCallersSpec.mode2_m_i.
+ rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_m_i
          /KeygenM23SingularSpec.singular_words_i in hslot.
  rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_m_i
          /KeygenM23SingularSpec.singular_words_i in hi.
  smt().
move: (hs1 (slot * KeygenM23SingularSpec.singular_words_i + i) hidx).
by smt().
qed.

lemma mode2_finalized_s2_slot_coefficient_bound2
    (s1 bp0 s2p0 ap0 bp s2 : BArray8192.t) (slot : int) :
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s2p0 KeygenSamplerCallersSpec.mode2_k_i =>
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    bp0 s2p0 ap0 bp s2 =>
  KeygenM23SingularFFTSpec.mode2_s1_count_i <= slot <
    KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  KeygenM23SingularFFTInitBridge.fft_coefficient_bound
    (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot) 2.
proof.
move=> hs20 hfinal hslot.
rewrite /KeygenM23SingularFFTInitBridge.fft_coefficient_bound.
move=> i hi.
rewrite mode2_s2_slice_get32 1:hslot 1:hi.
rewrite /KeygenSamplerCallersSpec.eta_vector_centered8192
        /KeygenEtaSamplerSpec.centered_interval8192 in hs20.
have hidx :
    0 <=
      (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
        KeygenM23SingularSpec.singular_words_i + i <
      KeygenSamplerCallersSpec.eta_vector_words_i
        KeygenSamplerCallersSpec.mode2_k_i.
+ rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_k_i
          /KeygenM23SingularFFTSpec.mode2_s1_count_i
          /KeygenM23SingularFFTSpec.mode2_slice_count_i
          /KeygenM23SingularSpec.singular_words_i in hslot.
  rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_k_i
          /KeygenM23SingularSpec.singular_words_i in hi.
  smt().
have hs2word :=
  hs20
    ((slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
      KeygenM23SingularSpec.singular_words_i + i) hidx.
have hactive :
    0 <=
      (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
        KeygenM23SingularSpec.singular_words_i + i <
      KeygenM23MatrixSpec.mode2_b_words_i.
+ rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_k_i in hidx.
  exact hidx.
move: hfinal => [hwords _].
have [_ hs2eq] :=
  hwords
    ((slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
      KeygenM23SingularSpec.singular_words_i + i) hactive.
have hlow :=
  KeygenM23FinalizeSemantics.vk_low_int_range
    (KeygenM23FinalizeArraySemantics.raw_residue
      (BArray8192.get32 bp0
        ((slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
          KeygenM23SingularSpec.singular_words_i + i))
      (BArray8192.get32 s2p0
        ((slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
          KeygenM23SingularSpec.singular_words_i + i))
      (BArray8192.get32 ap0
        ((slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
          KeygenM23SingularSpec.singular_words_i + i))).
rewrite hs2eq.
by smt().
qed.

lemma mode2_fft_inputs_bound2_of_sampler_finalize
    (s1 bp0 s2p0 ap0 bp s2 : BArray8192.t) :
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s1 KeygenSamplerCallersSpec.mode2_m_i =>
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s2p0 KeygenSamplerCallersSpec.mode2_k_i =>
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    bp0 s2p0 ap0 bp s2 =>
  mode2_fft_inputs_bound2 s1 s2.
proof.
move=> hs1 hs20 hfinal.
rewrite /mode2_fft_inputs_bound2.
move=> slot hslot.
case (slot < KeygenM23SingularFFTSpec.mode2_s1_count_i) => hbranch.
+ have hs1slot :
      0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i by smt().
  exact (mode2_s1_slot_coefficient_bound2 s1 s2 slot hs1 hs1slot).
have hs2slot :
    KeygenM23SingularFFTSpec.mode2_s1_count_i <= slot <
      KeygenM23SingularFFTSpec.mode2_slice_count_i by smt().
exact
  (mode2_finalized_s2_slot_coefficient_bound2
    s1 bp0 s2p0 ap0 bp s2 slot hs20 hfinal hs2slot).
qed.

lemma mode2_fft_inputs_bound2_of_mode2_sampler_finalize
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2p0 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (bp0 bp s2 : BArray8192.t) :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2p0 counter mat0 avec0 s10 s20 raw_seed0 =>
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    bp0 s2p0 avec bp s2 =>
  mode2_fft_inputs_bound2 s1 s2.
proof.
move=> hsampler hfinal.
have hs1 :
    KeygenSamplerCallersSpec.eta_vector_centered8192
      s1 KeygenSamplerCallersSpec.mode2_m_i.
+ move: hsampler.
  rewrite /TargetKeygenM23FinalizeComposition.mode2_sampler_facts.
  smt().
have hs20 :
    KeygenSamplerCallersSpec.eta_vector_centered8192
      s2p0 KeygenSamplerCallersSpec.mode2_k_i.
+ move: hsampler.
  rewrite /TargetKeygenM23FinalizeComposition.mode2_sampler_facts.
  smt().
exact
  (mode2_fft_inputs_bound2_of_sampler_finalize
    s1 bp0 s2p0 avec bp s2 hs1 hs20 hfinal).
qed.

lemma mode2_fft_slot_schedule_safe
    (data : BArray2048.t)
    (s1 s2 : BArray8192.t) (slot : int) :
  mode2_fft_inputs_bound2 s1 s2 =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  KeygenM23SingularFFTGlobalTrace.actual_fft_schedule_safe
    data (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot).
proof.
move=> hbound hslot.
apply
  KeygenM23SingularFFTGlobalTrace.actual_fft_schedule_safe_from_bound2.
exact (hbound slot hslot).
qed.

lemma mode2_fft_slot_full_word_bound2
    (data : BArray2048.t)
    (s1 s2 : BArray8192.t) (slot : int) :
  mode2_fft_inputs_bound2 s1 s2 =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  KeygenM23SingularFFTBounds.fft_word_bound
    (KeygenM23SingularFFTSpec.fft_full
      (KeygenM23SingularFFTScheduleBounds.actual_fft_init_data_bound2
        data (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot))
      KeygenMode2ParentTarget.jfft_roots)
    859963392.
proof.
move=> hbound hslot.
exact
  (KeygenM23SingularFFTScheduleBounds.actual_fft_full_word_bound2
    data (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot)
    (hbound slot hslot)).
qed.

lemma mode2_sampler_finalize_fft_slot_schedule_safe
    (data : BArray2048.t)
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2p0 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (bp0 bp s2 : BArray8192.t)
    (slot : int) :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2p0 counter mat0 avec0 s10 s20 raw_seed0 =>
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    bp0 s2p0 avec bp s2 =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  KeygenM23SingularFFTGlobalTrace.actual_fft_schedule_safe
    data (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot).
proof.
move=> hsampler hfinal hslot.
apply mode2_fft_slot_schedule_safe => //.
exact
  (mode2_fft_inputs_bound2_of_mode2_sampler_finalize
    seedbuf mat avec s1 s2p0 counter mat0 avec0 s10 s20 raw_seed0
    bp0 bp s2 hsampler hfinal).
qed.

lemma mode2_sampler_finalize_fft_slot_full_word_bound2
    (data : BArray2048.t)
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2p0 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t)
    (bp0 bp s2 : BArray8192.t)
    (slot : int) :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2p0 counter mat0 avec0 s10 s20 raw_seed0 =>
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    bp0 s2p0 avec bp s2 =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  KeygenM23SingularFFTBounds.fft_word_bound
    (KeygenM23SingularFFTSpec.fft_full
      (KeygenM23SingularFFTScheduleBounds.actual_fft_init_data_bound2
        data (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot))
      KeygenMode2ParentTarget.jfft_roots)
    859963392.
proof.
move=> hsampler hfinal hslot.
apply mode2_fft_slot_full_word_bound2 => //.
exact
  (mode2_fft_inputs_bound2_of_mode2_sampler_finalize
    seedbuf mat avec s1 s2p0 counter mat0 avec0 s10 s20 raw_seed0
    bp0 bp s2 hsampler hfinal).
qed.

end KeygenM23SingularFFTCoefficientReachability.
