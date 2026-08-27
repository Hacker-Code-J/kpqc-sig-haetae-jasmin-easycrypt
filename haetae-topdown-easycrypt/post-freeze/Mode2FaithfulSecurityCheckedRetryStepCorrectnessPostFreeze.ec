require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray128 BArray8192 BArray32768.
require import KeygenMode2ParentTarget
               KeygenSamplerCallersSpec KeygenEtaSamplerSpec
               KeygenM23MatrixSpec KeygenM23ArithmeticSpec
               KeygenM23FinalizeSpec
               KeygenM23FinalizeArraySemantics
               KeygenM23FinalizeHAETAEBridge
               KeygenM23SingularFFTSpec
               TargetKeygenMode2Parent
               TargetKeygenM23ParentComposition
               TargetKeygenM23Arithmetic
               TargetKeygenM23Finalize
               TargetKeygenM23FinalizeComposition
               TargetKeygenM23Singular
               TargetKeygenM23FullFirstAttempt
               Mode2KeygenCoreEquation
               Mode2FaithfulSecurityRetryEtaProgressPostFreeze
               Mode2FaithfulSecurityCheckedRetryStepPostFreeze.

theory Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze.

module Parent = KeygenMode2ParentTarget.M.
module RetryStep =
  Mode2FaithfulSecurityCheckedRetryStepPostFreeze.CheckedMode2RetryStep.

(* This layer gives one already-materialized retry state a semantic snapshot.
   It does not establish that the full loop reaches that state, a distribution
   for the state, an acceptance probability, whole-loop termination, packing,
   full key generation, or equality with [HAETAE.kg]. *)

type retry_step_snapshot =
  BArray128.t * BArray32768.t *
  BArray8192.t * BArray8192.t * BArray8192.t * W64.t *
  BArray8192.t * BArray8192.t *
  BArray8192.t * BArray8192.t *
  W64.t * W64.t * W64.t.

op retry_step_accepted (snapshot : retry_step_snapshot) : bool =
  snapshot.`13 = W64.zero.

op retry_step_score (snapshot : retry_step_snapshot) : W64.t =
  snapshot.`11.

op retry_step_score_within_bound
    (snapshot : retry_step_snapshot) : bool =
  W64.to_uint (retry_step_score snapshot) <= 611098.

op retry_step_guard (snapshot : retry_step_snapshot) : bool =
  ! (snapshot.`12 \ult snapshot.`11).

op retry_step_eta_pair_facts
    (seedbuf0 : BArray128.t)
    (s10 s20 : BArray8192.t)
    retry
    (sampled_s1 sampled_s2 : BArray8192.t)
    (next_counter : W64.t) : bool =
  KeygenSamplerCallersSpec.eta_vector_stream8192
    sampled_s1 seedbuf0
      (W64.of_int
        (KeygenSamplerCallersSpec.mode2_retry_counter_i retry))
      KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.eta_vector_centered8192
    sampled_s1 KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.eta_vector_frame8192
    s10 sampled_s1 KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.eta_vector_stream8192
    sampled_s2 seedbuf0
      (W64.of_int
        (KeygenSamplerCallersSpec.mode2_eta_nonce_i
          retry KeygenSamplerCallersSpec.mode2_m_i))
      KeygenSamplerCallersSpec.mode2_k_i /\
  KeygenSamplerCallersSpec.eta_vector_centered8192
    sampled_s2 KeygenSamplerCallersSpec.mode2_k_i /\
  KeygenSamplerCallersSpec.eta_vector_frame8192
    s20 sampled_s2 KeygenSamplerCallersSpec.mode2_k_i /\
  next_counter =
    W64.of_int
      (KeygenSamplerCallersSpec.mode2_retry_counter_i (retry + 1)).

op retry_step_decision_facts (snapshot : retry_step_snapshot) : bool =
  snapshot.`12 = W64.of_int 611098 /\
  snapshot.`13 =
    (if snapshot.`12 \ult snapshot.`11 then W64.one else W64.zero).

op checked_mode2_retry_step_snapshot_facts
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry
    (snapshot : retry_step_snapshot) : bool =
  snapshot.`1 = seedbuf0 /\
  snapshot.`2 = mat0 /\
  snapshot.`3 = avec0 /\
  Mode2KeygenCoreEquation.canonical_a_active snapshot.`3 /\
  retry_step_eta_pair_facts
    seedbuf0 s10 s20 retry snapshot.`4 snapshot.`5 snapshot.`6 /\
  TargetKeygenM23FinalizeComposition.mode2_m23_facts
    snapshot.`2 snapshot.`4 snapshot.`7 snapshot.`8 bp0 s1hat0 /\
  KeygenM23FinalizeSpec.finalize_output
    snapshot.`7 snapshot.`5 snapshot.`3 snapshot.`9 snapshot.`10 /\
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    snapshot.`7 snapshot.`5 snapshot.`3 snapshot.`9 snapshot.`10 /\
  KeygenM23FinalizeHAETAEBridge.finalize_haetae_semantic_output
    snapshot.`7 snapshot.`5 snapshot.`3 snapshot.`9 snapshot.`10 /\
  snapshot.`11 =
    KeygenM23SingularFFTSpec.mode2_singular_word
      snapshot.`4 snapshot.`10
      KeygenMode2ParentTarget.jfft_roots
      KeygenMode2ParentTarget.jfft_brv8 /\
  retry_step_decision_facts snapshot.

lemma retry_eta_centered_s2_active (s2 : BArray8192.t) :
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s2 KeygenSamplerCallersSpec.mode2_k_i =>
  Mode2KeygenCoreEquation.centered_s2_active s2.
proof.
move=> hcenter.
rewrite /Mode2KeygenCoreEquation.centered_s2_active.
move=> i hi.
rewrite /KeygenSamplerCallersSpec.eta_vector_centered8192
        /KeygenSamplerCallersSpec.eta_vector_words_i
        /KeygenSamplerCallersSpec.mode2_k_i
        /KeygenEtaSamplerSpec.centered_interval8192
        /KeygenEtaSamplerSpec.eta_poly_words_i /= in hcenter.
apply (hcenter i).
move: hi.
rewrite /KeygenM23MatrixSpec.mode2_b_words_i
        /KeygenM23MatrixSpec.mode2_rows_i
        /KeygenM23MatrixSpec.poly_words_i.
smt().
qed.

lemma retry_step_finalize_semantics
    (mat : BArray32768.t)
    (sampled_s1 pre_bp s1hatp bp0 s1hat0
      sampled_s2 avec final_bp final_s2 : BArray8192.t) :
  TargetKeygenM23FinalizeComposition.mode2_m23_facts
    mat sampled_s1 pre_bp s1hatp bp0 s1hat0 =>
  KeygenSamplerCallersSpec.eta_vector_centered8192
    sampled_s2 KeygenSamplerCallersSpec.mode2_k_i =>
  Mode2KeygenCoreEquation.canonical_a_active avec =>
  KeygenM23FinalizeSpec.finalize_output
    pre_bp sampled_s2 avec final_bp final_s2 =>
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
      pre_bp sampled_s2 avec final_bp final_s2 /\
  KeygenM23FinalizeHAETAEBridge.finalize_haetae_semantic_output
      pre_bp sampled_s2 avec final_bp final_s2.
proof.
rewrite /TargetKeygenM23FinalizeComposition.mode2_m23_facts.
move=> [hmat [hin [hout [hntt [hbpframe hhatframe]]]]]
        hcenter hcanonical hfinal.
have hs2active := retry_eta_centered_s2_active sampled_s2 hcenter.
have hreachable :=
  Mode2KeygenCoreEquation.finalize_reachable_inputs_from_matrix_output
    pre_bp sampled_s2 avec mat
    (KeygenM23ArithmeticSpec.wide_poly sampled_s1 0)
    (KeygenM23ArithmeticSpec.wide_poly
      sampled_s1 KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      sampled_s1 (2 * KeygenM23MatrixSpec.poly_words_i))
    hout hs2active hcanonical.
have hsemantic :=
  KeygenM23FinalizeArraySemantics.finalize_output_semantics
    pre_bp sampled_s2 avec final_bp final_s2 hreachable hfinal.
split; first exact hsemantic.
exact
  (KeygenM23FinalizeHAETAEBridge.finalize_semantic_output_haetae
    pre_bp sampled_s2 avec final_bp final_s2 hsemantic).
qed.

lemma checked_mode2_retry_step_snapshot_build
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry
    (sampled_s1 sampled_s2 : BArray8192.t)
    (next_counter : W64.t)
    (pre_bp s1hatp final_bp final_s2 : BArray8192.t)
    (sv : W64.t) :
  Mode2KeygenCoreEquation.canonical_a_active avec0 =>
  retry_step_eta_pair_facts
    seedbuf0 s10 s20 retry sampled_s1 sampled_s2 next_counter =>
  TargetKeygenM23FinalizeComposition.mode2_m23_facts
    mat0 sampled_s1 pre_bp s1hatp bp0 s1hat0 =>
  KeygenM23FinalizeSpec.finalize_output
    pre_bp sampled_s2 avec0 final_bp final_s2 =>
  sv =
    KeygenM23SingularFFTSpec.mode2_singular_word
      sampled_s1 final_s2
      KeygenMode2ParentTarget.jfft_roots
      KeygenMode2ParentTarget.jfft_brv8 =>
  checked_mode2_retry_step_snapshot_facts
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry
    (seedbuf0, mat0, avec0, sampled_s1, sampled_s2, next_counter,
     pre_bp, s1hatp, final_bp, final_s2, sv,
     W64.of_int 611098,
     (if W64.of_int 611098 \ult sv then W64.one else W64.zero)).
proof.
move=> hcanonical heta hm23 hfinal hsv.
have hs2center :
    KeygenSamplerCallersSpec.eta_vector_centered8192
      sampled_s2 KeygenSamplerCallersSpec.mode2_k_i.
+ move: heta.
  rewrite /retry_step_eta_pair_facts.
  smt().
have hsemantics :=
  retry_step_finalize_semantics
    mat0 sampled_s1 pre_bp s1hatp bp0 s1hat0
    sampled_s2 avec0 final_bp final_s2
    hm23 hs2center hcanonical hfinal.
move: hsemantics => [hsemantic hhaetae].
rewrite /checked_mode2_retry_step_snapshot_facts
        /retry_step_decision_facts /=.
split; first exact hcanonical.
split; first exact heta.
split; first exact hm23.
split; first exact hfinal.
split; first exact hsemantic.
split; first exact hhaetae.
exact hsv.
qed.

lemma checked_mode2_retry_step_snapshot_decision_facts
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry snapshot :
  checked_mode2_retry_step_snapshot_facts
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry snapshot =>
  retry_step_decision_facts snapshot.
proof.
rewrite /checked_mode2_retry_step_snapshot_facts.
smt().
qed.

lemma checked_mode2_retry_step_snapshot_accepted_scoreE
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry snapshot :
  checked_mode2_retry_step_snapshot_facts
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry snapshot =>
  (retry_step_accepted snapshot <=>
   retry_step_score_within_bound snapshot).
proof.
move=> hsnapshot.
have hdecision :=
  checked_mode2_retry_step_snapshot_decision_facts
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry snapshot hsnapshot.
rewrite /retry_step_decision_facts in hdecision.
move: hdecision => [hbound hreject].
rewrite /retry_step_accepted
        /retry_step_score_within_bound
        /retry_step_score hreject hbound.
exact (TargetKeygenM23FullFirstAttempt.mode2_singular_reject_zeroE
  snapshot.`11).
qed.

lemma checked_mode2_retry_step_snapshot_guardE
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry snapshot :
  checked_mode2_retry_step_snapshot_facts
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry snapshot =>
  (retry_step_guard snapshot <=>
   retry_step_score_within_bound snapshot).
proof.
move=> hsnapshot.
have hdecision :=
  checked_mode2_retry_step_snapshot_decision_facts
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry snapshot hsnapshot.
rewrite /retry_step_decision_facts in hdecision.
move: hdecision => [hbound _].
rewrite /retry_step_guard
        /retry_step_score_within_bound
        /retry_step_score hbound.
exact (TargetKeygenM23Singular.mode2_singular_guardE snapshot.`11).
qed.

lemma checked_mode2_retry_step_snapshot_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry :
  hoare [RetryStep.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    counter =
      W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i retry) /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_nowrap retry /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 mat0 /\
    Mode2KeygenCoreEquation.canonical_a_active avec0
    ==>
    checked_mode2_retry_step_snapshot_facts
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry res].
proof.
proc.
seq 8 :
  (seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
   bp = bp0 /\ s1hatp = s1hat0 /\
   kr = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
   mr = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
   Mode2FaithfulSecurityRetryEtaProgressPostFreeze
     .mode2_retry_eta_nowrap retry /\
   KeygenM23ArithmeticSpec.matrix_active_bound16 mat0 /\
   Mode2KeygenCoreEquation.canonical_a_active avec0 /\
   retry_step_eta_pair_facts
     seedbuf0 s10 s20 retry s1 s2 counter).
+ wp.
  call
    (TargetKeygenMode2Parent.expand_eta_stream_correct
      s20 seedbuf0
      (W64.of_int
        (KeygenSamplerCallersSpec.mode2_eta_nonce_i
          retry KeygenSamplerCallersSpec.mode2_m_i))
      KeygenSamplerCallersSpec.mode2_k_i).
  wp.
  call
    (TargetKeygenMode2Parent.expand_eta_stream_correct
      s10 seedbuf0
      (W64.of_int
        (KeygenSamplerCallersSpec.mode2_retry_counter_i retry))
      KeygenSamplerCallersSpec.mode2_m_i).
  auto => />.
  rewrite /retry_step_eta_pair_facts
          /KeygenSamplerCallersSpec.mode2_eta_nonce_i
          /KeygenSamplerCallersSpec.mode2_retry_counter_i
          /KeygenSamplerCallersSpec.mode2_retry_span_i
          /KeygenSamplerCallersSpec.mode2_m_i
          /KeygenSamplerCallersSpec.mode2_k_i
          /KeygenSamplerCallersSpec.eta_vector_words_i
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /BArray8192.size.
  smt().
seq 1 :
  (seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
   kr = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
   mr = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
   Mode2FaithfulSecurityRetryEtaProgressPostFreeze
     .mode2_retry_eta_nowrap retry /\
   Mode2KeygenCoreEquation.canonical_a_active avec0 /\
   retry_step_eta_pair_facts
     seedbuf0 s10 s20 retry s1 s2 counter /\
   TargetKeygenM23FinalizeComposition.mode2_m23_facts
     mat s1 bp s1hatp bp0 s1hat0).
+ exlim s1 => sampled_s1.
  call
    (TargetKeygenM23Arithmetic.kp_m23_matrix_mode2_arithmetic_correct
      bp0 s1hat0 mat0 sampled_s1
      (KeygenM23ArithmeticSpec.wide_poly sampled_s1 0)
      (KeygenM23ArithmeticSpec.wide_poly
        sampled_s1 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        sampled_s1 (2 * KeygenM23MatrixSpec.poly_words_i))).
  auto => />.
  rewrite /retry_step_eta_pair_facts
          /TargetKeygenM23FinalizeComposition.mode2_m23_facts.
  move=> &hr _ _ _ _ _ hcenter _ _ _ _.
  have hin :=
    TargetKeygenM23ParentComposition
      .sampler_eta_mode2_input_repr_bound16 sampled_s1 hcenter.
  move: hin.
  rewrite /KeygenM23ArithmeticSpec.mode2_input_repr_bound16
          /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  move=> [[_ hbound0] [[_ hbound1] [_ hbound2]]].
  by do split.
seq 2 :
  (seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
   kr = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
   mr = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
   Mode2FaithfulSecurityRetryEtaProgressPostFreeze
     .mode2_retry_eta_nowrap retry /\
   Mode2KeygenCoreEquation.canonical_a_active avec0 /\
   retry_step_eta_pair_facts
     seedbuf0 s10 s20 retry s1 sampled_s2 counter /\
   TargetKeygenM23FinalizeComposition.mode2_m23_facts
     mat s1 pre_bp s1hatp bp0 s1hat0 /\
   bp = pre_bp /\
   s2 = sampled_s2).
+ auto => />.
seq 11 :
  (seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
   Mode2FaithfulSecurityRetryEtaProgressPostFreeze
     .mode2_retry_eta_nowrap retry /\
   Mode2KeygenCoreEquation.canonical_a_active avec0 /\
   retry_step_eta_pair_facts
     seedbuf0 s10 s20 retry s1 sampled_s2 counter /\
   TargetKeygenM23FinalizeComposition.mode2_m23_facts
     mat s1 pre_bp s1hatp bp0 s1hat0 /\
   bp = pre_bp /\
   s2 = sampled_s2 /\
   count = W64.of_int KeygenM23MatrixSpec.mode2_b_words_i).
+ auto => />;
    rewrite /SLH64.protect_64 /SLH64.protect_ptr
            /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i;
    trivial.
seq 1 :
  (seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
   Mode2FaithfulSecurityRetryEtaProgressPostFreeze
     .mode2_retry_eta_nowrap retry /\
   Mode2KeygenCoreEquation.canonical_a_active avec0 /\
   retry_step_eta_pair_facts
     seedbuf0 s10 s20 retry s1 sampled_s2 counter /\
   TargetKeygenM23FinalizeComposition.mode2_m23_facts
     mat s1 pre_bp s1hatp bp0 s1hat0 /\
   KeygenM23FinalizeSpec.finalize_output
     pre_bp sampled_s2 avec bp s2).
+ exlim bp => prefinal_bp0.
  exlim s2 => sampled_s20.
  exlim avec => sampled_avec0.
  call
    (TargetKeygenM23Finalize.keypair_finalize_m23_mode2_correct
      prefinal_bp0 sampled_s20 sampled_avec0).
  auto => />.
seq 1 :
  (seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
   Mode2KeygenCoreEquation.canonical_a_active avec0 /\
   retry_step_eta_pair_facts
     seedbuf0 s10 s20 retry s1 sampled_s2 counter /\
   TargetKeygenM23FinalizeComposition.mode2_m23_facts
     mat s1 pre_bp s1hatp bp0 s1hat0 /\
   KeygenM23FinalizeSpec.finalize_output
     pre_bp sampled_s2 avec bp s2 /\
   sv =
     KeygenM23SingularFFTSpec.mode2_singular_word
       s1 s2
       KeygenMode2ParentTarget.jfft_roots
       KeygenMode2ParentTarget.jfft_brv8).
+ ecall (TargetKeygenM23Singular.singular_full_mode2_word_exact s1 s2).
  auto => />.
auto.
move=> &hr
  [hseed [hmat [havec [hcanonical [heta [hm23 [hfinal hsv]]]]]]].
have hm23' :
    TargetKeygenM23FinalizeComposition.mode2_m23_facts
      mat0 s1{hr} pre_bp{hr} s1hatp{hr} bp0 s1hat0.
+ by rewrite -hmat.
have hfinal' :
    KeygenM23FinalizeSpec.finalize_output
      pre_bp{hr} sampled_s2{hr} avec0 bp{hr} s2{hr}.
+ by rewrite -havec.
have hbuild :=
  checked_mode2_retry_step_snapshot_build
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry
    s1{hr} sampled_s2{hr} counter{hr}
    pre_bp{hr} s1hatp{hr} bp{hr} s2{hr} sv{hr}
    hcanonical heta hm23' hfinal' hsv.
rewrite /SLH64.protect_64 hseed hmat havec.
move: hbuild.
case: (W64.of_int 611098 \ult sv{hr}) => //=.
qed.

(* The peeled tail starts after retry zero.  This corollary records that
   schedule boundary only; it does not prove reachability of the loop state. *)
lemma checked_mode2_retry_tail_snapshot_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    retry :
  hoare [RetryStep.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    counter =
      W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i retry) /\
    1 <= retry /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_nowrap retry /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 mat0 /\
    Mode2KeygenCoreEquation.canonical_a_active avec0
    ==>
    checked_mode2_retry_step_snapshot_facts
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry res].
proof.
conseq
  (checked_mode2_retry_step_snapshot_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 retry) => //=.
qed.

end Mode2FaithfulSecurityCheckedRetryStepCorrectnessPostFreeze.
