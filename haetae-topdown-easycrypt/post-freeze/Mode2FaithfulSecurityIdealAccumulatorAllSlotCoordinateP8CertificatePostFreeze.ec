require import AllCore DList Distr Finite FSet IntDiv List Mu_mem Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenEtaSamplerSpec
  KeygenSamplerCallersSpec
  KeygenM23ComplexReal
  KeygenM23FinalizeSemantics
  KeygenM23IdealRootDFT
  KeygenM23MatrixSpec
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorProbability
  KeygenM23SingularFFTAccumulatorSafety
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTSpec
  KeygenM23SingularSpec
  TargetKeygenM23SingularFFTInputBounds
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalClassProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.
import KeygenM23SingularFFTAccumulatorProbability.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalClassProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.

theory Mode2FaithfulSecurityIdealAccumulatorAllSlotCoordinateP8CertificatePostFreeze.

(* This theory adds the three direct centered-trit [s1] FFT slots to the two
   finalized-[s2] slots already certified for the deterministic raw_seed=0
   accepted trace.  It closes only the five-slot coordinate-headroom event;
   prefix-energy events, random contexts, retry termination, and an
   unconditional keygen law remain outside this theorem. *)

op ideal_mode2_s1_coordinate_headroom : real =
  8278239%r / 65536%r.

op ideal_mode2_all_slot_coordinate_p8_target : real =
  1%r / 1024%r.

op ideal_mode2_s1_class4_pre_bp : BArray8192.t =
  BArray8192.init_arr W8.zero.

op ideal_mode2_s1_class4_coefficients : int list =
  nseq KeygenM23MatrixSpec.mode2_b_words_i 2.

op ideal_mode2_s1_class4_avec : BArray8192.t =
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .pack_eta_coefficients8192 ideal_mode2_s1_class4_coefficients.

lemma ideal_mode2_s1_class4_pre_bp_get32 i :
  0 <= i < BArray8192.size %/ 4 =>
  BArray8192.get32 ideal_mode2_s1_class4_pre_bp i = W32.zero.
proof.
move=> hi.
apply W32.ext_eq => bit hbit.
rewrite W4u8.get_bits8 1:hbit.
rewrite /ideal_mode2_s1_class4_pre_bp
        BArray8192.get32d_byte 1:/#.
rewrite BArray8192.initiE 1:/# W8.zerowE W32.zerowE.
trivial.
qed.

lemma ideal_mode2_s1_class4_avec_get32 i :
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  BArray8192.get32 ideal_mode2_s1_class4_avec i =
    W32.of_int 2.
proof.
move=> hi.
rewrite /ideal_mode2_s1_class4_avec.
rewrite
  (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .pack_eta_coefficients8192_get32
      ideal_mode2_s1_class4_coefficients i).
+ rewrite /ideal_mode2_s1_class4_coefficients size_nseq
          /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .eta_vector_word_capacity_i
          /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i
          /BArray8192.size.
  trivial.
+ move: hi.
  rewrite /ideal_mode2_s1_class4_coefficients size_nseq.
  smt().
rewrite /ideal_mode2_s1_class4_coefficients
  (nth_nseq 0 i KeygenM23MatrixSpec.mode2_b_words_i 2 hi).
trivial.
qed.

lemma ideal_mode2_s1_class4_scalar_class :
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_index W32.zero (W32.of_int 2) = 4.
proof.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_index
  /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.rho
  W32.to_sintE W32.to_uint0 W32.of_uintK
  /W32.smod /KeygenM23FinalizeSemantics.q /=.
trivial.
qed.

lemma ideal_mode2_s1_class4_scalar_residual_twice x :
  x \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution =>
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .math_output W32.zero (W32.of_int 2) x)%r -
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .ideal_final_s2_mean W32.zero (W32.of_int 2) =
  2%r * x%r.
proof.
move=> hx.
have hclass :
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .ideal_final_s2_class_mod2 W32.zero (W32.of_int 2).
+ rewrite
    /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .ideal_final_s2_class_mod2
    ideal_mode2_s1_class4_scalar_class.
  trivial.
have hout :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.class_output_table_eq
    W32.zero (W32.of_int 2) x hx.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.class_output_table
  ideal_mode2_s1_class4_scalar_class in hout.
have hxout :
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .math_output W32.zero (W32.of_int 2) x = 2 * x by
  exact hout.
have hmean :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.mean_mod2
    W32.zero (W32.of_int 2) hclass.
rewrite hxout hmean.
ring.
qed.

lemma ideal_mode2_s1_class4_trace_at j :
  0 <= j < 256 =>
  ideal_final_s2_row_class_trace
    ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 j = 4.
proof.
move=> hj.
rewrite /ideal_final_s2_row_class_trace
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_class_at
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_index /=.
rewrite ideal_mode2_s1_class4_pre_bp_get32 1:/#.
  rewrite ideal_mode2_s1_class4_avec_get32 1:/#.
exact ideal_mode2_s1_class4_scalar_class.
qed.

lemma ideal_mode2_s1_class4_residual_at_twice_source i x :
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  x \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution =>
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_centered_residual_at
      ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec i x =
  2%r * x%r.
proof.
move=> hi hx.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_centered_residual_at
  /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_bias_at.
rewrite ideal_mode2_s1_class4_pre_bp_get32 1:/#.
rewrite ideal_mode2_s1_class4_avec_get32 1:hi.
exact (ideal_mode2_s1_class4_scalar_residual_twice x hx).
qed.

lemma ideal_mode2_s1_class4_residual_twice_source j x :
  0 <= j < 256 =>
  x \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution =>
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value
      ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 j x =
  2%r * x%r.
proof.
move=> hj hx.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value
  /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_coord
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_index /=.
apply (ideal_mode2_s1_class4_residual_at_twice_source j x).
+ rewrite /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i.
  smt().
exact hx.
qed.

lemma class_moment_oracles_eq c1 c2 :
  c1 = c2 =>
  ideal_final_s2_class_moment2_oracle c1 =
    ideal_final_s2_class_moment2_oracle c2 /\
  ideal_final_s2_class_moment3_oracle c1 =
    ideal_final_s2_class_moment3_oracle c2 /\
  ideal_final_s2_class_moment4_oracle c1 =
    ideal_final_s2_class_moment4_oracle c2 /\
  ideal_final_s2_class_moment5_oracle c1 =
    ideal_final_s2_class_moment5_oracle c2 /\
  ideal_final_s2_class_moment6_oracle c1 =
    ideal_final_s2_class_moment6_oracle c2 /\
  ideal_final_s2_class_moment8_oracle c1 =
    ideal_final_s2_class_moment8_oracle c2.
proof.
move=> ->.
trivial.
qed.

lemma class_re_moment_terms_trace_eq trace1 trace2 k j :
  trace1 j = trace2 j =>
  ideal_final_s2_class_re_moment2_term trace1 k j =
    ideal_final_s2_class_re_moment2_term trace2 k j /\
  ideal_final_s2_class_re_moment3_term trace1 k j =
    ideal_final_s2_class_re_moment3_term trace2 k j /\
  ideal_final_s2_class_re_moment4_term trace1 k j =
    ideal_final_s2_class_re_moment4_term trace2 k j /\
  ideal_final_s2_class_re_moment5_term trace1 k j =
    ideal_final_s2_class_re_moment5_term trace2 k j /\
  ideal_final_s2_class_re_moment6_term trace1 k j =
    ideal_final_s2_class_re_moment6_term trace2 k j /\
  ideal_final_s2_class_re_moment8_term trace1 k j =
    ideal_final_s2_class_re_moment8_term trace2 k j.
proof.
move=> htj.
rewrite /ideal_final_s2_class_re_moment2_term
        /ideal_final_s2_class_re_moment3_term
        /ideal_final_s2_class_re_moment4_term
        /ideal_final_s2_class_re_moment5_term
        /ideal_final_s2_class_re_moment6_term
        /ideal_final_s2_class_re_moment8_term.
smt().
qed.

lemma class_im_moment_terms_trace_eq trace1 trace2 k j :
  trace1 j = trace2 j =>
  ideal_final_s2_class_im_moment2_term trace1 k j =
    ideal_final_s2_class_im_moment2_term trace2 k j /\
  ideal_final_s2_class_im_moment3_term trace1 k j =
    ideal_final_s2_class_im_moment3_term trace2 k j /\
  ideal_final_s2_class_im_moment4_term trace1 k j =
    ideal_final_s2_class_im_moment4_term trace2 k j /\
  ideal_final_s2_class_im_moment5_term trace1 k j =
    ideal_final_s2_class_im_moment5_term trace2 k j /\
  ideal_final_s2_class_im_moment6_term trace1 k j =
    ideal_final_s2_class_im_moment6_term trace2 k j /\
  ideal_final_s2_class_im_moment8_term trace1 k j =
    ideal_final_s2_class_im_moment8_term trace2 k j.
proof.
move=> htj.
rewrite /ideal_final_s2_class_im_moment2_term
        /ideal_final_s2_class_im_moment3_term
        /ideal_final_s2_class_im_moment4_term
        /ideal_final_s2_class_im_moment5_term
        /ideal_final_s2_class_im_moment6_term
        /ideal_final_s2_class_im_moment8_term.
smt().
qed.

lemma class_re_profile2_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_re_profile2 trace1 k n =
    ideal_final_s2_class_re_profile2 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_re_profile2.
apply BRA.eq_big_seq => j hj.
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
rewrite /ideal_final_s2_class_re_moment2_term.
have htj := ht j hjr.
smt().
qed.

lemma class_im_profile2_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_im_profile2 trace1 k n =
    ideal_final_s2_class_im_profile2 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_im_profile2.
apply BRA.eq_big_seq => j hj.
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
rewrite /ideal_final_s2_class_im_moment2_term.
have htj := ht j hjr.
smt().
qed.

lemma class_re_profile3_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_re_profile3 trace1 k n =
    ideal_final_s2_class_re_profile3 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_re_profile3.
apply BRA.eq_big_seq => j hj.
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
rewrite /ideal_final_s2_class_re_moment3_term.
have htj := ht j hjr.
smt().
qed.

lemma class_im_profile3_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_im_profile3 trace1 k n =
    ideal_final_s2_class_im_profile3 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_im_profile3.
apply BRA.eq_big_seq => j hj.
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
rewrite /ideal_final_s2_class_im_moment3_term.
have htj := ht j hjr.
smt().
qed.

lemma class_re_profile4_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_re_profile4 trace1 k n =
    ideal_final_s2_class_re_profile4 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_re_profile4.
rewrite -/ideal_final_s2_class_re_profile2.
apply BRA.eq_big_seq => j hj.
change
  (6%r * ideal_final_s2_class_re_profile2 trace1 k j *
      ideal_final_s2_class_re_moment2_term trace1 k j +
    ideal_final_s2_class_re_moment4_term trace1 k j =
   6%r * ideal_final_s2_class_re_profile2 trace2 k j *
      ideal_final_s2_class_re_moment2_term trace2 k j +
    ideal_final_s2_class_re_moment4_term trace2 k j).
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
have hp2 := class_re_profile2_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have [ht2 [_ [ht4 _]]] :=
  class_re_moment_terms_trace_eq trace1 trace2 k j (ht j hjr).
rewrite hp2 ht2 ht4.
trivial.
qed.

lemma class_im_profile4_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_im_profile4 trace1 k n =
    ideal_final_s2_class_im_profile4 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_im_profile4.
rewrite -/ideal_final_s2_class_im_profile2.
apply BRA.eq_big_seq => j hj.
change
  (6%r * ideal_final_s2_class_im_profile2 trace1 k j *
      ideal_final_s2_class_im_moment2_term trace1 k j +
    ideal_final_s2_class_im_moment4_term trace1 k j =
   6%r * ideal_final_s2_class_im_profile2 trace2 k j *
      ideal_final_s2_class_im_moment2_term trace2 k j +
    ideal_final_s2_class_im_moment4_term trace2 k j).
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
have hp2 := class_im_profile2_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have [ht2 [_ [ht4 _]]] :=
  class_im_moment_terms_trace_eq trace1 trace2 k j (ht j hjr).
rewrite hp2 ht2 ht4.
trivial.
qed.

lemma class_re_profile5_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_re_profile5 trace1 k n =
    ideal_final_s2_class_re_profile5 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_re_profile5.
rewrite -/ideal_final_s2_class_re_profile3
        -/ideal_final_s2_class_re_profile2.
apply BRA.eq_big_seq => j hj.
change
  (10%r * ideal_final_s2_class_re_profile3 trace1 k j *
      ideal_final_s2_class_re_moment2_term trace1 k j +
   10%r * ideal_final_s2_class_re_profile2 trace1 k j *
      ideal_final_s2_class_re_moment3_term trace1 k j +
   ideal_final_s2_class_re_moment5_term trace1 k j =
   10%r * ideal_final_s2_class_re_profile3 trace2 k j *
      ideal_final_s2_class_re_moment2_term trace2 k j +
   10%r * ideal_final_s2_class_re_profile2 trace2 k j *
      ideal_final_s2_class_re_moment3_term trace2 k j +
   ideal_final_s2_class_re_moment5_term trace2 k j).
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
have hp3 := class_re_profile3_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp2 := class_re_profile2_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have [ht2 [ht3 [_ [ht5 _]]]] :=
  class_re_moment_terms_trace_eq trace1 trace2 k j (ht j hjr).
rewrite hp3 hp2 ht2 ht3 ht5.
trivial.
qed.

lemma class_im_profile5_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_im_profile5 trace1 k n =
    ideal_final_s2_class_im_profile5 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_im_profile5.
rewrite -/ideal_final_s2_class_im_profile3
        -/ideal_final_s2_class_im_profile2.
apply BRA.eq_big_seq => j hj.
change
  (10%r * ideal_final_s2_class_im_profile3 trace1 k j *
      ideal_final_s2_class_im_moment2_term trace1 k j +
   10%r * ideal_final_s2_class_im_profile2 trace1 k j *
      ideal_final_s2_class_im_moment3_term trace1 k j +
   ideal_final_s2_class_im_moment5_term trace1 k j =
   10%r * ideal_final_s2_class_im_profile3 trace2 k j *
      ideal_final_s2_class_im_moment2_term trace2 k j +
   10%r * ideal_final_s2_class_im_profile2 trace2 k j *
      ideal_final_s2_class_im_moment3_term trace2 k j +
   ideal_final_s2_class_im_moment5_term trace2 k j).
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
have hp3 := class_im_profile3_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp2 := class_im_profile2_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have [ht2 [ht3 [_ [ht5 _]]]] :=
  class_im_moment_terms_trace_eq trace1 trace2 k j (ht j hjr).
rewrite hp3 hp2 ht2 ht3 ht5.
trivial.
qed.

lemma class_re_profile6_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_re_profile6 trace1 k n =
    ideal_final_s2_class_re_profile6 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_re_profile6.
rewrite -/ideal_final_s2_class_re_profile4
        -/ideal_final_s2_class_re_profile3
        -/ideal_final_s2_class_re_profile2.
apply BRA.eq_big_seq => j hj.
change
  (15%r * ideal_final_s2_class_re_profile4 trace1 k j *
      ideal_final_s2_class_re_moment2_term trace1 k j +
   20%r * ideal_final_s2_class_re_profile3 trace1 k j *
      ideal_final_s2_class_re_moment3_term trace1 k j +
   15%r * ideal_final_s2_class_re_profile2 trace1 k j *
      ideal_final_s2_class_re_moment4_term trace1 k j +
   ideal_final_s2_class_re_moment6_term trace1 k j =
   15%r * ideal_final_s2_class_re_profile4 trace2 k j *
      ideal_final_s2_class_re_moment2_term trace2 k j +
   20%r * ideal_final_s2_class_re_profile3 trace2 k j *
      ideal_final_s2_class_re_moment3_term trace2 k j +
   15%r * ideal_final_s2_class_re_profile2 trace2 k j *
      ideal_final_s2_class_re_moment4_term trace2 k j +
   ideal_final_s2_class_re_moment6_term trace2 k j).
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
have hp4 := class_re_profile4_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp3 := class_re_profile3_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp2 := class_re_profile2_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have [ht2 [ht3 [ht4 [_ [ht6 _]]]]] :=
  class_re_moment_terms_trace_eq trace1 trace2 k j (ht j hjr).
rewrite hp4 hp3 hp2 ht2 ht3 ht4 ht6.
trivial.
qed.

lemma class_im_profile6_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_im_profile6 trace1 k n =
    ideal_final_s2_class_im_profile6 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_im_profile6.
rewrite -/ideal_final_s2_class_im_profile4
        -/ideal_final_s2_class_im_profile3
        -/ideal_final_s2_class_im_profile2.
apply BRA.eq_big_seq => j hj.
change
  (15%r * ideal_final_s2_class_im_profile4 trace1 k j *
      ideal_final_s2_class_im_moment2_term trace1 k j +
   20%r * ideal_final_s2_class_im_profile3 trace1 k j *
      ideal_final_s2_class_im_moment3_term trace1 k j +
   15%r * ideal_final_s2_class_im_profile2 trace1 k j *
      ideal_final_s2_class_im_moment4_term trace1 k j +
   ideal_final_s2_class_im_moment6_term trace1 k j =
   15%r * ideal_final_s2_class_im_profile4 trace2 k j *
      ideal_final_s2_class_im_moment2_term trace2 k j +
   20%r * ideal_final_s2_class_im_profile3 trace2 k j *
      ideal_final_s2_class_im_moment3_term trace2 k j +
   15%r * ideal_final_s2_class_im_profile2 trace2 k j *
      ideal_final_s2_class_im_moment4_term trace2 k j +
   ideal_final_s2_class_im_moment6_term trace2 k j).
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
have hp4 := class_im_profile4_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp3 := class_im_profile3_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp2 := class_im_profile2_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have [ht2 [ht3 [ht4 [_ [ht6 _]]]]] :=
  class_im_moment_terms_trace_eq trace1 trace2 k j (ht j hjr).
rewrite hp4 hp3 hp2 ht2 ht3 ht4 ht6.
trivial.
qed.

lemma class_re_profile8_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_re_profile8 trace1 k n =
    ideal_final_s2_class_re_profile8 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_re_profile8.
rewrite -/ideal_final_s2_class_re_profile6
        -/ideal_final_s2_class_re_profile5
        -/ideal_final_s2_class_re_profile4
        -/ideal_final_s2_class_re_profile3
        -/ideal_final_s2_class_re_profile2.
apply BRA.eq_big_seq => j hj.
change
  (28%r * ideal_final_s2_class_re_profile6 trace1 k j *
      ideal_final_s2_class_re_moment2_term trace1 k j +
   56%r * ideal_final_s2_class_re_profile5 trace1 k j *
      ideal_final_s2_class_re_moment3_term trace1 k j +
   70%r * ideal_final_s2_class_re_profile4 trace1 k j *
      ideal_final_s2_class_re_moment4_term trace1 k j +
   56%r * ideal_final_s2_class_re_profile3 trace1 k j *
      ideal_final_s2_class_re_moment5_term trace1 k j +
   28%r * ideal_final_s2_class_re_profile2 trace1 k j *
      ideal_final_s2_class_re_moment6_term trace1 k j +
   ideal_final_s2_class_re_moment8_term trace1 k j =
   28%r * ideal_final_s2_class_re_profile6 trace2 k j *
      ideal_final_s2_class_re_moment2_term trace2 k j +
   56%r * ideal_final_s2_class_re_profile5 trace2 k j *
      ideal_final_s2_class_re_moment3_term trace2 k j +
   70%r * ideal_final_s2_class_re_profile4 trace2 k j *
      ideal_final_s2_class_re_moment4_term trace2 k j +
   56%r * ideal_final_s2_class_re_profile3 trace2 k j *
      ideal_final_s2_class_re_moment5_term trace2 k j +
   28%r * ideal_final_s2_class_re_profile2 trace2 k j *
      ideal_final_s2_class_re_moment6_term trace2 k j +
   ideal_final_s2_class_re_moment8_term trace2 k j).
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
have hp6 := class_re_profile6_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp5 := class_re_profile5_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp4 := class_re_profile4_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp3 := class_re_profile3_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp2 := class_re_profile2_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have [ht2 [ht3 [ht4 [ht5 [ht6 ht8]]]]] :=
  class_re_moment_terms_trace_eq trace1 trace2 k j (ht j hjr).
rewrite hp6 hp5 hp4 hp3 hp2 ht2 ht3 ht4 ht5 ht6 ht8.
trivial.
qed.

lemma class_im_profile8_trace_eq trace1 trace2 k n :
  (forall j, 0 <= j < n => trace1 j = trace2 j) =>
  ideal_final_s2_class_im_profile8 trace1 k n =
    ideal_final_s2_class_im_profile8 trace2 k n.
proof.
move=> ht.
rewrite /ideal_final_s2_class_im_profile8.
rewrite -/ideal_final_s2_class_im_profile6
        -/ideal_final_s2_class_im_profile5
        -/ideal_final_s2_class_im_profile4
        -/ideal_final_s2_class_im_profile3
        -/ideal_final_s2_class_im_profile2.
apply BRA.eq_big_seq => j hj.
change
  (28%r * ideal_final_s2_class_im_profile6 trace1 k j *
      ideal_final_s2_class_im_moment2_term trace1 k j +
   56%r * ideal_final_s2_class_im_profile5 trace1 k j *
      ideal_final_s2_class_im_moment3_term trace1 k j +
   70%r * ideal_final_s2_class_im_profile4 trace1 k j *
      ideal_final_s2_class_im_moment4_term trace1 k j +
   56%r * ideal_final_s2_class_im_profile3 trace1 k j *
      ideal_final_s2_class_im_moment5_term trace1 k j +
   28%r * ideal_final_s2_class_im_profile2 trace1 k j *
      ideal_final_s2_class_im_moment6_term trace1 k j +
   ideal_final_s2_class_im_moment8_term trace1 k j =
   28%r * ideal_final_s2_class_im_profile6 trace2 k j *
      ideal_final_s2_class_im_moment2_term trace2 k j +
   56%r * ideal_final_s2_class_im_profile5 trace2 k j *
      ideal_final_s2_class_im_moment3_term trace2 k j +
   70%r * ideal_final_s2_class_im_profile4 trace2 k j *
      ideal_final_s2_class_im_moment4_term trace2 k j +
   56%r * ideal_final_s2_class_im_profile3 trace2 k j *
      ideal_final_s2_class_im_moment5_term trace2 k j +
   28%r * ideal_final_s2_class_im_profile2 trace2 k j *
      ideal_final_s2_class_im_moment6_term trace2 k j +
   ideal_final_s2_class_im_moment8_term trace2 k j).
have hjr : 0 <= j < n by move: hj; rewrite mem_range; smt().
have hp6 := class_im_profile6_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp5 := class_im_profile5_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp4 := class_im_profile4_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp3 := class_im_profile3_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have hp2 := class_im_profile2_trace_eq trace1 trace2 k j _.
+ move=> i hi; apply ht; smt().
have [ht2 [ht3 [ht4 [ht5 [ht6 ht8]]]]] :=
  class_im_moment_terms_trace_eq trace1 trace2 k j (ht j hjr).
rewrite hp6 hp5 hp4 hp3 hp2 ht2 ht3 ht4 ht5 ht6 ht8.
trivial.
qed.

lemma ideal_mode2_s1_class4_profile8_abs_upper k :
  0 <= k =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256| <=
    interval_abs_upper (homogeneous_class4_re_profile8_interval k) /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256| <=
    interval_abs_upper (homogeneous_class4_im_profile8_interval k).
proof.
move=> hk.
have [hreE himE] :=
  ideal_final_s2_row_residual_profile8_class_traceE
    ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256.
have htrace : forall j, 0 <= j < 256 =>
    ideal_final_s2_row_class_trace
      ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 j =
    homogeneous_class4_trace j.
+ move=> j hj.
  rewrite (ideal_mode2_s1_class4_trace_at j hj)
          /homogeneous_class4_trace.
  trivial.
have hreprofile := class_re_profile8_trace_eq
  (ideal_final_s2_row_class_trace
    ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0)
  homogeneous_class4_trace k 256 htrace.
have himprofile := class_im_profile8_trace_eq
  (ideal_final_s2_row_class_trace
    ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0)
  homogeneous_class4_trace k 256 htrace.
have [hre_cert him_cert] := certified_odd_root_interval_certificates k 256 hk.
have [_ hrehold] := odd_root_re_class_profile8_interval_sound
  homogeneous_class4_trace (certified_odd_root_re_interval k) k 256 hre_cert.
have [_ himhold] := odd_root_im_class_profile8_interval_sound
  homogeneous_class4_trace (certified_odd_root_im_interval k) k 256 him_cert.
have hrehold2 :
    interval_holds (homogeneous_class4_re_profile8_interval k)
      (ideal_final_s2_class_re_profile8 homogeneous_class4_trace k 256).
+ rewrite homogeneous_class4_re_profile8_intervalE
          /certified_class_re_profile8_interval.
  exact hrehold.
have himhold2 :
    interval_holds (homogeneous_class4_im_profile8_interval k)
      (ideal_final_s2_class_im_profile8 homogeneous_class4_trace k 256).
+ rewrite homogeneous_class4_im_profile8_intervalE
          /certified_class_im_profile8_interval.
  exact himhold.
split.
+ apply (interval_holds_abs_le _ _).
  rewrite hreE hreprofile.
  exact hrehold2.
apply (interval_holds_abs_le _ _).
rewrite himE himprofile.
exact himhold2.
qed.

op ideal_mode2_s1_row_fft_sample (xs : int list) (k : int) : complex =
  odd_dft256 (fun j => cof_int (nth 0 xs j)) k.

op ideal_mode2_s1_row_fft_distribution (k : int) : complex distr =
  dmap
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_source_distribution 256)
    (fun xs => ideal_mode2_s1_row_fft_sample xs k).

lemma ideal_mode2_s1_row_fft_component_scale xs k :
  size xs = 256 =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    xs =>
  creal
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_sample
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 xs k) =
    2%r * creal (ideal_mode2_s1_row_fft_sample xs k) /\
  cimag
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_sample
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 xs k) =
    2%r * cimag (ideal_mode2_s1_row_fft_sample xs k).
proof.
move=> hsize hall.
split.
+ rewrite
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_sample_creal
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 xs k).
  rewrite /ideal_mode2_s1_row_fft_sample /odd_dft256
          Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze.creal_csum256.
  rewrite BRA.mulr_sumr.
  apply BRA.eq_big_seq => j hj.
  rewrite mem_range in hj.
  have hx : nth 0 xs j \in
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution.
  + move: hall; rewrite allP => hall.
    apply hall.
    apply mem_nth.
    rewrite hsize; exact hj.
  rewrite /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
            .ideal_final_s2_row_residual_re_term
          /ideal_mode2_s1_row_fft_sample /=.
  rewrite (ideal_mode2_s1_class4_residual_twice_source j (nth 0 xs j) hj hx).
  rewrite creal_mul creal_of_int cimag_of_int /=.
  ring.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_odd_dft256_sample_cimag
      ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 xs k).
rewrite /ideal_mode2_s1_row_fft_sample /odd_dft256
        Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze.cimag_csum256.
rewrite BRA.mulr_sumr.
apply BRA.eq_big_seq => j hj.
rewrite mem_range in hj.
have hx : nth 0 xs j \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution.
+ move: hall; rewrite allP => hall.
  apply hall.
  apply mem_nth.
  rewrite hsize; exact hj.
rewrite /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_im_term
        /ideal_mode2_s1_row_fft_sample /=.
rewrite (ideal_mode2_s1_class4_residual_twice_source j (nth 0 xs j) hj hx).
rewrite cimag_mul creal_of_int cimag_of_int /=.
ring.
qed.

lemma ideal_mode2_s1_row_fft_distribution_finite k :
  is_finite (support (ideal_mode2_s1_row_fft_distribution k)).
proof.
rewrite /ideal_mode2_s1_row_fft_distribution.
apply
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.finite_dmap.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_source_distribution_finite 256 _).
qed.

lemma ideal_mode2_s1_row_fft_real_moment8E k :
  E (ideal_mode2_s1_row_fft_distribution k) (fun z => creal z ^ 8) =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8
      ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
    256%r.
proof.
have hfin_src :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_source_distribution_finite 256 _.
+ smt().
have hfin_res :
    is_finite
      (support
        (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_odd_dft256_distribution
            ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k)).
+ rewrite
    /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_distribution.
  apply
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.finite_dmap.
  exact hfin_src.
have hfin_s1 := ideal_mode2_s1_row_fft_distribution_finite k.
have hscale :
    E
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_odd_dft256_distribution
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k)
      (fun z => creal z ^ 8) =
    256%r * E (ideal_mode2_s1_row_fft_distribution k)
      (fun z => creal z ^ 8).
+ rewrite
    /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_distribution
    /ideal_mode2_s1_row_fft_distribution.
  rewrite
    (exp_dmap
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_source_distribution 256)
      (fun xs =>
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_odd_dft256_sample
            ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 xs k)
      (fun z => creal z ^ 8)
      (hasE_finite _ _ hfin_res)).
  rewrite
    (exp_dmap
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_source_distribution 256)
      (fun xs => ideal_mode2_s1_row_fft_sample xs k)
      (fun z => creal z ^ 8)
      (hasE_finite _ _ hfin_s1)).
  rewrite
    (eq_exp
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_source_distribution 256)
      ((fun z => creal z ^ 8) \o
       (fun xs =>
         Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
           .ideal_final_s2_row_residual_odd_dft256_sample
             ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 xs k))
      (fun xs => 256%r * creal (ideal_mode2_s1_row_fft_sample xs k) ^ 8)).
  + move=> xs hxs.
    have hsize := supp_dlist_size
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution 256 xs _ hxs.
    + smt().
    have hall : all
        (support
          Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
            .ideal_eta_centered_trit_distribution) xs by
      move: hxs; rewrite supp_dlist 1:/#; smt().
    have [hre _] := ideal_mode2_s1_row_fft_component_scale xs k hsize hall.
    rewrite /(\o) hre.
    ring.
  rewrite
    (expZ
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_source_distribution 256)
      256%r
      (fun xs => creal (ideal_mode2_s1_row_fft_sample xs k) ^ 8)).
  trivial.
have hmom :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_fft_real_moment8E
      ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k _.
+ rewrite /KeygenM23SingularFFTSpec.mode2_s2_count_i; smt().
rewrite hscale in hmom.
field; smt().
qed.

lemma ideal_mode2_s1_row_fft_imag_moment8E k :
  E (ideal_mode2_s1_row_fft_distribution k) (fun z => cimag z ^ 8) =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8
      ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
    256%r.
proof.
have hfin_src :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_source_distribution_finite 256 _.
+ smt().
have hfin_res :
    is_finite
      (support
        (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_odd_dft256_distribution
            ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k)).
+ rewrite
    /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_distribution.
  apply
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.finite_dmap.
  exact hfin_src.
have hfin_s1 := ideal_mode2_s1_row_fft_distribution_finite k.
have hscale :
    E
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_odd_dft256_distribution
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k)
      (fun z => cimag z ^ 8) =
    256%r * E (ideal_mode2_s1_row_fft_distribution k)
      (fun z => cimag z ^ 8).
+ rewrite
    /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_odd_dft256_distribution
    /ideal_mode2_s1_row_fft_distribution.
  rewrite
    (exp_dmap
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_source_distribution 256)
      (fun xs =>
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_odd_dft256_sample
            ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 xs k)
      (fun z => cimag z ^ 8)
      (hasE_finite _ _ hfin_res)).
  rewrite
    (exp_dmap
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_source_distribution 256)
      (fun xs => ideal_mode2_s1_row_fft_sample xs k)
      (fun z => cimag z ^ 8)
      (hasE_finite _ _ hfin_s1)).
  rewrite
    (eq_exp
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_source_distribution 256)
      ((fun z => cimag z ^ 8) \o
       (fun xs =>
         Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
           .ideal_final_s2_row_residual_odd_dft256_sample
             ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 xs k))
      (fun xs => 256%r * cimag (ideal_mode2_s1_row_fft_sample xs k) ^ 8)).
  + move=> xs hxs.
    have hsize := supp_dlist_size
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution 256 xs _ hxs.
    + smt().
    have hall : all
        (support
          Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
            .ideal_eta_centered_trit_distribution) xs by
      move: hxs; rewrite supp_dlist 1:/#; smt().
    have [_ him] := ideal_mode2_s1_row_fft_component_scale xs k hsize hall.
    rewrite /(\o) him.
    ring.
  rewrite
    (expZ
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_source_distribution 256)
      256%r
      (fun xs => cimag (ideal_mode2_s1_row_fft_sample xs k) ^ 8)).
  trivial.
have hmom :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_fft_imag_moment8E
      ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k _.
+ rewrite /KeygenM23SingularFFTSpec.mode2_s2_count_i; smt().
rewrite hscale in hmom.
field; smt().
qed.

op ideal_mode2_s1_active_source (sampled_s1 : BArray8192.t) : int list =
  map
    (fun i => W32.to_sint (BArray8192.get32 sampled_s1 i))
    (iota_ 0 KeygenM23MatrixSpec.mode2_s1_words_i).

op ideal_mode2_s1_source_distribution : int list distr =
  dmap
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_packed_secret_pair_distribution
    (fun (pair :
          Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .ideal_eta_packed_secret_pair) =>
      ideal_mode2_s1_active_source pair.`1).

lemma ideal_mode2_s1_active_source_nth sampled_s1 i :
  0 <= i < KeygenM23MatrixSpec.mode2_s1_words_i =>
  nth 0 (ideal_mode2_s1_active_source sampled_s1) i =
  W32.to_sint (BArray8192.get32 sampled_s1 i).
proof.
move=> hi.
rewrite /ideal_mode2_s1_active_source.
rewrite (nth_map 0 0
  (fun j => W32.to_sint (BArray8192.get32 sampled_s1 j))
  i (iota_ 0 KeygenM23MatrixSpec.mode2_s1_words_i)).
+ by rewrite size_iota.
by rewrite nth_iota.
qed.

lemma ideal_mode2_s1_active_source_pack_eta_vector8192 polynomials :
  size polynomials = KeygenSamplerCallersSpec.mode2_m_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    polynomials =>
  ideal_mode2_s1_active_source
    (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .pack_eta_vector8192 polynomials) =
  flatten polynomials.
proof.
move=> hsize hall.
have hflat_size :=
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_vector_flatten_size
      polynomials KeygenSamplerCallersSpec.mode2_m_i hsize hall.
have hflat_support :=
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_vector_flatten_support polynomials hall.
have hcapacity :
    size (flatten polynomials) <=
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .eta_vector_word_capacity_i.
+ rewrite hflat_size
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_m_i
          /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
             .eta_vector_word_capacity_i
          /BArray8192.size.
  trivial.
apply (eq_from_nth 0).
+ rewrite /ideal_mode2_s1_active_source size_map size_iota hflat_size.
  rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_m_i
          /KeygenM23MatrixSpec.mode2_s1_words_i
          /KeygenM23MatrixSpec.mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i.
  trivial.
move=> i hi.
have hi_src : 0 <= i < KeygenM23MatrixSpec.mode2_s1_words_i.
+ move: hi.
  rewrite /ideal_mode2_s1_active_source size_map size_iota.
  trivial.
have hi_flat : 0 <= i < size (flatten polynomials).
+ move: hi.
  rewrite /ideal_mode2_s1_active_source size_map size_iota hflat_size
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_m_i
          /KeygenM23MatrixSpec.mode2_s1_words_i
          /KeygenM23MatrixSpec.mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i.
  trivial.
rewrite ideal_mode2_s1_active_source_nth 1:hi_src.
rewrite /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze.pack_eta_vector8192.
rewrite
  (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .pack_eta_coefficients8192_get32
      (flatten polynomials) i hcapacity hi_flat).
have hsupport :
    nth 0 (flatten polynomials) i \in
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution.
+ move: hflat_support; rewrite allP => hflat_support.
  exact (hflat_support _ (mem_nth 0 (flatten polynomials) i hi_flat)).
rewrite
  (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_centered_trit_to_sint
      (nth 0 (flatten polynomials) i) hsupport).
trivial.
qed.

lemma ideal_mode2_s1_source_distributionE :
  ideal_mode2_s1_source_distribution =
  dmap
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_s1_distribution
    flatten.
proof.
rewrite /ideal_mode2_s1_source_distribution.
rewrite
  /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_packed_secret_pair_distribution.
rewrite dmap_comp.
have -> :
    dmap
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_secret_pair_distribution
      ((fun (pair :
             Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
               .ideal_eta_packed_secret_pair) =>
           ideal_mode2_s1_active_source pair.`1) \o
       Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze.pack_eta_secret_pair) =
    dmap
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_secret_pair_distribution
      (fun (pair :
            Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
              .ideal_eta_secret_pair) =>
        flatten pair.`1).
+ apply eq_dmap_in => pair hpair.
  rewrite /(\o)
          /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .pack_eta_secret_pair /=.
  rewrite
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_secret_pair_support in hpair.
  move: hpair => [hsize [hall _]].
  exact
    (ideal_mode2_s1_active_source_pack_eta_vector8192
      pair.`1 hsize hall).
have -> :
    (fun (pair :
          Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .ideal_eta_secret_pair) => flatten pair.`1) =
    flatten \o
    (fun (pair :
          Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .ideal_eta_secret_pair) => pair.`1).
+ apply fun_ext => pair; trivial.
rewrite -dmap_comp.
rewrite /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
          .ideal_eta_secret_pair_distribution.
rewrite
  (dprod_marginalL
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_s1_distribution
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_s2_distribution
    idfun).
have hs2ll :=
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze.ideal_eta_s2_lossless.
rewrite /is_lossless in hs2ll.
rewrite hs2ll dmap_id dscalar1.
trivial.
qed.

lemma ideal_mode2_s1_source_distribution_iidE :
  ideal_mode2_s1_source_distribution =
  dlist
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    KeygenM23MatrixSpec.mode2_s1_words_i.
proof.
rewrite ideal_mode2_s1_source_distributionE.
rewrite
  /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze.ideal_eta_s1_distribution
  /Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_polynomial_distribution.
rewrite dlist_dlist.
+ by rewrite /KeygenEtaSamplerSpec.eta_poly_words_i.
+ by rewrite /KeygenSamplerCallersSpec.mode2_m_i.
have -> :
    KeygenEtaSamplerSpec.eta_poly_words_i *
      KeygenSamplerCallersSpec.mode2_m_i =
    KeygenM23MatrixSpec.mode2_s1_words_i.
+ rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
           /KeygenSamplerCallersSpec.mode2_m_i
           /KeygenM23MatrixSpec.mode2_s1_words_i
           /KeygenM23MatrixSpec.mode2_cols_i
           /KeygenM23MatrixSpec.poly_words_i.
  ring.
trivial.
qed.

op ideal_mode2_s1_row_offset (slot : int) : int =
  slot * KeygenM23SingularSpec.singular_words_i.

op ideal_mode2_s1_row_suffix (slot : int) : int =
  KeygenM23MatrixSpec.mode2_s1_words_i -
  (ideal_mode2_s1_row_offset slot + KeygenM23SingularSpec.singular_words_i).

op ideal_mode2_s1_row_projection (slot : int) (xs : int list) : int list =
  take KeygenM23SingularSpec.singular_words_i
    (drop (ideal_mode2_s1_row_offset slot) xs).

op ideal_mode2_s1_row_source_distribution (slot : int) : int list distr =
  dmap ideal_mode2_s1_source_distribution
    (ideal_mode2_s1_row_projection slot).

lemma ideal_mode2_s1_row_source_distributionE slot :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  ideal_mode2_s1_row_source_distribution slot =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_source_distribution 256.
proof.
move=> hslot.
rewrite /ideal_mode2_s1_row_source_distribution
        ideal_mode2_s1_source_distribution_iidE.
have hoff : 0 <= ideal_mode2_s1_row_offset slot by
  rewrite /ideal_mode2_s1_row_offset; smt().
have hlen : 0 <= KeygenM23SingularSpec.singular_words_i by
  rewrite /KeygenM23SingularSpec.singular_words_i; trivial.
have hsuf : 0 <= ideal_mode2_s1_row_suffix slot.
+ rewrite /ideal_mode2_s1_row_suffix /ideal_mode2_s1_row_offset
          /KeygenM23SingularFFTSpec.mode2_s1_count_i
          /KeygenM23SingularSpec.singular_words_i
          /KeygenM23MatrixSpec.mode2_s1_words_i
          /KeygenM23MatrixSpec.mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i.
  smt().
have -> :
    KeygenM23MatrixSpec.mode2_s1_words_i =
    ideal_mode2_s1_row_offset slot +
    KeygenM23SingularSpec.singular_words_i +
    ideal_mode2_s1_row_suffix slot by
  rewrite /ideal_mode2_s1_row_suffix; ring.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .dmap_dlist_take_drop_middle
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution
      (ideal_mode2_s1_row_offset slot)
      KeygenM23SingularSpec.singular_words_i
      (ideal_mode2_s1_row_suffix slot)
      hoff hlen hsuf
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_centered_trit_lossless).
qed.

lemma ideal_mode2_s1_row_projection_nth slot xs j :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  size xs = KeygenM23MatrixSpec.mode2_s1_words_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  nth 0 (ideal_mode2_s1_row_projection slot xs) j =
  nth 0 xs (ideal_mode2_s1_row_offset slot + j).
proof.
move=> hslot hsize hj.
have hoff : 0 <= ideal_mode2_s1_row_offset slot.
+ rewrite /ideal_mode2_s1_row_offset.
  smt().
have hbound :
    ideal_mode2_s1_row_offset slot +
      KeygenM23SingularSpec.singular_words_i <= size xs.
+ move: hslot hsize.
  rewrite /ideal_mode2_s1_row_offset
          /KeygenM23SingularFFTSpec.mode2_s1_count_i
          /KeygenM23SingularSpec.singular_words_i
          /KeygenM23MatrixSpec.mode2_s1_words_i
          /KeygenM23MatrixSpec.mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i.
  smt().
rewrite /ideal_mode2_s1_row_projection.
rewrite nth_take 1:/#.
+ smt().
rewrite nth_drop 1:hoff.
+ smt().
trivial.
qed.

lemma ideal_mode2_s1_slot_fftE sampled_s1 sampled_s2 slot k :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  KeygenM23SingularFFTAccumulatorBridge.mode2_ideal_fft_at
    sampled_s1 sampled_s2 slot k =
  ideal_mode2_s1_row_fft_sample
    (ideal_mode2_s1_row_projection slot
      (ideal_mode2_s1_active_source sampled_s1)) k.
proof.
move=> hslot.
rewrite /KeygenM23SingularFFTAccumulatorBridge.mode2_ideal_fft_at
        /ideal_mode2_s1_row_fft_sample
        /odd_dft256 /csum256.
congr.
apply eq_in_map => j hj.
rewrite mem_iota in hj.
have hj256 : 0 <= j < KeygenM23SingularSpec.singular_words_i.
+ move: hj.
  rewrite /KeygenM23SingularSpec.singular_words_i.
  smt().
have hsrcsize :
    size (ideal_mode2_s1_active_source sampled_s1) =
      KeygenM23MatrixSpec.mode2_s1_words_i by
  rewrite /ideal_mode2_s1_active_source size_map size_iota.
have hindex :
    0 <= ideal_mode2_s1_row_offset slot + j <
      KeygenM23MatrixSpec.mode2_s1_words_i.
+ move: hslot hj256.
  rewrite /ideal_mode2_s1_row_offset
          /KeygenM23SingularFFTSpec.mode2_s1_count_i
          /KeygenM23SingularSpec.singular_words_i
          /KeygenM23MatrixSpec.mode2_s1_words_i
          /KeygenM23MatrixSpec.mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i.
  smt().
simplify.
rewrite /KeygenM23SingularFFTInitBridge.fft_coefficient_vector.
rewrite
  (TargetKeygenM23SingularFFTInputBounds.mode2_s1_slice_get32
    sampled_s1 sampled_s2 slot j hslot hj256).
rewrite
  (ideal_mode2_s1_row_projection_nth
    slot (ideal_mode2_s1_active_source sampled_s1) j
    hslot hsrcsize hj256).
rewrite ideal_mode2_s1_active_source_nth 1:hindex.
rewrite /ideal_mode2_s1_row_offset /cof_int /cof_real /=.
trivial.
qed.

lemma ideal_mode2_accumulator_s1_slot_fft_muE
    pre_bp avec slot k (p : complex -> bool) :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      p
        (KeygenM23SingularFFTAccumulatorBridge.mode2_ideal_fft_at
          sample.`1 sample.`2 slot k)) =
  mu (ideal_mode2_s1_row_fft_distribution k) p.
proof.
move=> hslot.
rewrite
  /Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_distribution
  /ideal_mode2_s1_row_fft_distribution.
rewrite -(ideal_mode2_s1_row_source_distributionE slot hslot).
rewrite /ideal_mode2_s1_row_source_distribution
        /ideal_mode2_s1_source_distribution !dmapE.
apply mu_eq => pair /=.
rewrite /(\o)
        /Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
          .ideal_mode2_accumulator_sample.
rewrite
  (ideal_mode2_s1_slot_fftE
    (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .pack_eta_vector8192 pair.`1)
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_s2 pre_bp
        (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
          .pack_eta_vector8192 pair.`2)
        avec)
    slot k hslot).
trivial.
qed.

lemma ideal_mode2_s1_coordinate_headroomE :
  ideal_mode2_s1_coordinate_headroom =
  KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap -
  KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps.
proof.
rewrite /ideal_mode2_s1_coordinate_headroom
        /KeygenM23SingularFFTAccumulatorSafety
          .accumulator_q16_coordinate_cap
        /KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps.
ring.
qed.

lemma ideal_mode2_s1_coordinate_headroom_gt0 :
  0%r < ideal_mode2_s1_coordinate_headroom.
proof.
rewrite /ideal_mode2_s1_coordinate_headroom.
smt().
qed.

op ideal_mode2_s1_slot_real_markov8_rhs (k : int) : real =
  interval_abs_upper (homogeneous_class4_re_profile8_interval k) /
  (256%r * ideal_mode2_s1_coordinate_headroom ^ 8).

op ideal_mode2_s1_slot_imag_markov8_rhs (k : int) : real =
  interval_abs_upper (homogeneous_class4_im_profile8_interval k) /
  (256%r * ideal_mode2_s1_coordinate_headroom ^ 8).

op ideal_mode2_s1_slot_headroom_markov8_rhs (k : int) : real =
  ideal_mode2_s1_slot_real_markov8_rhs k +
  ideal_mode2_s1_slot_imag_markov8_rhs k.

lemma ideal_mode2_s1_row_fft_real_tail_mu_le_p8 k :
  0 <= k =>
  mu (ideal_mode2_s1_row_fft_distribution k)
    (fun z => ideal_mode2_s1_coordinate_headroom <= `|creal z|) <=
  ideal_mode2_s1_slot_real_markov8_rhs k.
proof.
move=> hk.
have htail :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .finite_eighth_moment_markov
      (ideal_mode2_s1_row_fft_distribution k)
      creal ideal_mode2_s1_coordinate_headroom
      (ideal_mode2_s1_row_fft_distribution_finite k)
      ideal_mode2_s1_coordinate_headroom_gt0.
rewrite ideal_mode2_s1_row_fft_real_moment8E in htail.
apply
  (ler_trans
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
     256%r /
     (ideal_mode2_s1_coordinate_headroom ^ 8))).
+ exact htail.
have [hprofile _] := ideal_mode2_s1_class4_profile8_abs_upper k hk.
have hnum :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 <=
    interval_abs_upper (homogeneous_class4_re_profile8_interval k).
+ apply
    (ler_trans
      `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_re_profile8
            ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec
            0 k 256|).
  + exact (ler_norm _).
  exact hprofile.
have hupper :
    0%r <= interval_abs_upper
      (homogeneous_class4_re_profile8_interval k).
+ apply
    (ler_trans
      `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_re_profile8
            ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec
            0 k 256|).
  + exact (normr_ge0 _).
  exact hprofile.
have hpow : 0%r < ideal_mode2_s1_coordinate_headroom ^ 8 by
  exact (expr_gt0 8 _ ideal_mode2_s1_coordinate_headroom_gt0).
have hden :
    0%r < 256%r * ideal_mode2_s1_coordinate_headroom ^ 8 by smt().
have hsame :
    256%r * ideal_mode2_s1_coordinate_headroom ^ 8 <=
    256%r * ideal_mode2_s1_coordinate_headroom ^ 8 by trivial.
have -> :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
      256%r /
      (ideal_mode2_s1_coordinate_headroom ^ 8) =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
      (256%r * ideal_mode2_s1_coordinate_headroom ^ 8) by
  field; smt().
rewrite /ideal_mode2_s1_slot_real_markov8_rhs.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_div_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256)
      (interval_abs_upper (homogeneous_class4_re_profile8_interval k))
      (256%r * ideal_mode2_s1_coordinate_headroom ^ 8)
      (256%r * ideal_mode2_s1_coordinate_headroom ^ 8)
      hden hsame hupper hnum).
qed.

lemma ideal_mode2_s1_row_fft_imag_tail_mu_le_p8 k :
  0 <= k =>
  mu (ideal_mode2_s1_row_fft_distribution k)
    (fun z => ideal_mode2_s1_coordinate_headroom <= `|cimag z|) <=
  ideal_mode2_s1_slot_imag_markov8_rhs k.
proof.
move=> hk.
have htail :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .finite_eighth_moment_markov
      (ideal_mode2_s1_row_fft_distribution k)
      cimag ideal_mode2_s1_coordinate_headroom
      (ideal_mode2_s1_row_fft_distribution_finite k)
      ideal_mode2_s1_coordinate_headroom_gt0.
rewrite ideal_mode2_s1_row_fft_imag_moment8E in htail.
apply
  (ler_trans
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
     256%r /
     (ideal_mode2_s1_coordinate_headroom ^ 8))).
+ exact htail.
have [_ hprofile] := ideal_mode2_s1_class4_profile8_abs_upper k hk.
have hnum :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 <=
    interval_abs_upper (homogeneous_class4_im_profile8_interval k).
+ apply
    (ler_trans
      `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_im_profile8
            ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec
            0 k 256|).
  + exact (ler_norm _).
  exact hprofile.
have hupper :
    0%r <= interval_abs_upper
      (homogeneous_class4_im_profile8_interval k).
+ apply
    (ler_trans
      `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_im_profile8
            ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec
            0 k 256|).
  + exact (normr_ge0 _).
  exact hprofile.
have hpow : 0%r < ideal_mode2_s1_coordinate_headroom ^ 8 by
  exact (expr_gt0 8 _ ideal_mode2_s1_coordinate_headroom_gt0).
have hden :
    0%r < 256%r * ideal_mode2_s1_coordinate_headroom ^ 8 by smt().
have hsame :
    256%r * ideal_mode2_s1_coordinate_headroom ^ 8 <=
    256%r * ideal_mode2_s1_coordinate_headroom ^ 8 by trivial.
have -> :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
      256%r /
      (ideal_mode2_s1_coordinate_headroom ^ 8) =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
      (256%r * ideal_mode2_s1_coordinate_headroom ^ 8) by
  field; smt().
rewrite /ideal_mode2_s1_slot_imag_markov8_rhs.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_div_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256)
      (interval_abs_upper (homogeneous_class4_im_profile8_interval k))
      (256%r * ideal_mode2_s1_coordinate_headroom ^ 8)
      (256%r * ideal_mode2_s1_coordinate_headroom ^ 8)
      hden hsame hupper hnum).
qed.

lemma ideal_mode2_accumulator_s1_slot_real_bad_mu_le_p8
    pre_bp avec slot k :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_real_bad_at sample slot k) <=
  ideal_mode2_s1_slot_real_markov8_rhs k.
proof.
move=> hslot hk.
rewrite /mode2_accumulator_coordinate_real_bad_at.
rewrite
  (ideal_mode2_accumulator_s1_slot_fft_muE
    pre_bp avec slot k
    (fun z =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
      `|creal z| +
        KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps)
    hslot).
apply
  (ler_trans
    (mu (ideal_mode2_s1_row_fft_distribution k)
      (fun z => ideal_mode2_s1_coordinate_headroom <= `|creal z|))).
+ apply mu_le => z hz hbad.
  rewrite ideal_mode2_s1_coordinate_headroomE.
  smt().
apply (ideal_mode2_s1_row_fft_real_tail_mu_le_p8 k).
smt().
qed.

lemma ideal_mode2_accumulator_s1_slot_imag_bad_mu_le_p8
    pre_bp avec slot k :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_imag_bad_at sample slot k) <=
  ideal_mode2_s1_slot_imag_markov8_rhs k.
proof.
move=> hslot hk.
rewrite /mode2_accumulator_coordinate_imag_bad_at.
rewrite
  (ideal_mode2_accumulator_s1_slot_fft_muE
    pre_bp avec slot k
    (fun z =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
      `|cimag z| +
        KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps)
    hslot).
apply
  (ler_trans
    (mu (ideal_mode2_s1_row_fft_distribution k)
      (fun z => ideal_mode2_s1_coordinate_headroom <= `|cimag z|))).
+ apply mu_le => z hz hbad.
  rewrite ideal_mode2_s1_coordinate_headroomE.
  smt().
apply (ideal_mode2_s1_row_fft_imag_tail_mu_le_p8 k).
smt().
qed.

lemma ideal_mode2_accumulator_s1_slot_headroom_bad_mu_le_p8
    pre_bp avec slot k :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_headroom_bad_at sample slot k) <=
  ideal_mode2_s1_slot_headroom_markov8_rhs k.
proof.
move=> hslot hk.
rewrite /ideal_mode2_s1_slot_headroom_markov8_rhs.
apply
  (mode2_accumulator_coordinate_headroom_bad_at_mu_le_split
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    slot k
    (ideal_mode2_s1_slot_real_markov8_rhs k)
    (ideal_mode2_s1_slot_imag_markov8_rhs k)).
+ exact
    (ideal_mode2_accumulator_s1_slot_real_bad_mu_le_p8
      pre_bp avec slot k hslot hk).
exact
  (ideal_mode2_accumulator_s1_slot_imag_bad_mu_le_p8
    pre_bp avec slot k hslot hk).
qed.

op ideal_mode2_accumulator_s1_coordinate_headroom_bad
    (sample : mode2_accumulator_sample) : bool =
  exists slot,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i /\
    exists k,
      0 <= k < KeygenM23SingularSpec.singular_words_i /\
      mode2_accumulator_coordinate_headroom_bad_at sample slot k.

op ideal_mode2_s1_coordinate_markov8_row_sum : real =
  BRA.bigi predT ideal_mode2_s1_slot_headroom_markov8_rhs
    0 KeygenM23SingularSpec.singular_words_i.

op ideal_mode2_s1_three_slot_coordinate_markov8_sum : real =
  BRA.bigi predT
    (fun _ => ideal_mode2_s1_coordinate_markov8_row_sum)
    0 KeygenM23SingularFFTSpec.mode2_s1_count_i.

op ideal_mode2_all_slot_coordinate_markov8_sum : real =
  ideal_mode2_s1_three_slot_coordinate_markov8_sum +
  zero_seed_accepted_trace_headroom_markov8_sum.

op ideal_mode2_all_slot_coordinate_p8_numeric_certificate : bool =
  zero_seed_accepted_trace_headroom_p8_numeric_certificate /\
  ideal_mode2_s1_three_slot_coordinate_markov8_sum < 1%r / 4096%r /\
  ideal_mode2_all_slot_coordinate_markov8_sum <
    ideal_mode2_all_slot_coordinate_p8_target.

lemma ideal_mode2_accumulator_s1_coordinate_headroom_bad_mu_le_p8_sum
    pre_bp avec :
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    ideal_mode2_accumulator_s1_coordinate_headroom_bad <=
  ideal_mode2_s1_three_slot_coordinate_markov8_sum.
proof.
rewrite /ideal_mode2_accumulator_s1_coordinate_headroom_bad
        /ideal_mode2_s1_three_slot_coordinate_markov8_sum
        /ideal_mode2_s1_coordinate_markov8_row_sum
        /ideal_mode2_accumulator_rowk_range_sum.
apply
  (ideal_mode2_accumulator_rowk_range_bad_mu_le
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun slot k sample =>
      mode2_accumulator_coordinate_headroom_bad_at sample slot k)
    (fun _ k => ideal_mode2_s1_slot_headroom_markov8_rhs k)
    KeygenM23SingularFFTSpec.mode2_s1_count_i
    KeygenM23SingularSpec.singular_words_i).
+ rewrite /KeygenM23SingularFFTSpec.mode2_s1_count_i.
  trivial.
+ rewrite /KeygenM23SingularSpec.singular_words_i.
  trivial.
move=> slot k hslot hk.
apply
  (ideal_mode2_accumulator_s1_slot_headroom_bad_mu_le_p8
    pre_bp avec slot k hslot).
move: hk.
rewrite /KeygenM23SingularSpec.singular_words_i.
trivial.
qed.

lemma ideal_mode2_accumulator_coordinate_headroom_bad_splitE sample :
  mode2_accumulator_coordinate_headroom_bad sample =
  (ideal_mode2_accumulator_s1_coordinate_headroom_bad sample \/
   ideal_mode2_accumulator_s2_slot_headroom_bad sample).
proof.
rewrite /mode2_accumulator_coordinate_headroom_bad
        /ideal_mode2_accumulator_s1_coordinate_headroom_bad.
rewrite ideal_mode2_accumulator_s2_slot_headroom_badE.
apply eq_iff; split.
+ move=> [sk [hsk hbad]].
  case: sk hsk hbad => slot k hsk hbad /=.
  rewrite mode2_coordinate_site_set_mem in hsk.
  move: hsk => [hslot hk].
  case: (slot < KeygenM23SingularFFTSpec.mode2_s1_count_i) => hs1.
  + left.
    exists slot.
    split; first smt().
    exists k.
    split; first exact hk.
    exact hbad.
  right.
  exists (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i).
  split.
  + move: hslot hs1.
    rewrite /KeygenM23SingularFFTSpec.mode2_s1_count_i
            /KeygenM23SingularFFTSpec.mode2_s2_count_i
            /KeygenM23SingularFFTSpec.mode2_slice_count_i.
    smt().
  exists k.
  split; first exact hk.
  rewrite /ideal_mode2_accumulator_s2_slot_headroom_bad_at
          /ideal_mode2_accumulator_s2_slot_real_bad_at
          /ideal_mode2_accumulator_s2_slot_imag_bad_at
          /KeygenM23SingularFFTSpec.mode2_s1_count_i.
  have -> : 3 + (slot - 3) = slot by smt().
  exact hbad.
move=> [hs1 | hs2].
+ move: hs1 => [slot [hslot [k [hk hbad]]]].
  exists (slot, k).
  split.
  + rewrite mode2_coordinate_site_set_mem.
    move: hslot hk.
    rewrite /KeygenM23SingularFFTSpec.mode2_s1_count_i
            /KeygenM23SingularFFTSpec.mode2_slice_count_i
            /KeygenM23SingularSpec.singular_words_i.
    smt().
  exact hbad.
move: hs2 => [row [hrow [k [hk hbad]]]].
exists
  (KeygenM23SingularFFTSpec.mode2_s1_count_i + row, k).
split.
+ rewrite mode2_coordinate_site_set_mem.
  move: hrow hk.
  rewrite /KeygenM23SingularFFTSpec.mode2_s1_count_i
          /KeygenM23SingularFFTSpec.mode2_s2_count_i
          /KeygenM23SingularFFTSpec.mode2_slice_count_i
          /KeygenM23SingularSpec.singular_words_i.
  smt().
rewrite /ideal_mode2_accumulator_s2_slot_headroom_bad_at
        /ideal_mode2_accumulator_s2_slot_real_bad_at
        /ideal_mode2_accumulator_s2_slot_imag_bad_at.
exact hbad.
qed.

lemma ideal_mode2_accumulator_coordinate_headroom_bad_mu_le_p8_sum
    pre_bp avec :
  zero_seed_accepted_trace_headroom_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    mode2_accumulator_coordinate_headroom_bad <=
  ideal_mode2_all_slot_coordinate_markov8_sum.
proof.
move=> hzero hctx htrace.
have -> :
    mode2_accumulator_coordinate_headroom_bad =
    predU
      ideal_mode2_accumulator_s1_coordinate_headroom_bad
      ideal_mode2_accumulator_s2_slot_headroom_bad.
+ apply fun_ext => sample /=.
  exact (ideal_mode2_accumulator_coordinate_headroom_bad_splitE sample).
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec)
      ideal_mode2_accumulator_s1_coordinate_headroom_bad +
     mu
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec)
      ideal_mode2_accumulator_s2_slot_headroom_bad)).
+ exact
    (mu_or_le
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec)
      ideal_mode2_accumulator_s1_coordinate_headroom_bad
      ideal_mode2_accumulator_s2_slot_headroom_bad).
rewrite /ideal_mode2_all_slot_coordinate_markov8_sum.
apply ler_add.
+ exact
    (ideal_mode2_accumulator_s1_coordinate_headroom_bad_mu_le_p8_sum
      pre_bp avec).
exact
  (ideal_mode2_accumulator_s2_slot_headroom_bad_mu_le_zero_seed_trace_sum
    pre_bp avec hzero hctx htrace).
qed.

lemma s1_coordinate_markov8_sum_lt_one_over_4096 :
  ideal_mode2_all_slot_coordinate_p8_numeric_certificate =>
  ideal_mode2_s1_three_slot_coordinate_markov8_sum < 1%r / 4096%r.
proof.
rewrite /ideal_mode2_all_slot_coordinate_p8_numeric_certificate.
smt().
qed.

lemma ideal_mode2_accumulator_coordinate_headroom_bad_mu_lt_one_over_1024
    pre_bp avec :
  ideal_mode2_all_slot_coordinate_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    mode2_accumulator_coordinate_headroom_bad <
  1%r / 1024%r.
proof.
move=> hnumeric hctx htrace.
have [hzero [_ hall]] := hnumeric.
have hbound :=
  ideal_mode2_accumulator_coordinate_headroom_bad_mu_le_p8_sum
    pre_bp avec hzero hctx htrace.
rewrite /ideal_mode2_all_slot_coordinate_p8_target in hall.
exact (ler_lt_trans _ _ _ hbound hall).
qed.

end Mode2FaithfulSecurityIdealAccumulatorAllSlotCoordinateP8CertificatePostFreeze.
