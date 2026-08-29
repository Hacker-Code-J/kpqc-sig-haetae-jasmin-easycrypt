require import AllCore DList Distr FSet IntDiv List Mu_mem Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenEtaSamplerSpec
  KeygenSamplerCallersSpec
  KeygenM23ComplexReal
  KeygenM23MatrixSpec
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorProbability
  KeygenM23SingularFFTAccumulatorSafety
  KeygenM23SingularFFTSpec
  KeygenM23SingularSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotTailPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal.
import KeygenM23SingularFFTAccumulatorProbability.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotTailPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8UnionLimitationPostFreeze.

(* This file lifts the deterministic raw_seed=0 accepted-context P8 profile
   through the finalized-[s2] accumulator slots and the complete 2 x 256 x 2
   componentwise union.  The exact interval/Markov sum is greater than 1, so
   the final theorem is deliberately a limitation certificate: it does not
   claim that the bad-event probability is greater than 1, nor does it give a
   useful subunit global probability.  Trace equality and the closed numeric
   sum remain explicit cross-language premises. *)

lemma ideal_final_s2_output_residual_muE
    pre_bp avec row k (p : complex -> bool) :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_flat_source_distribution)
    (fun xs =>
      p
        (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
          .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)) =
  mu
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_residual_odd_dft256_distribution
        pre_bp avec row k)
    (fun z =>
      p
        (cadd
          (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
            .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
          z)).
proof.
move=> hrow.
have -> :
    mu
      (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_flat_source_distribution)
      (fun xs =>
        p
          (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
            .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)) =
    mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_source_distribution row)
      (fun ys =>
        p
          (cadd
            (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
              .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
            (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
              .ideal_final_s2_row_residual_odd_dft256_sample
                pre_bp avec row ys k))).
+ rewrite
     /Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
       .ideal_final_s2_full_row_source_distribution dmapE.
  rewrite
     /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
       .ideal_final_s2_flat_source_distribution dmapE.
  rewrite dmapE.
  apply mu_eq_support => xs hxs.
  have hs2support :
      size xs = KeygenSamplerCallersSpec.mode2_k_i /\
      all
        (support
          Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
            .ideal_eta_polynomial_distribution)
        xs.
  + rewrite
      -Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_s2_support.
    exact hxs.
  have [hs2size hs2all] := hs2support.
  have hsize :
      size (flatten xs) = KeygenM23MatrixSpec.mode2_b_words_i.
  + have hflat :=
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_vector_flatten_size
          xs KeygenSamplerCallersSpec.mode2_k_i hs2size hs2all.
    move: hflat.
    rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
            /KeygenSamplerCallersSpec.mode2_k_i
            /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i.
    trivial.
  rewrite /(\o) /=.
  rewrite
    (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
      .ideal_final_s2_output_odd_dft256_cadd
        pre_bp avec row k (flatten xs)).
  rewrite
    (ideal_final_s2_residual_odd_dft256_row_projectionE
      pre_bp avec row (flatten xs) k hrow hsize).
  trivial.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .ideal_final_s2_full_row_source_distributionE row hrow).
have hdist :=
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .ideal_final_s2_full_row_residual_odd_dft256_distributionE
      pre_bp avec row k hrow.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_odd_dft256_distribution in hdist.
rewrite hdist dmapE.
trivial.
qed.

lemma ideal_mode2_accumulator_s2_slot_fft_muE
    pre_bp avec row k (p : complex -> bool) :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      p
        (KeygenM23SingularFFTAccumulatorBridge.mode2_ideal_fft_at
          sample.`1 sample.`2
          (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k)) =
  mu
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_flat_source_distribution)
    (fun xs =>
      p
        (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
          .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)).
proof.
move=> hctx hrow.
rewrite
  /Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_distribution.
rewrite dmapE.
have -> :
    mu
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_packed_secret_pair_distribution
      ((fun (sample : mode2_accumulator_sample) =>
          p
            (KeygenM23SingularFFTAccumulatorBridge.mode2_ideal_fft_at
              sample.`1 sample.`2
              (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k)) \o
       Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
         .ideal_mode2_accumulator_sample pre_bp avec) =
    mu
      ideal_mode2_s2_source_distribution
      (fun xs =>
        p
          (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
            .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)).
+ rewrite /ideal_mode2_s2_source_distribution dmapE.
  rewrite dmapE.
  rewrite dmapE.
  apply mu_eq_support => pair hpair.
  have hsecret := hpair.
  rewrite
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_secret_pair_support in hsecret.
  move: hsecret => [_ [_ [hs2size hs2all]]].
  have hs2center :
      KeygenSamplerCallersSpec.eta_vector_centered8192
        (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
          .pack_eta_vector8192 pair.`2)
        KeygenSamplerCallersSpec.mode2_k_i.
  + apply
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .pack_eta_vector8192_centered.
    + rewrite /KeygenSamplerCallersSpec.mode2_k_i.
      trivial.
    + rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
              /KeygenSamplerCallersSpec.mode2_k_i
              /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
                .eta_vector_word_capacity_i
              /BArray8192.size.
      trivial.
    + exact hs2size.
    exact hs2all.
  have hs2active :=
    Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_eta_centered_s2_active
        (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
          .pack_eta_vector8192 pair.`2)
        hs2center.
  rewrite /(\o)
          /Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
            .ideal_mode2_accumulator_sample
          /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .pack_eta_secret_pair /=.
  rewrite
    (ideal_mode2_pure_final_s2_slot_fftE
      pre_bp
      (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .pack_eta_vector8192 pair.`2)
      avec
      (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .pack_eta_vector8192 pair.`1)
      row k hctx hs2active hrow).
  trivial.
rewrite ideal_mode2_s2_source_distributionE.
trivial.
qed.

lemma ideal_final_s2_output_real_bad_mu_le_markov8
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_flat_source_distribution)
    (fun xs =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
        `|creal
            (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
              .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)| +
          KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8).
proof.
move=> hctx hrow hk.
rewrite
  (ideal_final_s2_output_residual_muE pre_bp avec row k
    (fun z =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
        `|creal z| +
          KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps)
    hrow).
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .ideal_final_s2_full_row_bias_residual_real_bad_mu_le_markov8
      pre_bp avec row k hctx hrow hk).
qed.

lemma ideal_final_s2_output_imag_bad_mu_le_markov8
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_flat_source_distribution)
    (fun xs =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
        `|cimag
            (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
              .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)| +
          KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8).
proof.
move=> hctx hrow hk.
rewrite
  (ideal_final_s2_output_residual_muE pre_bp avec row k
    (fun z =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
        `|cimag z| +
          KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps)
    hrow).
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .ideal_final_s2_full_row_bias_residual_imag_bad_mu_le_markov8
      pre_bp avec row k hctx hrow hk).
qed.

lemma ideal_mode2_accumulator_s2_slot_real_bad_mu_le_markov8
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_real_bad_at sample
        (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8).
proof.
move=> hctx hrow hk.
rewrite /mode2_accumulator_coordinate_real_bad_at.
rewrite
  (ideal_mode2_accumulator_s2_slot_fft_muE pre_bp avec row k
    (fun z =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
        `|creal z| +
          KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps)
    hctx hrow).
exact (ideal_final_s2_output_real_bad_mu_le_markov8
  pre_bp avec row k hctx hrow hk).
qed.

lemma ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_markov8
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_imag_bad_at sample
        (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8).
proof.
move=> hctx hrow hk.
rewrite /mode2_accumulator_coordinate_imag_bad_at.
rewrite
  (ideal_mode2_accumulator_s2_slot_fft_muE pre_bp avec row k
    (fun z =>
      KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
        `|cimag z| +
          KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps)
    hctx hrow).
exact (ideal_final_s2_output_imag_bad_mu_le_markov8
  pre_bp avec row k hctx hrow hk).
qed.

op zero_seed_accepted_s2_slot_real_markov8_rhs (row k : int) : real =
  interval_abs_upper (zero_seed_accepted_re_profile8_interval row k) /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom ^ 8).

op zero_seed_accepted_s2_slot_imag_markov8_rhs (row k : int) : real =
  interval_abs_upper (zero_seed_accepted_im_profile8_interval row k) /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom ^ 8).

op zero_seed_accepted_s2_slot_headroom_markov8_rhs (row k : int) : real =
  zero_seed_accepted_s2_slot_real_markov8_rhs row k +
  zero_seed_accepted_s2_slot_imag_markov8_rhs row k.

op zero_seed_accepted_s2_slot_headroom_markov8_row_sum (row : int) : real =
  BRA.bigi predT
    (fun k => zero_seed_accepted_s2_slot_headroom_markov8_rhs row k)
    0 256.

op zero_seed_accepted_s2_slot_headroom_markov8_sum : real =
  BRA.bigi predT
    zero_seed_accepted_s2_slot_headroom_markov8_row_sum
    0 2.

op zero_seed_accepted_s2_slot_headroom_markov8_row0_exact : real =
  38982172155216230333802550037313386939647176309529478840239445787624271058423278610194222277749669838158597108806117414834336691784294254553583820761118750409%r /
  12746869855271681870243555347728623393695291867714508644310259937487833179146033674927153363681559969630960245942988273704088442173087969422340393066406250000%r.

op zero_seed_accepted_s2_slot_headroom_markov8_row1_exact : real =
  138041712459395681475839667198045596276343528951853754307695956821260312117513525353508816498956593311658030401541521954214630546078532981653917506128540500697%r /
  50987479421086727480974221390914493574781167470858034577241039749951332716584134699708613454726239878523840983771953094816353768692351877689361572265625000000%r.

op zero_seed_accepted_s2_slot_headroom_markov8_exact : real =
  293970401080260602811049867347299144034932234189971669668653739971757396351206639794285705609955272664292418836765991613551977313215709999868252789173015502333%r /
  50987479421086727480974221390914493574781167470858034577241039749951332716584134699708613454726239878523840983771953094816353768692351877689361572265625000000%r.

op zero_seed_accepted_s2_slot_headroom_markov8_union_numeric_certificate : bool =
  zero_seed_accepted_s2_slot_headroom_markov8_row_sum 0 =
    zero_seed_accepted_s2_slot_headroom_markov8_row0_exact /\
  zero_seed_accepted_s2_slot_headroom_markov8_row_sum 1 =
    zero_seed_accepted_s2_slot_headroom_markov8_row1_exact /\
  zero_seed_accepted_s2_slot_headroom_markov8_sum =
    zero_seed_accepted_s2_slot_headroom_markov8_exact.

lemma ideal_mode2_accumulator_s2_slot_real_bad_mu_le_zero_seed_interval
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < 2 =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_real_bad_at sample
        (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) <=
  zero_seed_accepted_s2_slot_real_markov8_rhs row k.
proof.
move=> hctx hrow hk htrace.
have htail := ideal_mode2_accumulator_s2_slot_real_bad_mu_le_markov8
  pre_bp avec row k hctx hrow hk.
apply (ler_trans
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8))).
+ exact htail.
rewrite /zero_seed_accepted_s2_slot_real_markov8_rhs.
have hk0 : 0 <= k by smt().
have [hprofile _] :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
    .ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
      pre_bp avec row k 256 hk0.
rewrite htrace in hprofile.
rewrite -zero_seed_accepted_re_profile8_intervalE in hprofile.
have hac :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 <=
    interval_abs_upper (zero_seed_accepted_re_profile8_interval row k).
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact hprofile.
have hc :
    0%r <= interval_abs_upper
      (zero_seed_accepted_re_profile8_interval row k).
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256|).
  + exact (normr_ge0 _).
  exact hprofile.
have hhead :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom_le_real_headroom
      pre_bp avec row k hctx hrow hk.
have hmpos :
    0%r <
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 _
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom_gt0).
have hrange :
    0%r <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k by
  smt().
have hpowmono := ler_pexp 8
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k)
  _ hrange.
+ trivial.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_div_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256)
      (interval_abs_upper (zero_seed_accepted_re_profile8_interval row k))
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom ^ 8)
      hmpos hpowmono hc hac).
qed.

lemma ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_zero_seed_interval
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < 2 =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_imag_bad_at sample
        (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) <=
  zero_seed_accepted_s2_slot_imag_markov8_rhs row k.
proof.
move=> hctx hrow hk htrace.
have htail := ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_markov8
  pre_bp avec row k hctx hrow hk.
apply (ler_trans
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8))).
+ exact htail.
rewrite /zero_seed_accepted_s2_slot_imag_markov8_rhs.
have hk0 : 0 <= k by smt().
have [_ hprofile] :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
    .ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
      pre_bp avec row k 256 hk0.
rewrite htrace in hprofile.
rewrite -zero_seed_accepted_im_profile8_intervalE in hprofile.
have hac :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 <=
    interval_abs_upper (zero_seed_accepted_im_profile8_interval row k).
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact hprofile.
have hc :
    0%r <= interval_abs_upper
      (zero_seed_accepted_im_profile8_interval row k).
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256|).
  + exact (normr_ge0 _).
  exact hprofile.
have hhead :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom_le_imag_headroom
      pre_bp avec row k hctx hrow hk.
have hmpos :
    0%r <
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom ^ 8 by
  exact (expr_gt0 8 _
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
      .ideal_final_s2_uniform_min_headroom_gt0).
have hrange :
    0%r <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k by
  smt().
have hpowmono := ler_pexp 8
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_min_headroom
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k)
  _ hrange.
+ trivial.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_div_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256)
      (interval_abs_upper (zero_seed_accepted_im_profile8_interval row k))
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
        .ideal_final_s2_uniform_min_headroom ^ 8)
      hmpos hpowmono hc hac).
qed.

lemma ideal_mode2_accumulator_s2_slot_headroom_bad_mu_le_zero_seed_p8_sum
    pre_bp avec :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < 2 =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    ideal_mode2_accumulator_s2_slot_headroom_bad <=
  zero_seed_accepted_s2_slot_headroom_markov8_sum.
proof.
move=> hctx htrace.
have -> :
    ideal_mode2_accumulator_s2_slot_headroom_bad =
    (fun sample =>
      exists row,
        0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i /\
        exists k,
          0 <= k < KeygenM23SingularSpec.singular_words_i /\
          ideal_mode2_accumulator_s2_slot_headroom_bad_at sample row k).
+ apply fun_ext => sample.
  exact (ideal_mode2_accumulator_s2_slot_headroom_badE sample).
rewrite /zero_seed_accepted_s2_slot_headroom_markov8_sum.
apply
  (ideal_mode2_accumulator_rowk_range_bad_mu_le
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun row k sample =>
      ideal_mode2_accumulator_s2_slot_headroom_bad_at sample row k)
    zero_seed_accepted_s2_slot_headroom_markov8_rhs
    KeygenM23SingularFFTSpec.mode2_s2_count_i
    KeygenM23SingularSpec.singular_words_i).
+ rewrite /KeygenM23SingularFFTSpec.mode2_s2_count_i.
  trivial.
+ rewrite /KeygenM23SingularSpec.singular_words_i.
  trivial.
move=> row k hrow hk.
rewrite /ideal_mode2_accumulator_s2_slot_headroom_bad_at
        /zero_seed_accepted_s2_slot_headroom_markov8_rhs.
apply
  (mode2_accumulator_coordinate_headroom_bad_at_mu_le_split
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k
    (zero_seed_accepted_s2_slot_real_markov8_rhs row k)
    (zero_seed_accepted_s2_slot_imag_markov8_rhs row k)).
+ exact
    (ideal_mode2_accumulator_s2_slot_real_bad_mu_le_zero_seed_interval
      pre_bp avec row k hctx hrow hk (htrace row hrow)).
exact
  (ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_zero_seed_interval
    pre_bp avec row k hctx hrow hk (htrace row hrow)).
qed.

lemma zero_seed_accepted_s2_slot_headroom_markov8_exact_gt_one :
  1%r < zero_seed_accepted_s2_slot_headroom_markov8_exact.
proof.
rewrite /zero_seed_accepted_s2_slot_headroom_markov8_exact.
smt().
qed.

lemma zero_seed_accepted_s2_slot_headroom_markov8_sum_gt_one :
  zero_seed_accepted_s2_slot_headroom_markov8_union_numeric_certificate =>
  1%r < zero_seed_accepted_s2_slot_headroom_markov8_sum.
proof.
rewrite /zero_seed_accepted_s2_slot_headroom_markov8_union_numeric_certificate.
move=> [_ [_ hsum]].
rewrite hsum.
exact zero_seed_accepted_s2_slot_headroom_markov8_exact_gt_one.
qed.

lemma ideal_mode2_accumulator_s2_slot_headroom_bad_mu_le_zero_seed_p8_exact
    pre_bp avec :
  zero_seed_accepted_s2_slot_headroom_markov8_union_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < 2 =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    ideal_mode2_accumulator_s2_slot_headroom_bad <=
  zero_seed_accepted_s2_slot_headroom_markov8_exact.
proof.
rewrite /zero_seed_accepted_s2_slot_headroom_markov8_union_numeric_certificate.
move=> [_ [_ hsum]] hctx htrace.
have hbound :=
  ideal_mode2_accumulator_s2_slot_headroom_bad_mu_le_zero_seed_p8_sum
    pre_bp avec hctx htrace.
rewrite hsum in hbound.
exact hbound.
qed.

lemma zero_seed_accepted_s2_slot_headroom_markov8_bound_not_subunit :
  zero_seed_accepted_s2_slot_headroom_markov8_union_numeric_certificate =>
  ! (zero_seed_accepted_s2_slot_headroom_markov8_sum < 1%r).
proof.
move=> hnumeric.
have hgt := zero_seed_accepted_s2_slot_headroom_markov8_sum_gt_one hnumeric.
smt().
qed.

end Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8UnionLimitationPostFreeze.
