require import AllCore Distr IntDiv List Real Ring StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenEtaSamplerSpec
  KeygenSamplerCallersSpec
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23MatrixSpec
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorProbability
  KeygenM23SingularFFTAccumulatorSafety
  Mode2KeygenCoreEquation
  TargetKeygenM23Singular
  TargetKeygenM23SingularFFTInputBounds
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze.

import RealOrder.
import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorProbability.

theory Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotTailPostFreeze.

(* This file only bridges the finalized-[s2] ideal fixed-context row law into
   the mode-2 accumulator slots [3,4].  It does not certify [s1] slots, the
   five-slot joint certificate, prefix-energy events, actual/fixed-point FFT
   behavior, random contexts, SHAKE coupling, or any packed-array equality
   beyond the single-slot pushforwards proved below. *)

op ideal_mode2_s2_active_source (sampled_s2 : BArray8192.t) : int list =
  map
    (fun i => W32.to_sint (BArray8192.get32 sampled_s2 i))
    (iota_ 0 KeygenM23MatrixSpec.mode2_b_words_i).

op ideal_mode2_s2_source_distribution : int list distr =
  dmap
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_packed_secret_pair_distribution
    (fun (pair :
          Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .ideal_eta_packed_secret_pair) =>
      ideal_mode2_s2_active_source pair.`2).

op ideal_final_s2_output_odd_dft256_distribution
    (pre_bp avec : BArray8192.t) (row k : int) : complex distr =
  dmap
    Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_flat_source_distribution
    (fun xs =>
      Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k).

lemma ideal_mode2_s2_active_source_nth sampled_s2 i :
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  nth 0 (ideal_mode2_s2_active_source sampled_s2) i =
  W32.to_sint (BArray8192.get32 sampled_s2 i).
proof.
move=> hi.
rewrite /ideal_mode2_s2_active_source.
rewrite (nth_map 0 0
  (fun j => W32.to_sint (BArray8192.get32 sampled_s2 j))
  i (iota_ 0 KeygenM23MatrixSpec.mode2_b_words_i)).
+ by rewrite size_iota.
by rewrite nth_iota.
qed.

lemma ideal_mode2_s2_active_source_pack_eta_vector8192 polynomials :
  size polynomials = KeygenSamplerCallersSpec.mode2_k_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    polynomials =>
  ideal_mode2_s2_active_source
    (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .pack_eta_vector8192 polynomials) =
  flatten polynomials.
proof.
move=> hsize hall.
have hflat_size :=
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_vector_flatten_size
      polynomials
      KeygenSamplerCallersSpec.mode2_k_i
      hsize hall.
have hflat_support :=
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_vector_flatten_support polynomials hall.
have hcapacity :
    size (flatten polynomials) <=
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .eta_vector_word_capacity_i.
+ rewrite hflat_size
          /KeygenEtaSamplerSpec.eta_poly_words_i
          /KeygenSamplerCallersSpec.mode2_k_i
          /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
             .eta_vector_word_capacity_i
          /BArray8192.size.
   trivial.
apply (eq_from_nth 0).
+ rewrite /ideal_mode2_s2_active_source size_map size_iota hflat_size.
   trivial.
move=> i hi.
have hi_src : 0 <= i < KeygenM23MatrixSpec.mode2_b_words_i.
+ move: hi.
   rewrite /ideal_mode2_s2_active_source size_map size_iota.
   trivial.
have hi_flat : 0 <= i < size (flatten polynomials).
+ move: hi.
   rewrite /ideal_mode2_s2_active_source size_map size_iota hflat_size.
   trivial.
rewrite ideal_mode2_s2_active_source_nth 1:hi_src.
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

lemma ideal_mode2_s2_source_distributionE :
  ideal_mode2_s2_source_distribution =
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_flat_source_distribution.
proof.
rewrite /ideal_mode2_s2_source_distribution.
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
           ideal_mode2_s2_active_source pair.`2) \o
       Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
         .pack_eta_secret_pair) =
    dmap
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_secret_pair_distribution
      (fun (pair :
            Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
              .ideal_eta_secret_pair) =>
        flatten (pair.`2)).
+ apply eq_dmap_in => pair hpair.
   rewrite /(\o) /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
             .pack_eta_secret_pair /=.
   rewrite
     Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
       .ideal_eta_secret_pair_support in hpair.
   move: hpair => [_ [_ [hsize hall]]].
   exact
     (ideal_mode2_s2_active_source_pack_eta_vector8192
       pair.`2 hsize hall).
have -> :
    (fun (pair :
          Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .ideal_eta_secret_pair) =>
      flatten (pair.`2)) =
    flatten \o
    (fun (pair :
          Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
            .ideal_eta_secret_pair) =>
      pair.`2).
+ apply fun_ext => pair.
   rewrite /(\o).
   trivial.
rewrite -dmap_comp.
rewrite /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
          .ideal_eta_secret_pair_distribution.
rewrite
  (dprod_marginalR
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_s1_distribution
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_s2_distribution
    idfun).
have hs1ll :
    is_lossless
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_s1_distribution.
+ exact
     Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
       .ideal_eta_s1_lossless.
rewrite /is_lossless in hs1ll.
rewrite hs1ll dmap_id dscalar1.
rewrite /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_flat_source_distribution.
trivial.
qed.

lemma ideal_mode2_pure_final_s2_slot_wordE
    pre_bp sampled_s2 avec s1 row j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  BArray1024.get32
    (KeygenM23SingularFFTSpec.mode2_slice
      s1
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .pure_final_s2 pre_bp sampled_s2 avec)
      (KeygenM23SingularFFTSpec.mode2_s1_count_i + row))
    j =
  BArray8192.get32
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_s2 pre_bp sampled_s2 avec)
    (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
      .ideal_final_s2_row_index row j).
proof.
move=> hrow hj.
rewrite
  (TargetKeygenM23SingularFFTInputBounds.mode2_s2_slice_get32
    s1
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_s2 pre_bp sampled_s2 avec)
    (KeygenM23SingularFFTSpec.mode2_s1_count_i + row)
    j).
move: hrow.
rewrite /KeygenM23SingularFFTSpec.mode2_s1_count_i
        /KeygenM23SingularFFTSpec.mode2_s2_count_i
        /KeygenM23SingularFFTSpec.mode2_slice_count_i.
smt().
exact hj.
congr.
rewrite /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
          .ideal_final_s2_row_index.
ring.
qed.

lemma ideal_mode2_pure_final_s2_slot_output_coordE
    pre_bp sampled_s2 avec s1 row j :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  Mode2KeygenCoreEquation.centered_s2_active sampled_s2 =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  W32.to_sint
    (BArray1024.get32
      (KeygenM23SingularFFTSpec.mode2_slice
        s1
        (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
          .pure_final_s2 pre_bp sampled_s2 avec)
        (KeygenM23SingularFFTSpec.mode2_s1_count_i + row))
      j) =
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_output_coord
      pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_row_index row j)
      (W32.to_sint
        (BArray8192.get32 sampled_s2
          (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
            .ideal_final_s2_row_index row j))).
proof.
move=> hctx hs2 hrow hj.
rewrite (ideal_mode2_pure_final_s2_slot_wordE
  pre_bp sampled_s2 avec s1 row j hrow hj).
rewrite /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_output_coord.
exact
  (Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .pure_final_s2_active_math_output
      pre_bp sampled_s2 avec
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_row_index row j)
      hctx hs2
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_row_index_range row j hrow hj)).
qed.

lemma ideal_mode2_pure_final_s2_slot_fftE
    pre_bp sampled_s2 avec s1 row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  Mode2KeygenCoreEquation.centered_s2_active sampled_s2 =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  KeygenM23SingularFFTAccumulatorBridge.mode2_ideal_fft_at
    s1
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .pure_final_s2 pre_bp sampled_s2 avec)
    (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k =
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_output_odd_dft256
      pre_bp avec row (ideal_mode2_s2_active_source sampled_s2) k.
proof.
move=> hctx hs2 hrow.
rewrite /KeygenM23SingularFFTAccumulatorBridge.mode2_ideal_fft_at.
rewrite /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
          .ideal_final_s2_output_odd_dft256.
rewrite /odd_dft256 /csum256.
congr.
apply eq_in_map => j hj.
rewrite mem_iota in hj.
have hj256 : 0 <= j < 256 by smt().
simplify.
rewrite /KeygenM23SingularFFTInitBridge.fft_coefficient_vector.
rewrite
  (ideal_mode2_pure_final_s2_slot_output_coordE
    pre_bp sampled_s2 avec s1 row j
    hctx hs2 hrow hj256).
rewrite /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
          .ideal_final_s2_output_slice.
rewrite
  (ideal_mode2_s2_active_source_nth sampled_s2
    (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
      .ideal_final_s2_row_index row j)).
exact
  (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_row_index_range row j hrow hj256).
rewrite /cof_int /cof_real /=.
trivial.
qed.

lemma ideal_final_s2_full_row_source_projection_nth row xs j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  size xs = KeygenM23MatrixSpec.mode2_b_words_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  nth 0
    (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_full_row_source_projection row xs) j =
  nth 0 xs
    (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
      .ideal_final_s2_row_index row j).
proof.
move=> hrow hsize hj.
have hoff :
    0 <=
      Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_row_offset row.
+ rewrite /Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
          .ideal_final_s2_row_offset
          /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
            .ideal_final_s2_row_index.
   smt().
have hbound :
    Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
      .ideal_final_s2_row_offset row +
    KeygenM23SingularSpec.singular_words_i <= size xs.
+ move: hrow hsize.
   rewrite
     /Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
       .ideal_final_s2_row_offset
     /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
       .ideal_final_s2_row_index
     /KeygenM23SingularFFTSpec.mode2_s2_count_i
     /KeygenM23SingularSpec.singular_words_i
     /KeygenM23MatrixSpec.mode2_b_words_i
     /KeygenM23MatrixSpec.mode2_rows_i
     /KeygenM23MatrixSpec.poly_words_i.
   smt().
rewrite
  /Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
    .ideal_final_s2_full_row_source_projection.
rewrite nth_take 1:/#.
+ smt().
rewrite nth_drop 1:hoff.
+ smt().
rewrite /Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
          .ideal_final_s2_row_offset
        /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
          .ideal_final_s2_row_index
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_index.
ring.
qed.

lemma ideal_final_s2_residual_odd_dft256_row_projectionE
    pre_bp avec row xs k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  size xs = KeygenM23MatrixSpec.mode2_b_words_i =>
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_residual_odd_dft256 pre_bp avec row xs k =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_odd_dft256_sample
      pre_bp avec row
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_source_projection row xs)
      k.
proof.
move=> hrow hsize.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_residual_odd_dft256
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_odd_dft256_sample
  /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_residual_slice
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_slice
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_value
  /odd_dft256 /csum256.
congr.
apply eq_in_map => j hj.
rewrite mem_iota in hj.
have hj256 : 0 <= j < KeygenM23SingularSpec.singular_words_i by
  move: hj; rewrite /KeygenM23SingularSpec.singular_words_i; smt().
simplify.
rewrite
  (ideal_final_s2_full_row_source_projection_nth row xs j
    hrow hsize hj256).
rewrite /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
          .ideal_final_s2_row_index
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_index.
trivial.
qed.

lemma ideal_final_s2_output_real_bad_mu_le_markov4
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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom
      pre_bp avec row k ^ 4).
proof.
move=> hctx hrow hk.
have -> :
    mu
      (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_flat_source_distribution)
      (fun xs =>
        KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
          `|creal
              (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
                .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)| +
            KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps) =
    mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_source_distribution row)
      (fun ys =>
        KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
          `|creal
              (cadd
                (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
                  .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
                (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
                  .ideal_final_s2_row_residual_odd_dft256_sample
                    pre_bp avec row ys k))| +
            KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps).
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
           xs KeygenSamplerCallersSpec.mode2_k_i
           hs2size hs2all.
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
have htail :=
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_bias_residual_real_bad_mu_le_markov4
      pre_bp avec row k hctx hrow hk).
rewrite hdist dmapE in htail.
exact htail.
qed.

lemma ideal_final_s2_output_imag_bad_mu_le_markov4
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
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom
      pre_bp avec row k ^ 4).
proof.
move=> hctx hrow hk.
have -> :
    mu
      (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_flat_source_distribution)
      (fun xs =>
        KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
          `|cimag
              (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
                .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)| +
            KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps) =
    mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_source_distribution row)
      (fun ys =>
        KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
          `|cimag
              (cadd
                (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
                  .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
                (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
                  .ideal_final_s2_row_residual_odd_dft256_sample
                    pre_bp avec row ys k))| +
            KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps).
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
           xs KeygenSamplerCallersSpec.mode2_k_i
           hs2size hs2all.
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
have htail :=
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_bias_residual_imag_bad_mu_le_markov4
      pre_bp avec row k hctx hrow hk).
rewrite hdist dmapE in htail.
exact htail.
qed.

lemma ideal_mode2_accumulator_s2_slot_real_bad_mu_le_markov4
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      KeygenM23SingularFFTAccumulatorProbability
        .mode2_accumulator_coordinate_real_bad_at
          sample
          (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom
      pre_bp avec row k ^ 4).
proof.
move=> hctx hrow hk.
rewrite
  /Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_distribution.
rewrite dmapE.
have -> :
    mu
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_packed_secret_pair_distribution
      ((fun sample =>
          KeygenM23SingularFFTAccumulatorProbability
            .mode2_accumulator_coordinate_real_bad_at
              sample
              (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) \o
       Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
         .ideal_mode2_accumulator_sample pre_bp avec) =
    mu
      ideal_mode2_s2_source_distribution
      (fun xs =>
        KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
          `|creal
              (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
                .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)| +
            KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps).
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
             .pack_eta_secret_pair /=
           /KeygenM23SingularFFTAccumulatorProbability
             .mode2_accumulator_coordinate_real_bad_at.
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
exact
  (ideal_final_s2_output_real_bad_mu_le_markov4
      pre_bp avec row k hctx hrow hk).
qed.

lemma ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_markov4
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      KeygenM23SingularFFTAccumulatorProbability
        .mode2_accumulator_coordinate_imag_bad_at
          sample
          (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) <=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k 256 /
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom
      pre_bp avec row k ^ 4).
proof.
move=> hctx hrow hk.
rewrite
  /Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_accumulator_distribution.
rewrite dmapE.
have -> :
    mu
      Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
        .ideal_eta_packed_secret_pair_distribution
      ((fun sample =>
          KeygenM23SingularFFTAccumulatorProbability
            .mode2_accumulator_coordinate_imag_bad_at
              sample
              (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) \o
       Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
         .ideal_mode2_accumulator_sample pre_bp avec) =
    mu
      ideal_mode2_s2_source_distribution
      (fun xs =>
        KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap <
          `|cimag
              (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
                .ideal_final_s2_output_odd_dft256 pre_bp avec row xs k)| +
            KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps).
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
             .pack_eta_secret_pair /=
           /KeygenM23SingularFFTAccumulatorProbability
             .mode2_accumulator_coordinate_imag_bad_at.
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
exact
  (ideal_final_s2_output_imag_bad_mu_le_markov4
      pre_bp avec row k hctx hrow hk).
qed.

end Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotTailPostFreeze.
