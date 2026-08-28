require import AllCore IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety
  KeygenM23SingularFFTStageErrorBridge
  KeygenM23MatrixSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety.

theory Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze.

(* This file is an ideal fixed-context FFT artifact.  The [pre_bp] and [avec]
   arrays are parameters, and only the finalized-s2 bias decomposition is
   analyzed.  It does not model the actual/fixed-point FFT, random contexts,
   residual concentration, prefix-energy safety, cross-term control, or any
   SHAKE/actual sampler law. *)

op ideal_final_s2_row_index (row j : int) : int =
  row * KeygenM23SingularSpec.singular_words_i + j.

op ideal_final_s2_bias_row
    (pre_bp avec : BArray8192.t) (row : int) : int -> real =
  fun j =>
    Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
      .ideal_final_s2_bias_at
        pre_bp avec (ideal_final_s2_row_index row j).

op ideal_final_s2_bias_slice
    (pre_bp avec : BArray8192.t) (row : int) : int -> complex =
  fun j => cof_real (ideal_final_s2_bias_row pre_bp avec row j).

op ideal_final_s2_residual_slice
    (pre_bp avec : BArray8192.t) (row : int) (xs : int list) :
    int -> complex =
  fun j =>
    cof_real
      (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_residual_coord
          pre_bp avec
          (ideal_final_s2_row_index row j)
          (nth 0 xs (ideal_final_s2_row_index row j))).

op ideal_final_s2_output_slice
    (pre_bp avec : BArray8192.t) (row : int) (xs : int list) :
    int -> complex =
  fun j =>
    cof_real
      ((Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
         .ideal_final_s2_output_coord
           pre_bp avec
           (ideal_final_s2_row_index row j)
           (nth 0 xs (ideal_final_s2_row_index row j)))%r).

op ideal_final_s2_bias_odd_dft256
    (pre_bp avec : BArray8192.t) (row k : int) : complex =
  odd_dft256 (ideal_final_s2_bias_slice pre_bp avec row) k.

op ideal_final_s2_residual_odd_dft256
    (pre_bp avec : BArray8192.t) (row : int) (xs : int list) (k : int) :
    complex =
  odd_dft256 (ideal_final_s2_residual_slice pre_bp avec row xs) k.

op ideal_final_s2_output_odd_dft256
    (pre_bp avec : BArray8192.t) (row : int) (xs : int list) (k : int) :
    complex =
  odd_dft256 (ideal_final_s2_output_slice pre_bp avec row xs) k.

op bias_vector (b : int -> real) : cvector =
  fun j => cof_real (b j).

op bias_fft (b : int -> real) (k : int) : complex =
  odd_dft256 (bias_vector b) k.

op bias_l1 (b : int -> real) : real =
  BRA.bigi predT (fun j => `|b j|) 0 256.

op bias_l2_sq (b : int -> real) : real =
  BRA.bigi predT (fun j => (b j) ^ 2) 0 256.

lemma ideal_final_s2_row_index_range row j :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  0 <= ideal_final_s2_row_index row j <
    KeygenM23MatrixSpec.mode2_b_words_i.
proof.
rewrite /ideal_final_s2_row_index
        /KeygenM23SingularFFTSpec.mode2_s2_count_i
        /KeygenM23SingularSpec.singular_words_i
        /KeygenM23MatrixSpec.mode2_b_words_i
        /KeygenM23MatrixSpec.mode2_rows_i
        /KeygenM23MatrixSpec.poly_words_i.
smt().
qed.

lemma ideal_final_s2_row_slotE row :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  KeygenM23SingularFFTSpec.mode2_s1_count_i + row = 3 + row.
proof.
rewrite /KeygenM23SingularFFTSpec.mode2_s1_count_i.
trivial.
qed.

lemma ideal_final_s2_row_slot_range row :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= KeygenM23SingularFFTSpec.mode2_s1_count_i + row <
    KeygenM23SingularFFTSpec.mode2_slice_count_i.
proof.
rewrite /KeygenM23SingularFFTSpec.mode2_s1_count_i
        /KeygenM23SingularFFTSpec.mode2_s2_count_i
        /KeygenM23SingularFFTSpec.mode2_slice_count_i.
smt().
qed.

lemma one_third_ge0 :
  0%r <= 1%r / 3%r.
proof.
apply divr_ge0; smt().
qed.

lemma one_ninthE :
  1%r / 9%r = (1%r / 3%r) ^ 2.
proof.
field; trivial.
qed.

lemma bias_square_le_one_ninth x :
  `|x| <= 1%r / 3%r =>
  x ^ 2 <= 1%r / 9%r.
proof.
move=> hx.
have hsqeq : x ^ 2 = `|x| ^ 2.
+ case (0%r <= x) => hx0.
  + rewrite (ger0_norm x hx0).
    trivial.
  have hxle : x <= 0%r by smt().
  rewrite (ler0_norm x hxle).
  ring.
rewrite hsqeq.
rewrite one_ninthE.
apply ler_pexp.
+ smt().
have hx0 : 0%r <= `|x|.
+ apply normr_ge0.
smt().
qed.

lemma square_le_of_abs_bound (x bound : real) :
  0%r <= bound =>
  `|x| <= bound =>
  x ^ 2 <= bound ^ 2.
proof.
move=> hbound hx.
have hsqeq : x ^ 2 = `|x| ^ 2.
+ case (0%r <= x) => hx0.
  + rewrite (ger0_norm x hx0).
    trivial.
  have hxle : x <= 0%r by smt().
  rewrite (ler0_norm x hxle).
  ring.
rewrite hsqeq.
apply ler_pexp.
+ smt().
have hx0 : 0%r <= `|x|.
+ apply normr_ge0.
smt().
qed.

lemma bias_fft_cnorm2_constantE :
  (256%r / 3%r) ^ 2 + (256%r / 3%r) ^ 2 =
  131072%r / 9%r.
proof.
field; trivial.
qed.

lemma ideal_final_s2_bias_abs_le_one_third
    (pre_bp avec : BArray8192.t) row j :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  `|ideal_final_s2_bias_row pre_bp avec row j| <= 1%r / 3%r.
proof.
move=> hctx hrow hj.
rewrite /ideal_final_s2_bias_row.
apply
  (Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_bias_abs_bound_at
      pre_bp avec (ideal_final_s2_row_index row j)).
+ exact hctx.
exact (ideal_final_s2_row_index_range row j hrow hj).
qed.

lemma creal_csum (xs : complex list) :
  creal (csum xs) = BRA.big predT creal xs.
proof.
elim: xs => [|z zs ih].
+ rewrite /csum /= BRA.big_nil creal_zero.
   trivial.
rewrite /csum /= BRA.big_cons /= creal_add ih.
trivial.
qed.

lemma cimag_csum (xs : complex list) :
  cimag (csum xs) = BRA.big predT cimag xs.
proof.
elim: xs => [|z zs ih].
+ rewrite /csum /= BRA.big_nil cimag_zero.
   trivial.
rewrite /csum /= BRA.big_cons /= cimag_add ih.
trivial.
qed.

lemma creal_csum256 (f : int -> complex) :
  creal (csum256 f) = BRA.bigi predT (fun j => creal (f j)) 0 256.
proof.
rewrite /csum256 creal_csum BRA.big_mapT /(\o).
trivial.
qed.

lemma cimag_csum256 (f : int -> complex) :
  cimag (csum256 f) = BRA.bigi predT (fun j => cimag (f j)) 0 256.
proof.
rewrite /csum256 cimag_csum BRA.big_mapT /(\o).
trivial.
qed.

lemma csum_map_cadd (xs : int list) (f g : int -> complex) :
  csum (map (fun j => cadd (f j) (g j)) xs) =
  cadd (csum (map f xs)) (csum (map g xs)).
proof.
elim: xs => [|x xs ih].
+ by rewrite /csum /= cadd0.
rewrite /csum /=.
have ih' := ih.
rewrite /csum in ih'.
rewrite ih'.
apply complex_ext.
+ rewrite !creal_add.
   ring.
+ rewrite !cimag_add.
   ring.
qed.

lemma csum256_cadd (f g : int -> complex) :
  csum256 (fun j => cadd (f j) (g j)) =
  cadd (csum256 f) (csum256 g).
proof.
rewrite /csum256.
exact (csum_map_cadd (iota_ 0 256) f g).
qed.

lemma odd_dft256_cadd (f g : int -> complex) k :
  odd_dft256 (fun j => cadd (f j) (g j)) k =
  cadd (odd_dft256 f k) (odd_dft256 g k).
proof.
rewrite /odd_dft256.
have -> :
    (fun j =>
      cmul ((fun j => cadd (f j) (g j)) j) (cpow (odd_root k) j)) =
    (fun j =>
      cadd
        (cmul (f j) (cpow (odd_root k) j))
        (cmul (g j) (cpow (odd_root k) j))).
+ apply fun_ext => j.
   rewrite cmul_addl.
   trivial.
rewrite csum256_cadd.
trivial.
qed.

lemma odd_kernel_coordinate_bound1 k j :
  0 <= k < 256 =>
  0 <= j < 256 =>
  `|creal (cpow (odd_root k) j)| <= 1%r /\
  `|cimag (cpow (odd_root k) j)| <= 1%r.
proof.
move=> hk hj.
rewrite /odd_root ideal_root_power.
apply KeygenM23SingularFFTStageErrorBridge.ideal_root_coordinate_bound1.
smt().
qed.

lemma bias_l1_le b :
  (forall j, 0 <= j < 256 => `|b j| <= 1%r / 3%r) =>
  bias_l1 b <= 256%r / 3%r.
proof.
move=> hb.
rewrite /bias_l1.
change
  (BRA.big predT (fun j => `|b j|) (range 0 256) <=
   256%r / 3%r).
apply (ler_trans
  (BRA.big predT (fun _ : int => 1%r / 3%r) (range 0 256))).
+ apply ler_sum_seq => j hj _.
   rewrite mem_range in hj.
   exact (hb j hj).
rewrite Bigreal.sumr_const count_predT size_range /=.
trivial.
qed.

lemma bias_l2_sq_le b :
  (forall j, 0 <= j < 256 => `|b j| <= 1%r / 3%r) =>
  bias_l2_sq b <= 256%r / 9%r.
proof.
move=> hb.
rewrite /bias_l2_sq.
change
  (BRA.big predT (fun j => (b j) ^ 2) (range 0 256) <=
   256%r / 9%r).
apply (ler_trans
  (BRA.big predT (fun _ : int => 1%r / 9%r) (range 0 256))).
+ apply ler_sum_seq => j hj _.
   have hj' := hj.
   rewrite mem_range in hj'.
   have hsq := bias_square_le_one_ninth (b j) (hb j hj').
   exact hsq.
rewrite Bigreal.sumr_const count_predT size_range /=.
trivial.
qed.

lemma bias_fft_real_le_l1 b k :
  0 <= k < 256 =>
  `|creal (bias_fft b k)| <= bias_l1 b.
proof.
move=> hk.
rewrite /bias_fft /odd_dft256 creal_csum256.
have hnorm :
    `|BRA.bigi predT
        (fun j => creal (cmul (bias_vector b j)
          (cpow (odd_root k) j))) 0 256| <=
    BRA.bigi predT
      (fun j => `|creal (cmul (bias_vector b j)
        (cpow (odd_root k) j))|) 0 256.
+ change
      (`|BRA.big predT
          (fun j => creal (cmul (bias_vector b j)
            (cpow (odd_root k) j))) (range 0 256)| <=
       BRA.big predT
         (fun j => `|creal (cmul (bias_vector b j)
           (cpow (odd_root k) j))|) (range 0 256)).
    exact (big_normr predT
      (fun j => creal (cmul (bias_vector b j)
        (cpow (odd_root k) j))) (range 0 256)).
apply (ler_trans
  (BRA.bigi predT
    (fun j => `|creal (cmul (bias_vector b j)
      (cpow (odd_root k) j))|) 0 256)).
+ exact hnorm.
rewrite /bias_l1.
change
  (BRA.big predT
     (fun j => `|creal (cmul (bias_vector b j)
       (cpow (odd_root k) j))|) (range 0 256) <=
   BRA.big predT (fun j => `|b j|) (range 0 256)).
apply ler_sum_seq => j hj _.
rewrite mem_range in hj.
have [hre him] := odd_kernel_coordinate_bound1 k j hk hj.
rewrite /bias_vector /=.
rewrite creal_mul creal_of_real cimag_of_real /=.
rewrite normrM.
have hnonneg : 0%r <= `|b j| by apply normr_ge0.
have h := ler_wpmul2l `|b j| hnonneg
  `|creal (cpow (odd_root k) j)| 1%r hre.
exact h.
qed.

lemma bias_fft_imag_le_l1 b k :
  0 <= k < 256 =>
  `|cimag (bias_fft b k)| <= bias_l1 b.
proof.
move=> hk.
rewrite /bias_fft /odd_dft256 cimag_csum256.
have hnorm :
    `|BRA.bigi predT
        (fun j => cimag (cmul (bias_vector b j)
          (cpow (odd_root k) j))) 0 256| <=
    BRA.bigi predT
      (fun j => `|cimag (cmul (bias_vector b j)
        (cpow (odd_root k) j))|) 0 256.
+ change
      (`|BRA.big predT
          (fun j => cimag (cmul (bias_vector b j)
            (cpow (odd_root k) j))) (range 0 256)| <=
       BRA.big predT
         (fun j => `|cimag (cmul (bias_vector b j)
           (cpow (odd_root k) j))|) (range 0 256)).
    exact (big_normr predT
      (fun j => cimag (cmul (bias_vector b j)
        (cpow (odd_root k) j))) (range 0 256)).
apply (ler_trans
  (BRA.bigi predT
    (fun j => `|cimag (cmul (bias_vector b j)
      (cpow (odd_root k) j))|) 0 256)).
+ exact hnorm.
rewrite /bias_l1.
change
  (BRA.big predT
     (fun j => `|cimag (cmul (bias_vector b j)
       (cpow (odd_root k) j))|) (range 0 256) <=
   BRA.big predT (fun j => `|b j|) (range 0 256)).
apply ler_sum_seq => j hj _.
rewrite mem_range in hj.
have [hre him] := odd_kernel_coordinate_bound1 k j hk hj.
rewrite /bias_vector /=.
rewrite cimag_mul creal_of_real cimag_of_real /=.
rewrite normrM.
have hnonneg : 0%r <= `|b j| by apply normr_ge0.
have h := ler_wpmul2l `|b j| hnonneg
  `|cimag (cpow (odd_root k) j)| 1%r him.
exact h.
qed.

lemma ideal_final_s2_row_bias_l1_le
    (pre_bp avec : BArray8192.t) row :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  bias_l1 (ideal_final_s2_bias_row pre_bp avec row) <= 256%r / 3%r.
proof.
move=> hctx hrow.
apply bias_l1_le => j hj.
exact (ideal_final_s2_bias_abs_le_one_third pre_bp avec row j hctx hrow hj).
qed.

lemma ideal_final_s2_row_bias_l2_sq_le
    (pre_bp avec : BArray8192.t) row :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  bias_l2_sq (ideal_final_s2_bias_row pre_bp avec row) <= 256%r / 9%r.
proof.
move=> hctx hrow.
apply bias_l2_sq_le => j hj.
exact (ideal_final_s2_bias_abs_le_one_third pre_bp avec row j hctx hrow hj).
qed.

lemma ideal_final_s2_output_slice_cadd
    (pre_bp avec : BArray8192.t) (row j : int) (xs : int list) :
  ideal_final_s2_output_slice pre_bp avec row xs j =
  cadd
    (ideal_final_s2_bias_slice pre_bp avec row j)
    (ideal_final_s2_residual_slice pre_bp avec row xs j).
proof.
rewrite /ideal_final_s2_output_slice
        /ideal_final_s2_bias_slice
        /ideal_final_s2_bias_row
        /ideal_final_s2_residual_slice
        /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_output_coord
        /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_coord
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_bias_at
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_residual_at.
rewrite -cof_real_add.
congr.
ring.
qed.

lemma ideal_final_s2_output_odd_dft256_cadd
    (pre_bp avec : BArray8192.t) (row k : int) (xs : int list) :
  ideal_final_s2_output_odd_dft256 pre_bp avec row xs k =
  cadd
    (ideal_final_s2_bias_odd_dft256 pre_bp avec row k)
    (ideal_final_s2_residual_odd_dft256 pre_bp avec row xs k).
proof.
rewrite /ideal_final_s2_output_odd_dft256
        /ideal_final_s2_bias_odd_dft256
        /ideal_final_s2_residual_odd_dft256.
have -> :
    ideal_final_s2_output_slice pre_bp avec row xs =
    (fun j =>
      cadd
        (ideal_final_s2_bias_slice pre_bp avec row j)
        (ideal_final_s2_residual_slice pre_bp avec row xs j)).
+ apply fun_ext => j.
   exact (ideal_final_s2_output_slice_cadd pre_bp avec row j xs).
exact
  (odd_dft256_cadd
    (ideal_final_s2_bias_slice pre_bp avec row)
    (ideal_final_s2_residual_slice pre_bp avec row xs)
    k).
qed.

lemma ideal_final_s2_bias_fft_component_bounds
    (pre_bp avec : BArray8192.t) row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  `|creal (ideal_final_s2_bias_odd_dft256 pre_bp avec row k)| <= 256%r / 3%r /\
  `|cimag (ideal_final_s2_bias_odd_dft256 pre_bp avec row k)| <= 256%r / 3%r.
proof.
move=> hctx hrow hk.
have hl1 :=
  ideal_final_s2_row_bias_l1_le pre_bp avec row hctx hrow.
have hre :=
  bias_fft_real_le_l1 (ideal_final_s2_bias_row pre_bp avec row) k hk.
have him :=
  bias_fft_imag_le_l1 (ideal_final_s2_bias_row pre_bp avec row) k hk.
rewrite /ideal_final_s2_bias_odd_dft256 /ideal_final_s2_bias_slice
        /bias_fft /bias_vector in hre.
rewrite /ideal_final_s2_bias_odd_dft256 /ideal_final_s2_bias_slice
        /bias_fft /bias_vector in him.
split.
+ exact (ler_trans _ _ _ hre hl1).
exact (ler_trans _ _ _ him hl1).
qed.

lemma ideal_final_s2_bias_fft_cnorm2_le
    (pre_bp avec : BArray8192.t) row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  cnorm2 (ideal_final_s2_bias_odd_dft256 pre_bp avec row k) <=
    131072%r / 9%r.
proof.
move=> hctx hrow hk.
have [hre him] :=
  ideal_final_s2_bias_fft_component_bounds pre_bp avec row k hctx hrow hk.
have hbound : 0%r <= 256%r / 3%r by smt().
have hre2 := square_le_of_abs_bound
  (creal (ideal_final_s2_bias_odd_dft256 pre_bp avec row k))
  (256%r / 3%r) hbound hre.
have him2 := square_le_of_abs_bound
  (cimag (ideal_final_s2_bias_odd_dft256 pre_bp avec row k))
  (256%r / 3%r) hbound him.
rewrite RField.expr2 in hre2.
rewrite RField.expr2 in him2.
rewrite /cnorm2 -bias_fft_cnorm2_constantE.
apply ler_add.
+ exact hre2.
exact him2.
qed.

lemma ideal_final_s2_bias_fft_coordinate_headroom_ready
    (pre_bp avec : BArray8192.t) row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  `|creal (ideal_final_s2_bias_odd_dft256 pre_bp avec row k)| +
      mode2_fft_endpoint_eps <=
    accumulator_q16_coordinate_cap /\
  `|cimag (ideal_final_s2_bias_odd_dft256 pre_bp avec row k)| +
      mode2_fft_endpoint_eps <=
    accumulator_q16_coordinate_cap.
proof.
move=> hctx hrow hk.
have [hre him] :=
  ideal_final_s2_bias_fft_component_bounds pre_bp avec row k hctx hrow hk.
rewrite /mode2_fft_endpoint_eps /accumulator_q16_coordinate_cap.
smt().
qed.

end Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze.
