require import AllCore IntDiv List StdRing StdOrder.
from Jasmin require import JModel_x86.
require import ApiTarget HyperballWitnessSpec HyperballReferenceConstants
  HyperballFixedPointSpec HyperballFixedPointCorrectness HyperballScaleSpec
  HyperballScaleCorrectness HyperballNormSpec HyperballNormCorrectness
  HyperballWitnessArithmetic HyperballWitnessNewton.
import HyperballScaleSpec HyperballScaleCorrectness HyperballNormCorrectness.

module HWN = ApiTarget.M(ApiTarget.Syscall).

op hwn_coefficients (values : BArray8192.t) (count : int) (coefficient : W32.t) : bool =
  forall i, 0 <= i < count => BArray8192.get32 values i = coefficient.

lemma hwn_prefix_norm_constant (values : BArray8192.t) (coefficient : W32.t) count :
  0 <= count => hwn_coefficients values count coefficient =>
  hyperball_prefix_sqnorm values count =
    count * (W32.to_sint coefficient * W32.to_sint coefficient).
proof.
  elim: count => [|count hc ih] hcoeff.
  + by rewrite hyperball_prefix_sqnorm0.
  have hprev : hwn_coefficients values count coefficient.
  + move=> i hi; apply hcoeff; smt().
  have hlast := hcoeff count _; first smt().
  rewrite (hyperball_prefix_sqnormS values count hc) (ih hprev)
    /hyperball_coeff_square hlast.
  ring.
qed.

lemma hwn_norm_constant (a b : BArray8192.t) (coefficient : W32.t) na nb :
  0 <= na => 0 <= nb =>
  hwn_coefficients a na coefficient => hwn_coefficients b nb coefficient =>
  hyperball_sqnorm a na b nb = (na+nb) *
    (W32.to_sint coefficient * W32.to_sint coefficient).
proof.
  move=> ha hb hca hcb; rewrite /hyperball_sqnorm
    (hwn_prefix_norm_constant a coefficient na ha hca)
    (hwn_prefix_norm_constant b coefficient nb hb hcb).
  ring.
qed.

lemma hwn_zero_sign i : 0 <= i < 4096 => hb_sign_bit hbw_signs i = W8.zero.
proof.
  move=> hi; have hj : 0 <= i %/ 8 < 512 by smt(divz_cmp).
  by rewrite /hb_sign_bit /hbw_signs (BArray512.initiE _ _ hj) /=.
qed.

lemma hwn_scaled_coeff_constant samples sample scale coefficient i :
  0 <= i < 4096 => BArray32768.get64 samples i = sample =>
  hb_mul_rnd13 sample scale W64.zero = coefficient =>
  hb_scaled_coeff samples hbw_signs (hb_pack scale) i = coefficient.
proof.
  move=> hi hs hc.
  have hz : zeroextu64 W8.zero = W64.zero by
    apply W64.to_uint_eq; rewrite W8u8.to_uint_zeroextu64 W8.to_uint0 W64.to_uint0.
  by rewrite /hb_scaled_coeff hs (hwn_zero_sign i hi) /hb_scale_sample hb_load_pack hz.
qed.

lemma hwn_scale_layout before1 before2 samples sample scale coefficient l count :
  hb_scale_bounds l count =>
  (forall i, 0 <= i < count => BArray32768.get64 samples i = sample) =>
  hb_mul_rnd13 sample scale W64.zero = coefficient =>
  let result = hb_scale_result before1 before2 samples hbw_signs (hb_pack scale) l count in
  hwn_coefficients result.`1 l coefficient /\
  hwn_coefficients result.`2 (count-l) coefficient /\
  hb_output_frame before1 result.`1 l /\ hb_output_frame before2 result.`2 (count-l).
proof.
  move=> hb hs hc /=.
  have hword : forall i, 0 <= i < count =>
      hb_scaled_coeff samples hbw_signs (hb_pack scale) i = coefficient.
  + move=> i hi; apply (hwn_scaled_coeff_constant samples sample scale coefficient i) => //.
    - move: hb; rewrite /hb_scale_bounds; smt().
    exact (hs i hi).
  have [hleft [hright [hfleft hfright]]] :=
    hb_scale_result_layout before1 before2 samples hbw_signs (hb_pack scale) l count hb.
  do split.
  + move=> i hi; have hidx : 0 <= i < 2048 by move: hb; rewrite /hb_scale_bounds; smt().
    rewrite (hleft i hidx) iftrue 1:/#; apply hword; move: hb; rewrite /hb_scale_bounds; smt().
  + move=> i hi; have hidx : 0 <= i < 2048 by move: hb; rewrite /hb_scale_bounds; smt().
    rewrite (hright i hidx) iftrue 1:/#; apply hword; move: hb; rewrite /hb_scale_bounds; smt().
  + exact hfleft.
  exact hfright.
qed.

lemma hwn_scale_norm before1 before2 samples sample scale coefficient l count :
  hb_scale_bounds l count =>
  (forall i, 0 <= i < count => BArray32768.get64 samples i = sample) =>
  hb_mul_rnd13 sample scale W64.zero = coefficient =>
  hb_scale_norm before1 before2 samples hbw_signs (hb_pack scale) l count =
    count * (W32.to_sint coefficient * W32.to_sint coefficient).
proof.
  move=> hb hs hc.
  have [hl [hr hf]] := hwn_scale_layout before1 before2 samples sample scale coefficient l count hb hs hc.
  have hl0 : 0 <= l by move: hb; rewrite /hb_scale_bounds; smt().
  have hr0 : 0 <= count-l by move: hb; rewrite /hb_scale_bounds; smt().
  rewrite /hb_scale_norm.
  have h := hwn_norm_constant _ _ coefficient l (count-l) hl0 hr0 hl hr.
  rewrite /= h; ring.
qed.

lemma hbw_samples_active mode i :
  0 <= i < hbw_count mode => hbw_count mode <= 4096 =>
  BArray32768.get64 (hbw_samples mode) i = hbw_sample mode.
proof.
  move=> hi hc; apply W8u8.wordP => byte hb.
  rewrite BArray32768.get64d_byte 1:hb.
  have hj : 0 <= 8*i+byte < 32768 by smt().
  rewrite /hbw_samples (BArray32768.initiE _ _ hj) /= iftrue 1:/#.
  have hm : (8*i+byte) %% 8 = byte by rewrite (mulzC 8 i) modzMDl modz_small; smt().
  by rewrite hm.
qed.

lemma hbw_repeated_scale_norm mode before1 before2 samples :
  hbw_mode mode =>
  (forall i, 0 <= i < hbw_count mode =>
    BArray32768.get64 samples i = hbw_sample mode) =>
  hb_mul_rnd13 (hbw_sample mode) (hbw_scale mode) W64.zero =
    W32.of_int (hbw_coefficient mode) =>
  hb_scale_norm before1 before2 samples hbw_signs (hb_pack (hbw_scale mode))
    (hbw_left mode) (hbw_count mode) = hbw_total mode.
proof.
  move=> hm hs hc.
  have hb := hbw_storage_bounds mode hm.
  have [ht _] := hbw_fixture_norm mode hm.
  have h := hwn_scale_norm before1 before2 samples (hbw_sample mode) (hbw_scale mode)
    (W32.of_int (hbw_coefficient mode)) (hbw_left mode) (hbw_count mode) hb hs hc.
  by move: h; rewrite (hbw_coefficient_sint mode hm) ht.
qed.

(* The integer total is retained next to its 64-bit reduction. Acceptance
   describes the actual word comparison and does not assert a radius bound. *)
op hbw_norm_result mode (before1 before2 : BArray8192.t)
    (result : BArray8192.t * BArray8192.t * W64.t) : bool =
  let norm = hyperball_sqnorm result.`1 (hbw_left mode)
    result.`2 (hbw_count mode-hbw_left mode) in
  result.`3 = W64.one /\
  hwn_coefficients result.`1 (hbw_left mode) (W32.of_int (hbw_coefficient mode)) /\
  hwn_coefficients result.`2 (hbw_count mode-hbw_left mode) (W32.of_int (hbw_coefficient mode)) /\
  norm = hbw_total mode /\ norm %% W64.modulus = hbw_residue mode /\
  W64.to_uint (W64.of_int norm) = hbw_residue mode /\
  W64.to_uint (hb_ref_bound mode) < W64.modulus /\ W64.modulus <= norm /\
  hb_output_frame before1 result.`1 (hbw_left mode) /\
  hb_output_frame before2 result.`2 (hbw_count mode-hbw_left mode).

lemma hbw_scale_check_result_good mode before1 before2 samples :
  hbw_mode mode =>
  (forall i, 0 <= i < hbw_count mode =>
    BArray32768.get64 samples i = hbw_sample mode) =>
  hb_mul_rnd13 (hbw_sample mode) (hbw_scale mode) W64.zero =
    W32.of_int (hbw_coefficient mode) =>
  hbw_norm_result mode before1 before2
    (hb_scale_check_result before1 before2 samples hbw_signs (hb_pack (hbw_scale mode))
      (hbw_left mode) (hbw_count mode) (hb_ref_bound mode)).
proof.
  move=> hm hs hc.
  have hb := hbw_storage_bounds mode hm.
  have hl := hwn_scale_layout before1 before2 samples (hbw_sample mode) (hbw_scale mode)
    (W32.of_int (hbw_coefficient mode)) (hbw_left mode) (hbw_count mode) hb hs hc.
  have hn := hbw_repeated_scale_norm mode before1 before2 samples hm hs hc.
  have [ht [hr [hz [haccept [hbound hlarge]]]]] := hbw_fixture_norm mode hm.
  have he : (hbw_residue mode <= W64.to_uint (hb_ref_bound mode)) = true by smt().
  rewrite /hb_scale_check_result hn hr he /= /hbw_norm_result /=.
  rewrite /hb_scale_norm /= in hn.
  rewrite hn hr W64.of_uintK hr.
  have [hc1 [hc2 [hf1 hf2]]] := hl.
  rewrite /b2i /=; do split.
  + exact hc1.
  + exact hc2.
  + exact hbound.
  + exact hlarge.
  + exact hf1.
  exact hf2.
qed.

lemma hbw_scale_and_check_from_coefficient_hoare mode
    (before1 before2 : BArray8192.t) (samples : BArray32768.t) :
  hbw_mode mode =>
  (forall i, 0 <= i < hbw_count mode =>
    BArray32768.get64 samples i = hbw_sample mode) =>
  hb_mul_rnd13 (hbw_sample mode) (hbw_scale mode) W64.zero =
    W32.of_int (hbw_coefficient mode) =>
  hoare [HWN._sf_scale_and_check :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples /\ signsp=hbw_signs /\
    scalep=hb_pack (hbw_scale mode) /\ lcount=W64.of_int (hbw_left mode) /\
    total=W64.of_int (hbw_count mode) /\ bound=hb_ref_bound mode ==>
    hbw_norm_result mode before1 before2 res].
proof.
  move=> hm hs hc.
  have hb := hbw_storage_bounds mode hm.
  have hp := hbw_scale_check_result_good mode before1 before2 samples hm hs hc.
  conseq (hb_scale_and_check_correct before1 before2 samples hbw_signs
    (hb_pack (hbw_scale mode)) (hbw_left mode) (hbw_count mode) (hb_ref_bound mode)) => />.
qed.

lemma hbw_scale_and_check_from_coefficient_total mode
    (before1 before2 : BArray8192.t) (samples : BArray32768.t) :
  hbw_mode mode =>
  (forall i, 0 <= i < hbw_count mode =>
    BArray32768.get64 samples i = hbw_sample mode) =>
  hb_mul_rnd13 (hbw_sample mode) (hbw_scale mode) W64.zero =
    W32.of_int (hbw_coefficient mode) =>
  phoare [HWN._sf_scale_and_check :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples /\ signsp=hbw_signs /\
    scalep=hb_pack (hbw_scale mode) /\ lcount=W64.of_int (hbw_left mode) /\
    total=W64.of_int (hbw_count mode) /\ bound=hb_ref_bound mode ==>
    hbw_norm_result mode before1 before2 res] = 1%r.
proof.
  move=> hm hs hc.
  by conseq hb_scale_and_check_ll
    (hbw_scale_and_check_from_coefficient_hoare mode before1 before2 samples hm hs hc).
qed.

lemma hbw_actual_norm_total mode (a b : BArray8192.t) :
  hbw_mode mode =>
  hwn_coefficients a (hbw_left mode) (W32.of_int (hbw_coefficient mode)) =>
  hwn_coefficients b (hbw_count mode-hbw_left mode) (W32.of_int (hbw_coefficient mode)) =>
  phoare [HWN._polyfixveclk_sqnorm2_2048 :
    ap=a /\ acount=W64.of_int (hbw_left mode) /\
    bp=b /\ bcount=W64.of_int (hbw_count mode-hbw_left mode) ==>
    res=W64.of_int (hbw_residue mode) /\ W64.to_uint res=hbw_residue mode] = 1%r.
proof.
  move=> hm ha hb.
  have hd := hbw_storage_bounds mode hm.
  have [ht [hr [hz [hle [hbound hlarge]]]]] := hbw_fixture_norm mode hm.
  have hl0 : 0 <= hbw_left mode by move: hd; rewrite /hb_scale_bounds; smt().
  have hr0 : 0 <= hbw_count mode-hbw_left mode by move: hd; rewrite /hb_scale_bounds; smt().
  have hn := hwn_norm_constant a b (W32.of_int (hbw_coefficient mode))
    (hbw_left mode) (hbw_count mode-hbw_left mode) hl0 hr0 ha hb.
  have hnorm : hyperball_sqnorm a (hbw_left mode) b
      (hbw_count mode-hbw_left mode) = hbw_total mode.
  + rewrite hn (hbw_coefficient_sint mode hm).
    have he : hbw_left mode+(hbw_count mode-hbw_left mode) = hbw_count mode by ring.
    by rewrite he ht.
  have hw : W64.of_int (hbw_total mode) = W64.of_int (hbw_residue mode) by
    rewrite -(W64.of_int_mod (hbw_total mode)) hr.
  have hu : W64.to_uint (W64.of_int (hbw_residue mode)) = hbw_residue mode by
    rewrite W64.of_uintK modz_small; smt().
  conseq (polyfixveclk_sqnorm2_total_correct a (hbw_left mode) b
    (hbw_count mode-hbw_left mode)) => />.
  smt().
  move=> &hr -> _ -> _.
  by rewrite hnorm hw hu.
qed.

lemma hbw_repeated_scale_norm_exact mode before1 before2 samples :
  hbw_mode mode =>
  (forall i, 0 <= i < hbw_count mode =>
    BArray32768.get64 samples i = hbw_sample mode) =>
  hb_scale_norm before1 before2 samples hbw_signs (hb_pack (hbw_scale mode))
    (hbw_left mode) (hbw_count mode) = hbw_total mode.
proof.
  move=> hm hs.
  exact (hbw_repeated_scale_norm mode before1 before2 samples hm hs
    (hbw_coefficient_exact mode hm)).
qed.

(* These final contracts discharge the scalar coefficient premise with the
   checked word evaluation. Samples outside the active prefix are arbitrary.
   They are concrete array/call witnesses, without a SHAKE-seed assertion. *)
lemma hbw_scale_and_check_repeated_total mode
    (before1 before2 : BArray8192.t) (samples : BArray32768.t) :
  hbw_mode mode =>
  (forall i, 0 <= i < hbw_count mode =>
    BArray32768.get64 samples i = hbw_sample mode) =>
  phoare [HWN._sf_scale_and_check :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples /\ signsp=hbw_signs /\
    scalep=hb_pack (hbw_scale mode) /\ lcount=W64.of_int (hbw_left mode) /\
    total=W64.of_int (hbw_count mode) /\ bound=hb_ref_bound mode ==>
    hbw_norm_result mode before1 before2 res] = 1%r.
proof.
  move=> hm hs.
  exact (hbw_scale_and_check_from_coefficient_total mode before1 before2 samples hm hs
    (hbw_coefficient_exact mode hm)).
qed.

lemma hbw_scale_and_check_fixture_total mode : hbw_mode mode =>
  phoare [HWN._sf_scale_and_check :
    y1p=hbw_zero_output /\ y2p=hbw_zero_output /\ samplesp=hbw_samples mode /\
    signsp=hbw_signs /\ scalep=hb_pack (hbw_scale mode) /\
    lcount=W64.of_int (hbw_left mode) /\ total=W64.of_int (hbw_count mode) /\
    bound=hb_ref_bound mode ==>
    hbw_norm_result mode hbw_zero_output hbw_zero_output res] = 1%r.
proof.
  move=> hm.
  have hd := hbw_storage_bounds mode hm.
  have hc : hbw_count mode <= 4096 by move: hd; rewrite /hb_scale_bounds; smt().
  have hs : forall i, 0 <= i < hbw_count mode =>
      BArray32768.get64 (hbw_samples mode) i = hbw_sample mode.
  + move=> i hi; exact (hbw_samples_active mode i hi hc).
  exact (hbw_scale_and_check_repeated_total mode hbw_zero_output hbw_zero_output
    (hbw_samples mode) hm hs).
qed.
