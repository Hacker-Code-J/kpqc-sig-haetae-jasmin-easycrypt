require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HardenedHyperballTarget CheckedScaleSpec CheckedScalarCorrectness
  CheckedVectorCorrectness CheckedNormCorrectness CheckedAcceptanceCorrectness
  HyperballFixedPointSpec HyperballFixedPointCorrectness HyperballScaleSpec
  HyperballScaleCorrectness HyperballNormSpec HyperballWitnessSpec
  HyperballWitnessArithmetic HyperballWitnessExecution HyperballReferenceConstants
  GaussianStreamCorrectness.
import SLH64 HyperballScaleSpec HyperballScaleCorrectness GaussianStreamCorrectness.

module HRR = HardenedHyperballTarget.M.
type hrr_output = BArray8192.t * BArray8192.t * W64.t.

(* Both arrays retain the legacy word coefficients. Acceptance additionally
   includes the checked conversion and integer norm-overflow masks. *)
op hrr_checked_result (before1 before2 : BArray8192.t)
    (samples : BArray32768.t) (signs : BArray512.t) (scale : BArray16.t)
    (left total : int) (bound : W64.t) : hrr_output =
  let output = hb_scale_result before1 before2 samples signs scale left total in
  let norm = hyperball_sqnorm output.`1 left output.`2 (total-left) in
  (output.`1,output.`2,
   hca_finish (hcv_mask samples scale total) (cn_overflow_mask norm)
     (W64.of_int (-b2i (W64.to_uint bound<W64.to_uint (W64.of_int norm))))).

op hrr_result (mode : int) (samples : BArray32768.t)
    (signs : BArray512.t) (squares : BArray16.t) : hrr_output =
  hrr_checked_result hbw_zero_output hbw_zero_output samples signs
    (hbwe_scale mode squares) (hbw_left mode) (hbw_count mode) (hb_ref_bound mode).

module HyperballRenyiArithmetic = {
  proc run(mode : int, samples : BArray32768.t, signs : BArray512.t,
      squares : BArray16.t) : hrr_output = {
    var half, inverse, scale : BArray16.t;
    var y1, y2 : BArray8192.t;
    var accepted : W64.t;
    half <@ HRR._fixpoint_half_round(squares);
    inverse <@ HRR._fixpoint_newton_invsqrt(hb_pack (W64.zero,W64.zero),half,
      hb_pack (hb_ref_cube mode),hb_pack (hb_ref_three mode));
    scale <@ HRR._fixpoint_mul_high(hb_pack (W64.zero,W64.zero),inverse,hb_ref_scale mode);
    (y1,y2,accepted) <@ HRR._hb_checked_scale_and_check_values
      (hbw_zero_output,hbw_zero_output,samples,signs,scale,
       W64.of_int (hbw_left mode),W64.of_int (hbw_count mode),hb_ref_bound mode);
    return (y1,y2,accepted);
  }
}.

lemma hrr_pointer_legacy :
  equiv [HRR._hb_checked_mul_rnd13 ~ HB._fixpoint_mul_rnd13 :
    ={x,yp,sign} ==> res{1}.`1=res{2}].
proof.
  proc.
  ecall{1} (hcs_regs_total x{1} y0{1} y1{1} s{1}).
  ecall{2} (hb_mul_rnd13_regs_total x{2} y0{2} y1{2} s{2}).
  wp; skip; auto => />.
  by move=> &2; rewrite /protect_ptr /hcs_scalar /= hcs_coefficient_legacy.
qed.

lemma hrr_bit_legacy :
  equiv [HRR.__bit_at_u8 ~ HS.__bit_at_u8 : ={x,shift} ==> ={res}].
proof. proc; sim. qed.

lemma hrr_vector_legacy :
  equiv [HRR._hb_checked_scale_samples ~ HS._polyfixveclk_scale_samples :
    ={y1p,y2p,samplesp,signsp,scalep,counts} ==>
    (res{1}.`1,res{1}.`2)=res{2}].
proof.
  proc.
  while (={y1p,y2p,samplesp,signsp,scalep,total,i,j}).
  + wp; call hrr_pointer_legacy.
    wp; call hrr_bit_legacy.
    by auto => />; rewrite /protect_ptr /protect_64.
  wp.
  while (={y1p,y2p,samplesp,signsp,scalep,lcount,total,i}).
  + wp; call hrr_pointer_legacy.
    wp; call hrr_bit_legacy.
    by auto => />; rewrite /protect_ptr /protect_64.
  by auto => />; rewrite /protect_ptr /protect_64.
qed.

lemma hrr_vector_outputs_correct
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) :
  hoare [HRR._hb_checked_scale_samples :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples0 /\ signsp=signs0 /\ scalep=scale0 /\
    counts=W64.of_int (t*4294967296+l) /\ hb_scale_bounds l t ==>
    (res.`1,res.`2)=hb_scale_result before1 before2 samples0 signs0 scale0 l t].
proof.
  by conseq hrr_vector_legacy
    (hb_scale_samples_correct before1 before2 samples0 signs0 scale0 l t) => /#.
qed.

lemma hrr_vector_total
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) :
  phoare [HRR._hb_checked_scale_samples :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples0 /\ signsp=signs0 /\ scalep=scale0 /\
    counts=W64.of_int (t*4294967296+l) /\ hb_scale_bounds l t ==>
    res=((hb_scale_result before1 before2 samples0 signs0 scale0 l t).`1,
         (hb_scale_result before1 before2 samples0 signs0 scale0 l t).`2,
         hcv_mask samples0 scale0 t)] = 1%r.
proof.
  conseq (hcv_scale_mask_total samples0 scale0 l t)
    (hrr_vector_outputs_correct before1 before2 samples0 signs0 scale0 l t) => />; smt().
qed.

lemma hrr_vector_correct
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) :
  hoare [HRR._hb_checked_scale_samples :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples0 /\ signsp=signs0 /\ scalep=scale0 /\
    counts=W64.of_int (t*4294967296+l) /\ hb_scale_bounds l t ==>
    res=((hb_scale_result before1 before2 samples0 signs0 scale0 l t).`1,
         (hb_scale_result before1 before2 samples0 signs0 scale0 l t).`2,
         hcv_mask samples0 scale0 t)].
proof. by conseq (hrr_vector_total before1 before2 samples0 signs0 scale0 l t). qed.

lemma hrr_checked_correct
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) (bound0 : W64.t) :
  hoare [HRR._hb_checked_scale_and_check_values :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples0 /\ signsp=signs0 /\ scalep=scale0 /\
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    res=hrr_checked_result before1 before2 samples0 signs0 scale0 l t bound0].
proof.
  proc; wp; ecall (checked_sqnorm2_correct y1p l y2p (t-l)).
  wp; call (hrr_vector_correct before1 before2 samples0 signs0 scale0 l t).
  auto => />; rewrite /protect_64.
  try rewrite /protect_ptr.
  try rewrite -W64.of_intS.
  move=> hl0 hlmax hk0 hkmax ht.
  rewrite /W64.(`<<`) W8.of_uintK /= gs_pack_counts_word 1:/#.
  rewrite /=.
  move=> result0 hnorm hover.
  by rewrite hnorm hover /hrr_checked_result /= hca_final_word.
qed.

lemma hrr_checked_total
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) (bound0 : W64.t) :
  phoare [HRR._hb_checked_scale_and_check_values :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples0 /\ signsp=signs0 /\ scalep=scale0 /\
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    res=hrr_checked_result before1 before2 samples0 signs0 scale0 l t bound0] = 1%r.
proof.
  by conseq hca_scale_and_check_ll
    (hrr_checked_correct before1 before2 samples0 signs0 scale0 l t bound0).
qed.

lemma hrr_half_legacy :
  equiv [HRR._fixpoint_half_round ~ HB._fixpoint_half_round : ={xp} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma hrr_newton_legacy :
  equiv [HRR._fixpoint_newton_invsqrt ~ HB._fixpoint_newton_invsqrt :
    ={rp,xhalfp,start_cubep,start_threep} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma hrr_high_legacy :
  equiv [HRR._fixpoint_mul_high ~ HB._fixpoint_mul_high : ={rp,xp,y} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma hrr_half_correct xp0 :
  hoare [HRR._fixpoint_half_round : xp=xp0 ==>
    res=hb_pack (hb_half_round (hb_load xp0))].
proof. by conseq hrr_half_legacy (hb_half_round_correct xp0) => /#. qed.

lemma hrr_newton_correct xp0 cube0 three0 :
  hoare [HRR._fixpoint_newton_invsqrt :
    xhalfp=xp0 /\ start_cubep=cube0 /\ start_threep=three0 ==>
    res=hb_pack (hb_newton (hb_load xp0) (hb_load cube0) (hb_load three0))].
proof. by conseq hrr_newton_legacy (hb_newton_correct xp0 cube0 three0) => /#. qed.

lemma hrr_high_correct xp0 yy :
  hoare [HRR._fixpoint_mul_high : xp=xp0 /\ y=yy ==>
    res=hb_pack (hb_mul_high (hb_load xp0) yy)].
proof. by conseq hrr_high_legacy (hb_mul_high_correct xp0 yy) => /#. qed.

lemma hrr_half_ll : islossless HRR._fixpoint_half_round.
proof. by conseq hrr_half_legacy hb_half_round_ll => /#. qed.

lemma hrr_newton_ll : islossless HRR._fixpoint_newton_invsqrt.
proof. by conseq hrr_newton_legacy hb_newton_ll => /#. qed.

lemma hrr_high_ll : islossless HRR._fixpoint_mul_high.
proof. by conseq hrr_high_legacy hb_mul_high_ll => /#. qed.

lemma hrr_correct mode0 samples0 signs0 squares0 :
  hoare [HyperballRenyiArithmetic.run :
    mode=mode0 /\ samples=samples0 /\ signs=signs0 /\ squares=squares0 /\ hbw_mode mode0 ==>
    res=hrr_result mode0 samples0 signs0 squares0].
proof.
  proc.
  ecall (hrr_checked_correct hbw_zero_output hbw_zero_output samples0 signs0 scale
    (hbw_left mode0) (hbw_count mode0) (hb_ref_bound mode0)).
  ecall (hrr_high_correct inverse (hb_ref_scale mode0)).
  ecall (hrr_newton_correct half (hb_pack (hb_ref_cube mode0))
    (hb_pack (hb_ref_three mode0))).
  ecall (hrr_half_correct squares0).
  skip; auto => />.
  move=> hm.
  have hs := hbw_storage_bounds mode0 hm.
  move: hs; rewrite /hb_scale_bounds; smt().
qed.

lemma hrr_ll : islossless HyperballRenyiArithmetic.run.
proof.
  proc; call hca_scale_and_check_ll; call hrr_high_ll; call hrr_newton_ll;
    call hrr_half_ll; auto.
qed.

lemma hrr_total mode0 samples0 signs0 squares0 :
  phoare [HyperballRenyiArithmetic.run :
    mode=mode0 /\ samples=samples0 /\ signs=signs0 /\ squares=squares0 /\ hbw_mode mode0 ==>
    res=hrr_result mode0 samples0 signs0 squares0] = 1%r.
proof. by conseq hrr_ll (hrr_correct mode0 samples0 signs0 squares0). qed.
