require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HyperballWitnessSpec HyperballWitnessArithmetic
  HyperballFixedPointSpec HyperballFixedPointCorrectness
  HyperballReferenceConstants HyperballScaleSpec HyperballScaleCorrectness
  HyperballNormSpec HyperballNormCorrectness.
import HyperballScaleSpec HyperballScaleCorrectness HyperballNormCorrectness.

type hbwe_result = BArray8192.t * BArray8192.t * W64.t * W64.t.

op hbwe_scale mode (squares : BArray16.t) : BArray16.t =
  hb_pack (hb_scale_factor (hb_load squares) (hb_ref_cube mode)
    (hb_ref_three mode) (hb_ref_scale mode)).

op hbwe_result_spec mode samples signs squares : hbwe_result =
  let out = hb_scale_check_result hbw_zero_output hbw_zero_output
    samples signs (hbwe_scale mode squares) (hbw_left mode) (hbw_count mode)
    (hb_ref_bound mode) in
  (out.`1,out.`2,out.`3,
    W64.of_int (hyperball_sqnorm out.`1 (hbw_left mode) out.`2
      (hbw_count mode-hbw_left mode))).

(* This is a deterministic composition of the actual extracted helpers.
   It supplies no expected intermediate values to those procedures. *)
module HyperballWitnessExecution = {
  proc run(mode : int, samples : BArray32768.t, signs : BArray512.t,
      squares : BArray16.t) : hbwe_result = {
    var half, inverse, scale : BArray16.t;
    var y1, y2 : BArray8192.t;
    var accepted, norm : W64.t;
    half <@ HB._fixpoint_half_round(squares);
    inverse <@ HB._fixpoint_newton_invsqrt(hb_pack (W64.zero,W64.zero),half,
      hb_pack (hb_ref_cube mode),hb_pack (hb_ref_three mode));
    scale <@ HB._fixpoint_mul_high(hb_pack (W64.zero,W64.zero),inverse,hb_ref_scale mode);
    (y1,y2,accepted) <@ HS._sf_scale_and_check(hbw_zero_output,hbw_zero_output,
      samples,signs,scale,W64.of_int (hbw_left mode),W64.of_int (hbw_count mode),
      hb_ref_bound mode);
    norm <@ Signer._polyfixveclk_sqnorm2_2048(y1,W64.of_int (hbw_left mode),
      y2,W64.of_int (hbw_count mode-hbw_left mode));
    return (y1,y2,accepted,norm);
  }
}.

lemma hbwe_correct mode0 samples0 signs0 squares0 :
  hoare [HyperballWitnessExecution.run :
    mode=mode0 /\ samples=samples0 /\ signs=signs0 /\ squares=squares0 /\
    hbw_mode mode0 ==> res=hbwe_result_spec mode0 samples0 signs0 squares0].
proof.
  proc.
  ecall (polyfixveclk_sqnorm2_correct y1 (hbw_left mode0) y2
    (hbw_count mode0-hbw_left mode0)).
  ecall (hb_scale_and_check_correct hbw_zero_output hbw_zero_output
    samples0 signs0 scale (hbw_left mode0) (hbw_count mode0) (hb_ref_bound mode0)).
  ecall (hb_mul_high_correct inverse (hb_ref_scale mode0)).
  ecall (hb_newton_correct half (hb_pack (hb_ref_cube mode0))
    (hb_pack (hb_ref_three mode0))).
  ecall (hb_half_round_correct squares0).
  skip; auto => />.
  move=> hm; have h := hbw_storage_bounds mode0 hm.
  move: h; rewrite /hb_scale_bounds; smt().
qed.

lemma hbwe_ll : islossless HyperballWitnessExecution.run.
proof.
  proc; call polyfixveclk_sqnorm2_ll; call hb_scale_and_check_ll;
    call hb_mul_high_ll; call hb_newton_ll; call hb_half_round_ll; auto.
qed.

lemma hbwe_total mode0 samples0 signs0 squares0 :
  phoare [HyperballWitnessExecution.run :
    mode=mode0 /\ samples=samples0 /\ signs=signs0 /\ squares=squares0 /\
    hbw_mode mode0 ==> res=hbwe_result_spec mode0 samples0 signs0 squares0] = 1%r.
proof. by conseq hbwe_ll (hbwe_correct mode0 samples0 signs0 squares0). qed.
