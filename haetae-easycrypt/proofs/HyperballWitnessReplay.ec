require import AllCore IntDiv StdOrder.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec HyperballWitnessSpec HyperballWitnessArithmetic
  HyperballWitnessExecution HyperballWitnessNorm HyperballWitnessSampling HyperballWitnessNewton
  HyperballFixedPointSpec HyperballFixedPointCorrectness
  HyperballReferenceConstants HyperballScaleSpec HyperballNormSpec.
import HyperballScaleSpec.

(* The mathematical norm is computed from the returned arrays. Its large
   fixture value is a conclusion, never a premise of the replay. *)
op [opaque] hbwr_boundary mode (result : hbwe_result) : bool =
  hbw_norm_result mode hbw_zero_output hbw_zero_output
    (result.`1,result.`2,result.`3) /\
  result.`4 = W64.of_int (hbw_residue mode) /\
  W64.to_uint result.`4 = hbw_residue mode /\
  W64.to_uint result.`4 <= W64.to_uint (hb_ref_bound mode).

module HyperballWitnessReplay = {
  proc run(mode : int) : hbwe_result = {
    var draw : gib_result;
    var output : hbwe_result;
    draw <@ HyperballWitnessSampling.sample(mode);
    output <@ HyperballWitnessExecution.run(mode,draw.`1,draw.`2,draw.`3);
    return output;
  }
}.

lemma hbwr_observed_norm mode (out : BArray8192.t * BArray8192.t * W64.t) :
  hbw_mode mode => hbw_norm_result mode hbw_zero_output hbw_zero_output out =>
  hbwr_boundary mode (out.`1,out.`2,out.`3,
    W64.of_int (hyperball_sqnorm out.`1 (hbw_left mode) out.`2
      (hbw_count mode-hbw_left mode))).
proof.
  case: out => a b accepted; move=> hm hg.
  rewrite /hbwr_boundary /=; split; first exact hg.
  have hg0 := hg; rewrite /hbw_norm_result /= in hg0.
  have [_ [_ [_ [_ [_ [hu _]]]]]] := hg0.
  have hw : W64.of_int (hyperball_sqnorm a (hbw_left mode) b
      (hbw_count mode-hbw_left mode)) = W64.of_int (hbw_residue mode).
  + by rewrite -hu W64.to_uintK.
  split; first exact hw.
  split; first exact hu.
  rewrite hu.
  have [_ [_ [_ [hle _]]]] := hbw_fixture_norm mode hm.
  exact hle.
qed.

lemma hbwr_result_from_scale mode samples :
  hbw_mode mode =>
  (forall i, 0 <= i < hbw_count mode =>
    BArray32768.get64 samples i = hbw_sample mode) =>
  hbwe_scale mode (hb_pack (hbw_sum mode)) = hb_pack (hbw_scale mode) =>
  hb_mul_rnd13 (hbw_sample mode) (hbw_scale mode) W64.zero =
    W32.of_int (hbw_coefficient mode) =>
  hbwr_boundary mode (hbwe_result_spec mode samples hbw_signs (hb_pack (hbw_sum mode))).
proof.
  move=> hm hs hscale hcoefficient.
  have hg := hbw_scale_check_result_good mode hbw_zero_output hbw_zero_output
    samples hm hs hcoefficient.
  rewrite /hbwe_result_spec hscale.
  exact (hbwr_observed_norm mode _ hm hg).
qed.

lemma hbwr_scale_exact mode : hbw_mode mode =>
  hbwe_scale mode (hb_pack (hbw_sum mode)) = hb_pack (hbw_scale mode).
proof.
  move=> hm; rewrite /hbwe_scale /hb_scale_factor hb_load_pack
    (hbw_half_round_exact mode hm) (hbw_newton_exact mode hm)
    (hbw_scale_exact mode hm).
  trivial.
qed.

lemma hbwr_result_exact mode samples : hbw_mode mode =>
  (forall i, 0 <= i < hbw_count mode =>
    BArray32768.get64 samples i = hbw_sample mode) =>
  hbwr_boundary mode (hbwe_result_spec mode samples hbw_signs (hb_pack (hbw_sum mode))).
proof.
  move=> hm hs; exact (hbwr_result_from_scale mode samples hm hs
    (hbwr_scale_exact mode hm) (hbw_coefficient_exact mode hm)).
qed.

lemma hbwr_execution_total mode0 samples0 : hbw_mode mode0 =>
  (forall i, 0 <= i < hbw_count mode0 =>
    BArray32768.get64 samples0 i = hbw_sample mode0) =>
  phoare [HyperballWitnessExecution.run : mode=mode0 /\ samples=samples0 /\
    signs=hbw_signs /\ squares=hb_pack (hbw_sum mode0)
    ==> hbwr_boundary mode0 res] = 1%r.
proof.
  move=> hm hs; have hb := hbwr_result_exact mode0 samples0 hm hs.
  by conseq hbwe_ll
    (hbwe_correct mode0 samples0 hbw_signs (hb_pack (hbw_sum mode0))) => />.
qed.

lemma hbwr_execution_guarded mode0 :
  phoare [HyperballWitnessExecution.run : mode=mode0 /\ hbw_mode mode0 /\
    signs=hbw_signs /\ squares=hb_pack (hbw_sum mode0) /\
    (forall i, 0 <= i < hbw_count mode0 => BArray32768.get64 samples i=hbw_sample mode0)
    ==> hbwr_boundary mode0 res] = 1%r.
proof.
  bypr => &m [hmode [hm [hsigns [hsquares hs]]]].
  by byphoare (hbwr_execution_total mode0 samples{m} hm hs).
qed.

(* Only the selected mode is supplied. Sample values, square accumulation,
   scale and the overflowing norm are derived by the calls in this program. *)
lemma hbwr_total mode0 :
  phoare [HyperballWitnessReplay.run : mode=mode0 /\ hbw_mode mode0
    ==> hbwr_boundary mode0 res] = 1%r.
proof.
  proc; call (hbwr_execution_guarded mode0); call (hbw_sampling_total mode0).
  auto => />.
qed.

lemma hbwr_outside_radius mode (out : hbwe_result) : hbwr_boundary mode out =>
  out.`3=W64.one /\ W64.to_uint (hb_ref_bound mode) <
    hyperball_sqnorm out.`1 (hbw_left mode) out.`2 (hbw_count mode-hbw_left mode).
proof.
  rewrite /hbwr_boundary /hbw_norm_result /=; move=> [h _].
  have [ha [_ [_ [_ [_ [_ [hb [hn _]]]]]]]] := h.
  split; first exact ha.
  exact (IntOrder.ltr_le_trans _ _ _ hb hn).
qed.

lemma hbwr_correct mode0 :
  hoare [HyperballWitnessReplay.run : mode=mode0 /\ hbw_mode mode0
    ==> hbwr_boundary mode0 res].
proof. by conseq (hbwr_total mode0). qed.

lemma hbwr_lossless mode0 :
  phoare [HyperballWitnessReplay.run : mode=mode0 /\ hbw_mode mode0 ==> true] = 1%r.
proof.
  proc; call hbwe_ll; call (hbw_sampling_total mode0); auto.
qed.

lemma hbwr_accepted_outside_radius_total mode0 :
  phoare [HyperballWitnessReplay.run : mode=mode0 /\ hbw_mode mode0 ==>
    res.`3=W64.one /\
    W64.to_uint (hb_ref_bound mode0) <
      hyperball_sqnorm res.`1 (hbw_left mode0) res.`2
        (hbw_count mode0-hbw_left mode0)] = 1%r.
proof.
  conseq (hbwr_lossless mode0) (hbwr_correct mode0) => />.
  move=> _ result hb; exact (hbwr_outside_radius mode0 result hb).
qed.
