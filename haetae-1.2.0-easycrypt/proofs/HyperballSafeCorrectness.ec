require import AllCore IntDiv StdOrder.
from Jasmin require import JModel_x86.
require import HyperballSafeSpec HyperballSafeConstants
  HyperballSafeScale HyperballSafeNewton
  HyperballWitnessSpec HyperballWitnessArithmetic HyperballWitnessExecution
  HyperballFixedPointSpec HyperballFixedPointCorrectness
  HyperballReferenceConstants HyperballNormSpec HyperballScaleSpec.
import HyperballScaleSpec.

(* Reuse the generic composition of the actual half/Newton/mul-high,
   scale-and-check and norm-observer procedures. Inputs remain arbitrary. *)
module HyperballSafeExecution = HyperballWitnessExecution.

op [opaque] hsc_norm mode (out : hbwe_result) : int =
  hyperball_sqnorm out.`1 (hbw_left mode) out.`2 (hbw_count mode-hbw_left mode).

op [opaque] hsc_result mode (out : hbwe_result) : bool =
  hyperball_coeff_bound out.`1 (hbw_left mode) hbs_coefficient_cap /\
  hyperball_coeff_bound out.`2 (hbw_count mode-hbw_left mode) hbs_coefficient_cap /\
  0 <= hsc_norm mode out < W64.modulus /\
  W64.to_uint out.`4 = hsc_norm mode out /\
  (out.`3=W64.one) = (hsc_norm mode out <= W64.to_uint (hb_ref_bound mode)).

lemma hsc_mode mode : hbs_mode mode => hbw_mode mode.
proof. by rewrite /hbs_mode /hbw_mode. qed.

lemma hsc_shape mode : hbs_mode mode =>
  hb_scale_bounds (hbw_left mode) (hbw_count mode) /\ hbw_count mode <= 2816.
proof.
  move=> hm; split; first exact (hbw_storage_bounds mode (hsc_mode mode hm)).
  move: hm; rewrite /hbs_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_count /hb_ref_l /hb_ref_k.
qed.



lemma hsc_bit_one (b : bool) : (W64.of_int (b2i b)=W64.one) = b.
proof. by case b; rewrite /b2i /= ?W64.to_uint_eq /=. qed.

lemma hsc_observe mode (a b : BArray8192.t) (accepted : W64.t) :
  hyperball_coeff_bound a (hbw_left mode) hbs_coefficient_cap =>
  hyperball_coeff_bound b (hbw_count mode-hbw_left mode) hbs_coefficient_cap =>
  0 <= hyperball_sqnorm a (hbw_left mode) b (hbw_count mode-hbw_left mode) < W64.modulus =>
  accepted = W64.of_int (b2i (hyperball_sqnorm a (hbw_left mode) b
    (hbw_count mode-hbw_left mode) <= W64.to_uint (hb_ref_bound mode))) =>
  hsc_result mode (a,b,accepted,W64.of_int (hyperball_sqnorm a (hbw_left mode) b
    (hbw_count mode-hbw_left mode))).
proof.
  move=> ha hb hn hacc.
  rewrite /hsc_result /hsc_norm /= hacc hsc_bit_one W64.of_uintK modz_small 1:hn.
  smt().
qed.

(* The earlier prescribed overflow examples are excluded by the input
   interval itself; their output values are not part of the safe predicate. *)
lemma hsc_prescribed_witness_outside mode : hbs_mode mode =>
  !hbs_good mode (hbw_sum mode).
proof.
  rewrite /hbs_mode; move=> [-> | [-> | ->]];
    by rewrite /hbs_good /hbs_mode /hbs_canonical /hbs_radix /hbw_sum
      /hbs_sum_min /hbs_sum_max /hbs_events /hb_ref_l /hb_ref_k /hb_value /=
      ?W64.of_uintK /=.
qed.

lemma hsc_bounded_scale_result mode samples signs squares : hbs_mode mode =>
  hbs_canonical (hb_load (hbwe_scale mode squares)) =>
  hb_value (hb_load (hbwe_scale mode squares)) <= hbs_scale_cap =>
  hsc_result mode (hbwe_result_spec mode samples signs squares).
proof.
  move=> hm hc hv; have [hshape hcount] := hsc_shape mode hm.
  have [ha [hb [hn hacc]]] := hsa_scale_result_safe
    hbw_zero_output hbw_zero_output samples signs (hbwe_scale mode squares)
    (hbw_left mode) (hbw_count mode) (hb_ref_bound mode) hshape hcount hc hv.
  rewrite /hbwe_result_spec /=.
  apply hsc_observe.
  + by rewrite /hb_scale_check_result /=; exact ha.
  + by rewrite /hb_scale_check_result /=; exact hb.
  + by move: hn; rewrite /hb_scale_norm /hb_scale_check_result /=.
  by move: hacc; rewrite /hb_scale_norm /hb_scale_check_result /=.
qed.

lemma hsc_computed_scale mode squares : hbs_good mode (hb_load squares) =>
  hbs_canonical (hb_load (hbwe_scale mode squares)) /\
  hb_value (hb_load (hbwe_scale mode squares)) <= hbs_scale_cap.
proof.
  move=> hg.
  have hm : hbs_mode mode by move: hg; rewrite /hbs_good; smt().
  have [hc [hz hv]] := hbs_safe_newton mode (hb_load squares) hg.
  rewrite /hbwe_scale /hb_scale_factor !hb_load_pack.
  exact (hsa_mode_scale_bound mode _ hm hc hv).
qed.

lemma hsc_full_magnitude mode squares (sample : W64.t) :
  hbs_good mode (hb_load squares) =>
  hb_rnd13_magnitude sample (hb_load (hbwe_scale mode squares)) <= hbs_coefficient_cap.
proof.
  move=> hg; have [hc hv] := hsc_computed_scale mode squares hg.
  have [_ hu] := hsa_rnd13_bound sample (hb_load (hbwe_scale mode squares)) hc hv.
  exact hu.
qed.

lemma hsc_result_good mode samples signs squares : hbs_good mode (hb_load squares) =>
  hsc_result mode (hbwe_result_spec mode samples signs squares).
proof.
  move=> hg; have [hc hv] := hsc_computed_scale mode squares hg.
  have hm : hbs_mode mode by move: hg; rewrite /hbs_good; smt().
  exact (hsc_bounded_scale_result mode samples signs squares hm hc hv).
qed.

lemma hsc_fixed_total mode0 samples0 signs0 squares0 :
  hbs_good mode0 (hb_load squares0) =>
  phoare [HyperballSafeExecution.run :
    mode=mode0 /\ samples=samples0 /\ signs=signs0 /\ squares=squares0
    ==> hsc_result mode0 res] = 1%r.
proof.
  move=> hg; have hr := hsc_result_good mode0 samples0 signs0 squares0 hg.
  have hm : hbw_mode mode0 by apply hsc_mode; move: hg; rewrite /hbs_good; smt().
  by conseq hbwe_ll (hbwe_correct mode0 samples0 signs0 squares0) => />.
qed.

(* Public premises concern only the entry mode and the canonical input
   square sum. There are no premises on sample/sign arrays or output fit. *)
lemma hsc_total mode0 :
  phoare [HyperballSafeExecution.run : mode=mode0 /\ hbs_good mode0 (hb_load squares)
    ==> hsc_result mode0 res] = 1%r.
proof.
  bypr => &m [hmode hg].
  by byphoare (hsc_fixed_total mode0 samples{m} signs{m} squares{m} hg).
qed.

lemma hsc_correct mode0 :
  hoare [HyperballSafeExecution.run : mode=mode0 /\ hbs_good mode0 (hb_load squares)
    ==> hsc_result mode0 res].
proof. by conseq (hsc_total mode0). qed.

lemma hsc_accept_radius mode (out : hbwe_result) : hsc_result mode out =>
  out.`3=W64.one => hsc_norm mode out <= W64.to_uint (hb_ref_bound mode).
proof. rewrite /hsc_result; smt(). qed.

lemma hsc_accepted_radius_total mode0 :
  phoare [HyperballSafeExecution.run : mode=mode0 /\ hbs_good mode0 (hb_load squares) ==>
    res.`3=W64.one => hsc_norm mode0 res <= W64.to_uint (hb_ref_bound mode0)] = 1%r.
proof.
  conseq hbwe_ll (hsc_correct mode0) => />.
  move=> &m _ _ _ _ result hs; exact (hsc_accept_radius mode{m} result hs).
qed.
