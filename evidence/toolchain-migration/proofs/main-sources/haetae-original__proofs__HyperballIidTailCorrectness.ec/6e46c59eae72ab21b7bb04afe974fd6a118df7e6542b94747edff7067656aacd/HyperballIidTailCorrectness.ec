require import AllCore IntDiv List Real Distr DList StdRing StdOrder.
from Jasmin require import JModel_x86.
require import IidExponentialTail HyperballTailSpec HyperballTailConstants
  HyperballIidPayloadSpec HyperballIidPayloadBatch HyperballIidSquareLaw
  HyperballIidAttemptSafety HyperballSafeSpec HyperballSafeCorrectness
  HyperballFixedPointSpec HyperballReferenceConstants
  GaussianPayloadSpec GaussianRawSquare GaussianSquareMoments GaussianStreamAccumulator.
import RField RealOrder.

lemma hti_raw_sum history :
  iet_sum ht_raw_square history=(gpd_sum history)%r/ht_q%r.
proof.
  elim: history => [|code history ih].
  + by rewrite /iet_sum /gpd_sum.
  have hs : iet_sum ht_raw_square (code::history)=
      ht_raw_square code+iet_sum ht_raw_square history by rewrite /iet_sum.
  have hg : gpd_sum (code::history)=gpd_square code+gpd_sum history by rewrite /gpd_sum.
  rewrite hs ih hg /ht_raw_square fromintD; ring.
qed.

lemma hti_inside_scaled mode value :
  hips_inside mode value =
    ((ht_count mode)%r*(3%r/4%r) <= value%r/ht_q%r <= (ht_count mode)%r*(5%r/4%r)).
proof.
  have hq : 0%r<ht_q%r by rewrite /ht_q.
  have hcount : hbs_events mode=ht_count mode by rewrite /ht_count hips_events.
  have hmin : ht_q%r*((ht_count mode)%r*(3%r/4%r))=(hbs_sum_min mode)%r.
  + rewrite /hbs_sum_min hcount !fromintM /ht_q /=; field; trivial.
  have hmax : ht_q%r*((ht_count mode)%r*(5%r/4%r))=(hbs_sum_max mode)%r.
  + rewrite /hbs_sum_max hcount !fromintM /ht_q /=; field; trivial.
  have hv : ht_q%r*(value%r/ht_q%r)=value%r by field; rewrite /ht_q; trivial.
  have hl := ler_pmul2l ht_q%r hq ((ht_count mode)%r*(3%r/4%r)) (value%r/ht_q%r).
  move: hl; rewrite hmin hv => hl.
  have hu := ler_pmul2l ht_q%r hq (value%r/ht_q%r) ((ht_count mode)%r*(5%r/4%r)).
  move: hu; rewrite hv hmax => hu.
  rewrite /hips_inside -!le_fromint; smt().
qed.

lemma hti_outside_scaled mode value :
  (!hips_inside mode value) =
    (value%r/ht_q%r < (ht_count mode)%r*(3%r/4%r) \/
      (ht_count mode)%r*(5%r/4%r) < value%r/ht_q%r).
proof. rewrite hti_inside_scaled; smt(). qed.

(* The generic bridge makes the two scalar moment obligations explicit.
   The public endpoints below discharge them with GaussianSquareMoments. *)
lemma ht_list_tail_from_moments mode : ht_mode mode =>
  E gpd_accepted ht_centered_plus <= ht_rplus =>
  E gpd_accepted ht_centered_minus <= ht_rminus =>
  mu (dlist gpd_accepted (ht_count mode))
    (fun history => !hips_inside mode (gpd_sum history)) < ht_epsilon mode.
proof.
  move=> hm hplus hminus.
  have hmode : hip_mode mode by move: hm; rewrite /ht_mode.
  have hp := hip_mode_polys mode hmode.
  have hn : 0<=ht_count mode by rewrite /ht_count /hip_total /hip_count; smt().
  have htm : 0%r<ht_tminus by rewrite /ht_tminus; smt().
  have htp : 0%r<ht_tplus by rewrite /ht_tplus; smt().
  have h := iet_iid_exponential_outside gpd_accepted ht_raw_square (ht_count mode)
    (3%r/4%r) (5%r/4%r) ht_tminus ht_tplus ht_rminus ht_rplus
    gps_accepted_finite hn htm htp hminus hplus.
  have he : mu (dlist gpd_accepted (ht_count mode))
      (fun history => !hips_inside mode (gpd_sum history)) =
    mu (dlist gpd_accepted (ht_count mode))
      (fun history => iet_sum ht_raw_square history < (ht_count mode)%r*(3%r/4%r) \/
        (ht_count mode)%r*(5%r/4%r) < iet_sum ht_raw_square history).
  + apply mu_eq => history.
    rewrite /= hti_raw_sum.
    have hf := hti_outside_scaled mode (gpd_sum history); smt().
  have hpower := ht_mode_power_bound mode hm.
  rewrite he; smt().
qed.

lemma ht_iid_list_tail mode : ht_mode mode =>
  mu (dlist gpd_accepted (ht_count mode))
    (fun history => !hips_inside mode (gpd_sum history)) < ht_epsilon mode.
proof.
  move=> hm; exact (ht_list_tail_from_moments mode hm gsm_centered_plus gsm_centered_minus).
qed.

(* These endpoints concern the explicit iid-byte controller. The unsafe
   event is the joint event of acceptance and excessive integer norm. *)
lemma ht_iid_square_tail mode &m : ht_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m : !hbs_good mode (hb_load res.`3)] <
    ht_epsilon mode.
proof.
  move=> hm; have hmode : hip_mode mode by move: hm; rewrite /ht_mode.
  rewrite (hia_bad_input_probability mode &m hmode) -/(ht_count mode).
  exact (ht_iid_list_tail mode hm).
qed.

lemma ht_iid_square_interval mode &m : ht_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m :
    gauss_stream_value res.`3<hbs_sum_min mode \/ hbs_sum_max mode<gauss_stream_value res.`3] <
    ht_epsilon mode.
proof.
  move=> hm; have hmode : hip_mode mode by move: hm; rewrite /ht_mode.
  rewrite (hips_actual_square_law mode
    (fun value => value<hbs_sum_min mode \/ hbs_sum_max mode<value) &m hmode).
  have he : (fun history => gpd_sum history<hbs_sum_min mode \/ hbs_sum_max mode<gpd_sum history) =
      (fun history => !hips_inside mode (gpd_sum history)) by
    apply fun_ext => history; rewrite /hips_inside; smt().
  rewrite he -/(ht_count mode); exact (ht_iid_list_tail mode hm).
qed.

lemma ht_iid_unsafe_acceptance mode &m : ht_mode mode =>
  Pr[HyperballIidAttempt.sample(mode) @ &m : hia_unsafe mode res] < ht_epsilon mode.
proof.
  move=> hm; have hmode : hip_mode mode by move: hm; rewrite /ht_mode.
  exact (ler_lt_trans _ _ _ (hia_unsafe_probability mode &m hmode) (ht_iid_square_tail mode &m hm)).
qed.

lemma ht_iid_accepted_outside_radius mode &m : ht_mode mode =>
  Pr[HyperballIidAttempt.sample(mode) @ &m :
    res.`3=W64.one /\ W64.to_uint (hb_ref_bound mode)<hsc_norm mode res] < ht_epsilon mode.
proof. move=> hm; have h := ht_iid_unsafe_acceptance mode &m hm; by move: h; rewrite /hia_unsafe. qed.

lemma ht_iid_unsafe_mode2 &m :
  Pr[HyperballIidAttempt.sample(2) @ &m : hia_unsafe 2 res] < 1%r/536870912%r.
proof. have h := ht_iid_unsafe_acceptance 2 &m _; first by rewrite /ht_mode /hip_mode. exact h. qed.

lemma ht_iid_unsafe_mode3 &m :
  Pr[HyperballIidAttempt.sample(3) @ &m : hia_unsafe 3 res] < 1%r/17592186044416%r.
proof. have h := ht_iid_unsafe_acceptance 3 &m _; first by rewrite /ht_mode /hip_mode. exact h. qed.

lemma ht_iid_unsafe_mode5 &m :
  Pr[HyperballIidAttempt.sample(5) @ &m : hia_unsafe 5 res] < 1%r/18014398509481984%r.
proof. have h := ht_iid_unsafe_acceptance 5 &m _; first by rewrite /ht_mode /hip_mode. exact h. qed.
