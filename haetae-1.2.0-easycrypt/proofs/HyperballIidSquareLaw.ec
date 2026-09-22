require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import HyperballIidPayloadSpec HyperballIidPayloadBatch
  GaussianPayloadSpec GaussianPayloadEncoding GaussianPayloadBufferSpec GaussianIidBufferSpec
  GaussianStreamAccumulator GaussianAccumulatorCorrectness HyperballGaussianBounds
  HyperballSafeSpec HyperballFixedPointSpec HyperballReferenceConstants.

(* Both components are functions of the same complete accepted history.
   The square sum includes the two payloads omitted from the visible vector. *)
op hips_target mode : (int list * int) distr =
  dmap (dlist gpd_accepted (hip_total mode)) hip_projection.
op hips_inside mode value : bool = hbs_sum_min mode <= value <= hbs_sum_max mode.

lemma hips_modes mode : hip_mode mode = hbs_mode mode.
proof. by rewrite /hip_mode /hbs_mode. qed.

lemma hips_events mode : hip_total mode = hbs_events mode.
proof. by rewrite /hip_total /hip_count /hip_polys /hbs_events. qed.

lemma hips_mode_totals :
  hip_total 2=1538 /\ hip_total 3=2306 /\ hip_total 5=2818.
proof. by rewrite /hip_total /hip_count /hip_polys /hb_ref_l /hb_ref_k. qed.

lemma hips_value squares : hb_value (hb_load squares)=gauss_stream_value squares.
proof. by rewrite /hb_value /hb_load /gauss_stream_value /gauss_limb_value. qed.

lemma hips_safe_iff mode squares : hip_mode mode =>
  hb_cumulative_square_bound (hip_total mode) squares =>
  hbs_good mode (hb_load squares) = hips_inside mode (gauss_stream_value squares).
proof.
  move=> hm hc.
  have [hlo hhi] := hb_cumulative_canonical (hip_total mode) squares hc.
  have hmode : hbs_mode mode by rewrite -hips_modes.
  by rewrite /hbs_good hmode /hbs_canonical /hbs_radix /hb_load /= hlo
    -/(hb_load squares) hips_value /hips_inside.
qed.

lemma hips_target_ll mode : is_lossless (hips_target mode).
proof. by rewrite /hips_target dmap_ll dlist_ll //; exact gpd_accepted_ll. qed.

lemma hips_safe_observation mode (state : gib_result) history : hip_mode mode =>
  hip_observe mode state=hip_projection history =>
  hb_cumulative_square_bound (hip_total mode) state.`3 =>
  hbs_good mode (hb_load state.`3)=hips_inside mode (gpd_sum history).
proof.
  move=> hm he hc.
  rewrite (hips_safe_iff mode state.`3 hm hc).
  have hs : gauss_stream_value state.`3=gpd_sum history by
    move: he; rewrite /hip_observe /hip_projection; smt().
  by rewrite hs.
qed.

lemma hips_history_phoare mode0 (event : int list -> bool) : hip_mode mode0 =>
  phoare [HyperballIidPayload.sample : mode=mode0 ==> event res.`2] =
    (mu (dlist gpd_accepted (hip_total mode0)) event).
proof.
  move=> hm; bypr => &m ->.
  exact (hip_batch_history_law mode0 event &m hm).
qed.

lemma hips_payload_joint_phoare mode0 (event : int list * int -> bool) : hip_mode mode0 =>
  phoare [HyperballIidPayload.sample : mode=mode0 ==> event (hip_observe mode0 res.`1)] =
    (mu (hips_target mode0) event).
proof.
  move=> hm; rewrite /hips_target dmapE.
  conseq (hips_history_phoare mode0 (fun history => event (hip_projection history)) hm)
    (hip_payload_observe mode0 hm) => />; smt().
qed.

(* Public joint law: actual buffered calls, zero initial arrays, all modes.
   No square distribution, output fit or headroom is assumed in the premise. *)
lemma hips_actual_joint_law mode (event : int list * int -> bool) &m : hip_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m : event (hip_observe mode res)] =
    mu (hips_target mode) event.
proof.
  move=> hm.
  have he : Pr[HyperballIidGaussian.sample(mode) @ &m : event (hip_observe mode res)] =
    Pr[HyperballIidPayload.sample(mode) @ &m : event (hip_observe mode res.`1)] by
    byequiv hip_actual_payload.
  rewrite he; by byphoare (hips_payload_joint_phoare mode event hm).
qed.

lemma hips_actual_square_law mode (event : int -> bool) &m : hip_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m : event (gauss_stream_value res.`3)] =
    mu (dlist gpd_accepted (hip_total mode)) (fun history => event (gpd_sum history)).
proof.
  move=> hm.
  have he := hips_actual_joint_law mode (fun out : int list * int => event out.`2) &m hm.
  by move: he; rewrite /hip_observe /hips_target dmapE /hip_projection /=.
qed.

lemma hips_payload_safe_phoare mode0 : hip_mode mode0 =>
  phoare [HyperballIidPayload.sample : mode=mode0 ==>
    hbs_good mode0 (hb_load res.`1.`3)] =
    (mu (dlist gpd_accepted (hip_total mode0))
      (fun history => hips_inside mode0 (gpd_sum history))).
proof.
  move=> hm.
  conseq (hips_history_phoare mode0
    (fun history => hips_inside mode0 (gpd_sum history)) hm)
    (hip_payload_observe mode0 hm) => />; smt(hips_safe_observation).
qed.

(* This is an exact probability identity, not a numerical concentration bound. *)
lemma hips_actual_safe_probability mode &m : hip_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m : hbs_good mode (hb_load res.`3)] =
    mu (dlist gpd_accepted (hip_total mode))
      (fun history => hips_inside mode (gpd_sum history)).
proof.
  move=> hm.
  have he : Pr[HyperballIidGaussian.sample(mode) @ &m : hbs_good mode (hb_load res.`3)] =
    Pr[HyperballIidPayload.sample(mode) @ &m : hbs_good mode (hb_load res.`1.`3)] by
    byequiv hip_actual_payload.
  rewrite he; by byphoare (hips_payload_safe_phoare mode hm).
qed.

lemma hips_actual_terminates mode &m : hip_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m : true] = 1%r.
proof.
  move=> hm.
  have he := hips_actual_joint_law mode (fun _ => true) &m hm.
  rewrite /= in he; rewrite he; exact (hips_target_ll mode).
qed.
