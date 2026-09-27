require import AllCore Real Distr StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 GaussianPayloadSpec GaussianRenyiSpec GaussianIidBufferSpec
  HyperballIidPayloadSpec HyperballWitnessSpec HyperballRenyiPayload
  HyperballRenyiBatch HyperballRenyiBatchBounds HyperballRenyiMap HyperballRenyiProduct
  HyperballRenyiJoint HyperballRenyiHardened HyperballRenyiArithmetic.
import RealOrder.

(* Observe one entire attempt, including rejected candidates and its exact
   acceptance bit. No conditioning on that bit occurs in this comparison. *)
op hrf_project mode (input : hrj_input) : hrr_output =
  let state=hrj_reconstruct input in hrr_result mode state.`1 state.`2 state.`3.

op hrf_actual mode : hrr_output distr =
  dmap (hrj_source gpd_accepted mode) (hrf_project mode).
op hrf_exact (p : BArray26.t) mode : hrr_output distr =
  dmap (hrj_source (hrp_exact_payload p) mode) (hrf_project mode).

lemma hrf_outputs_ll p mode :
  is_lossless (hrf_actual mode) /\ is_lossless (hrf_exact p mode).
proof.
  have [ha hb] := hrbb_sources_ll p mode.
  split; rewrite /hrf_actual /hrf_exact; apply dmap_ll; assumption.
qed.

lemma hrf_renyi_bounds p mode order : hip_mode mode => 2<=order<=1024 =>
  grn_renyi order (hrf_actual mode) (hrf_exact p mode) <=
    (1%r+grn_epsilon)^(hip_total mode) /\
  grn_renyi order (hrf_exact p mode) (hrf_actual mode) <=
    (1%r+grn_epsilon)^(hip_total mode).
proof.
  move=> hm ho.
  have [ha hb] := hrbb_sources_ll p mode.
  have [hfa hfb] := hrbb_sources_finite p mode hm.
  have [hab hba] := hrbb_source_supports p mode hm.
  have h1 := hrm_renyi_map order (hrj_source gpd_accepted mode)
    (hrj_source (hrp_exact_payload p) mode) (hrf_project mode) ha hb hfa hfb hab _; first smt().
  have h2 := hrm_renyi_map order (hrj_source (hrp_exact_payload p) mode)
    (hrj_source gpd_accepted mode) (hrf_project mode) hb ha hfb hfa hba _; first smt().
  have hu := hrbb_renyi_bounds p mode order hm ho.
  rewrite /hrf_actual /hrf_exact; smt().
qed.

lemma hrf_common_bound p mode order : hip_mode mode => 2<=order<=1024 =>
  grn_renyi order (hrf_actual mode) (hrf_exact p mode) < 1%r+1%r/72057594037927936%r /\
  grn_renyi order (hrf_exact p mode) (hrf_actual mode) < 1%r+1%r/72057594037927936%r.
proof.
  move=> hm ho; have hu := hrf_renyi_bounds p mode order hm ho.
  have [_ [hn _]] := hrj_mode_budget mode hm.
  have hc := hrt_common_bound (hip_total mode) hn; smt().
qed.

lemma hrf_hardened_state_law mode (event : gib_result -> bool) &m : hip_mode mode =>
  Pr[HyperballRenyiHardenedBatch.sample(mode) @ &m : event res] =
    (mu (hrj_actual_state mode) event).
proof.
  move=> hm; have he :
    Pr[HyperballIidGaussian.sample(mode) @ &m : event res] =
    Pr[HyperballRenyiHardenedBatch.sample(mode) @ &m : event res]
    by byequiv hrh_batch_equiv.
  rewrite -he; exact (hrj_actual_law mode event &m hm).
qed.

lemma hrf_hardened_state_phoare mode0 (event : gib_result -> bool) : hip_mode mode0 =>
  phoare [HyperballRenyiHardenedBatch.sample : mode=mode0 ==> event res] =
    (mu (hrj_actual_state mode0) event).
proof.
  move=> hm; bypr => &m ->; exact (hrf_hardened_state_law mode0 event &m hm).
qed.

module HyperballRenyiAttempt = {
  proc sample(mode : int) : hrr_output = {
    var state : gib_result;
    var output : hrr_output;
    state <@ HyperballRenyiHardenedBatch.sample(mode);
    output <@ HyperballRenyiArithmetic.run(mode,state.`1,state.`2,state.`3);
    return output;
  }
}.

module HRFActualPure = {
  proc sample(mode : int) : hrr_output = {
    var state : gib_result;
    state <@ HyperballRenyiHardenedBatch.sample(mode);
    return hrr_result mode state.`1 state.`2 state.`3;
  }
}.

lemma hrf_actual_pure :
  equiv [HyperballRenyiAttempt.sample ~ HRFActualPure.sample :
    ={mode} /\ hip_mode mode{1} ==> ={res}].
proof.
  proc; ecall{1} (hrr_total mode{1} state{1}.`1 state{1}.`2 state{1}.`3).
  call (_ : ={mode} ==> ={res}); first by sim.
  auto => />; rewrite /hip_mode /hbw_mode; smt().
qed.

lemma hrf_actual_pure_law mode0 (event : hrr_output -> bool) &m : hip_mode mode0 =>
  Pr[HRFActualPure.sample(mode0) @ &m : event res]=mu (hrf_actual mode0) event.
proof.
  move=> hm.
  have hc := hrf_hardened_state_phoare mode0
    (fun (state : gib_result) => event (hrr_result mode0 state.`1 state.`2 state.`3)) hm.
  rewrite /hrj_actual_state dmapE /(\o) in hc.
  rewrite /hrf_actual dmapE /hrf_project /(\o) /=.
  byphoare (_ : mode=mode0 ==> event res) => //.
  proc; call hc; auto.
qed.

lemma hrf_attempt_law mode (event : hrr_output -> bool) &m : hip_mode mode =>
  Pr[HyperballRenyiAttempt.sample(mode) @ &m : event res]=mu (hrf_actual mode) event.
proof.
  move=> hm; have he : Pr[HyperballRenyiAttempt.sample(mode) @ &m : event res]=
    Pr[HRFActualPure.sample(mode) @ &m : event res] by byequiv hrf_actual_pure.
  rewrite he; exact (hrf_actual_pure_law mode event &m hm).
qed.

op hrf_exact_state (p : BArray26.t) mode : gib_result distr =
  dmap (hrj_source (hrp_exact_payload p) mode) hrj_reconstruct.

module HRFExactState = {
  proc sample(p : BArray26.t, mode : int) : gib_result = {
    var input : hrj_input;
    var state : gib_result;
    input <$ hrj_source (hrp_exact_payload p) mode;
    state <- hrj_reconstruct input;
    return state;
  }
}.

lemma hrf_exact_state_law p0 mode0 (event : gib_result -> bool) &m :
  Pr[HRFExactState.sample(p0,mode0) @ &m : event res]=mu (hrf_exact_state p0 mode0) event.
proof.
  rewrite /hrf_exact_state dmapE.
  byphoare (_ : p=p0 /\ mode=mode0 ==> event res) => //.
  proc; wp; rnd; skip; auto.
qed.

lemma hrf_exact_state_phoare p0 mode0 (event : gib_result -> bool) :
  phoare [HRFExactState.sample : p=p0 /\ mode=mode0 ==> event res] =
    (mu (hrf_exact_state p0 mode0) event).
proof.
  bypr => &m [-> ->]; exact (hrf_exact_state_law p0 mode0 event &m).
qed.

module HyperballRenyiExactAttempt = {
  proc sample(p : BArray26.t, mode : int) : hrr_output = {
    var state : gib_result;
    var output : hrr_output;
    state <@ HRFExactState.sample(p,mode);
    output <@ HyperballRenyiArithmetic.run(mode,state.`1,state.`2,state.`3);
    return output;
  }
}.

module HRFExactPure = {
  proc sample(p : BArray26.t, mode : int) : hrr_output = {
    var state : gib_result;
    state <@ HRFExactState.sample(p,mode);
    return hrr_result mode state.`1 state.`2 state.`3;
  }
}.

lemma hrf_exact_pure :
  equiv [HyperballRenyiExactAttempt.sample ~ HRFExactPure.sample :
    ={p,mode} /\ hip_mode mode{1} ==> ={res}].
proof.
  proc; ecall{1} (hrr_total mode{1} state{1}.`1 state{1}.`2 state{1}.`3).
  call (_ : ={p,mode} ==> ={res}); first by sim.
  auto => />; rewrite /hip_mode /hbw_mode; smt().
qed.

lemma hrf_exact_pure_law p0 mode0 (event : hrr_output -> bool) &m :
  Pr[HRFExactPure.sample(p0,mode0) @ &m : event res]=mu (hrf_exact p0 mode0) event.
proof.
  have hc := hrf_exact_state_phoare p0 mode0
    (fun (state : gib_result) => event (hrr_result mode0 state.`1 state.`2 state.`3)).
  rewrite /hrf_exact_state dmapE /(\o) in hc.
  rewrite /hrf_exact dmapE /hrf_project /(\o) /=.
  byphoare (_ : p=p0 /\ mode=mode0 ==> event res) => //.
  proc; call hc; auto.
qed.

lemma hrf_exact_law p0 mode0 (event : hrr_output -> bool) &m : hip_mode mode0 =>
  Pr[HyperballRenyiExactAttempt.sample(p0,mode0) @ &m : event res]=mu (hrf_exact p0 mode0) event.
proof.
  move=> hm; have he : Pr[HyperballRenyiExactAttempt.sample(p0,mode0) @ &m : event res]=
    Pr[HRFExactPure.sample(p0,mode0) @ &m : event res] by byequiv hrf_exact_pure.
  rewrite he; exact (hrf_exact_pure_law p0 mode0 event &m).
qed.

lemma hrf_attempt_terminates mode &m : hip_mode mode =>
  Pr[HyperballRenyiAttempt.sample(mode) @ &m : true]=1%r.
proof.
  move=> hm; rewrite (hrf_attempt_law mode (fun _ => true) &m hm).
  have [h _] := hrf_outputs_ll witness mode; exact h.
qed.

lemma hrf_exact_terminates p mode &m : hip_mode mode =>
  Pr[HyperballRenyiExactAttempt.sample(p,mode) @ &m : true]=1%r.
proof.
  move=> hm; rewrite (hrf_exact_law p mode (fun _ => true) &m hm).
  have [_ h] := hrf_outputs_ll p mode; exact h.
qed.
