require import AllCore IntDiv List Distr DList StdOrder.
from Jasmin require import JModel_x86.
require import HyperballIidPayloadSpec HyperballIidPayloadBatch HyperballIidSquareLaw
  GaussianIidBufferSpec GaussianPayloadSpec GaussianPayloadEncoding
  HyperballSafeSpec HyperballSafeCorrectness HyperballFixedPointSpec
  HyperballWitnessSpec HyperballWitnessExecution HyperballReferenceConstants.
import RealOrder.

(* One actual attempt with the explicit iid byte source. No retry loop,
   conditioning on acceptance, or concrete SHAKE randomness is assumed. *)
module HyperballIidAttempt = {
  proc sample(mode : int) : hbwe_result = {
    var state : gib_result;
    var output : hbwe_result;
    state <@ HyperballIidGaussian.sample(mode);
    output <@ HyperballSafeExecution.run(mode,state.`1,state.`2,state.`3);
    return output;
  }
}.

(* An input-only observation used for a relational event implication. *)
module HyperballIidAttemptInput = {
  proc sample(mode : int) : gib_result = {
    var state : gib_result;
    state <@ HyperballIidGaussian.sample(mode);
    return state;
  }
}.

op [opaque] hia_unsafe (mode : int) (output : hbwe_result) : bool =
  output.`3=W64.one /\ W64.to_uint (hb_ref_bound mode)<hsc_norm mode output.

lemma hia_modes mode : hip_mode mode = hbw_mode mode.
proof. by rewrite /hip_mode /hbw_mode. qed.

lemma hia_spec_guarded mode samples signs squares :
  hia_unsafe mode (hbwe_result_spec mode samples signs squares) =>
  !hbs_good mode (hb_load squares).
proof.
  move=> hbad; apply negP => hgood.
  have hr := hsc_result_good mode samples signs squares hgood.
  have hs := hsc_accept_radius mode (hbwe_result_spec mode samples signs squares) hr.
  move: hbad; rewrite /hia_unsafe; smt().
qed.

lemma hia_execution_guarded mode0 samples0 signs0 squares0 :
  phoare [HyperballSafeExecution.run :
    mode=mode0 /\ samples=samples0 /\ signs=signs0 /\ squares=squares0 /\ hip_mode mode0
    ==> hia_unsafe mode0 res => !hbs_good mode0 (hb_load squares0)] = 1%r.
proof.
  conseq hbwe_ll (hbwe_correct mode0 samples0 signs0 squares0) => />;
    smt(hia_modes hia_spec_guarded).
qed.

lemma hia_batch_total mode0 : hip_mode mode0 =>
  phoare [HyperballIidGaussian.sample : mode=mode0 ==> true] = 1%r.
proof.
  move=> hm; bypr => &m ->; exact (hips_actual_terminates mode0 &m hm).
qed.

lemma hia_total mode0 : hip_mode mode0 =>
  phoare [HyperballIidAttempt.sample : mode=mode0 ==> true] = 1%r.
proof.
  move=> hm; proc; call hbwe_ll; call (hia_batch_total mode0 hm); auto.
qed.

lemma hia_terminates mode &m : hip_mode mode =>
  Pr[HyperballIidAttempt.sample(mode) @ &m : true] = 1%r.
proof. move=> hm; by byphoare (hia_total mode hm). qed.

lemma hia_input_forward :
  equiv [HyperballIidAttemptInput.sample ~ HyperballIidGaussian.sample :
    ={mode} ==> ={res}].
proof. proc; inline HyperballIidGaussian.sample; sim. qed.

lemma hia_attempt_input mode0 :
  equiv [HyperballIidAttempt.sample ~ HyperballIidAttemptInput.sample :
    mode{1}=mode0 /\ mode{2}=mode0 /\ hip_mode mode0 ==>
    hia_unsafe mode0 res{1} => !hbs_good mode0 (hb_load res{2}.`3)].
proof.
  proc.
  ecall{1} (hia_execution_guarded mode0 state{1}.`1 state{1}.`2 state{1}.`3).
  call (_ : ={mode} ==> ={res}); first by sim.
  by auto.
qed.

lemma hia_unsafe_probability mode &m : hip_mode mode =>
  Pr[HyperballIidAttempt.sample(mode) @ &m : hia_unsafe mode res] <=
  Pr[HyperballIidGaussian.sample(mode) @ &m : !hbs_good mode (hb_load res.`3)].
proof.
  move=> hm.
  have he : Pr[HyperballIidAttemptInput.sample(mode) @ &m : !hbs_good mode (hb_load res.`3)] =
      Pr[HyperballIidGaussian.sample(mode) @ &m : !hbs_good mode (hb_load res.`3)] by
    byequiv hia_input_forward.
  rewrite -he; by byequiv (hia_attempt_input mode).
qed.

lemma hia_bad_input_probability mode &m : hip_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m : !hbs_good mode (hb_load res.`3)] =
  mu (dlist gpd_accepted (hip_total mode))
    (fun history => !hips_inside mode (gpd_sum history)).
proof.
  move=> hm.
  have hl := hips_actual_terminates mode &m hm.
  have hs := hips_actual_safe_probability mode &m hm.
  have hd := dlist_ll gpd_accepted (hip_total mode) gpd_accepted_ll.
  rewrite Pr [mu_not] hl hs mu_not hd.
  trivial.
qed.

lemma hia_unsafe_tail_bound mode &m : hip_mode mode =>
  Pr[HyperballIidAttempt.sample(mode) @ &m : hia_unsafe mode res] <=
  mu (dlist gpd_accepted (hip_total mode))
    (fun history => !hips_inside mode (gpd_sum history)).
proof.
  move=> hm; rewrite -(hia_bad_input_probability mode &m hm).
  exact (hia_unsafe_probability mode &m hm).
qed.

lemma hia_unsafe_epsilon mode (epsilon : real) &m : hip_mode mode =>
  mu (dlist gpd_accepted (hip_total mode))
    (fun history => !hips_inside mode (gpd_sum history)) <= epsilon =>
  Pr[HyperballIidAttempt.sample(mode) @ &m : hia_unsafe mode res] <= epsilon.
proof.
  move=> hm he; exact (ler_trans _ _ _ (hia_unsafe_tail_bound mode &m hm) he).
qed.

lemma hia_accepted_outside_bound mode &m : hip_mode mode =>
  Pr[HyperballIidAttempt.sample(mode) @ &m :
    res.`3=W64.one /\ W64.to_uint (hb_ref_bound mode)<hsc_norm mode res] <=
  mu (dlist gpd_accepted (hbs_events mode))
    (fun history => !hips_inside mode (gpd_sum history)).
proof.
  move=> hm; have h := hia_unsafe_tail_bound mode &m hm.
  by move: h; rewrite /hia_unsafe hips_events.
qed.
