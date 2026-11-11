require import AllCore IntDiv List Real Distr DInterval Finite StdRing StdOrder.
from Jasmin require import JModel_x86.
require import GaussianPayloadSpec GaussianPayloadEncoding GaussianRetryCore
  GaussianUniformBytes GaussianRetryInputs GaussianTraceSpec GaussianTraceProperties
  SigmaCorrectness SigmaRawSpec SigmaRawNoiseSpec RawSquareMomentSpec
  SigmaRejection48Bridge SigmaNoise72Bridge SigmaCDT83Patch CDTDistributionBridge
  Rejection48Spec Rejection48Correctness SigmaExpInputBounds SigmaRawAcceptanceCorrectness
  SigmaExpAcceptanceCorrectness.
import RField RealOrder.

op gpm_accept_weight (weight : int -> real) (outcome : int * bool) : real =
  if outcome.`2 then weight outcome.`1 else 0%r.

lemma gpm_finite_map ['a 'b] (d : 'a distr) (f : 'a -> 'b) :
  is_finite (Distr.support d) => is_finite (Distr.support (dmap d f)).
proof.
  move=> hd; rewrite /dmap; apply finite_dlet => // x hx; exact (finite_dunit (f x)).
qed.

lemma gpm_candidate_finite p : is_finite (Distr.support (gr_candidate_distribution p)).
proof.
  rewrite /gr_candidate_distribution; apply finite_dlet; first exact (finite_dinter 0 (cdt83_modulus-1)).
  move=> u hu; apply finite_dlet; first by rewrite /sr_noise_uniform; apply finite_dinter.
  move=> y hy; apply gpm_finite_map; by rewrite /rejection48_uniform; apply finite_dinter.
qed.

lemma gpm_trial_canonical p :
  gpd_trial = dmap (gr_candidate_distribution p) gpd_observer.
proof.
  have hleft : gpd_trial = dmap (dmap gbc_candidate sigma76_spec)
      (fun event : gauss_event => (gpd_pack event,gauss_event_accepted event)).
  + by rewrite dmap_comp /gpd_trial /gpd_observer.
  rewrite hleft (gbc_candidate_sigma_law p) dmap_comp.
  by rewrite /gpd_observer.
qed.

lemma gpm_trial_finite : is_finite (Distr.support gpd_trial).
proof. rewrite (gpm_trial_canonical witness); apply gpm_finite_map; exact (gpm_candidate_finite witness). qed.

lemma gpm_accepted_finite : is_finite (Distr.support gpd_accepted).
proof.
  rewrite /gpd_accepted /gr_output; apply gpm_finite_map; apply finite_dcond; exact gpm_trial_finite.
qed.

(* This identity keeps the actual acceptance denominator. *)
lemma gpm_conditioned_moment (weight : int -> real) :
  E gpd_accepted weight = E gpd_trial (gpm_accept_weight weight) / mu gpd_trial gr_accept.
proof.
  rewrite /gpd_accepted /gr_output exp_dmap.
  + apply hasE_finite; apply gpm_finite_map; apply finite_dcond; exact gpm_trial_finite.
  by rewrite exp_dcond /Ec /gpm_accept_weight /gr_accept /=.
qed.

lemma gpm_rejection_acceptance p :
  mu rejection48_uniform (fun v =>
    (sigma76_spec (sigma_rejection48_patch p v)).`4 = W64.one) = sr_actual_probability p.
proof.
  have ht := sigma_exp_threshold_fit p.
  have ht0 := W64.to_uint_cmp (sigma_rejection48_threshold p).
  have hbound : 0<=W64.to_uint (sigma_rejection48_threshold p)<9223372036854775808 by smt().
  rewrite /sr_actual_probability -(rejection48_word_probability _ _ hbound) W64.to_uintK.
  apply mu_eq_support => v hv /=.
  have hr : 0<=v<281474976710656 by move: hv; rewrite /rejection48_uniform supp_dinter; smt().
  by rewrite (sigma_rejection48_patched_acceptance p v hr).
qed.

lemma gpm_rejection_candidate p v :
  sr_candidate (sigma_rejection48_patch p v) = sr_candidate p.
proof.
  by rewrite /sr_candidate /sr_noise /sr_cdt sigma_rejection48_patch_noise_low
    sigma_rejection48_patch_noise_high sigma_rejection48_patch_cdt_low
    sigma_rejection48_patch_cdt_high.
qed.

lemma gpm_rejection_moment p (weight raw_weight : int -> real) :
  (forall candidate, weight (gpd_pack (sigma76_spec candidate)) = raw_weight (sr_candidate candidate)) =>
  E (dmap rejection48_uniform (sigma_rejection48_patch p))
    (fun candidate => gpm_accept_weight weight (gpd_observer candidate)) =
  raw_weight (sr_candidate p) * sr_actual_probability p.
proof.
  move=> hweight.
  rewrite exp_dmap.
  + apply hasE_finite; apply gpm_finite_map; by rewrite /rejection48_uniform; apply finite_dinter.
  have he : E rejection48_uniform
      (fun v => gpm_accept_weight weight (gpd_observer (sigma_rejection48_patch p v))) =
    E rejection48_uniform (fun v =>
      if (sigma76_spec (sigma_rejection48_patch p v)).`4=W64.one
      then raw_weight (sr_candidate p) else 0%r).
  + apply eq_exp => v hv /=.
    rewrite /gpm_accept_weight /gpd_observer /= gr_candidate_event_accept
      /gr_candidate_observer /= hweight gpm_rejection_candidate.
    trivial.
  by rewrite /= he expC_cond gpm_rejection_acceptance.
qed.

lemma gpm_proposal_moment p (weight raw_weight : int -> real) :
  (forall candidate, weight (gpd_pack (sigma76_spec candidate)) = raw_weight (sr_candidate candidate)) =>
  E gpd_trial (gpm_accept_weight weight) = rsm_actual p raw_weight.
proof.
  move=> hweight.
  rewrite (gpm_trial_canonical p) exp_dmap.
  + apply hasE_finite; apply gpm_finite_map; exact (gpm_candidate_finite p).
  rewrite /gr_candidate_distribution exp_dlet.
  + apply hasE_finite; exact (gpm_candidate_finite p).
  rewrite /rsm_actual; apply eq_exp => u hu /=.
  rewrite exp_dlet.
  + apply hasE_finite; apply finite_dlet; first by rewrite /sr_noise_uniform; apply finite_dinter.
    move=> y hy; apply gpm_finite_map; by rewrite /rejection48_uniform; apply finite_dinter.
  apply eq_exp => y hy /=.
  rewrite /gr_candidate_patch.
  exact (gpm_rejection_moment (sigma_noise72_patch (sj_cdt83_patch p u) y)
    weight raw_weight hweight).
qed.

lemma gpm_raw_conditioned_moment p (weight raw_weight : int -> real) :
  (forall candidate, weight (gpd_pack (sigma76_spec candidate)) = raw_weight (sr_candidate candidate)) =>
  E gpd_accepted weight = rsm_actual p raw_weight / mu gpd_trial gr_accept.
proof. move=> hw; by rewrite gpm_conditioned_moment (gpm_proposal_moment p weight raw_weight hw). qed.

lemma gpm_acceptance p : rsm_actual p (fun _ => 1%r) = mu gpd_trial gr_accept.
proof.
  have he := gpm_proposal_moment p (fun _ => 1%r) (fun _ => 1%r) _; first trivial.
  move: he; rewrite /gpm_accept_weight expC_cond /gr_accept /=; smt().
qed.
