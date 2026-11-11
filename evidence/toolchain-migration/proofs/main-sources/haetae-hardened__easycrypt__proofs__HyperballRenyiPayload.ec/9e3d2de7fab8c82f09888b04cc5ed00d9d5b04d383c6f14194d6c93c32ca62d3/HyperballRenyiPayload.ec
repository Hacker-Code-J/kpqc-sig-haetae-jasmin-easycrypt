require import AllCore IntDiv Real Distr DInterval DBool Finite RealSeries StdRing StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 SigmaSpec SigmaCorrectness SigmaRejection48Bridge
  SigmaNoise72Bridge SigmaCDT83Patch SigmaRawNoiseSpec SigmaRawAcceptanceCorrectness
  SigmaExpAcceptanceCorrectness Rejection48Spec CDTDistributionBridge
  GaussianTraceSpec GaussianTraceProperties GaussianAccumulatorCorrectness
  HyperballGaussianBounds GaussianPayloadSpec GaussianPayloadEncoding
  GaussianPayloadMoments GaussianRetryInputs GaussianRetryCore
  GaussianRenyiSpec GaussianRenyiMoment GaussianRenyiActual
  GaussianRenyiConditioning GaussianRenyiKernelBounds.
import RField RealOrder.

op hrp_value (bytes : BArray26.t) : int = gpd_pack (sigma76_spec bytes).
op hrp_actual_payload (p : BArray26.t) : int distr =
  grk_output (grx_proposal p) sr_actual_probability hrp_value.

(* The reference changes only the acceptance probability to the exact exp
   of the actual quantized Xi, retaining the finite CDT and rounded-zero
   factor. Its output keeps the rounded word and both raw square limbs. *)
op hrp_exact_payload (p : BArray26.t) : int distr =
  grk_output (grx_proposal p) sigma_exp_acceptance_target hrp_value.

lemma hrp_value_decode bytes :
  gpd_magnitude (hrp_value bytes) = W64.to_uint (sigma76_spec bytes).`1 /\
  gpd_square (hrp_value bytes) %% 281474976710656 = W64.to_uint (sigma76_spec bytes).`2 /\
  gpd_square (hrp_value bytes) %/ 281474976710656 = W64.to_uint (sigma76_spec bytes).`3.
proof.
  have hb := hb_sigma76_event_bounded bytes.
  have hl : W64.to_uint (sigma76_spec bytes).`2 < 281474976710656 by
    move: hb; rewrite /hb_event_bounded; smt().
  have hs := gpd_pack_square_limbs (sigma76_spec bytes) hl.
  rewrite /hrp_value gpd_pack_magnitude; smt().
qed.

lemma hrp_rejection_payload p v :
  hrp_value (sigma_rejection48_patch p v) = hrp_value p.
proof.
  by rewrite /hrp_value /gpd_pack /sigma76_spec
    sigma_rejection48_patch_cdt_low sigma_rejection48_patch_cdt_high
    /sigma_from_cdt /= sigma_rejection48_patch_noise_low sigma_rejection48_patch_noise_high.
qed.

(* Integrate the rejection bits before comparing the two proposal kernels. *)
lemma hrp_rejection_joint p (event : int -> bool) :
  mu (dmap rejection48_uniform (sigma_rejection48_patch p))
    (fun bytes => (gpd_observer bytes).`2 /\ event (gpd_observer bytes).`1) =
  sr_actual_probability p * b2r (event (hrp_value p)).
proof.
  rewrite dmapE /(\o) /gpd_observer /=.
  have he : (fun v => gauss_event_accepted (sigma76_spec (sigma_rejection48_patch p v)) /\
      event (gpd_pack (sigma76_spec (sigma_rejection48_patch p v)))) =
    (fun v => (sigma76_spec (sigma_rejection48_patch p v)).`4=W64.one /\ event (hrp_value p)).
  + apply fun_ext => v.
    by rewrite gr_candidate_event_accept /gr_candidate_observer /=
      -/(hrp_value (sigma_rejection48_patch p v)) hrp_rejection_payload.
  rewrite he /b2r.
  case (event (hrp_value p)) => hcase /=.
  + exact (gpm_rejection_acceptance p).
  by rewrite mu0.
qed.

lemma hrp_actual_joint (p : BArray26.t) (event : int -> bool) :
  mu (grk_pair (grx_proposal p) sr_actual_probability hrp_value)
    (fun (r : int * bool) => r.`2 /\ event r.`1) =
  mu gpd_trial (fun (r : int * bool) => r.`2 /\ event r.`1).
proof.
  rewrite (gpm_trial_canonical p) dmapE /grk_pair /grx_proposal
    /gr_candidate_distribution dlet_dlet !dletE.
  apply RealSeries.eq_sum => u /=.
  rewrite dlet_dmap dletE; congr; rewrite dletE.
  apply RealSeries.eq_sum => y /=.
  rewrite /gr_candidate_patch hrp_rejection_joint.
  rewrite dmapE /(\o) /= Biased.dbiasedE
    (Biased.clamp_id _ (grb_actual_range (sigma_noise72_patch (sj_cdt83_patch p u) y))).
  rewrite /b2r; case (event (hrp_value (sigma_noise72_patch (sj_cdt83_patch p u) y))) => he /=; smt().
qed.

lemma hrp_actual_conditioned p : hrp_actual_payload p = gpd_accepted.
proof.
  apply eq_distr => value.
  rewrite /hrp_actual_payload /grk_output /gpd_accepted /gr_output !dmapE !dcondE
    /predI /(\o) /gr_accept /=.
  rewrite (hrp_actual_joint p (pred1 value)).
  have h := hrp_actual_joint p (fun _ => true).
  by move: h; rewrite /= => ->.
qed.

lemma hrp_outputs_finite p :
  is_finite (support gpd_accepted) /\ is_finite (support (hrp_exact_payload p)).
proof.
  split; first exact gpm_accepted_finite.
  rewrite /hrp_exact_payload; apply grk_output_finite; exact (grx_proposal_finite p).
qed.

lemma hrp_outputs_ll p : is_lossless gpd_accepted /\ is_lossless (hrp_exact_payload p).
proof.
  have h := grk_outputs_ll (grx_proposal p) sr_actual_probability sigma_exp_acceptance_target
    hrp_value (grx_proposal_finite p) (grx_proposal_ll p) (grx_kernel_conditions p).
  by move: h; rewrite -/(hrp_actual_payload p) -/(hrp_exact_payload p) hrp_actual_conditioned.
qed.

lemma hrp_output_relative p value :
  ((1%r-grk_delta)*mu1 (hrp_exact_payload p) value <= mu1 gpd_accepted value <=
    (1%r+grk_delta)*mu1 (hrp_exact_payload p) value) /\
  ((1%r-grk_delta)*mu1 gpd_accepted value <= mu1 (hrp_exact_payload p) value <=
    (1%r+grk_delta)*mu1 gpd_accepted value).
proof.
  have h := grk_output_bounds (grx_proposal p) sr_actual_probability sigma_exp_acceptance_target
    hrp_value value (grx_proposal_finite p) (grx_proposal_ll p) (grx_kernel_conditions p).
  by move: h; rewrite -/(hrp_actual_payload p) -/(hrp_exact_payload p) hrp_actual_conditioned.
qed.

lemma hrp_mass_bounds p :
  grn_mass_bounds gpd_accepted (hrp_exact_payload p) /\
  grn_mass_bounds (hrp_exact_payload p) gpd_accepted.
proof.
  rewrite /grn_mass_bounds; split => value; have h := hrp_output_relative p value;
    move: h; rewrite /grk_delta /grn_delta; smt().
qed.

lemma hrp_support p code : (code \in gpd_accepted) = (code \in hrp_exact_payload p).
proof.
  have [hb hbr] := hrp_mass_bounds p.
  have h1 := grn_support_inclusion gpd_accepted (hrp_exact_payload p) hb code.
  have h2 := grn_support_inclusion (hrp_exact_payload p) gpd_accepted hbr code.
  smt().
qed.

lemma hrp_exact_valid p code : code \in hrp_exact_payload p => gpd_valid code.
proof. rewrite -hrp_support; exact (gpd_accepted_valid code). qed.

lemma hrp_renyi_bounds (p : BArray26.t) (order : int) : 2<=order<=1024 =>
  grn_renyi order gpd_accepted (hrp_exact_payload p) <= 1%r+grn_epsilon /\
  grn_renyi order (hrp_exact_payload p) gpd_accepted <= 1%r+grn_epsilon.
proof.
  move=> ho; have [ha hb] := hrp_outputs_ll p.
  have [hfa hfb] := hrp_outputs_finite p.
  have [hab hba] := hrp_mass_bounds p.
  split.
  + exact (grn_finite_bound order gpd_accepted (hrp_exact_payload p) ha hb hfa hfb hab ho).
  exact (grn_finite_bound order (hrp_exact_payload p) gpd_accepted hb ha hfb hfa hba ho).
qed.
