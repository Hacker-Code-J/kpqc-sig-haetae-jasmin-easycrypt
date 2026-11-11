require import AllCore IntDiv Real Distr DInterval DBool Finite RealSeries StdRing StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 CDTDistributionBridge SigmaCDT83Patch SigmaRawNoiseSpec
  SigmaNoise72Bridge SigmaRejection48Bridge SigmaRawAcceptanceCorrectness
  SigmaExpAcceptanceCorrectness SigmaJointAttemptBridge SigmaJoint203Bridge
  SigmaConditionalSpec GaussianRenyiConditioning GaussianRenyiKernelBounds.
import RField RealOrder.

(* Only CDT and noise belong to the common proposal. The 48 rejection bits
   have already been integrated into sr_actual_probability. Retaining their
   deterministic decision as part of a full-byte proposal would be a different
   comparison and would not have the small relative bound used here. *)
op grx_proposal (p : BArray26.t) : BArray26.t distr =
  dlet (dinter 0 (cdt83_modulus-1)) (fun u =>
    dmap sr_noise_uniform (fun y => sigma_noise72_patch (sj_cdt83_patch p u) y)).

op grx_value (bytes : BArray26.t) : int = W64.to_uint (sigma_rejection48_rounded bytes).

op grx_actual_output (p : BArray26.t) : int distr =
  grk_output (grx_proposal p) sr_actual_probability grx_value.

(* The exact-exp reference keeps the actual finite CDT, quantized exponent,
   rounded-zero correction, and returned-word projection. *)
op grx_exact_output (p : BArray26.t) : int distr =
  grk_output (grx_proposal p) sigma_exp_acceptance_target grx_value.

lemma grx_proposal_finite p : is_finite (support (grx_proposal p)).
proof.
  rewrite /grx_proposal; apply finite_dlet; first apply DInterval.finite_dinter.
  move=> u _; apply grk_finite_map.
  rewrite /sr_noise_uniform; apply DInterval.finite_dinter.
qed.

lemma grx_proposal_ll p : is_lossless (grx_proposal p).
proof.
  rewrite /grx_proposal; apply dlet_ll; first exact sj203_uniform_ll.
  move=> u _; apply dmap_ll; exact sr_noise_uniform_ll.
qed.

lemma grx_kernel_conditions p :
  grk_kernel_conditions (grx_proposal p) sr_actual_probability sigma_exp_acceptance_target.
proof.
  rewrite /grk_kernel_conditions => bytes _.
  have h := grb_kernel_relative bytes.
  move: h; rewrite /grb_epsilon /grk_relative_error; smt().
qed.

lemma grx_actual_joint (p : BArray26.t) (event : int -> bool) :
  mu (grk_pair (grx_proposal p) sr_actual_probability grx_value)
    (fun (r : int * bool) => r.`2 /\ event r.`1) =
  mu (sc_actual_pair p) (fun (r : int * bool) => r.`2 /\ event r.`1).
proof.
  rewrite /grk_pair /grx_proposal /sc_actual_pair dlet_dlet !dletE.
  apply RealSeries.eq_sum => u /=.
  rewrite dlet_dmap dletE; congr; rewrite dletE.
  apply RealSeries.eq_sum => y /=.
  rewrite !dmapE /(\o) /= sigma_joint_fixed_output_mass.
  rewrite Biased.dbiasedE
    (Biased.clamp_id _ (grb_actual_range (sigma_noise72_patch (sj_cdt83_patch p u) y)))
    /grx_value /b2r /=.
  case (event (W64.to_uint (sigma_rejection48_rounded
    (sigma_noise72_patch (sj_cdt83_patch p u) y)))) => he /=; smt().
qed.

lemma grx_actual_conditioned p : grx_actual_output p = sc_actual_conditioned p.
proof.
  apply eq_distr => value.
  rewrite /grx_actual_output /grk_output /sc_actual_conditioned !dmapE !dcondE
    /predI /(\o) /sc_accepted /sc_output /=.
  rewrite (grx_actual_joint p (pred1 value)).
  have h := grx_actual_joint p (fun _ => true).
  by move: h; rewrite /= => ->.
qed.

lemma grx_outputs_finite p :
  is_finite (support (grx_actual_output p)) /\ is_finite (support (grx_exact_output p)).
proof.
  split; rewrite /grx_actual_output /grx_exact_output;
    apply grk_output_finite; exact (grx_proposal_finite p).
qed.

lemma grx_outputs_ll p :
  is_lossless (grx_actual_output p) /\ is_lossless (grx_exact_output p).
proof.
  exact (grk_outputs_ll (grx_proposal p) sr_actual_probability sigma_exp_acceptance_target
    grx_value (grx_proposal_finite p) (grx_proposal_ll p) (grx_kernel_conditions p)).
qed.

lemma grx_output_relative p value :
  ((1%r-grk_delta)*mu1 (grx_exact_output p) value <= mu1 (grx_actual_output p) value <=
    (1%r+grk_delta)*mu1 (grx_exact_output p) value) /\
  ((1%r-grk_delta)*mu1 (grx_actual_output p) value <= mu1 (grx_exact_output p) value <=
    (1%r+grk_delta)*mu1 (grx_actual_output p) value).
proof.
  exact (grk_output_bounds (grx_proposal p) sr_actual_probability sigma_exp_acceptance_target
    grx_value value (grx_proposal_finite p) (grx_proposal_ll p) (grx_kernel_conditions p)).
qed.
