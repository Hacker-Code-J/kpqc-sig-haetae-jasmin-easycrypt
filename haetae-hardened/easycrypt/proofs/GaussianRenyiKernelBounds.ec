require import AllCore Real RealExp Distr StdRing StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 ApproxExpSpec ApproxExpWordCorrectness SigmaExpInputBounds
  SigmaExpAcceptanceCorrectness SigmaRawAcceptanceCorrectness
  SigmaRejection48Bridge Rejection48Spec ExponentialLipschitz.
import RField RealOrder.

op grb_epsilon : real = 84%r/281474976710656%r.

(* The target retains the actual quantized Xi and rounded-zero factor.
   These are relative bounds on acceptance weights, not a raw Gaussian law. *)
lemma grb_quantized_domain (p : BArray26.t) :
  0%r <= (W64.to_uint (sigma_exp_argument p))%r/ae_scale%r <= 2%r/3%r.
proof.
  have hd := ae_sigma_domain p.
  rewrite /ae_domain in hd.
  have h0 : 0%r <= (W64.to_uint (sigma_exp_argument p))%r by rewrite le_fromint; smt().
  have h3 : 3%r*(W64.to_uint (sigma_exp_argument p))%r <= 2%r*ae_scale%r
    by rewrite -!fromintM le_fromint; smt().
  move: h3; rewrite /ae_scale; smt().
qed.

lemma grb_exponential_range (p : BArray26.t) :
  1%r/3%r <= RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r/ae_scale%r)) <= 1%r.
proof.
  have hd := grb_quantized_domain p.
  have hl := exp_neg_linear_lower ((W64.to_uint (sigma_exp_argument p))%r/ae_scale%r).
  have hu := ae_real_probability_range (sigma_exp_argument p).
  smt().
qed.

lemma grb_factor_range (p : BArray26.t) :
  1%r/2%r <= rejection48_factor (sigma_rejection48_rounded p) <= 1%r.
proof.
  rewrite /rejection48_factor; case (sigma_rejection48_rounded p=W64.zero); smt().
qed.

lemma grb_target_range (p : BArray26.t) :
  1%r/6%r <= sigma_exp_acceptance_target p <= 1%r.
proof.
  have he := grb_exponential_range p; have hf := grb_factor_range p.
  rewrite /sigma_exp_acceptance_target; smt().
qed.

lemma grb_target_positive (p : BArray26.t) : 0%r < sigma_exp_acceptance_target p.
proof. have h := grb_target_range p; smt(). qed.

lemma grb_actual_range (p : BArray26.t) : 0%r <= sr_actual_probability p <= 1%r.
proof.
  have hb := rejection48_base_bounds (W64.to_uint (sigma_rejection48_threshold p)).
  rewrite /sr_actual_probability /rejection48_probability /rejection48_factor.
  case (sigma_rejection48_rounded p=W64.zero); smt().
qed.

lemma grb_absolute_error (p : BArray26.t) :
  `|sr_actual_probability p-sigma_exp_acceptance_target p| <=
    rejection48_factor (sigma_rejection48_rounded p)*(28%r/ae_scale%r).
proof.
  have h : forall &m,
      `|sr_actual_probability p-sigma_exp_acceptance_target p| <=
        rejection48_factor (sigma_rejection48_rounded p)*(28%r/ae_scale%r).
  + move=> &m.
    have he := sigma_exp_acceptance_error p &m.
    by move: he; rewrite (sr_actual_probability_law p &m).
  smt().
qed.

lemma grb_relative_error (p : BArray26.t) :
  `|sr_actual_probability p-sigma_exp_acceptance_target p| <=
    grb_epsilon*sigma_exp_acceptance_target p.
proof.
  have he := grb_absolute_error p.
  have hl := grb_exponential_range p.
  have hf := grb_factor_range p.
  rewrite /grb_epsilon /sigma_exp_acceptance_target.
  move: he; rewrite /ae_scale; smt().
qed.

lemma grb_epsilon_half : 0%r < grb_epsilon < 1%r/2%r.
proof. rewrite /grb_epsilon; smt(). qed.

lemma grb_actual_positive (p : BArray26.t) : 0%r < sr_actual_probability p.
proof.
  have he := grb_relative_error p; have hb := grb_target_range p.
  have heps := grb_epsilon_half.
  move: he; rewrite ler_norml; smt().
qed.

lemma grb_kernel_relative (p : BArray26.t) :
  0%r < sr_actual_probability p <= 1%r /\
  1%r/6%r <= sigma_exp_acceptance_target p <= 1%r /\
  `|sr_actual_probability p-sigma_exp_acceptance_target p| <=
    grb_epsilon*sigma_exp_acceptance_target p.
proof.
  have ha := grb_actual_range p; have hp := grb_actual_positive p.
  have hb := grb_target_range p; have he := grb_relative_error p.
  smt().
qed.

lemma grb_kernel_ratio_bounds (p : BArray26.t) :
  (1%r-grb_epsilon)*sigma_exp_acceptance_target p <= sr_actual_probability p <=
    (1%r+grb_epsilon)*sigma_exp_acceptance_target p.
proof. have h := grb_relative_error p; move: h; rewrite ler_norml; smt(). qed.

lemma grb_normalization_margin :
  2%r*grb_epsilon/(1%r-grb_epsilon) <= 4%r*grb_epsilon /\
  4%r*grb_epsilon < 1%r/549755813888%r.
proof. rewrite /grb_epsilon; smt(). qed.
