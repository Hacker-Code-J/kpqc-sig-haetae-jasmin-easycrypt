require import AllCore IntDiv Real RealExp Distr DInterval Finite StdRing StdOrder.
from Jasmin require import JModel_x86.
require import ApproxExpSpec SigmaExpInputBounds SigmaExpAcceptanceCorrectness
  SigmaRawAcceptanceCorrectness SigmaRawNoiseSpec SigmaRejection48Bridge
  Rejection48Spec ExponentialLipschitz FiniteExpectationError
  SigmaJointFixedCorrectness SigmaJoint203Bridge SigmaJointIdealCorrectness
  SigmaJointCorrectness SigmaNoise72Bridge SigmaCDT83Patch CDTDistributionBridge.
import RField RealOrder.

lemma sc_quantized_exponential_lower (p : BArray26.t) :
  1%r / 3%r <= RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r)).
proof.
  have hi := sigma_exp_argument_two_thirds p.
  have hr : 3%r * (W64.to_uint (sigma_exp_argument p))%r <=
      2%r * 281474976710656%r.
  + rewrite -!fromintM le_fromint; exact hi.
  have h := exp_neg_linear_lower ((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r).
  rewrite /ae_scale in h; smt().
qed.

(* The zero guard contributes at least one half. The exponential and
   threshold rounding errors are already checked for every input buffer. *)
lemma sc_actual_point_lower (p : BArray26.t) :
  1%r / 7%r <= sr_actual_probability p.
proof.
  have hl := sc_quantized_exponential_lower p.
  have hp := ae_real_probability_range (sigma_exp_argument p).
  have he := sigma_exp_threshold_error p.
  have he' : `|(W64.to_uint (sigma_rejection48_threshold p))%r / 281474976710656%r -
      RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r))| <=
      27%r / ae_scale%r by move: he; rewrite /ae_scale.
  have h := rejection48_probability_error
    (W64.to_uint (sigma_rejection48_threshold p)) (sigma_rejection48_rounded p)
    (RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r)))
    (27%r / ae_scale%r) hp he'.
  rewrite ler_norml in h.
  rewrite /sr_actual_probability.
  move: h; rewrite /rejection48_factor /ae_scale.
  case (sigma_rejection48_rounded p = W64.zero); smt().
qed.

lemma sc_actual_noise_lower (p : BArray26.t) :
  1%r / 7%r <= sj_actual_noise_mass p (fun (_ : int) => true).
proof.
  have hfin : is_finite (Distr.support sr_noise_uniform).
  + rewrite /sr_noise_uniform; apply DInterval.finite_dinter.
  have h := finite_expectation_le sr_noise_uniform (fun _ => 1%r / 7%r)
    (fun y => sr_actual_probability (sigma_noise72_patch p y)) hfin _.
  + move=> y _; exact (sc_actual_point_lower (sigma_noise72_patch p y)).
  rewrite expC sr_noise_uniform_ll /= in h.
  by rewrite /sj_actual_noise_mass /sj_actual_kernel /b2r /=.
qed.

lemma sc_actual_acceptance_lower (p : BArray26.t) &m :
  1%r / 7%r <= Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2].
proof.
  have hfin := DInterval.finite_dinter 0 (cdt83_modulus-1).
  have h := finite_expectation_le (dinter 0 (cdt83_modulus-1))
    (fun _ => 1%r / 7%r)
    (fun u => sj_actual_noise_mass (sj_cdt83_patch p u) (fun (_ : int) => true)) hfin _.
  + move=> u _; exact (sc_actual_noise_lower (sj_cdt83_patch p u)).
  rewrite expC sj203_uniform_ll /= in h.
  have /= hlaw := sj_actual203_law p (fun (_ : int) => true) &m.
  by rewrite hlaw.
qed.

(* Transfer the lower bound through the checked joint-event comparison;
   no truncation of the ideal Gaussian's infinite CDT support is introduced. *)
lemma sc_ideal_acceptance_lower &m :
  1%r / 8%r <= Pr[SigmaJointIdeal.sample() @ &m : res.`2].
proof.
  have ha := sc_actual_acceptance_lower witness &m.
  have [_ he] := sj_joint_output_error_strict witness (fun (_ : int) => true) &m.
  move: he; rewrite /= ltr_norml; smt().
qed.
