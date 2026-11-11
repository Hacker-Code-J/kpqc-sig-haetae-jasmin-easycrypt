require import AllCore Real Distr DInterval Finite StdRing StdOrder.
require import SigmaRawSpec SigmaRawNoiseSpec SigmaRawAcceptanceCorrectness
  SigmaNoise72Bridge FiniteExpectationError Rejection48Spec SigmaRejection48Bridge.
import RField RealOrder.

(* Average the independently defined raw Gaussian acceptance rule over the
   same explicit 72-bit noise law as the actual single-attempt experiment. *)
op [opaque] sr_average_target (p : BArray26.t) : real =
  E sr_noise_uniform (fun y => sr_acceptance_target (sigma_noise72_patch p y)).

lemma sr_average_actual_probability (p : BArray26.t) &m :
  Pr[SigmaNoise72Experiment.sample(p) @ &m : res] =
    E sr_noise_uniform (fun y => sr_actual_probability (sigma_noise72_patch p y)).
proof. by rewrite sigma_noise72_actual_probability /sr_actual_probability. qed.

lemma sr_average_target_range (p : BArray26.t) :
  0%r <= sr_average_target p <= 1%r.
proof.
  have hfin : is_finite (Distr.support sr_noise_uniform).
  + rewrite /sr_noise_uniform; apply DInterval.finite_dinter.
  have hlo := finite_expectation_le sr_noise_uniform (fun _ => 0%r)
    (fun y => sr_acceptance_target (sigma_noise72_patch p y)) hfin _.
  + move=> y hy; have := sr_acceptance_target_range (sigma_noise72_patch p y); smt().
  have hhi := finite_expectation_le sr_noise_uniform
    (fun y => sr_acceptance_target (sigma_noise72_patch p y)) (fun _ => 1%r) hfin _.
  + move=> y hy; have := sr_acceptance_target_range (sigma_noise72_patch p y); smt().
  rewrite expC sr_noise_uniform_ll /= in hlo.
  rewrite expC sr_noise_uniform_ll /= in hhi.
  rewrite /sr_average_target; smt().
qed.

lemma sr_average_acceptance_error (p : BArray26.t) &m :
  `|Pr[SigmaNoise72Experiment.sample(p) @ &m : res] - sr_average_target p| <=
    sr_regular_error +
      (if sr_cdt p = 0 then 32767%r / 9444732965739290427392%r else 0%r).
proof.
  have hfin : is_finite (Distr.support sr_noise_uniform).
  + rewrite /sr_noise_uniform; apply DInterval.finite_dinter.
  have he : 0%r <= sr_regular_error by rewrite /sr_regular_error /sr_scale; smt().
  have hp : forall y, y \in sr_noise_uniform =>
    `|sr_actual_probability (sigma_noise72_patch p y) -
      sr_acceptance_target (sigma_noise72_patch p y)| <=
        sr_regular_error + (1%r/2%r) * b2r (sr_noise_mismatch (sr_cdt p) y).
  + move=> y hy.
    have hyr : 0 <= y < sr_noise_modulus by
      move: hy; rewrite sr_noise_uniform_support /sr_noise_modulus.
    have h := sr_acceptance_error (sigma_noise72_patch p y).
    rewrite (sigma_noise72_patch_mismatch p y hyr) in h.
    move: h; rewrite /b2r; case (sr_noise_mismatch (sr_cdt p) y); smt().
  have h := finite_expectation_error sr_noise_uniform
    (fun y => sr_actual_probability (sigma_noise72_patch p y))
    (fun y => sr_acceptance_target (sigma_noise72_patch p y))
    (fun y => sr_noise_mismatch (sr_cdt p) y)
    sr_regular_error (1%r/2%r) hfin sr_noise_uniform_ll he _ hp;
    first smt().
  rewrite sr_noise_half_effect in h.
  by rewrite sr_average_actual_probability /sr_average_target.
qed.

lemma sr_average_acceptance_error_strict (p : BArray26.t) &m :
  `|Pr[SigmaNoise72Experiment.sample(p) @ &m : res] - sr_average_target p| <
    29%r / sr_scale%r /\
  `|Pr[SigmaNoise72Experiment.sample(p) @ &m : res] - sr_average_target p| <
    1%r / (2^43)%r.
proof.
  have he := sr_average_acceptance_error p &m.
  have hpow : 2^43 = 8796093022208 by ring.
  rewrite hpow /sr_scale.
  move: he; rewrite /sr_regular_error /sr_scale.
  case (sr_cdt p = 0); smt().
qed.
