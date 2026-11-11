require import AllCore Real Distr DInterval Finite StdRing StdOrder.
from Jasmin require import JModel_x86.
require import SigmaJointSpec SigmaJointKernelCorrectness SigmaJointAttemptBridge
  SigmaRawSpec SigmaRawNoiseSpec SigmaRawAcceptanceCorrectness
  SigmaNoise72Bridge SigmaRejection48Bridge FiniteExpectationError.
import RField RealOrder.

op [opaque] sj_actual_kernel (p : BArray26.t) (event : int -> bool) : real =
  b2r (event (W64.to_uint (sigma_rejection48_rounded p))) * sr_actual_probability p.

op [opaque] sj_actual_noise_mass (p : BArray26.t) (event : int -> bool) : real =
  E sr_noise_uniform (fun y => sj_actual_kernel (sigma_noise72_patch p y) event).

op sj_word_error : real =
  sr_regular_error + 32767%r / 9444732965739290427392%r.

(* The output event is applied before averaging. A scalar acceptance-rate
   bound alone would not justify this statement for every output set. *)
lemma sj_point_error (p : BArray26.t) (event : int -> bool) :
  `|sj_actual_kernel p event - sj_kernel (sr_cdt p) (sr_noise p) event| <=
    sr_regular_error + (if sr_zero_mismatch p then 1%r/2%r else 0%r).
proof.
  have h := sr_acceptance_error p.
  have h0 : 0%r <= sr_regular_error by rewrite /sr_regular_error /sr_scale; smt().
  rewrite /sj_actual_kernel sj_kernel_actual /b2r.
  case (event (W64.to_uint (sigma_rejection48_rounded p))) => he /=; smt().
qed.

lemma sj_fixed_actual_law (p : BArray26.t) (event : int -> bool) &m :
  Pr[SigmaJointNoise72.sample(p) @ &m : res.`2 /\ event res.`1] =
    sj_actual_noise_mass p event.
proof. by rewrite sigma_joint_noise72_law /sj_actual_noise_mass /sj_actual_kernel. qed.

lemma sj_fixed_mean_error (p : BArray26.t) (event : int -> bool) :
  `|sj_actual_noise_mass p event - sj_noise_kernel (sr_cdt p) event| <=
    sr_regular_error +
      (if sr_cdt p = 0 then 32767%r / 9444732965739290427392%r else 0%r).
proof.
  have hfin : is_finite (Distr.support sr_noise_uniform).
  + rewrite /sr_noise_uniform; apply DInterval.finite_dinter.
  have he : 0%r <= sr_regular_error by rewrite /sr_regular_error /sr_scale; smt().
  have hp : forall y, y \in sr_noise_uniform =>
    `|sj_actual_kernel (sigma_noise72_patch p y) event - sj_kernel (sr_cdt p) y event| <=
      sr_regular_error + (1%r/2%r) * b2r (sr_noise_mismatch (sr_cdt p) y).
  + move=> y hy.
    have hyr : 0 <= y < sr_noise_modulus by
      move: hy; rewrite sr_noise_uniform_support /sr_noise_modulus.
    have h := sj_point_error (sigma_noise72_patch p y) event.
    rewrite sigma_noise72_patch_cdt (sigma_noise72_patch_decode p y hyr)
      (sigma_noise72_patch_mismatch p y hyr) in h.
    move: h; rewrite /b2r; case (sr_noise_mismatch (sr_cdt p) y); smt().
  have h := finite_expectation_error sr_noise_uniform
    (fun y => sj_actual_kernel (sigma_noise72_patch p y) event)
    (fun y => sj_kernel (sr_cdt p) y event)
    (fun y => sr_noise_mismatch (sr_cdt p) y)
    sr_regular_error (1%r/2%r) hfin sr_noise_uniform_ll he _ hp;
    first smt().
  rewrite sr_noise_half_effect in h.
  by rewrite /sj_actual_noise_mass /sj_noise_kernel.
qed.

lemma sj_fixed_uniform_error (p : BArray26.t) (event : int -> bool) :
  `|sj_actual_noise_mass p event - sj_noise_kernel (sr_cdt p) event| <= sj_word_error.
proof.
  have h := sj_fixed_mean_error p event.
  move: h; rewrite /sj_word_error; case (sr_cdt p = 0); smt().
qed.

lemma sj_word_error_margin :
  0%r <= sj_word_error /\ sj_word_error < 29%r / sr_scale%r.
proof. rewrite /sj_word_error /sr_regular_error /sr_scale; smt(). qed.

lemma sj_fixed_joint_error (p : BArray26.t) (event : int -> bool) &m :
  `|Pr[SigmaJointNoise72.sample(p) @ &m : res.`2 /\ event res.`1] -
    sj_noise_kernel (sr_cdt p) event| <= sj_word_error.
proof. by rewrite sj_fixed_actual_law; apply sj_fixed_uniform_error. qed.
