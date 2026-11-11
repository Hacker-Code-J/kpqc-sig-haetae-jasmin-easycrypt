require import AllCore IntDiv Real RealExp Distr StdOrder StdRing.
from Jasmin require import JModel_x86.
require import SigmaJointSpec SigmaRawSpec SigmaRawNoiseSpec SigmaRawExponentCorrectness
  SigmaRejection48Bridge SigmaNoise72Bridge SigmaRoundedOutputCorrectness.
import IntOrder RField RealOrder.

lemma sj_raw_exponent_nonnegative x y :
  0 <= x => 0 <= y => 0%r <= sj_raw_exponent x y.
proof.
  move=> hx hy.
  have hn : 0 <= y * (y + 2 * sr_noise_modulus * x) by
    rewrite /sr_noise_modulus; smt().
  rewrite /sj_raw_exponent; smt().
qed.

lemma sj_acceptance_range x y : 0%r <= sj_acceptance x y <= 1%r.
proof.
  rewrite /sj_acceptance.
  case (0 <= x /\ 0 <= y < sr_noise_modulus) => hvalid; last trivial.
  have he0 := sj_raw_exponent_nonnegative x y _ _; first 2 smt().
  have hp := RealExp.exp_gt0 (-sj_raw_exponent x y).
  have hu : RealExp.exp (-sj_raw_exponent x y) <= RealExp.exp 0%r by
    apply RealExp.exp_mono; smt().
  rewrite RealExp.exp0 in hu.
  case (y + sr_noise_modulus * x = 0); smt().
qed.

lemma sj_kernel_range x y (event : int -> bool) :
  0%r <= sj_kernel x y event <= 1%r.
proof.
  have h := sj_acceptance_range x y.
  rewrite /sj_kernel /b2r.
  case (event (sj_round x y)); smt().
qed.

(* Bounded kernels are integrable for arbitrary distributions, including
   the independent Gaussian law with infinite support. *)
lemma sj_unit_interval_hasE (d : int distr) (f : int -> real) :
  (forall x, 0%r <= f x <= 1%r) => hasE d f.
proof.
  move=> hf.
  apply (hasE_le d f (fun (_ : int) => 1%r)).
  + exact (hasEC d 1%r).
  move=> x; have hx := hf x.
  rewrite /= ler_norml; smt().
qed.

lemma sj_unit_interval_expectation (d : int distr) (f : int -> real) :
  (forall x, 0%r <= f x <= 1%r) => 0%r <= E d f <= 1%r.
proof.
  move=> hf.
  have hsum := sj_unit_interval_hasE d f hf.
  have hconstant := hasEC d 1%r.
  have hsub := expB d (fun (_ : int) => 1%r) f hconstant hsum.
  have hnonneg : 0%r <= E d f by
    apply exp_ge0 => x _; have hx := hf x; smt().
  have hgap : 0%r <= E d (fun x => 1%r - f x) by
    apply exp_ge0 => x _; have hx := hf x; smt().
  rewrite hsub expC /= in hgap.
  have hweight := le1_mu d predT.
  smt().
qed.

lemma sj_noise_kernel_range x (event : int -> bool) :
  0%r <= sj_noise_kernel x event <= 1%r.
proof.
  rewrite /sj_noise_kernel; apply sj_unit_interval_expectation => y.
  exact (sj_kernel_range x y event).
qed.

lemma sj_noise_kernel_hasE (d : int distr) (event : int -> bool) :
  hasE d (fun x => sj_noise_kernel x event).
proof.
  apply sj_unit_interval_hasE => x.
  exact (sj_noise_kernel_range x event).
qed.

lemma sj_ideal_joint_range (event : int -> bool) :
  0%r <= sj_ideal_joint event <= 1%r.
proof.
  rewrite /sj_ideal_joint; apply sj_unit_interval_expectation => x.
  exact (sj_noise_kernel_range x event).
qed.

lemma sj_raw_exponent_actual (p : BArray26.t) :
  sj_raw_exponent (sr_cdt p) (sr_noise p) = sr_exponent p.
proof. by rewrite /sj_raw_exponent /sr_exponent /sr_numerator. qed.

(* This evaluates the ideal acceptance weight at the decoded array. It does
   not equate that weight with the implementation's rejection decision. *)
lemma sj_acceptance_actual (p : BArray26.t) :
  sj_acceptance (sr_cdt p) (sr_noise p) = sr_acceptance_target p.
proof.
  have hc := sr_cdt_bounds p.
  have hn := sr_noise_bounds p.
  have hvalid : 0 <= sr_cdt p /\ 0 <= sr_noise p < sr_noise_modulus by smt().
  by rewrite /sj_acceptance hvalid /= sj_raw_exponent_actual
    /sr_acceptance_target /sr_raw_factor /sr_candidate.
qed.

lemma sj_kernel_actual (p : BArray26.t) (event : int -> bool) :
  sj_kernel (sr_cdt p) (sr_noise p) event =
    sr_acceptance_target p * b2r (event (W64.to_uint (sigma_rejection48_rounded p))).
proof.
  by rewrite /sj_kernel sj_acceptance_actual -(sj_actual_rounding p).
qed.

lemma sj_acceptance_noise_patch (p : BArray26.t) y : 0 <= y < sr_noise_modulus =>
  sj_acceptance (sr_cdt p) y = sr_acceptance_target (sigma_noise72_patch p y).
proof.
  move=> hy; have h := sj_acceptance_actual (sigma_noise72_patch p y).
  by move: h; rewrite sigma_noise72_patch_cdt (sigma_noise72_patch_decode p y hy).
qed.

lemma sj_kernel_noise_patch (p : BArray26.t) y (event : int -> bool) :
  0 <= y < sr_noise_modulus =>
  sj_kernel (sr_cdt p) y event =
    sr_acceptance_target (sigma_noise72_patch p y) *
      b2r (event (W64.to_uint (sigma_rejection48_rounded (sigma_noise72_patch p y)))).
proof.
  move=> hy; have h := sj_kernel_actual (sigma_noise72_patch p y) event.
  by move: h; rewrite sigma_noise72_patch_cdt (sigma_noise72_patch_decode p y hy).
qed.

lemma sj_kernel_noise_support (p : BArray26.t) y (event : int -> bool) :
  y \in sr_noise_uniform =>
  sj_kernel (sr_cdt p) y event =
    sr_acceptance_target (sigma_noise72_patch p y) *
      b2r (event (W64.to_uint (sigma_rejection48_rounded (sigma_noise72_patch p y)))).
proof.
  move=> hy; exact (sj_kernel_noise_patch p y event (sigma_noise72_support y hy)).
qed.
