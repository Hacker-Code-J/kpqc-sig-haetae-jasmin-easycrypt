require import AllCore IntDiv Real RealExp Distr DInterval.
from Jasmin require import JModel_x86.
require import HyperballTailSpec SigmaRawSpec SigmaRawNoiseSpec SigmaJointSpec
  SigmaRawAcceptanceCorrectness SigmaNoise72Bridge SigmaCDT83Patch
  CDTDistributionBridge HalfGaussianSpec.
import HalfGaussianSpec.

(* Candidate and weights before output rounding. The ideal proposal keeps
   its full infinite CDT support; clipping is a bounded-comparison device. *)
op rsm_z (x y : int) : int = sr_noise_modulus*x+y.
op rsm_square (z : int) : int = z*z %/ ht_q.
op rsm_plus z : real = RealExp.exp (ht_tplus*(rsm_square z)%r/ht_q%r).
op rsm_minus z : real = RealExp.exp (-ht_tminus*(rsm_square z)%r/ht_q%r).
op rsm_gaussian_plus z : real = RealExp.exp (ht_tplus*(z*z)%r/(ht_q*ht_q)%r).
op rsm_gaussian_minus z : real = RealExp.exp (-ht_tminus*(z*z)%r/(ht_q*ht_q)%r).

op rsm_actual (p : BArray26.t) (weight : int -> real) : real =
  E (dinter 0 (cdt83_modulus-1)) (fun u =>
    E sr_noise_uniform (fun y =>
      let candidate = sigma_noise72_patch (sj_cdt83_patch p u) y in
      weight (sr_candidate candidate) * sr_actual_probability candidate)).

op rsm_kernel (weight : int -> real) x y : real =
  weight (rsm_z x y) * sj_acceptance x y.
op rsm_noise_kernel (weight : int -> real) x : real =
  E sr_noise_uniform (fun y => rsm_kernel weight x y).
op rsm_ideal (weight : int -> real) : real =
  E hg16_distr (rsm_noise_kernel weight).
op rsm_clipped_kernel (weight : int -> real) x : real =
  if 0<=x<=166 then rsm_noise_kernel weight x else 0%r.
op rsm_clipped_ideal (weight : int -> real) : real =
  E hg16_distr (rsm_clipped_kernel weight).
