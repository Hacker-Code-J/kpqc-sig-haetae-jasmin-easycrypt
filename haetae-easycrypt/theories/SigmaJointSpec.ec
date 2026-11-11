require import AllCore IntDiv Real RealExp Distr.
require import SigmaRawSpec SigmaRawNoiseSpec HalfGaussianSpec.
import HalfGaussianSpec.

(* Mathematical output rounding. This integer is deliberately unbounded:
   the independent Gaussian CDT target has infinite support. *)
op [opaque] sj_round (x y : int) : int =
  (y + sr_noise_modulus * x + 32768) %/ 65536.

op [opaque] sj_raw_exponent (x y : int) : real =
  (y * (y + 2 * sr_noise_modulus * x))%r /
    11417981541647679048466287755595961091061972992%r.

(* Raw Gaussian acceptance, extended by zero outside the candidate domain.
   Neither machine exponent rounding nor the rounded-zero guard defines it. *)
op [opaque] sj_acceptance (x y : int) : real =
  if 0 <= x /\ 0 <= y < sr_noise_modulus then
    (if y + sr_noise_modulus * x = 0 then 1%r / 2%r else 1%r) *
      RealExp.exp (-sj_raw_exponent x y)
  else 0%r.

op [opaque] sj_kernel (x y : int) (event : int -> bool) : real =
  sj_acceptance x y * b2r (event (sj_round x y)).

op [opaque] sj_noise_kernel (x : int) (event : int -> bool) : real =
  E sr_noise_uniform (fun y => sj_kernel x y event).

(* Joint accepted-output mass, before conditioning on acceptance. *)
op [opaque] sj_ideal_joint (event : int -> bool) : real =
  E hg16_distr (fun x => sj_noise_kernel x event).
