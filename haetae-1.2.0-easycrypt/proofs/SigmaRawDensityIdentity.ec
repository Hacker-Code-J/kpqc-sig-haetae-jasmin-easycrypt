require import AllCore IntDiv StdRing StdOrder RealExp.
from Jasmin require import JModel_x86.
require import SigmaSpec SigmaRawSpec CDTCorrectness HalfGaussianSpec.
import RField RealOrder HalfGaussianSpec.

(* With N=2^72, the independent raw candidate is r=y+N*x. Its
   rejection numerator is the difference of the two integer squares. *)
lemma sr_numerator_square_difference (p : BArray26.t) :
  sr_numerator p = (sr_candidate p)^2 - (sr_noise_modulus * sr_cdt p)^2.
proof.
  rewrite /sr_numerator /sr_candidate !Ring.IntID.expr2; ring.
qed.

(* 2*sigma^2=2^153 for sigma=2^76, and 2^153=512*(2^72)^2.
   Thus the raw exponent is exactly the difference of the Gaussian
   exponents, before any fixed-point rounding or polynomial evaluation. *)
lemma sr_exponent_density_ratio (p : BArray26.t) :
  sr_exponent p =
    ((sr_candidate p)^2)%r / 11417981541647679048466287755595961091061972992%r -
    ((sr_cdt p)^2)%r / 512%r.
proof.
  rewrite /sr_exponent sr_numerator_square_difference !Ring.IntID.expr2.
  rewrite fromintB !fromintM /sr_noise_modulus /=; field; trivial.
qed.

lemma sr_halfgaussian_weight_positive (p : BArray26.t) :
  0%r < hg16_rho (sr_cdt p).
proof.
  have h := cdt_count_range (cdt_lo_input p) (cdt_hi_input p) 166 _;
    first trivial.
  have hx : 0 <= sr_cdt p by rewrite /sr_cdt; smt().
  by rewrite /hg16_rho hx /=; apply RealExp.exp_gt0.
qed.

lemma sr_gaussian_weight_identity (p : BArray26.t) :
  hg16_rho (sr_cdt p) * RealExp.exp (-sr_exponent p) =
    RealExp.exp (-((sr_candidate p)^2)%r /
      11417981541647679048466287755595961091061972992%r).
proof.
  have h := cdt_count_range (cdt_lo_input p) (cdt_hi_input p) 166 _;
    first trivial.
  have hx : 0 <= sr_cdt p by rewrite /sr_cdt; smt().
  rewrite /hg16_rho hx /= -RealExp.expD.
  congr; rewrite sr_exponent_density_ratio !Ring.IntID.expr2; ring.
qed.

lemma sr_gaussian_density_ratio (p : BArray26.t) :
  RealExp.exp (-sr_exponent p) =
    RealExp.exp (-((sr_candidate p)^2)%r /
      11417981541647679048466287755595961091061972992%r) /
    hg16_rho (sr_cdt p).
proof.
  have hp := sr_halfgaussian_weight_positive p.
  rewrite -sr_gaussian_weight_identity; field; smt().
qed.
