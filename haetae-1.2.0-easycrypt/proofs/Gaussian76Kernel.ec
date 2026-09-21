require import AllCore IntDiv Real RealExp Distr DInterval StdOrder StdRing.
require import Gaussian76Spec SigmaRawSpec SigmaRawNoiseSpec SigmaJointSpec
  HalfGaussianSpec HalfGaussianProperties.
import IntOrder RField RealOrder HalfGaussianSpec HalfGaussianProperties.

lemma g76_noise_scale_positive : 0%r < sr_noise_modulus%r.
proof. by rewrite /sr_noise_modulus. qed.

lemma g76_proposal_normalizer_positive :
  0%r < sr_noise_modulus%r * hg16_normalizer.
proof.
  apply mulr_gt0; first exact g76_noise_scale_positive.
  exact hg16_normalizer_pos.
qed.

lemma g76_proposal_normalizer_nonzero :
  sr_noise_modulus%r * hg16_normalizer <> 0%r.
proof. have := g76_proposal_normalizer_positive; smt(). qed.

(* N=2^72 and 512*N^2=2^153. This is an identity over unbounded
   mathematical coordinates, without a CDT-table or machine-word cutoff. *)
lemma g76_exponent_cancellation x y :
  -(x*x)%r / 512%r + (-sj_raw_exponent x y) =
    -((sr_noise_modulus*x+y)*(sr_noise_modulus*x+y))%r / g76_denominator%r.
proof.
  rewrite /sj_raw_exponent /sr_noise_modulus /g76_denominator
    !fromintM !fromintD !fromintM.
  field; trivial.
qed.

lemma g76_rho_product x y :
  RealExp.exp (-(x*x)%r / 512%r) * RealExp.exp (-sj_raw_exponent x y) =
    g76_rho (sr_noise_modulus*x+y).
proof.
  rewrite -RealExp.expD /g76_rho.
  congr; exact (g76_exponent_cancellation x y).
qed.

lemma g76_gaussian_cancellation x y :
  0 <= x => 0 <= y < sr_noise_modulus =>
  hg16_rho x * sj_acceptance x y = g76_accept_weight (sr_noise_modulus*x+y).
proof.
  move=> hx hy.
  have hvalid : 0 <= x /\ 0 <= y < sr_noise_modulus by smt().
  have hz : 0 <= sr_noise_modulus*x+y by
    move: hy; rewrite /sr_noise_modulus; smt().
  have hcomm : y + sr_noise_modulus*x = sr_noise_modulus*x+y by ring.
  rewrite /hg16_rho hx /sj_acceptance hvalid /g76_accept_weight hz /= hcomm.
  rewrite -(g76_rho_product x y).
  ring.
qed.

lemma g76_rounding_identity x y :
  sj_round x y = g76_round_magnitude (sr_noise_modulus*x+y).
proof.
  have hcomm : y + sr_noise_modulus*x = sr_noise_modulus*x+y by ring.
  by rewrite /sj_round /g76_round_magnitude hcomm.
qed.

lemma g76_event_kernel x y (event : int -> bool) :
  0 <= x => 0 <= y < sr_noise_modulus =>
  hg16_rho x * sj_kernel x y event =
    g76_accept_weight (sr_noise_modulus*x+y) *
      b2r (event (g76_round_magnitude (sr_noise_modulus*x+y))).
proof.
  move=> hx hy.
  by rewrite /sj_kernel mulrA (g76_gaussian_cancellation x y hx hy)
    g76_rounding_identity.
qed.

lemma g76_noise_mu1 y : 0 <= y < sr_noise_modulus =>
  mu1 sr_noise_uniform y = 1%r / sr_noise_modulus%r.
proof.
  move=> hy.
  have hvalid : 0 <= y <= 4722366482869645213695 by
    move: hy; rewrite /sr_noise_modulus; smt().
  by rewrite /sr_noise_uniform DInterval.dinter1E hvalid /sr_noise_modulus /=.
qed.

lemma g76_full_contribution x y (event : int -> bool) :
  mu1 hg16_distr x * mu1 sr_noise_uniform y * sj_kernel x y event =
    inv (sr_noise_modulus%r * hg16_normalizer) *
      (if 0 <= x /\ 0 <= y < sr_noise_modulus then
         g76_accept_weight (sr_noise_modulus*x+y) *
           b2r (event (g76_round_magnitude (sr_noise_modulus*x+y)))
       else 0%r).
proof.
  case (0 <= x /\ 0 <= y < sr_noise_modulus) => hvalid.
  + have [hx hy] := hvalid.
    have hn : sr_noise_modulus%r <> 0%r by have := g76_noise_scale_positive; smt().
    have hh : hg16_normalizer <> 0%r by have := hg16_normalizer_pos; smt().
    have hnorm := g76_proposal_normalizer_nonzero.
    rewrite hg16_mu1 /hg16_pmf (g76_noise_mu1 y hy).
    rewrite -(g76_event_kernel x y event hx hy).
    field; smt().
  by rewrite /sj_kernel /sj_acceptance hvalid /=.
qed.
