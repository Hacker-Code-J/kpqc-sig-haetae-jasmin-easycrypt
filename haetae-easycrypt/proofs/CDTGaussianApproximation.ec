require import AllCore List Distr SDist StdOrder StdRing.
require import CDTDistributionSpec CDTDistribution CDTDistributionBridge
  HalfGaussianSpec HalfGaussianProperties CDTGaussianCertificate
  CDTGaussianEnclosure CDTGaussianTableBridge DistributionIntervalBounds.
import RField RealOrder HalfGaussianSpec HalfGaussianProperties.

(* Independent target: rho(k)=exp(-k^2/512), normalized over all k>=0.
   The implementation distribution is derived from uniform 83-bit input.
   The infinite tail and all finite numeric inequalities are proved, not
   premises of either public approximation theorem below. *)
lemma cdt83_half_gaussian_statistical_distance :
  SDist.sdist (cdt_distribution cdt83_modulus cdt83_thresholds) hg16_distr <
    32%r / gi_input_size%r.
proof.
  have hp := cdt_distribution_lossless cdt83_modulus cdt83_thresholds cdt83_modulus_positive.
  have hps : forall k, k \in cdt_distribution cdt83_modulus cdt83_thresholds => 0 <= k < 256.
  + move=> k hk; move: hk; rewrite cdt83_distribution_support; smt().
  have hqs : forall k, k \in hg16_distr => 0 <= k.
  + move=> k; by rewrite hg16_support.
  have he : forall k, 0 <= k < 256 =>
      `|mu1 (cdt_distribution cdt83_modulus cdt83_thresholds) k - mu1 hg16_distr k| <= gi_error k.
  + move=> k hk; exact (gi_point_error_transport k (mu1 hg16_distr k) hk (gi_pmf_interval k hk)).
  have h := sdist_finite_interval_tail
    (cdt_distribution cdt83_modulus cdt83_thresholds) hg16_distr 256 gi_error
    (gi_tail_probability_upper%r / gi_probability_scale%r)
    hp hg16_distr_ll hps hqs he gi_tail_probability.
  exact (ler_lt_trans _ _ _ h gi_error_budget).
qed.

lemma cdt83_gaussian_error_bound :
  32%r / gi_input_size%r = 1%r / (2^78)%r.
proof.
  have hp : (2^78) = 302231454903657293676544 by ring.
  by rewrite hp /gi_input_size /=.
qed.

(* This procedure really calls the extracted Jasmin CDT function. Uniform
   input is explicit in the experiment, not inferred from SHAKE semantics. *)
lemma uniform83_jasmin_half_gaussian_error (event : int -> bool) &m :
  `|Pr[Uniform83Jasmin.sample() @ &m : event res] - mu hg16_distr event| <
    1%r / (2^78)%r.
proof.
  rewrite uniform83_jasmin_law -cdt83_gaussian_error_bound.
  have h := SDist.sdist_upper_bound
    (cdt_distribution cdt83_modulus cdt83_thresholds) hg16_distr event.
  exact (ler_lt_trans _ _ _ h cdt83_half_gaussian_statistical_distance).
qed.
