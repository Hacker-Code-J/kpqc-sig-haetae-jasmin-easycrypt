require import AllCore IntDiv Real RealExp RealSeries Distr StdRing StdOrder.
require import GaussianLatticeSum Gaussian76Spec Gaussian76Properties Gaussian76Folding
  Gaussian76Identification SigmaRawSpec SigmaConditionalSpec
  HalfGaussianSpec HalfGaussianProperties GaussianAcceptanceConstants.
import RField RealOrder HalfGaussianSpec HalfGaussianProperties.

lemma gai_half_negative k : k < 0 => g76_half_rho k = 0%r.
proof. rewrite /g76_half_rho; smt(). qed.

lemma gai_half_decreasing i j : 0 <= i <= j => g76_half_rho j <= g76_half_rho i.
proof.
  move=> hij.
  have hi : 0 <= i by smt().
  have hj : 0 <= j by smt().
  rewrite /g76_half_rho hi hj /= /g76_rho.
  apply RealExp.exp_mono.
  have hs : i*i <= j*j by smt().
  rewrite /g76_denominator; smt().
qed.

(* Every 2^72-th point of the fine Gaussian is exactly the sigma16
   proposal weight. This identity includes the zero and negative cases. *)
lemma gai_coarse_stride : gls_stride g76_half_rho sr_noise_modulus = hg16_rho.
proof.
  apply fun_ext => k; rewrite /gls_stride /g76_half_rho /hg16_rho.
  case (0 <= k) => hk /=; last trivial.
  have hnk : 0 <= sr_noise_modulus*k by rewrite /sr_noise_modulus; smt().
  rewrite hnk /= /g76_rho /sr_noise_modulus /g76_denominator !fromintM /=.
  congr; field; trivial.
qed.

lemma gai_fine_half_sum :
  RealSeries.sum g76_half_rho = g76_normalizer/2%r + 1%r/2%r.
proof.
  have hhalf := RealSeries.sumD1 g76_half_rho 0 g76_half_summable.
  have hraw := RealSeries.sumD1 g76_accept_weight 0 g76_accept_weight_summable.
  have hzero : g76_half_rho 0 = 1%r by rewrite /g76_half_rho /= g76_rho0.
  have hrawzero : g76_accept_weight 0 = 1%r/2%r by
    rewrite /g76_accept_weight /= g76_rho0.
  have he : RealSeries.sum (fun k => if k<>0 then g76_accept_weight k else 0%r) =
      RealSeries.sum (fun k => if k<>0 then g76_half_rho k else 0%r).
  + apply RealSeries.eq_sum => k /=.
    rewrite /g76_accept_weight /g76_half_rho.
    case (k<>0); case (0<=k); smt().
  move: hhalf hraw.
  rewrite hzero hrawzero he g76_accept_weight_sum.
  smt().
qed.

lemma gai_normalizer_block_lower :
  sr_noise_modulus%r * (hg16_normalizer-1%r) + 1%r/2%r <= g76_normalizer/2%r.
proof.
  have hn : 0 < sr_noise_modulus by rewrite /sr_noise_modulus.
  have h := gls_sum_bounds g76_half_rho sr_noise_modulus hn
    g76_half_summable gai_half_negative gai_half_decreasing.
  rewrite gai_coarse_stride -/(hg16_normalizer) gai_fine_half_sum
    /g76_half_rho /= g76_rho0 fromintB /= in h.
  smt().
qed.

(* The one-half treatment of the raw zero is already present in the exact
   ideal-acceptance formula. No integral estimate or acceptance premise is used. *)
lemma gai_ideal_acceptance_normalizer_lower :
  1%r-1%r/hg16_normalizer <= mu sc_ideal_pair sc_accepted.
proof.
  have hh := hg16_normalizer_pos.
  have hb := gai_normalizer_block_lower.
  have hn : 0%r < sr_noise_modulus%r by rewrite /sr_noise_modulus.
  have hd : 0%r < 2%r*(sr_noise_modulus%r*hg16_normalizer) by smt().
  rewrite g76_ideal_acceptance_formula (ler_pdivl_mulr _ _ _ hd).
  have he : (1%r-1%r/hg16_normalizer)*(2%r*(sr_noise_modulus%r*hg16_normalizer)) =
      2%r*sr_noise_modulus%r*(hg16_normalizer-1%r) by field; smt().
  rewrite he; smt().
qed.

lemma gai_ideal_acceptance_39_41 :
  39%r/41%r <= mu sc_ideal_pair sc_accepted.
proof.
  have hh := gac_normalizer_lower.
  have hp := hg16_normalizer_pos.
  have hi : 1%r/hg16_normalizer <= 2%r/41%r.
  + rewrite (ler_pdivr_mulr _ _ _ hp); smt().
  have h := gai_ideal_acceptance_normalizer_lower.
  smt().
qed.

lemma gai_ideal_acceptance_lower :
  951%r/1000%r <= mu sc_ideal_pair sc_accepted.
proof. have h := gai_ideal_acceptance_39_41; smt(). qed.
