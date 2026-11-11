require import AllCore IntDiv Real RealSeries Distr StdRing StdOrder.
require import RawSquareMomentSpec SigmaRawSpec SigmaRawNoiseSpec SigmaJointSpec
  Gaussian76Spec Gaussian76Properties Gaussian76Folding Gaussian76Kernel
  Gaussian76Identification GaussianBlockReindex HalfGaussianSpec HalfGaussianProperties
  SigmaConditionalSpec.
import RField RealOrder HalfGaussianSpec HalfGaussianProperties.

op rsi_clip (weight : int -> real) z : real =
  if 0<=z<167*sr_noise_modulus then weight z else 0%r.

lemma rsi_rho_summable (weight : int -> real) : hasE g76_distr weight =>
  RealSeries.summable (fun z => g76_rho z * weight z).
proof.
  move=> hE; have hz := g76_normalizer_positive.
  have hs := RealSeries.summableZ
    (fun z => weight z * mu1 g76_distr z) g76_normalizer hE.
  apply (RealSeries.eqL_summable _ _ hs) => z /=.
  rewrite g76_distr_mu1 /g76_pmf; field; smt().
qed.

lemma rsi_rho_expectation (weight : int -> real) :
  RealSeries.sum (fun z => g76_rho z * weight z) = g76_normalizer * E g76_distr weight.
proof.
  rewrite /E -RealSeries.sumZ.
  apply RealSeries.eq_sum => z /=.
  rewrite g76_distr_mu1 /g76_pmf.
  have hz := g76_normalizer_positive; field; smt().
qed.

lemma rsi_accept_summable (weight : int -> real) : hasE g76_distr weight =>
  RealSeries.summable (fun z => g76_accept_weight z * weight z).
proof.
  move=> hE; have hs := rsi_rho_summable weight hE.
  have hf := g76_fold_summable (fun z => g76_rho z * weight z) hs.
  have hh := RealSeries.summableZ _ (1%r/2%r) hf.
  apply (RealSeries.eqL_summable _ _ hh) => z /=.
  rewrite /g76_accept_weight; case (0<=z); case (z=0); smt().
qed.

lemma rsi_accept_expectation (weight : int -> real) : hasE g76_distr weight =>
  (forall z, weight (-z)=weight z) =>
  RealSeries.sum (fun z => g76_accept_weight z * weight z) =
    (g76_normalizer/2%r) * E g76_distr weight.
proof.
  move=> hE heven; have hs := rsi_rho_summable weight hE.
  have he : forall z, g76_rho (-z)*weight (-z)=g76_rho z*weight z by
    move=> z; rewrite g76_rho_symmetry heven.
  have hfold := g76_even_sum_fold (fun z => g76_rho z * weight z) hs he.
  have htwo : (fun z =>
      if 0<=z then (if z=0 then 1%r else 2%r)*(g76_rho z*weight z) else 0%r) =
    (fun z => 2%r * (g76_accept_weight z * weight z)).
  + apply fun_ext => z /=.
    rewrite /g76_accept_weight; case (0<=z); case (z=0); smt().
  have hfinal := hfold.
  rewrite htwo RealSeries.sumZ rsi_rho_expectation in hfinal; smt().
qed.

lemma rsi_full_contribution (weight : int -> real) x y :
  mu1 hg16_distr x * mu1 sr_noise_uniform y * rsm_kernel weight x y =
    inv (sr_noise_modulus%r * hg16_normalizer) *
      (if 0<=x /\ 0<=y<sr_noise_modulus then
        g76_accept_weight (sr_noise_modulus*x+y)*weight (sr_noise_modulus*x+y) else 0%r).
proof.
  have h := g76_full_contribution x y (fun _ => true).
  rewrite /sj_kernel /b2r /= in h.
  rewrite /rsm_kernel /rsm_z.
  case (0<=x /\ 0<=y<sr_noise_modulus); smt().
qed.

lemma rsi_ideal_formula (weight : int -> real) :
  RealSeries.summable (fun z => g76_accept_weight z * weight z) =>
  rsm_ideal weight = RealSeries.sum (fun z => g76_accept_weight z * weight z) /
    (sr_noise_modulus%r * hg16_normalizer).
proof.
  move=> hs; pose f := fun z => g76_accept_weight z * weight z.
  have hneg : forall z, z<0 => f z=0%r by
    move=> z hz; rewrite /f (g76_accept_weight_negative z hz).
  have hn : 0<sr_noise_modulus by rewrite /sr_noise_modulus.
  have hjoint : rsm_ideal weight = RealSeries.sum (fun x => RealSeries.sum (fun y =>
      mu1 hg16_distr x * mu1 sr_noise_uniform y * rsm_kernel weight x y)).
  + rewrite /rsm_ideal /rsm_noise_kernel /E.
    apply RealSeries.eq_sum => x /=.
    rewrite -RealSeries.sumZr; apply RealSeries.eq_sum => y /=; ring.
  have he : rsm_ideal weight =
    inv (sr_noise_modulus%r * hg16_normalizer) *
    RealSeries.sum (fun x => RealSeries.sum (fun y =>
      if 0<=x /\ 0<=y<sr_noise_modulus then f (sr_noise_modulus*x+y) else 0%r)).
  + rewrite hjoint -(RealSeries.sumZ (fun x => RealSeries.sum (fun y =>
      if 0<=x /\ 0<=y<sr_noise_modulus then f (sr_noise_modulus*x+y) else 0%r))
      (inv (sr_noise_modulus%r * hg16_normalizer))).
    apply RealSeries.eq_sum => x /=.
    rewrite -(RealSeries.sumZ (fun y =>
      if 0<=x /\ 0<=y<sr_noise_modulus then f (sr_noise_modulus*x+y) else 0%r)
      (inv (sr_noise_modulus%r * hg16_normalizer))).
    apply RealSeries.eq_sum => y /=.
    exact (rsi_full_contribution weight x y).
  rewrite he (gb_block_sum sr_noise_modulus f hn hs hneg) /f; ring.
qed.

lemma rsi_ideal_expectation (weight : int -> real) : hasE g76_distr weight =>
  (forall z, weight (-z)=weight z) =>
  rsm_ideal weight = mu sc_ideal_pair sc_accepted * E g76_distr weight.
proof.
  move=> hE he.
  rewrite (rsi_ideal_formula weight (rsi_accept_summable weight hE))
    (rsi_accept_expectation weight hE he) g76_ideal_acceptance_formula.
  have hn := g76_proposal_normalizer_nonzero; field; smt().
qed.

lemma rsi_clip_domain x y : 0<=y<sr_noise_modulus =>
  (0<=sr_noise_modulus*x+y<167*sr_noise_modulus) = (0<=x<=166).
proof. rewrite /sr_noise_modulus; smt(). qed.

lemma rsi_clipped_ideal (weight : int -> real) :
  rsm_clipped_ideal weight = rsm_ideal (rsi_clip weight).
proof.
  rewrite /rsm_clipped_ideal /rsm_ideal; apply eq_exp => x hx /=.
  rewrite /rsm_clipped_kernel /rsm_noise_kernel.
  case (0<=x<=166) => hc /=.
  + apply eq_exp => y hy /=.
    have hyr : 0<=y<sr_noise_modulus by
      move: hy; rewrite sr_noise_uniform_support /sr_noise_modulus.
    by rewrite /rsm_kernel /rsi_clip /rsm_z (rsi_clip_domain x y hyr) hc.
  have hz : E sr_noise_uniform (fun _ => 0%r)=0%r by rewrite expC.
  rewrite -hz; apply eq_exp => y hy /=.
  have hyr : 0<=y<sr_noise_modulus by
    move: hy; rewrite sr_noise_uniform_support /sr_noise_modulus.
  by rewrite /rsm_kernel /rsi_clip /rsm_z (rsi_clip_domain x y hyr) hc.
qed.

(* Only the numerator is clipped. The full ideal acceptance denominator
   remains available through rsi_ideal_expectation. *)
lemma rsi_clipped_upper (weight major : int -> real) :
  hasE g76_distr major => (forall z, major (-z)=major z) =>
  (forall z, 0%r<=major z) =>
  (forall z, 0<=z<167*sr_noise_modulus => 0%r<=weight z<=major z) =>
  rsm_clipped_ideal weight <= mu sc_ideal_pair sc_accepted * E g76_distr major.
proof.
  move=> hE he hpos hdom.
  have hs := rsi_accept_summable major hE.
  have hpoint : forall z, 0%r<=g76_accept_weight z*rsi_clip weight z <=
      g76_accept_weight z*major z.
  + move=> z; have ha := g76_accept_weight_ge0 z; have hm := hpos z.
    rewrite /rsi_clip; case (0<=z<167*sr_noise_modulus) => hz /=; last smt().
    have hw := hdom z hz; smt().
  have hclip : RealSeries.summable (fun z => g76_accept_weight z*rsi_clip weight z).
  + apply (RealSeries.summable_le (fun z => g76_accept_weight z*major z) _ hs) => z /=.
    have hp := hpoint z; rewrite !ger0_norm; smt().
  have hsum := RealSeries.ler_sum_pos _ _ hpoint hs.
  rewrite rsi_clipped_ideal (rsi_ideal_formula _ hclip).
  rewrite -(rsi_ideal_expectation major hE he) (rsi_ideal_formula _ hs).
  have hd := g76_proposal_normalizer_positive; smt().
qed.
