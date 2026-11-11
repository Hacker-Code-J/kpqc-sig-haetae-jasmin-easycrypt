require import AllCore IntDiv Real Distr DInterval Finite SDist StdRing StdOrder.
from Jasmin require import JModel_x86.
require import RawSquareMomentSpec HyperballTailSpec SigmaRawSpec SigmaRawNoiseSpec
  SigmaRawExponentCorrectness SigmaRawAcceptanceCorrectness SigmaNoise72Bridge
  SigmaCDT83Patch SigmaJointSpec SigmaJointKernelCorrectness SigmaJointFixedCorrectness
  SigmaJointCorrectness SigmaJoint203Bridge SigmaJointIdealCorrectness SigmaAcceptanceLowerBound
  FiniteExpectationError DistributionExpectationDistance CDTDistributionSpec
  CDTDistributionBridge CDTGaussianApproximation HalfGaussianSpec.
import RField RealOrder HalfGaussianSpec.

op rsa_noise_actual (p : BArray26.t) (weight : int -> real) : real =
  E sr_noise_uniform (fun y =>
    weight (sr_candidate (sigma_noise72_patch p y)) *
      sr_actual_probability (sigma_noise72_patch p y)).
op rsa_cdt_mean (weight : int -> real) : real =
  E (cdt_distribution cdt83_modulus cdt83_thresholds) (rsm_noise_kernel weight).

lemma rsa_hasE_bounded ['a] (d : 'a distr) (f : 'a -> real) W :
  0%r <= W => (forall x, 0%r <= f x <= W) => hasE d f.
proof.
  move=> hW hf; apply (hasE_le d f (fun _ => W)); first exact (hasEC d W).
  move=> x; have hx := hf x.
  rewrite /= !ger0_norm 1..2:/#; smt().
qed.

lemma rsa_expectation_distance_scaled ['a] (d1 d2 : 'a distr) (f : 'a -> real) W :
  0%r <= W => (forall x, 0%r <= f x <= W) =>
  `|E d1 f-E d2 f| <= W*sdist d1 d2.
proof.
  move=> hW hf; case (W=0%r) => hz.
  + have he : f = (fun _ => 0%r) by apply fun_ext => x; have h := hf x; smt().
    by rewrite he !expC hz /=.
  have hp : 0%r < W by smt().
  have hn : forall x, 0%r <= f x/W <= 1%r.
  + move=> x; have hx := hf x; split.
    - apply divr_ge0; smt().
    rewrite ler_pdivr_mulr 1:hp /=; smt().
  have hdist := distribution_expectation_distance_global d1 d2 (fun x => f x/W) hn.
  have he : f = (fun x => W*(f x/W)) by apply fun_ext => x; field; smt().
  rewrite he !expZ -mulrBr normrM (ger0_norm W hW).
  exact (ler_wpmul2l W hW _ _ hdist).
qed.

lemma rsa_candidate_window x y : 0 <= x <= 166 => 0 <= y < sr_noise_modulus =>
  0 <= rsm_z x y < 167*sr_noise_modulus.
proof. rewrite /rsm_z /sr_noise_modulus; smt(). qed.

lemma rsa_candidate_bounds (p : BArray26.t) :
  0 <= sr_candidate p < 167*sr_noise_modulus.
proof.
  have hn := sr_noise_bounds p; have hx := sr_cdt_bounds p.
  rewrite /sr_candidate /sr_noise_modulus.
  move: hn; rewrite /sr_noise_modulus; smt().
qed.

lemma rsa_patch_candidate (p : BArray26.t) y : 0 <= y < sr_noise_modulus =>
  sr_candidate (sigma_noise72_patch p y) = rsm_z (sr_cdt p) y.
proof.
  move=> hy; rewrite /sr_candidate (sigma_noise72_patch_decode p y hy)
    sigma_noise72_patch_cdt /rsm_z; ring.
qed.

lemma rsa_regular_error_nonnegative : 0%r <= sr_regular_error.
proof. rewrite /sr_regular_error /sr_scale; smt(). qed.

lemma rsa_point_weighted_error (p : BArray26.t) (w W : real) : 0%r <= w <= W =>
  `|w*sr_actual_probability p-w*sr_acceptance_target p| <=
    W*sr_regular_error+(W/2%r)*b2r (sr_zero_mismatch p).
proof.
  move=> [hw0 hwW].
  have h := sr_acceptance_error p.
  have he0 : 0%r <= sr_regular_error+(if sr_zero_mismatch p then 1%r/2%r else 0%r)
    by have := rsa_regular_error_nonnegative; smt().
  have hs := ler_wpmul2l w hw0 _ _ h.
  have hc := ler_wpmul2r
    (sr_regular_error+(if sr_zero_mismatch p then 1%r/2%r else 0%r)) he0 w W hwW.
  have hb := ler_trans _ _ _ hs hc.
  rewrite -mulrBr normrM (ger0_norm w hw0).
  move: hb; rewrite /b2r; case (sr_zero_mismatch p); smt().
qed.

lemma rsa_fixed_noise_error (p : BArray26.t) (weight : int -> real) W :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  `|rsa_noise_actual p weight-rsm_noise_kernel weight (sr_cdt p)| <= W*sj_word_error.
proof.
  move=> hW hw.
  have hfin : is_finite (Distr.support sr_noise_uniform) by
    rewrite /sr_noise_uniform; apply finite_dinter.
  have hreg := rsa_regular_error_nonnegative.
  have heps : 0%r <= W*sr_regular_error by apply mulr_ge0.
  have hcost : 0%r <= W/2%r by smt().
  have hp : forall y, y \in sr_noise_uniform =>
    `|weight (sr_candidate (sigma_noise72_patch p y))*
        sr_actual_probability (sigma_noise72_patch p y)-rsm_kernel weight (sr_cdt p) y| <=
      W*sr_regular_error+(W/2%r)*b2r (sr_noise_mismatch (sr_cdt p) y).
  + move=> y hy; have hyr := sigma_noise72_support y hy.
    have hc := rsa_candidate_bounds (sigma_noise72_patch p y).
    have h := rsa_point_weighted_error (sigma_noise72_patch p y)
      (weight (sr_candidate (sigma_noise72_patch p y))) W (hw _ hc).
    rewrite /rsm_kernel -(rsa_patch_candidate p y hyr) (sj_acceptance_noise_patch p y hyr).
    by move: h; rewrite (sigma_noise72_patch_mismatch p y hyr).
  have h := finite_expectation_error sr_noise_uniform
    (fun y => weight (sr_candidate (sigma_noise72_patch p y))*
      sr_actual_probability (sigma_noise72_patch p y))
    (fun y => rsm_kernel weight (sr_cdt p) y)
    (fun y => sr_noise_mismatch (sr_cdt p) y)
    (W*sr_regular_error) (W/2%r) hfin sr_noise_uniform_ll heps hcost hp.
  have hh : (1%r/2%r)*mu sr_noise_uniform (fun y => sr_noise_mismatch (sr_cdt p) y) <=
      32767%r/9444732965739290427392%r.
  + rewrite sr_noise_half_effect; case (sr_cdt p=0); smt().
  have hm := ler_wpmul2l W hW _ _ hh.
  rewrite /rsa_noise_actual /rsm_noise_kernel /sj_word_error; smt().
qed.

lemma rsa_kernel_range (weight : int -> real) W x y :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  0 <= x <= 166 => 0 <= y < sr_noise_modulus =>
  0%r <= rsm_kernel weight x y <= W.
proof.
  move=> hW hw hx hy.
  have hz := rsa_candidate_window x y hx hy.
  have hweight := hw (rsm_z x y) hz.
  have ha := sj_acceptance_range x y.
  rewrite /rsm_kernel; smt().
qed.

lemma rsa_noise_kernel_range (weight : int -> real) W x :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  0 <= x <= 166 => 0%r <= rsm_noise_kernel weight x <= W.
proof.
  move=> hW hw hx.
  have hfin : is_finite (Distr.support sr_noise_uniform) by
    rewrite /sr_noise_uniform; apply finite_dinter.
  have hpoint : forall y, y \in sr_noise_uniform => 0%r <= rsm_kernel weight x y <= W.
  + move=> y hy; exact (rsa_kernel_range weight W x y hW hw hx (sigma_noise72_support y hy)).
  rewrite /rsm_noise_kernel; split.
  + apply exp_ge0 => y hy; have h := hpoint y hy; smt().
  have h := finite_expectation_le sr_noise_uniform (fun y => rsm_kernel weight x y)
    (fun _ => W) hfin _.
  + move=> y hy; have hp := hpoint y hy; smt().
  by move: h; rewrite expC sr_noise_uniform_ll /=.
qed.

lemma rsa_clipped_kernel_range (weight : int -> real) W x :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  0%r <= rsm_clipped_kernel weight x <= W.
proof.
  move=> hW hw; rewrite /rsm_clipped_kernel.
  case (0<=x<=166) => hx; first exact (rsa_noise_kernel_range weight W x hW hw hx).
  smt().
qed.

lemma rsa_clipped_hasE (weight : int -> real) W (d : int distr) :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  hasE d (rsm_clipped_kernel weight).
proof.
  move=> hW hw; apply (rsa_hasE_bounded d _ W hW) => x.
  exact (rsa_clipped_kernel_range weight W x hW hw).
qed.

lemma rsa_actual_outer_law (p : BArray26.t) (weight : int -> real) :
  rsm_actual p weight = E (dinter 0 (cdt83_modulus-1))
    (fun u => rsa_noise_actual (sj_cdt83_patch p u) weight).
proof. by rewrite /rsm_actual /rsa_noise_actual /=. qed.

lemma rsa_implementation_error (p : BArray26.t) (weight : int -> real) W :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  `|rsm_actual p weight-rsa_cdt_mean weight| <= W*sj_word_error.
proof.
  move=> hW hw.
  have hfin := finite_dinter 0 (cdt83_modulus-1).
  have [he _] := sj_word_error_margin.
  have heps : 0%r <= W*sj_word_error by apply mulr_ge0.
  have hp : forall u, u \in dinter 0 (cdt83_modulus-1) =>
    `|rsa_noise_actual (sj_cdt83_patch p u) weight-
      rsm_noise_kernel weight (cdt_rank cdt83_thresholds u)| <=
        W*sj_word_error+0%r*b2r false.
  + move=> u hu.
    have hur : 0 <= u < cdt83_modulus by move: hu; rewrite supp_dinter; smt().
    have h := rsa_fixed_noise_error (sj_cdt83_patch p u) weight W hW hw.
    by move: h; rewrite (sj_cdt83_patch_count p u hur) /=.
  have h := finite_expectation_error (dinter 0 (cdt83_modulus-1))
    (fun u => rsa_noise_actual (sj_cdt83_patch p u) weight)
    (fun u => rsm_noise_kernel weight (cdt_rank cdt83_thresholds u))
    (fun _ => false) (W*sj_word_error) 0%r hfin sj203_uniform_ll heps _ hp;
    first trivial.
  rewrite /= (sj_cdt83_expectation (rsm_noise_kernel weight)) in h.
  by rewrite rsa_actual_outer_law /rsa_cdt_mean.
qed.

lemma rsa_cdt_clipped (weight : int -> real) :
  rsa_cdt_mean weight =
    E (cdt_distribution cdt83_modulus cdt83_thresholds) (rsm_clipped_kernel weight).
proof.
  rewrite /rsa_cdt_mean; apply eq_exp => x hx.
  have hr : 0 <= x <= 166 by move: hx; rewrite cdt83_distribution_support.
  by rewrite /rsm_clipped_kernel hr.
qed.

lemma rsa_clipped_cdt_error (weight : int -> real) W :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  `|rsa_cdt_mean weight-rsm_clipped_ideal weight| <=
    W*sdist (cdt_distribution cdt83_modulus cdt83_thresholds) hg16_distr.
proof.
  move=> hW hw; rewrite rsa_cdt_clipped /rsm_clipped_ideal.
  apply (rsa_expectation_distance_scaled _ _ _ W hW) => x.
  exact (rsa_clipped_kernel_range weight W x hW hw).
qed.

lemma rsa_error_margin :
  sj_word_error+sdist (cdt_distribution cdt83_modulus cdt83_thresholds) hg16_distr <= ht_eta.
proof.
  have [_ hw] := sj_word_error_margin.
  have hc := cdt83_half_gaussian_statistical_distance.
  rewrite cdt83_gaussian_error_bound in hc.
  have h78 : 2^78 = 302231454903657293676544 by ring.
  move: hw hc; rewrite /sr_scale h78 /ht_eta; smt().
qed.

lemma rsa_weighted_clipped_error (p : BArray26.t) (weight : int -> real) W :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  `|rsm_actual p weight-rsm_clipped_ideal weight| <= W*ht_eta.
proof.
  move=> hW hw.
  have hactual := rsa_implementation_error p weight W hW hw.
  have hcdt := rsa_clipped_cdt_error weight W hW hw.
  have hmargin := ler_wpmul2l W hW _ _ rsa_error_margin.
  rewrite ler_norml in hactual.
  rewrite ler_norml in hcdt.
  rewrite ler_norml; smt().
qed.

lemma rsa_weighted_upper (p : BArray26.t) (weight : int -> real) W :
  0%r <= W =>
  (forall z, 0 <= z < 167*sr_noise_modulus => 0%r <= weight z <= W) =>
  rsm_actual p weight <= rsm_clipped_ideal weight+W*ht_eta.
proof.
  move=> hW hw; have h := rsa_weighted_clipped_error p weight W hW hw.
  move: h; rewrite ler_norml; smt().
qed.

lemma rsa_actual_acceptance_law (p : BArray26.t) &m :
  rsm_actual p (fun _ => 1%r) = Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2].
proof.
  have h := sigma_joint203_law p (fun _ => true) &m.
  by move: h; rewrite /rsm_actual /= => ->.
qed.

lemma rsa_ideal_acceptance_joint :
  rsm_ideal (fun _ => 1%r) = sj_ideal_joint (fun _ => true).
proof.
  by rewrite /rsm_ideal /rsm_noise_kernel /rsm_kernel /sj_ideal_joint
    /sj_noise_kernel /sj_kernel /b2r /=.
qed.

(* The denominator uses the full ideal CDT support. Its constant-one
   acceptance kernel is integrable independently of the clipping argument. *)
lemma rsa_ideal_acceptance_hasE :
  hasE hg16_distr (rsm_noise_kernel (fun _ => 1%r)).
proof.
  have he : rsm_noise_kernel (fun _ => 1%r) =
    (fun x => sj_noise_kernel x (fun _ => true)).
  + apply fun_ext => x; by rewrite /rsm_noise_kernel /rsm_kernel /sj_noise_kernel
      /sj_kernel /b2r /=.
  rewrite he; exact (sj_noise_kernel_hasE hg16_distr (fun _ => true)).
qed.

lemma rsa_ideal_acceptance_law &m :
  rsm_ideal (fun _ => 1%r) = Pr[SigmaJointIdeal.sample() @ &m : res.`2].
proof.
  rewrite rsa_ideal_acceptance_joint.
  have h := sj_ideal_joint_law (fun _ => true) &m.
  by move: h; rewrite /= => ->.
qed.

lemma rsa_acceptance_error_at (p : BArray26.t) &m :
  `|rsm_actual p (fun _ => 1%r)-rsm_ideal (fun _ => 1%r)| <= ht_eta.
proof.
  rewrite (rsa_actual_acceptance_law p &m) (rsa_ideal_acceptance_law &m) /ht_eta.
  have [_ h] := sj_joint_output_error_strict p (fun _ => true) &m.
  move: h; rewrite /=; smt().
qed.

lemma rsa_acceptance_error (p : BArray26.t) :
  `|rsm_actual p (fun _ => 1%r)-rsm_ideal (fun _ => 1%r)| <= ht_eta.
proof. have h := rsa_acceptance_error_at p; smt(). qed.

lemma rsa_actual_acceptance_lower_at (p : BArray26.t) &m :
  1%r/7%r <= rsm_actual p (fun _ => 1%r).
proof.
  rewrite (rsa_actual_acceptance_law p &m).
  exact (sc_actual_acceptance_lower p &m).
qed.

lemma rsa_actual_acceptance_lower (p : BArray26.t) :
  1%r/7%r <= rsm_actual p (fun _ => 1%r).
proof. have h := rsa_actual_acceptance_lower_at p; smt(). qed.
