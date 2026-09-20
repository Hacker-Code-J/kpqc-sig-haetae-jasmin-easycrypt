require import AllCore Real Distr DInterval Finite SDist StdRing StdOrder.
require import SigmaJointSpec SigmaJointKernelCorrectness SigmaJointFixedCorrectness
  SigmaJoint203Bridge SigmaJointIdealCorrectness SigmaCDT83Patch
  SigmaJointAttemptBridge SigmaRawSpec SigmaRawNoiseSpec SigmaRawAcceptanceCorrectness
  SigmaNoise72Bridge SigmaRejection48Bridge FiniteExpectationError
  DistributionExpectationDistance CDTDistributionSpec CDTDistributionBridge
  CDTGaussianApproximation HalfGaussianSpec.
import RField RealOrder HalfGaussianSpec.

(* The first comparison keeps the actual finite CDT law and replaces only
   the implementation acceptance computation. The second changes the CDT
   law under a bounded, independent mathematical kernel. *)
op [opaque] sj_cdt_joint (event : int -> bool) : real =
  E (cdt_distribution cdt83_modulus cdt83_thresholds)
    (fun x => sj_noise_kernel x event).

lemma sj_actual203_law (p : BArray26.t) (event : int -> bool) &m :
  Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2 /\ event res.`1] =
    E (dinter 0 (cdt83_modulus - 1))
      (fun u => sj_actual_noise_mass (sj_cdt83_patch p u) event).
proof.
  by rewrite sigma_joint203_law /sj_actual_noise_mass /sj_actual_kernel.
qed.

lemma sj_implementation_error (p : BArray26.t) (event : int -> bool) &m :
  `|Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2 /\ event res.`1] -
    sj_cdt_joint event| <= sj_word_error.
proof.
  have hfin := DInterval.finite_dinter 0 (cdt83_modulus - 1).
  have hll : is_lossless (dinter 0 (cdt83_modulus - 1)).
  + apply DInterval.dinter_ll; have := cdt83_modulus_positive; smt().
  have [he _] := sj_word_error_margin.
  have hp : forall u, u \in dinter 0 (cdt83_modulus - 1) =>
    `|sj_actual_noise_mass (sj_cdt83_patch p u) event -
      sj_noise_kernel (cdt_rank cdt83_thresholds u) event| <=
        sj_word_error + 0%r * b2r false.
  + move=> u hu.
    have hur : 0 <= u < cdt83_modulus by move: hu; rewrite DInterval.supp_dinter; smt().
    have h := sj_fixed_uniform_error (sj_cdt83_patch p u) event.
    by move: h; rewrite (sj_cdt83_patch_count p u hur) /=.
  have h := finite_expectation_error (dinter 0 (cdt83_modulus - 1))
    (fun u => sj_actual_noise_mass (sj_cdt83_patch p u) event)
    (fun u => sj_noise_kernel (cdt_rank cdt83_thresholds u) event)
    (fun _ => false) sj_word_error 0%r hfin hll he _ hp;
    first trivial.
  rewrite /= (sj_cdt83_expectation (fun x => sj_noise_kernel x event)) in h.
  by rewrite sj_actual203_law /sj_cdt_joint.
qed.

lemma sj_cdt_kernel_distance (event : int -> bool) :
  `|sj_cdt_joint event - sj_ideal_joint event| <=
    SDist.sdist (cdt_distribution cdt83_modulus cdt83_thresholds) hg16_distr.
proof.
  rewrite /sj_cdt_joint /sj_ideal_joint.
  apply distribution_expectation_distance_global => x.
  exact (sj_noise_kernel_range x event).
qed.

lemma sj_joint_mass_error (p : BArray26.t) (event : int -> bool) &m :
  `|Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2 /\ event res.`1] -
    sj_ideal_joint event| <=
    sj_word_error + SDist.sdist (cdt_distribution cdt83_modulus cdt83_thresholds) hg16_distr.
proof.
  have ha := sj_implementation_error p event &m.
  have hb := sj_cdt_kernel_distance event.
  rewrite ler_norml in ha.
  rewrite ler_norml in hb.
  rewrite ler_norml; smt().
qed.

(* Every set of integer outputs is allowed. This is a joint event with
   acceptance, without dividing either side by its acceptance probability. *)
lemma sj_joint_output_error (p : BArray26.t) (event : int -> bool) &m :
  `|Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2 /\ event res.`1] -
    Pr[SigmaJointIdeal.sample() @ &m : res.`2 /\ event res.`1]| <
      29%r / sr_scale%r + 1%r / (2^78)%r.
proof.
  rewrite sj_ideal_joint_law.
  have he := sj_joint_mass_error p event &m.
  have hc := cdt83_half_gaussian_statistical_distance.
  rewrite cdt83_gaussian_error_bound in hc.
  have [_ hw] := sj_word_error_margin.
  smt().
qed.

lemma sj_joint_output_error_strict (p : BArray26.t) (event : int -> bool) &m :
  `|Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2 /\ event res.`1] -
    Pr[SigmaJointIdeal.sample() @ &m : res.`2 /\ event res.`1]| < 30%r / sr_scale%r /\
  `|Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2 /\ event res.`1] -
    Pr[SigmaJointIdeal.sample() @ &m : res.`2 /\ event res.`1]| < 1%r / (2^43)%r.
proof.
  have h := sj_joint_output_error p event &m.
  have h78 : 2^78 = 302231454903657293676544 by ring.
  have h43 : 2^43 = 8796093022208 by ring.
  rewrite h43 /sr_scale.
  move: h; rewrite h78 /sr_scale; smt().
qed.
