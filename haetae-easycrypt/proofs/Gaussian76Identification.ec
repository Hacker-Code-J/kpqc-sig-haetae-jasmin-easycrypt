require import AllCore IntDiv Real RealSeries Distr SDist StdRing StdOrder StdBigop.
require import Gaussian76Spec Gaussian76Properties Gaussian76Folding
  GaussianBlockReindex Gaussian76Kernel Gaussian76Rounding SigmaRawSpec SigmaRawNoiseSpec
  SigmaJointSpec SigmaConditionalSpec SigmaConditionalIdeal
  SigmaConditionalCorrectness HalfGaussianSpec HalfGaussianProperties.
import RField RealOrder HalfGaussianSpec HalfGaussianProperties.

lemma g76_denominator_power : g76_denominator = 2^153.
proof. by rewrite /g76_denominator /=. qed.

lemma g76_rounded_ll : is_lossless g76_rounded.
proof. rewrite /g76_rounded; apply dmap_ll; exact g76_distr_ll. qed.

lemma g76_gaussian_mass (k : int) :
  mu1 g76_distr k = RealExp.exp (-(k*k)%r / (2^153)%r) /
    RealSeries.sum (fun j : int => RealExp.exp (-(j*j)%r / (2^153)%r)).
proof.
  by rewrite g76_distr_mu1 /g76_pmf /g76_normalizer /g76_rho g76_denominator_power.
qed.

(* Scalar linearity aligns the nested expectations with the pointwise
   Gaussian identity. No unsupported swap of infinite sums is used. *)
lemma g76_ideal_joint_series (event : int -> bool) :
  sj_ideal_joint event =
  RealSeries.sum (fun x => RealSeries.sum (fun y =>
    mu1 hg16_distr x * mu1 sr_noise_uniform y * sj_kernel x y event)).
proof.
  rewrite /sj_ideal_joint /sj_noise_kernel /E.
  apply RealSeries.eq_sum => x /=.
  rewrite -RealSeries.sumZr.
  apply RealSeries.eq_sum => y /=; ring.
qed.

lemma g76_ideal_joint_formula (event : int -> bool) :
  sj_ideal_joint event =
    RealSeries.sum (fun z =>
      g76_accept_weight z * b2r (event (g76_round_magnitude z))) /
    (sr_noise_modulus%r * hg16_normalizer).
proof.
  pose f := fun z => g76_accept_weight z * b2r (event (g76_round_magnitude z)).
  have hs : RealSeries.summable f by exact (g76_accept_event_summable event).
  have hneg : forall z, z < 0 => f z = 0%r.
  + move=> z hz; by rewrite /f (g76_accept_weight_negative z hz) /=.
  have hN : 0 < sr_noise_modulus by rewrite /sr_noise_modulus.
  have hweighted :
    RealSeries.sum (fun x => RealSeries.sum (fun y =>
      mu1 hg16_distr x * mu1 sr_noise_uniform y * sj_kernel x y event)) =
    inv (sr_noise_modulus%r * hg16_normalizer) *
      RealSeries.sum (fun x => RealSeries.sum (fun y =>
        if 0 <= x /\ 0 <= y < sr_noise_modulus then f (sr_noise_modulus*x+y) else 0%r)).
  + rewrite -(RealSeries.sumZ (fun x => RealSeries.sum (fun y =>
      if 0 <= x /\ 0 <= y < sr_noise_modulus then f (sr_noise_modulus*x+y) else 0%r))
      (inv (sr_noise_modulus%r * hg16_normalizer))).
    apply RealSeries.eq_sum => x /=.
    rewrite -(RealSeries.sumZ (fun y =>
      if 0 <= x /\ 0 <= y < sr_noise_modulus then f (sr_noise_modulus*x+y) else 0%r)
      (inv (sr_noise_modulus%r * hg16_normalizer))).
    apply RealSeries.eq_sum => y /=.
    exact (g76_full_contribution x y event).
  rewrite g76_ideal_joint_series hweighted (gb_block_sum sr_noise_modulus f hN hs hneg).
  rewrite /f; ring.
qed.

lemma g76_ideal_joint_total :
  sj_ideal_joint (fun (_ : int) => true) =
    g76_normalizer / (2%r * (sr_noise_modulus%r * hg16_normalizer)).
proof.
  rewrite g76_ideal_joint_formula /b2r /= g76_accept_weight_sum.
  have hn := g76_proposal_normalizer_nonzero.
  field; smt().
qed.

lemma g76_ideal_acceptance_kernel :
  mu sc_ideal_pair sc_accepted = sj_ideal_joint (fun (_ : int) => true).
proof.
  have h := sc_ideal_joint_kernel (fun (_ : int) => true).
  by move: h; rewrite /=.
qed.

lemma g76_ideal_acceptance_formula :
  mu sc_ideal_pair sc_accepted =
    g76_normalizer / (2%r * (sr_noise_modulus%r * hg16_normalizer)).
proof. by rewrite g76_ideal_acceptance_kernel g76_ideal_joint_total. qed.

(* Zero is counted once in the signed Gaussian and twice nowhere. The
   one-half raw-zero correction cancels with the same factor in the total
   acceptance mass, yielding the full rounded-absolute Gaussian law. *)
lemma g76_ideal_conditioned_event (event : int -> bool) :
  mu sc_ideal_conditioned event = mu g76_rounded event.
proof.
  rewrite /sc_ideal_conditioned dmapE dcondE /predI /(\o).
  rewrite (sc_ideal_joint_kernel event) g76_ideal_acceptance_formula
    g76_ideal_joint_formula g76_rounded_accept_event_law.
  have hz := g76_normalizer_positive.
  have hn := g76_proposal_normalizer_nonzero.
  field; smt().
qed.

lemma g76_ideal_conditioned_eq : sc_ideal_conditioned = g76_rounded.
proof.
  apply eq_distr => r.
  exact (g76_ideal_conditioned_event (pred1 r)).
qed.

lemma g76_actual_conditioned_sdist (p : BArray26.t) &m :
  SDist.sdist (sc_actual_conditioned p) g76_rounded < 1%r / (2^39)%r.
proof.
  rewrite -g76_ideal_conditioned_eq.
  exact (sc_conditioned_sdist_strict p &m).
qed.

lemma g76_actual_conditioned_event_error (p : BArray26.t) (event : int -> bool) &m :
  `|mu (sc_actual_conditioned p) event - mu g76_rounded event| < 1%r / (2^39)%r.
proof.
  rewrite -g76_ideal_conditioned_eq.
  exact (sc_conditioned_event_error_strict p event &m).
qed.

lemma g76_actual_gaussian_correct (p : BArray26.t) &m :
  is_lossless (sc_actual_conditioned p) /\ is_lossless g76_rounded /\
  SDist.sdist (sc_actual_conditioned p) g76_rounded < 1%r / (2^39)%r.
proof.
  rewrite -g76_ideal_conditioned_eq.
  exact (sc_conditioned_distributions_correct p &m).
qed.

lemma g76_actual_rounded_mass_error (p : BArray26.t) (r : int) &m :
  `|mu1 (sc_actual_conditioned p) r -
    (if 0 <= r then
      Bigreal.BRA.bigi (fun (_ : int) => true) g76_fold_weight
        (g76_round_bin_lower r) (g76_round_bin_upper r) / g76_normalizer
     else 0%r)| < 1%r / (2^39)%r.
proof.
  have h := g76_actual_conditioned_event_error p (pred1 r) &m.
  by move: h; rewrite g76_rounded_mass.
qed.
