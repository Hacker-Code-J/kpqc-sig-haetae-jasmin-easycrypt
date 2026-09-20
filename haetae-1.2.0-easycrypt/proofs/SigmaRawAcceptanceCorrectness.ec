require import AllCore IntDiv Real RealExp Distr StdRing StdOrder.
from Jasmin require import JModel_x86.
require import SigmaRawSpec SigmaRawExponentCorrectness SigmaRawZeroCorrectness
  ExponentialLipschitz ApproxExpSpec SigmaExpInputBounds
  SigmaExpAcceptanceCorrectness SigmaRejection48Bridge
  Rejection48Spec Rejection48Correctness.
import RField RealOrder.

op [opaque] sr_actual_probability (p : BArray26.t) : real =
  rejection48_probability (W64.to_uint (sigma_rejection48_threshold p))
    (sigma_rejection48_rounded p).

op sr_regular_error : real = 57%r / (2%r * sr_scale%r).

lemma sr_actual_probability_law (p : BArray26.t) &m :
  Pr[SigmaRejection48Experiment.sample(p) @ &m : res] = sr_actual_probability p.
proof.
  rewrite /sr_actual_probability; apply sigma_rejection48_actual_probability.
  have := sigma_exp_threshold_fit p; smt().
qed.

lemma sr_exponential_range (p : BArray26.t) :
  0%r <= RealExp.exp (-sr_exponent p) <= 1%r.
proof.
  have h0 := sr_exponent_nonnegative p.
  have hp := RealExp.exp_gt0 (-sr_exponent p).
  have hu : RealExp.exp (-sr_exponent p) <= RealExp.exp 0%r.
  + apply RealExp.exp_mono; smt().
  rewrite RealExp.exp0 in hu; smt().
qed.

lemma sr_acceptance_target_range (p : BArray26.t) :
  0%r <= sr_acceptance_target p <= 1%r.
proof.
  have he := sr_exponential_range p.
  rewrite /sr_acceptance_target /sr_raw_factor.
  case (sr_candidate p = 0); smt().
qed.

lemma sr_exponential_error (p : BArray26.t) :
  `|RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r)) -
    RealExp.exp (-sr_exponent p)| <= 1%r / (2%r * sr_scale%r).
proof.
  apply exp_neg_perturbation.
  + have hx := sigma_exp_argument_bound p.
    rewrite /ae_scale; smt().
  + exact (sr_exponent_nonnegative p).
  have he := sigma_raw_exponent_error p.
  by move: he; rewrite /ae_scale /sr_scale.
qed.

(* Keep the actual rounded-zero factor while changing the exponent to the
   independently defined raw expression. *)
lemma sr_rounded_acceptance_error (p : BArray26.t) :
  `|sr_actual_probability p - rejection48_factor (sigma_rejection48_rounded p) *
    RealExp.exp (-sr_exponent p)| <=
  rejection48_factor (sigma_rejection48_rounded p) * sr_regular_error.
proof.
  have hp := ae_real_probability_range (sigma_exp_argument p).
  have ht := sigma_exp_threshold_error p.
  have ht' : `|(W64.to_uint (sigma_rejection48_threshold p))%r / 281474976710656%r -
    RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r))| <=
    27%r / ae_scale%r by move: ht; rewrite /ae_scale.
  have hq := rejection48_probability_error
    (W64.to_uint (sigma_rejection48_threshold p)) (sigma_rejection48_rounded p)
    (RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r)))
    (27%r / ae_scale%r) hp ht'.
  have he := sr_exponential_error p.
  rewrite ler_norml in hq.
  rewrite ler_norml in he.
  rewrite ler_norml /sr_actual_probability /sr_regular_error.
  move: hq he.
  rewrite /rejection48_factor /ae_scale /sr_scale.
  case (sigma_rejection48_rounded p = W64.zero); smt().
qed.

(* A fixed candidate in the small rounded-zero interval can differ by almost
   one half. The event is explicit instead of assuming the two zero rules agree. *)
lemma sr_acceptance_error (p : BArray26.t) :
  `|sr_actual_probability p - sr_acceptance_target p| <=
    sr_regular_error + (if sr_zero_mismatch p then 1%r / 2%r else 0%r).
proof.
  have ha := sr_rounded_acceptance_error p.
  have hf := sr_zero_factor_difference p.
  have he := sr_exponential_range p.
  rewrite ler_norml in ha.
  rewrite ler_norml /sr_acceptance_target.
  move: ha hf.
  rewrite /rejection48_factor /sr_regular_error /sr_scale.
  case (sigma_rejection48_rounded p = W64.zero);
    case (sr_zero_mismatch p); smt().
qed.

lemma sr_actual_acceptance_error (p : BArray26.t) &m :
  `|Pr[SigmaRejection48Experiment.sample(p) @ &m : res] - sr_acceptance_target p| <=
    sr_regular_error + (if sr_zero_mismatch p then 1%r / 2%r else 0%r).
proof. by rewrite sr_actual_probability_law; apply sr_acceptance_error. qed.

lemma sr_actual_acceptance_regular (p : BArray26.t) &m :
  !sr_zero_mismatch p =>
  `|Pr[SigmaRejection48Experiment.sample(p) @ &m : res] - sr_acceptance_target p| <
    1%r / (2^43)%r.
proof.
  move=> hn; have he := sr_actual_acceptance_error p &m.
  move: he; rewrite hn /= /sr_regular_error /sr_scale.
  smt().
qed.
