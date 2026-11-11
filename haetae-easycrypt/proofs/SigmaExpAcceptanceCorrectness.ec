require import AllCore IntDiv Real RealExp Distr StdRing StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 ApproxExpSpec ApproxExpWordCorrectness ApproxExpNumericalCorrectness
  SigmaExpInputBounds SigmaRejection48Bridge Rejection48Spec Rejection48Correctness.
import RField RealOrder.

(* The reference here retains the actual quantized exponent argument and the
   actual rounded-zero correction. It is not a full Gaussian sampling law. *)
op [opaque] sigma_exp_acceptance_target (p : BArray26.t) : real =
  rejection48_factor (sigma_rejection48_rounded p) *
    RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r)).

lemma sigma_exp_threshold_fit (p : BArray26.t) :
  0 <= W64.to_uint (sigma_rejection48_threshold p) < 9223372036854775808.
proof.
  have hd := ae_sigma_domain p.
  have hb := ae_integer_bound (W64.to_uint (sigma_exp_argument p)) hd.
  have h0 := ae_integer_nonnegative (W64.to_uint (sigma_exp_argument p)) hd.
  rewrite /sigma_rejection48_threshold ae_approx_exp_unsigned 1:hd.
  move: hb; rewrite /ae_bound; smt().
qed.

lemma ae_real_probability_range (w : W64.t) :
  0%r <= RealExp.exp (-((W64.to_uint w)%r / ae_scale%r)) <= 1%r.
proof.
  have hw := W64.to_uint_cmp w.
  have hwr : 0%r <= (W64.to_uint w)%r by rewrite le_fromint; smt().
  have hz : 0%r <= (W64.to_uint w)%r / ae_scale%r
    by rewrite /ae_scale; smt().
  have hp := RealExp.exp_gt0 (-((W64.to_uint w)%r / ae_scale%r)).
  have he : RealExp.exp (-((W64.to_uint w)%r / ae_scale%r)) <= RealExp.exp 0%r.
  + apply RealExp.exp_mono; smt().
  rewrite RealExp.exp0 in he; smt().
qed.

lemma sigma_exp_threshold_error (p : BArray26.t) :
  `|(W64.to_uint (sigma_rejection48_threshold p))%r / ae_scale%r -
    RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r))| <= 27%r/ae_scale%r.
proof.
  have [he _] := approx_exp_word_numerical_error (sigma_exp_argument p) (ae_sigma_domain p).
  by move: he; rewrite /ae_numerical_error /sigma_rejection48_threshold.
qed.

lemma sigma_exp_acceptance_error (p : BArray26.t) &m :
  `|Pr[SigmaRejection48Experiment.sample(p) @ &m : res] - sigma_exp_acceptance_target p| <=
    rejection48_factor (sigma_rejection48_rounded p) * (28%r/ae_scale%r).
proof.
  have [_ hfit] := sigma_exp_threshold_fit p.
  rewrite (sigma_rejection48_actual_probability p &m hfit) /sigma_exp_acceptance_target.
  have hp := ae_real_probability_range (sigma_exp_argument p).
  have he := sigma_exp_threshold_error p.
  have he' : `|(W64.to_uint (sigma_rejection48_threshold p))%r / 281474976710656%r -
    RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r))| <= 27%r/ae_scale%r.
  + by move: he; rewrite /ae_scale.
  have h := rejection48_probability_error (W64.to_uint (sigma_rejection48_threshold p))
    (sigma_rejection48_rounded p)
    (RealExp.exp (-((W64.to_uint (sigma_exp_argument p))%r / ae_scale%r)))
    (27%r/ae_scale%r) hp he'.
  have hs : 27%r/ae_scale%r + 1%r/281474976710656%r = 28%r/ae_scale%r.
  + rewrite /ae_scale; ring.
  move: h; rewrite hs; trivial.
qed.

lemma sigma_exp_acceptance_error_strict (p : BArray26.t) &m :
  `|Pr[SigmaRejection48Experiment.sample(p) @ &m : res] - sigma_exp_acceptance_target p| <
    1%r/(2^43)%r.
proof.
  have h := sigma_exp_acceptance_error p &m.
  have hf : 0%r <= rejection48_factor (sigma_rejection48_rounded p) <= 1%r.
  + by rewrite /rejection48_factor; case (sigma_rejection48_rounded p = W64.zero); smt().
  have he : 0%r <= 28%r/ae_scale%r by rewrite /ae_scale; smt().
  have hb : 28%r/ae_scale%r < 1%r/(2^43)%r.
  + have hpow : (2^43) = 8796093022208 by ring.
    rewrite hpow /ae_scale; smt().
  have hscale : rejection48_factor (sigma_rejection48_rounded p) * (28%r/ae_scale%r)
      <= 28%r/ae_scale%r.
  + have hfle : rejection48_factor (sigma_rejection48_rounded p) <= 1%r by smt().
    have hs := ler_wpmul2r (28%r/ae_scale%r) he _ _ hfle.
    by rewrite mul1r in hs.
  exact (ler_lt_trans _ _ _ (ler_trans _ _ _ h hscale) hb).
qed.
