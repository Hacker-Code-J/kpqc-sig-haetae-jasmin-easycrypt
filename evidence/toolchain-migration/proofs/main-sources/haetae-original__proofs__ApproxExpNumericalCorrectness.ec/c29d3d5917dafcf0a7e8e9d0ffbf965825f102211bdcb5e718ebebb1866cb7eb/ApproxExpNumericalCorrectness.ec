require import AllCore IntDiv List Real RealExp StdRing StdOrder.
from Jasmin require import JModel_x86.
require import ApproxExpSpec ApproxExpWordCorrectness ApproxExpPolynomialBound
  FixedPointSpec FixedPointCorrectness SamplerTarget SigningSamplerBridge SigmaExpInputBounds.
import RField RealOrder.

op [opaque] ae_numerical_error (input output : W64.t) : real =
  `|(W64.to_uint output)%r / ae_scale%r -
    RealExp.exp (-((W64.to_uint input)%r / ae_scale%r))|.

lemma ae_combine_errors (a p e s : real) :
  0%r < s => 0%r <= a-p <= 3%r/s => `|p-e| <= 24%r/s =>
  `|a-e| <= 27%r/s.
proof.
  move=> hs hr hp.
  have h0 : 0%r <= 3%r/s by apply divr_ge0; smt().
  have he : 3%r/s + 24%r/s = 27%r/s by ring.
  rewrite ler_norml in hp.
  rewrite ler_norml; smt().
qed.

lemma ae_final_error_margin : 27%r/ae_scale%r < 1%r/(2^43)%r.
proof.
  have hp : (2^43) = 8796093022208 by ring.
  rewrite hp /ae_scale; smt().
qed.

lemma approx_exp_integer_error x : ae_domain x =>
  `|(ae_integer x)%r/ae_scale%r - RealExp.exp (-(x%r/ae_scale%r))| <= 27%r/ae_scale%r /\
  `|(ae_integer x)%r/ae_scale%r - RealExp.exp (-(x%r/ae_scale%r))| < 1%r/(2^43)%r.
proof.
  move=> hx.
  have hr := ae_rounding_error3 x hx.
  have hp := approx_exp_polynomial_error x hx.
  have hs : 0%r < ae_scale%r by rewrite /ae_scale.
  have h := ae_combine_errors ((ae_integer x)%r/ae_scale%r)
    (ae_polynomial (x%r/ae_scale%r)) (RealExp.exp (-(x%r/ae_scale%r))) ae_scale%r hs hr hp.
  have hb := ae_final_error_margin; smt().
qed.

lemma ae_error_of_uint_equality (w output : W64.t) :
  ae_domain (W64.to_uint w) => W64.to_uint output = ae_integer (W64.to_uint w) =>
  ae_numerical_error w output <= 27%r/ae_scale%r /\
  ae_numerical_error w output < 1%r/(2^43)%r.
proof.
  move=> hd he; rewrite /ae_numerical_error he.
  exact (approx_exp_integer_error _ hd).
qed.

lemma approx_exp_word_numerical_error (w : W64.t) : ae_domain (W64.to_uint w) =>
  ae_numerical_error w (approx_exp_word w) <= 27%r/ae_scale%r /\
  ae_numerical_error w (approx_exp_word w) < 1%r/(2^43)%r.
proof.
  move=> hd; exact (ae_error_of_uint_equality w (approx_exp_word w)
    hd (ae_approx_exp_unsigned w hd)).
qed.

lemma approx_exp_internal_numerical_total (w : W64.t) :
  ae_domain (W64.to_uint w) =>
  phoare [SamplerTarget.M._approx_exp : x=w ==>
    ae_numerical_error w res <= 27%r/ae_scale%r /\
    ae_numerical_error w res < 1%r/(2^43)%r] = 1%r.
proof.
  move=> hd.
  have he := approx_exp_word_numerical_error w hd.
  by conseq approx_exp_lossless (approx_exp_correct w) => />.
qed.

lemma approx_exp_jazz_numerical_total (w : W64.t) :
  ae_domain (W64.to_uint w) =>
  phoare [SamplerTarget.M.approx_exp_jazz : x=w ==>
    ae_numerical_error w res <= 27%r/ae_scale%r /\
    ae_numerical_error w res < 1%r/(2^43)%r] = 1%r.
proof.
  move=> hd.
  have he := approx_exp_word_numerical_error w hd.
  by conseq approx_exp_jazz_lossless (approx_exp_jazz_correct w) => />.
qed.

lemma approx_exp_signer_numerical_total (w : W64.t) :
  ae_domain (W64.to_uint w) =>
  phoare [SigningSamplerBridge.Signer._approx_exp : x=w ==>
    ae_numerical_error w res <= 27%r/ae_scale%r /\
    ae_numerical_error w res < 1%r/(2^43)%r] = 1%r.
proof.
  move=> hd.
  by conseq SigningSamplerBridge.signer_approx_exp_equiv
    (approx_exp_internal_numerical_total w hd) => /#.
qed.

(* The real sigma76 input expression satisfies the numerical domain for every
   input byte array. No separate numerical-fit or probability premise remains. *)
lemma sigma76_approx_exp_numerical_total (p : BArray26.t) :
  phoare [SigningSamplerBridge.Signer._approx_exp : x=sigma_exp_argument p ==>
    ae_numerical_error (sigma_exp_argument p) res <= 27%r/ae_scale%r /\
    ae_numerical_error (sigma_exp_argument p) res < 1%r/(2^43)%r] = 1%r.
proof.
  exact (approx_exp_signer_numerical_total (sigma_exp_argument p) (ae_sigma_domain p)).
qed.
