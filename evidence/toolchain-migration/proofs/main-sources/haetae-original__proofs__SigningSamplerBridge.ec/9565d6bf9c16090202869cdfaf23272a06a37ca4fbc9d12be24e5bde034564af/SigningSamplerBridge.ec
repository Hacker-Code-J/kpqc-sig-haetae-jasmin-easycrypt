require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import ApiTarget SamplerTarget CDTCorrectness FixedPointCorrectness
               SigmaCorrectness.

(* ApiTarget is extracted from the complete production signing entry points.
   These bridges establish that its own sampler helper instances inherit the
   focused proofs.  They do not assert correctness or termination of Sign. *)
theory SigningSamplerBridge.

module Signer = ApiTarget.M(ApiTarget.Syscall).
module Sampler = SamplerTarget.M.

lemma signer_cdt83_equiv :
  equiv [Signer._sample_gauss83 ~ Sampler._sample_gauss83 :
    ={rand_lo, rand_hi} ==> ={res}].
proof. proc; sim. qed.

lemma signer_smulh48_equiv :
  equiv [Signer.__smulh48 ~ Sampler.__smulh48 :
    ={a, b} ==> ={res}].
proof. proc; sim. qed.

lemma signer_approx_exp_equiv :
  equiv [Signer._approx_exp ~ Sampler._approx_exp :
    ={x} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma signer_sigma76_equiv :
  equiv [Signer.__sample_gauss_sigma76_regs ~ Sampler.__sample_gauss_sigma76_regs :
    ={randp} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma signer_cdt83_correct (lo : W64.t) (hi : W32.t) :
  hoare [Signer._sample_gauss83 : rand_lo = lo /\ rand_hi = hi
    ==> W64.to_uint res = CDTCorrectness.cdt_count lo hi 166 /\
        0 <= W64.to_uint res <= 166].
proof.
by conseq signer_cdt83_equiv (CDTCorrectness.sample_gauss83_correct lo hi) => /#.
qed.

lemma signer_cdt83_total_correct (lo : W64.t) (hi : W32.t) :
  phoare [Signer._sample_gauss83 : rand_lo = lo /\ rand_hi = hi
    ==> W64.to_uint res = CDTCorrectness.cdt_count lo hi 166 /\
        0 <= W64.to_uint res <= 166] = 1%r.
proof.
by conseq signer_cdt83_equiv (CDTCorrectness.sample_gauss83_total lo hi) => /#.
qed.

lemma signer_smulh48_correct (aa bb : W64.t) :
  hoare [Signer.__smulh48 : a = aa /\ b = bb
    ==> res = W64.of_int (FixedPointSpec.smulh48_ceil aa bb)].
proof.
by conseq signer_smulh48_equiv (FixedPointCorrectness.smulh48_integer_correct aa bb) => /#.
qed.

lemma signer_smulh48_total_correct (aa bb : W64.t) :
  phoare [Signer.__smulh48 : a = aa /\ b = bb
    ==> res = W64.of_int (FixedPointSpec.smulh48_ceil aa bb)] = 1%r.
proof.
by conseq signer_smulh48_equiv (FixedPointCorrectness.smulh48_total_correct aa bb) => /#.
qed.

lemma signer_smulh48_signed_correct (aa bb : W64.t) :
  -9223372036854775808 <= FixedPointSpec.smulh48_ceil aa bb <= 9223372036854775807 =>
  hoare [Signer.__smulh48 : a = aa /\ b = bb
    ==> W64.to_sint res = FixedPointSpec.smulh48_ceil aa bb].
proof.
move=> hfit.
by conseq signer_smulh48_equiv
  (FixedPointCorrectness.smulh48_signed_correct aa bb hfit) => /#.
qed.

lemma signer_approx_exp_correct (xx : W64.t) :
  hoare [Signer._approx_exp : x = xx
    ==> res = FixedPointSpec.approx_exp_word xx].
proof.
by conseq signer_approx_exp_equiv (FixedPointCorrectness.approx_exp_correct xx) => /#.
qed.

lemma signer_approx_exp_total_correct (xx : W64.t) :
  phoare [Signer._approx_exp : x = xx
    ==> res = FixedPointSpec.approx_exp_word xx] = 1%r.
proof.
by conseq signer_approx_exp_equiv (FixedPointCorrectness.approx_exp_total_correct xx) => /#.
qed.

lemma signer_approx_exp_reference_total_correct (xx : W64.t) :
  phoare [Signer._approx_exp : x = xx
    ==> res = ReferenceConstants.reference_approx_exp
      (fun a b => W64.of_int (FixedPointSpec.smulh48_ceil a b)) xx] = 1%r.
proof.
conseq (signer_approx_exp_total_correct xx) => />.
by rewrite FixedPointCorrectness.approx_exp_integer_reference.
qed.

lemma signer_sigma76_correct (p : BArray26.t) :
  hoare [Signer.__sample_gauss_sigma76_regs : randp = p
    ==> res = SigmaCorrectness.sigma76_spec p].
proof.
by conseq signer_sigma76_equiv (SigmaCorrectness.sigma76_regs_correct p) => /#.
qed.

lemma signer_sigma76_total_correct (p : BArray26.t) :
  phoare [Signer.__sample_gauss_sigma76_regs : randp = p
    ==> res = SigmaCorrectness.sigma76_spec p] = 1%r.
proof.
by conseq signer_sigma76_equiv (SigmaCorrectness.sigma76_regs_total_correct p) => /#.
qed.

end SigningSamplerBridge.
