require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HardenedHyperballTarget HardenedSignerTarget HardenedPhaseTarget.

(* These are three fresh production extractions, never aliases for the old
   ApiTarget. Their shared checked helpers have identical execution semantics. *)
module HPS = HardenedSignerTarget.M(HardenedSignerTarget.Syscall).
module HPH = HardenedHyperballTarget.M.
module HPP = HardenedPhaseTarget.M.

lemma hardened_signer_scalar_equiv :
  equiv [HPS._hb_checked_mul_rnd13_regs ~ HPH._hb_checked_mul_rnd13_regs :
    ={x, y0, y1, sign} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma hardened_signer_norm_equiv :
  equiv [HPS._hb_checked_sqnorm2_2048 ~ HPH._hb_checked_sqnorm2_2048 :
    ={ap, acount, bp, bcount} ==> ={res}].
proof. proc; sim. qed.

lemma hardened_signer_vector_equiv :
  equiv [HPS._hb_checked_scale_samples ~ HPH._hb_checked_scale_samples :
    ={y1p, y2p, samplesp, signsp, scalep, counts} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma hardened_signer_check_equiv :
  equiv [HPS._hb_checked_scale_and_check_values ~ HPH._hb_checked_scale_and_check_values :
    ={y1p, y2p, samplesp, signsp, scalep, lcount, total, bound} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma hardened_phase_check_equiv :
  equiv [HPP._hb_checked_scale_and_check_values ~ HPH._hb_checked_scale_and_check_values :
    ={y1p, y2p, samplesp, signsp, scalep, lcount, total, bound} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma hardened_signer_wrapper_equiv :
  equiv [HPS._sf_scale_and_check ~ HPH._polyfixveclk_scale_and_check_values :
    ={y1p, y2p, samplesp, signsp, scalep, lcount, total, bound} ==> ={res}].
proof. proc; inline *; sim. qed.
