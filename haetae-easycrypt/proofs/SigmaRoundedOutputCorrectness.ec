require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SigmaSpec SigmaRoundingCorrectness SigmaRawSpec SigmaRejection48Bridge
  SigmaJointSpec.

(* These are Euclidean integer identities. In particular they do not restrict
   the ideal integer output to the finite range of a machine word. *)
lemma sj_round_low_identity (lo : int) :
  (lo %/ 32768 + 1) %/ 2 = (lo + 32768) %/ 65536.
proof.
  have -> : 65536 = 32768 * 2 by trivial.
  rewrite divz_mulp 1,2://.
  have he : (lo + 32768) %/ 32768 = lo %/ 32768 + 1.
  + have h := divzMDr 1 lo 32768 _; first trivial.
    smt().
  by rewrite he.
qed.

lemma sj_sigma_round_int (lo hi x : int) :
  sigma_round_int lo hi x =
    (lo + 281474976710656 * (hi + 16777216*x) + 32768) %/ 65536.
proof.
  have he : lo + 281474976710656 * (hi + 16777216*x) + 32768 =
    ((hi + 16777216*x)*4294967296)*65536 + (lo + 32768) by ring.
  rewrite he divzMDl 1:// /sigma_round_int sj_round_low_identity.
  ring.
qed.

(* The word result is interpreted as an unsigned integer. The existing
   sampler-domain proof supplies every range condition internally. *)
lemma sj_actual_rounding (p : BArray26.t) :
  W64.to_uint (sigma_rejection48_rounded p) = sj_round (sr_cdt p) (sr_noise p).
proof.
  rewrite /sigma_rejection48_rounded sigma76_spec_rounding
    /sigma76_rounding_int sj_sigma_round_int /sj_round
    /sr_noise /sr_scale /sr_noise_modulus /sr_cdt.
  apply (congr1 (fun n : int => n %/ 65536)); ring.
qed.
