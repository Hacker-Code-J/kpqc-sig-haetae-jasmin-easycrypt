require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import SamplerTarget ReferenceConstants FixedPointSpec.

(* ReferenceConstants is generated from C, independently of the Jasmin target.
   These certificates therefore compare two separate sources of literal data. *)
lemma cdt83_hi_matches_reference :
  SamplerTarget.jcdt83_hi = reference_cdt83_hi.
proof.
  by rewrite /SamplerTarget.jcdt83_hi
    /reference_cdt83_hi /reference_cdt83_hi_words.
qed.

lemma cdt83_lo_matches_reference :
  SamplerTarget.jcdt83_lo = reference_cdt83_lo.
proof.
  by rewrite /SamplerTarget.jcdt83_lo
    /reference_cdt83_lo /reference_cdt83_lo_words.
qed.

lemma reference_cdt83_hi_length : size reference_cdt83_hi_words = 76.
proof. by rewrite /reference_cdt83_hi_words /=. qed.

lemma reference_cdt83_lo_length : size reference_cdt83_lo_words = 166.
proof. by rewrite /reference_cdt83_lo_words /=. qed.

lemma cdt83_hi_last_word :
  BArray304.get32 SamplerTarget.jcdt83_hi 75 = W32.of_int 524286.
proof.
  rewrite cdt83_hi_matches_reference /reference_cdt83_hi
    BArray304.get32_of_list32 1:reference_cdt83_hi_length 1://.
  by rewrite /reference_cdt83_hi_words /=.
qed.

lemma cdt83_lo_last_word :
  BArray1328.get64 SamplerTarget.jcdt83_lo 165 = W64.of_int (-2).
proof.
  rewrite cdt83_lo_matches_reference /reference_cdt83_lo
    BArray1328.get64_of_list64 1:reference_cdt83_lo_length 1://.
  by rewrite /reference_cdt83_lo_words /=.
qed.

lemma cdt83_last_threshold_matches_reference :
  reference_cdt83_tail_hi * W64.modulus +
    W64.to_uint (BArray1328.get64 SamplerTarget.jcdt83_lo 165) =
  reference_cdt83_last_threshold.
proof.
  by rewrite cdt83_lo_last_word W64.of_uintK
    /reference_cdt83_tail_hi /reference_cdt83_last_threshold /=.
qed.

lemma cdt83_max_input_matches_reference :
  W32.to_uint (W32.of_int 524287) * W64.modulus +
    W64.to_uint (W64.of_int (-1)) = reference_cdt83_max_input.
proof.
  by rewrite W32.of_uintK W64.of_uintK /reference_cdt83_max_input /=.
qed.

lemma cdt83_max_input_above_last_threshold :
  reference_cdt83_max_input = reference_cdt83_last_threshold + 1.
proof.
  by rewrite /reference_cdt83_max_input /reference_cdt83_last_threshold.
qed.

lemma reference_exp_degree10 : size reference_exp_coefficients = 11.
proof. by rewrite /reference_exp_coefficients /=. qed.

(* Check the coefficient sequence before unfolding the nested evaluator.
   A changed C coefficient then fails as a literal-data mismatch. *)
lemma reference_exp_coefficients_match :
  reference_exp_coefficients =
    [55868746; -743564434; 6953427278; -55833338892; 390932311155;
     -2345623661771; 11728123872951; -46912496106200; 140737488354861;
     -281474976710650; 281474976710657].
proof. by rewrite /reference_exp_coefficients. qed.

lemma approx_exp_matches_reference (x : W64.t) :
  approx_exp_word x = reference_approx_exp smulh48_word x.
proof. by rewrite /approx_exp_word /reference_approx_exp. qed.
