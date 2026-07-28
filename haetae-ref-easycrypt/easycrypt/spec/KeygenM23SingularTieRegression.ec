require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenM23SingularSpec KeygenM23SingularBoundary
               KeygenM23FixedPointSemantics KeygenM23FinalizeSemantics.

theory KeygenM23SingularTieRegression.

(* This is a finish-stage regression vector.  Reachability from the FFT is
   deliberately not asserted.  Five selected entries with this value cross
   the mode-2 guard under the paper's fixed weights but not under the current
   multiplicity-sensitive implementation weights. *)
op threshold_tie_value_i : int = 204733952.

op threshold_tie_value_word : W32.t =
  W32.of_int threshold_tie_value_i.

op threshold_tie_term_word : W32.t =
  KeygenM23SingularSpec.finish_term_word
    threshold_tie_value_word threshold_tie_value_word.

op implementation_threshold_tie_acc_word : W32.t =
  ((((W32.zero + threshold_tie_term_word) + threshold_tie_term_word) +
     threshold_tie_term_word) + threshold_tie_term_word) +
    threshold_tie_term_word.

op implementation_threshold_tie_score_word : W64.t =
  (sigextu64 implementation_threshold_tie_acc_word + W64.of_int 32)
    `|>>` W8.of_int 6.

op paper_threshold_tie_score_i : int =
  let shifted = (threshold_tie_value_i + 66048) %/ 1024 in
  (shifted * KeygenM23SingularBoundary.paper_fixed_weight_i + 32) %/ 64.

op mode2_singular_bound_i : int = 611098.

lemma finish_factor_equal_exact (value : W32.t) :
  KeygenM23SingularSpec.finish_factor_word value value =
    W32.of_int KeygenM23SingularSpec.mode2_rem_i.
proof.
rewrite /KeygenM23SingularSpec.finish_factor_word.
have -> : value - value = W32.zero by ring.
rewrite /= KeygenM23SingularBoundary.w32_sar_zero
        W32.and0w W32.xor0w.
rewrite KeygenM23SingularBoundary.w32_max_word W32.and1w.
trivial.
qed.

lemma threshold_tie_term_exact :
  threshold_tie_term_word = W32.of_int 4800000.
proof.
rewrite /threshold_tie_term_word
        /threshold_tie_value_word
        /threshold_tie_value_i
        /KeygenM23SingularSpec.finish_term_word
        finish_factor_equal_exact
        /KeygenM23SingularSpec.mode2_rem_i /=.
rewrite /(`|>>`) W8.of_uintK /=.
have hs32 :
    W32.sar (W32.of_int 204800000) 10 = W32.of_int 200000.
+ rewrite KeygenM23FinalizeSemantics.w32_sar_nonnegative_of_int
          1,2:/#.
  done.
by rewrite hs32 W32.of_intM'.
qed.

lemma implementation_threshold_tie_acc_exact :
  implementation_threshold_tie_acc_word = W32.of_int 24000000.
proof.
rewrite /implementation_threshold_tie_acc_word
        threshold_tie_term_exact !W32.of_intD' /=.
trivial.
qed.

lemma implementation_threshold_tie_score_exact :
  W64.to_uint implementation_threshold_tie_score_word = 375000.
proof.
rewrite /implementation_threshold_tie_score_word
        implementation_threshold_tie_acc_exact
        KeygenM23FixedPointSemantics.sigextu64_semantics
        W32.to_sintK_small 1:/#
        W64.of_intD'.
rewrite /(`|>>`) W8.of_uintK /=.
rewrite KeygenM23FinalizeSemantics.w64_sar_nonnegative_of_int
        1,2:/#.
rewrite W64.to_uint_small 1:/#.
trivial.
qed.

lemma paper_threshold_tie_score_exact :
  paper_threshold_tie_score_i = 800000.
proof.
by rewrite /paper_threshold_tie_score_i /threshold_tie_value_i
           KeygenM23SingularBoundary.paper_fixed_weight_exact /=.
qed.

lemma threshold_tie_guard_discrepancy :
  W64.to_uint implementation_threshold_tie_score_word <=
    mode2_singular_bound_i /\
  mode2_singular_bound_i < paper_threshold_tie_score_i.
proof.
by rewrite implementation_threshold_tie_score_exact
           paper_threshold_tie_score_exact
           /mode2_singular_bound_i.
qed.

end KeygenM23SingularTieRegression.
