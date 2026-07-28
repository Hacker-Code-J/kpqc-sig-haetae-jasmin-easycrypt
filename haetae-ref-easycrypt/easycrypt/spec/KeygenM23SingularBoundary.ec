require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray20 BArray1024.
require import KeygenM23SingularSpec KeygenM23FixedPointSemantics
               KeygenM23FinalizeSemantics.

theory KeygenM23SingularBoundary.

(* Integer interpretations used only to state the numerical obligations that
   must be discharged before relating the fixed-point program to a DFT. *)
op s32_fits (z : int) : bool =
  -2147483648 <= z < 2147483648.

op nonnegative_s32_fits (z : int) : bool =
  0 <= z < 2147483648.

op s64_fits (z : int) : bool =
  -9223372036854775808 <= z < 9223372036854775808.

op mulrnd16_safe (x y : W32.t) : bool =
  let product = W32.to_sint x * W32.to_sint y in
  s64_fits product /\
  s64_fits (product + KeygenM23FixedPointSemantics.q16_half) /\
  s32_fits
    (KeygenM23FixedPointSemantics.mulrnd16_int
      (W32.to_sint x) (W32.to_sint y)).

op fft_init_product_safe (coefficient root : W32.t) : bool =
  s32_fits (W32.to_sint coefficient * W32.to_sint root).

op fft_butterfly_safe
    (ureal uimag oreal oimag rreal rimag : W32.t) : bool =
  let rr_or =
    KeygenM23FixedPointSemantics.mulrnd16_int
      (W32.to_sint rreal) (W32.to_sint oreal) in
  let ri_oi =
    KeygenM23FixedPointSemantics.mulrnd16_int
      (W32.to_sint rimag) (W32.to_sint oimag) in
  let rr_oi =
    KeygenM23FixedPointSemantics.mulrnd16_int
      (W32.to_sint rreal) (W32.to_sint oimag) in
  let ri_or =
    KeygenM23FixedPointSemantics.mulrnd16_int
      (W32.to_sint rimag) (W32.to_sint oreal) in
  let treal = rr_or - ri_oi in
  let timag = rr_oi + ri_or in
  mulrnd16_safe rreal oreal /\
  mulrnd16_safe rimag oimag /\
  mulrnd16_safe rreal oimag /\
  mulrnd16_safe rimag oreal /\
  s32_fits treal /\
  s32_fits timag /\
  s32_fits (W32.to_sint ureal + treal) /\
  s32_fits (W32.to_sint uimag + timag) /\
  s32_fits (W32.to_sint ureal - treal) /\
  s32_fits (W32.to_sint uimag - timag).

op fft_sqabs_int (real imag : W32.t) : int =
  KeygenM23FixedPointSemantics.mulrnd16_int
    (W32.to_sint real) (W32.to_sint real) +
  KeygenM23FixedPointSemantics.mulrnd16_int
    (W32.to_sint imag) (W32.to_sint imag).

op fft_sqabs_safe (real imag : W32.t) : bool =
  mulrnd16_safe real real /\
  mulrnd16_safe imag imag /\
  nonnegative_s32_fits (fft_sqabs_int real imag).

op fft_accumulate_safe (sum real imag : W32.t) : bool =
  fft_sqabs_safe real imag /\
  nonnegative_s32_fits (W32.to_sint sum) /\
  nonnegative_s32_fits
    (W32.to_sint sum + fft_sqabs_int real imag).

op implementation_finish_factor_i (minimum value : int) : int =
  if minimum = value
  then KeygenM23SingularSpec.mode2_rem_i
  else KeygenM23SingularSpec.mode2_tau_i.

op finish_entry_safe (minimum value : W32.t) : bool =
  let min_i = W32.to_sint minimum in
  let value_i = W32.to_sint value in
  let shifted = (value_i + 66048) %/ 1024 in
  let factor = implementation_finish_factor_i min_i value_i in
  0 <= min_i <= value_i /\
  s32_fits (min_i - value_i) /\
  nonnegative_s32_fits (value_i + 66048) /\
  nonnegative_s32_fits (shifted * factor).

op finish_accumulation_safe
    (best : BArray20.t) (minimum : W32.t) : bool =
  forall i, 0 <= i < KeygenM23SingularSpec.mode2_best_count_i =>
    finish_entry_safe minimum (BArray20.get32 best i) /\
    nonnegative_s32_fits
      (W32.to_sint
         (KeygenM23SingularSpec.finish_acc_prefix best minimum i) +
       ((W32.to_sint (BArray20.get32 best i) + 66048) %/ 1024) *
         implementation_finish_factor_i
           (W32.to_sint minimum)
           (W32.to_sint (BArray20.get32 best i))).

op singular_finish_safe (sum : BArray1024.t) : bool =
  let best = KeygenM23SingularSpec.best_scan sum in
  let minimum = KeygenM23SingularSpec.best_min best in
  finish_accumulation_safe best minimum.

(* The implementation assigns the remainder weight to every selected entry
   tied at the minimum.  The following exact finish-stage calculation starts
   from five already-selected zero entries; it does not characterize the
   output of the preceding FFT and selector on any full mode-2 input. *)
op implementation_zero_tie_weight_i : int =
  KeygenM23SingularSpec.mode2_best_count_i *
  W32.to_uint
    (KeygenM23SingularSpec.finish_factor_word W32.zero W32.zero).

op implementation_zero_tie_acc_word : W32.t =
  let term =
    KeygenM23SingularSpec.finish_term_word W32.zero W32.zero in
  ((((W32.zero + term) + term) + term) + term) + term.

op implementation_zero_tie_score_word : W64.t =
  (sigextu64 implementation_zero_tie_acc_word + W64.of_int 32)
    `|>>` W8.of_int 6.

(* The fixed allocation has one remainder weight and four tau weights, so its
   total is exactly N=256 even when the selected values are tied. *)
op paper_fixed_weight_i : int =
  KeygenM23SingularSpec.mode2_rem_i +
  (KeygenM23SingularSpec.mode2_best_count_i - 1) *
    KeygenM23SingularSpec.mode2_tau_i.

op paper_zero_tie_score_i : int =
  ((((0 + 66048) %/ 1024) * paper_fixed_weight_i) + 32) %/ 64.

lemma w32_sar_zero (shift : W8.t) :
  W32.zero `|>>` shift = W32.zero.
proof.
rewrite /(`|>>`) sarE.
apply W32.ext_eq => i hi.
by rewrite initiE 1:hi.
qed.

lemma w32_max_word :
  W32.of_int 4294967295 = W32.onew.
proof. by rewrite /W32.onew. qed.

lemma finish_factor_zero_exact :
  KeygenM23SingularSpec.finish_factor_word W32.zero W32.zero =
    W32.of_int 24.
proof.
rewrite /KeygenM23SingularSpec.finish_factor_word
        /KeygenM23SingularSpec.mode2_rem_i
        /KeygenM23SingularSpec.mode2_tau_i /=.
by rewrite w32_sar_zero W32.and0w W32.xor0w
           w32_max_word W32.and1w.
qed.

lemma implementation_zero_tie_weight_exact :
  implementation_zero_tie_weight_i = 120.
proof.
by rewrite /implementation_zero_tie_weight_i finish_factor_zero_exact
           /KeygenM23SingularSpec.mode2_best_count_i /=.
qed.

lemma paper_fixed_weight_exact :
  paper_fixed_weight_i = 256.
proof.
by rewrite /paper_fixed_weight_i
           /KeygenM23SingularSpec.mode2_rem_i
           /KeygenM23SingularSpec.mode2_best_count_i
           /KeygenM23SingularSpec.mode2_tau_i /=.
qed.

lemma implementation_zero_tie_score_exact :
  W64.to_uint implementation_zero_tie_score_word = 120.
proof.
rewrite /implementation_zero_tie_score_word
        /implementation_zero_tie_acc_word
        /KeygenM23SingularSpec.finish_term_word
        finish_factor_zero_exact /=.
rewrite /(`|>>`) !W8.of_uintK /=.
have hs32 :
    W32.sar (W32.of_int 66048) 10 = W32.of_int 64.
+ rewrite KeygenM23FinalizeSemantics.w32_sar_nonnegative_of_int
          1,2:/#.
  done.
rewrite !hs32 !W32.of_intM' !W32.of_intD' /=.
rewrite KeygenM23FixedPointSemantics.sigextu64_semantics
        W32.to_sintK_small 1:/# W64.of_intD'.
have hs64 :
    W64.sar (W64.of_int 7712) 6 = W64.of_int 120.
+ rewrite KeygenM23FinalizeSemantics.w64_sar_nonnegative_of_int
          1,2:/#.
  done.
rewrite hs64 W64.to_uint_small 1:/#.
trivial.
qed.

lemma paper_zero_tie_score_exact :
  paper_zero_tie_score_i = 256.
proof.
by rewrite /paper_zero_tie_score_i paper_fixed_weight_exact /=.
qed.

lemma zero_tie_finish_discrepancy :
  W64.to_uint implementation_zero_tie_score_word = 120 /\
  paper_zero_tie_score_i = 256 /\
  W64.to_uint implementation_zero_tie_score_word <>
    paper_zero_tie_score_i.
proof.
rewrite implementation_zero_tie_score_exact paper_zero_tie_score_exact.
trivial.
qed.

end KeygenM23SingularBoundary.
