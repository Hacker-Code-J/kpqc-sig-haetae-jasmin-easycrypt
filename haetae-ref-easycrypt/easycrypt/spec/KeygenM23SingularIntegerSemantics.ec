require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

require import BArray1024 BArray2048.
require import KeygenM23SingularSpec KeygenM23SingularFFTSpec
               KeygenM23FixedPointSemantics KeygenM23SingularBoundary.

theory KeygenM23SingularIntegerSemantics.

op fft_treal_int
    (oreal oimag rreal rimag : W32.t) : int =
  KeygenM23FixedPointSemantics.mulrnd16_int
    (W32.to_sint rreal) (W32.to_sint oreal) -
  KeygenM23FixedPointSemantics.mulrnd16_int
    (W32.to_sint rimag) (W32.to_sint oimag).

op fft_timag_int
    (oreal oimag rreal rimag : W32.t) : int =
  KeygenM23FixedPointSemantics.mulrnd16_int
    (W32.to_sint rreal) (W32.to_sint oimag) +
  KeygenM23FixedPointSemantics.mulrnd16_int
    (W32.to_sint rimag) (W32.to_sint oreal).

op fft_even_real_int
    (ureal oreal oimag rreal rimag : W32.t) : int =
  W32.to_sint ureal + fft_treal_int oreal oimag rreal rimag.

op fft_even_imag_int
    (uimag oreal oimag rreal rimag : W32.t) : int =
  W32.to_sint uimag + fft_timag_int oreal oimag rreal rimag.

op fft_odd_real_int
    (ureal oreal oimag rreal rimag : W32.t) : int =
  W32.to_sint ureal - fft_treal_int oreal oimag rreal rimag.

op fft_odd_imag_int
    (uimag oreal oimag rreal rimag : W32.t) : int =
  W32.to_sint uimag - fft_timag_int oreal oimag rreal rimag.

lemma s32_fits_bounds (z : int) :
  KeygenM23SingularBoundary.s32_fits z =>
  W32.min_sint <= z <= W32.max_sint.
proof.
rewrite /KeygenM23SingularBoundary.s32_fits.
smt().
qed.

lemma nonnegative_s32_fits_bounds (z : int) :
  KeygenM23SingularBoundary.nonnegative_s32_fits z =>
  W32.min_sint <= z <= W32.max_sint.
proof.
rewrite /KeygenM23SingularBoundary.nonnegative_s32_fits.
smt().
qed.

lemma word_add_to_sint (a b : W32.t) :
  KeygenM23SingularBoundary.s32_fits
    (W32.to_sint a + W32.to_sint b) =>
  W32.to_sint (a + b) = W32.to_sint a + W32.to_sint b.
proof.
move=> hfit.
apply W32.to_sintD_small.
exact (s32_fits_bounds _ hfit).
qed.

lemma word_sub_to_sint (a b : W32.t) :
  KeygenM23SingularBoundary.s32_fits
    (W32.to_sint a - W32.to_sint b) =>
  W32.to_sint (a - b) = W32.to_sint a - W32.to_sint b.
proof.
move=> hfit.
apply W32.to_sintB_small.
exact (s32_fits_bounds _ hfit).
qed.

lemma w32_of_sintK (w : W32.t) :
  W32.of_int (W32.to_sint w) = w.
proof.
rewrite /W32.to_sint /W32.smod.
case (2 ^ (W32.size - 1) <= W32.to_uint w) => _.
+ by rewrite -W32.of_intS' W32.to_uintK'
             W32.of_int_modulus subr0.
+ by rewrite W32.to_uintK'.
qed.

lemma mulrnd16_safe_to_sint (x y : W32.t) :
  KeygenM23SingularBoundary.mulrnd16_safe x y =>
  W32.to_sint (KeygenM23SingularSpec.mulrnd16_word x y) =
    KeygenM23FixedPointSemantics.mulrnd16_int
      (W32.to_sint x) (W32.to_sint y).
proof.
move=> hsafe.
apply KeygenM23FixedPointSemantics.mulrnd16_word_to_sint.
move: hsafe.
rewrite /KeygenM23SingularBoundary.mulrnd16_safe
        /KeygenM23SingularBoundary.s32_fits
        /KeygenM23FixedPointSemantics.mulrnd16_result_fits /=.
smt().
qed.

lemma fft_init_product_to_sint (coefficient root : W32.t) :
  KeygenM23SingularBoundary.fft_init_product_safe coefficient root =>
  W32.to_sint (coefficient * root) =
    W32.to_sint coefficient * W32.to_sint root.
proof.
move=> hsafe.
have hword :
    coefficient * root =
      W32.of_int (W32.to_sint coefficient * W32.to_sint root).
+ by rewrite -W32.of_intM' !w32_of_sintK.
rewrite hword.
apply W32.to_sintK_small.
move: hsafe.
rewrite /KeygenM23SingularBoundary.fft_init_product_safe
        /KeygenM23SingularBoundary.s32_fits.
smt().
qed.

lemma fft_butterfly_terms_to_sint
    (ureal uimag oreal oimag rreal rimag : W32.t) :
  KeygenM23SingularBoundary.fft_butterfly_safe
    ureal uimag oreal oimag rreal rimag =>
  W32.to_sint
    (KeygenM23SingularSpec.mulrnd16_word rreal oreal -
     KeygenM23SingularSpec.mulrnd16_word rimag oimag) =
      fft_treal_int oreal oimag rreal rimag /\
  W32.to_sint
    (KeygenM23SingularSpec.mulrnd16_word rreal oimag +
     KeygenM23SingularSpec.mulrnd16_word rimag oreal) =
      fft_timag_int oreal oimag rreal rimag.
proof.
rewrite /KeygenM23SingularBoundary.fft_butterfly_safe /=.
move=> [hrr_or [hri_oi [hrr_oi [hri_or
        [htreal [htimag _]]]]]].
have drr_or := mulrnd16_safe_to_sint rreal oreal hrr_or.
have dri_oi := mulrnd16_safe_to_sint rimag oimag hri_oi.
have drr_oi := mulrnd16_safe_to_sint rreal oimag hrr_oi.
have dri_or := mulrnd16_safe_to_sint rimag oreal hri_or.
split.
+ rewrite word_sub_to_sint.
  + by rewrite drr_or dri_oi /fft_treal_int.
  + by rewrite drr_or dri_oi.
+ rewrite word_add_to_sint.
  + by rewrite drr_oi dri_or /fft_timag_int.
  + by rewrite drr_oi dri_or.
qed.

lemma fft_butterfly_outputs_to_sint
    (ureal uimag oreal oimag rreal rimag : W32.t) :
  KeygenM23SingularBoundary.fft_butterfly_safe
    ureal uimag oreal oimag rreal rimag =>
  let treal =
    KeygenM23SingularSpec.mulrnd16_word rreal oreal -
      KeygenM23SingularSpec.mulrnd16_word rimag oimag in
  let timag =
    KeygenM23SingularSpec.mulrnd16_word rreal oimag +
      KeygenM23SingularSpec.mulrnd16_word rimag oreal in
  W32.to_sint (ureal + treal) =
    fft_even_real_int ureal oreal oimag rreal rimag /\
  W32.to_sint (uimag + timag) =
    fft_even_imag_int uimag oreal oimag rreal rimag /\
  W32.to_sint (ureal - treal) =
    fft_odd_real_int ureal oreal oimag rreal rimag /\
  W32.to_sint (uimag - timag) =
    fft_odd_imag_int uimag oreal oimag rreal rimag.
proof.
move=> hsafe /=.
have hterms :=
  fft_butterfly_terms_to_sint
    ureal uimag oreal oimag rreal rimag hsafe.
move: hterms => [dtreal dtimag].
move: hsafe.
rewrite /KeygenM23SingularBoundary.fft_butterfly_safe /=.
move=> [_ [_ [_ [_ [_ [_ [heven_r [heven_i [hodd_r hodd_i]]]]]]]]].
do split.
+ rewrite word_add_to_sint.
  + by rewrite dtreal /fft_even_real_int.
  + by rewrite dtreal.
+ rewrite word_add_to_sint.
  + by rewrite dtimag /fft_even_imag_int.
  + by rewrite dtimag.
+ rewrite word_sub_to_sint.
  + by rewrite dtreal /fft_odd_real_int.
  + by rewrite dtreal.
+ rewrite word_sub_to_sint.
  + by rewrite dtimag /fft_odd_imag_int.
  + by rewrite dtimag.
qed.

lemma fft_sqabs_at_to_sint (input : BArray2048.t) (i : int) :
  let real = BArray2048.get32 input (2 * i) in
  let imag = BArray2048.get32 input (2 * i + 1) in
  KeygenM23SingularBoundary.fft_sqabs_safe real imag =>
  W32.to_sint (KeygenM23SingularSpec.fft_sqabs_at input i) =
    KeygenM23SingularBoundary.fft_sqabs_int real imag.
proof.
rewrite /KeygenM23SingularBoundary.fft_sqabs_safe /=.
move=> [hreal [himag hsum]].
have dreal := mulrnd16_safe_to_sint _ _ hreal.
have dimag := mulrnd16_safe_to_sint _ _ himag.
rewrite /KeygenM23SingularSpec.fft_sqabs_at /=.
rewrite word_add_to_sint.
+ rewrite dreal dimag.
   move: hsum.
   rewrite /KeygenM23SingularBoundary.nonnegative_s32_fits
           /KeygenM23SingularBoundary.s32_fits.
   smt().
+ by rewrite dreal dimag /KeygenM23SingularBoundary.fft_sqabs_int.
qed.

lemma accumulate_step_at_to_sint
    (input : BArray2048.t) (sum : BArray1024.t) (i : int) :
  0 <= i < KeygenM23SingularSpec.singular_words_i =>
  let real = BArray2048.get32 input (2 * i) in
  let imag = BArray2048.get32 input (2 * i + 1) in
  KeygenM23SingularBoundary.fft_accumulate_safe
    (BArray1024.get32 sum i) real imag =>
  W32.to_sint
    (BArray1024.get32
      (KeygenM23SingularSpec.accumulate_step input sum i) i) =
    W32.to_sint (BArray1024.get32 sum i) +
      KeygenM23SingularBoundary.fft_sqabs_int real imag.
proof.
move=> hi /= hsafe.
move: hsafe.
rewrite /KeygenM23SingularBoundary.fft_accumulate_safe /=.
move=> [hsq [_ hacc]].
rewrite /KeygenM23SingularSpec.accumulate_step.
rewrite BArray1024.get_set32E 1:/# 1:/# /=.
rewrite word_add_to_sint.
+ rewrite fft_sqabs_at_to_sint 1:hsq.
   move: hacc.
   rewrite /KeygenM23SingularBoundary.nonnegative_s32_fits
           /KeygenM23SingularBoundary.s32_fits.
   smt().
+ rewrite fft_sqabs_at_to_sint 1:hsq.
   done.
qed.

lemma accumulate_step_frame
    (input : BArray2048.t) (sum : BArray1024.t) (i j : int) :
  0 <= i < KeygenM23SingularSpec.singular_words_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  i <> j =>
  BArray1024.get32
    (KeygenM23SingularSpec.accumulate_step input sum i) j =
  BArray1024.get32 sum j.
proof.
move=> hi hj hne.
rewrite /KeygenM23SingularSpec.accumulate_step.
rewrite BArray1024.get_set32E 1:/# 1:/#.
by rewrite ifF.
qed.

end KeygenM23SingularIntegerSemantics.
