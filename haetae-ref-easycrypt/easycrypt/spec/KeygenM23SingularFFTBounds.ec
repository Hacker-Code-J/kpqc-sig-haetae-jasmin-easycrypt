require import AllCore IntDiv List Ring StdOrder Real BitEncoding.

from Jasmin require import JModel_x86.

import RField.
import BitReverse.

require import BArray1024 BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23IdealFFTSchedule
  KeygenM23FixedPointSemantics
  KeygenM23SingularBoundary
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTKPrefixBridge
  KeygenM23SingularIntegerSemantics
  KeygenM23FFTTableCertificate
  KeygenMode2ParentTarget.

import KeygenM23SingularFFTInitBridge.
import KeygenM23SingularFFTButterflyBridge.
import KeygenM23SingularFFTKPrefixBridge.
import KeygenM23ComplexReal.

theory KeygenM23SingularFFTBounds.

(* Raw signed-Q16 coordinate bounds.  Keeping this invariant over integers
   makes every machine overflow premise explicit before decoding to reals. *)
op fft_word_bound (data : BArray2048.t) (bound : int) : bool =
  forall i, 0 <= i < 256 =>
    -bound <= W32.to_sint (fft_real_word data i) <= bound /\
    -bound <= W32.to_sint (fft_imag_word data i) <= bound.

op fft_root_word_bound (roots : BArray2048.t) : bool =
  fft_word_bound roots 65536.

op fft_round_word_bound (round : int) : int =
  131072 * 3 ^ round.

op fft_word_bound_at
    (data : BArray2048.t) (i bound : int) : bool =
  -bound <= W32.to_sint (fft_real_word data i) <= bound /\
  -bound <= W32.to_sint (fft_imag_word data i) <= bound.

op fft_k_input_word_bound
    (data : BArray2048.t) (n md2 stride : W64.t)
    (processed bound : int) : bool =
  forall k, 0 <= k < processed =>
    fft_word_bound_at data (fft_k_even_index n k) bound /\
    fft_word_bound_at data (fft_k_odd_index n md2 k) bound.

lemma fft_word_bound_at_global
    (data : BArray2048.t) (i bound : int) :
  0 <= i < 256 =>
  fft_word_bound data bound =>
  fft_word_bound_at data i bound.
proof.
move=> hi hdata.
rewrite /fft_word_bound_at.
exact (hdata i hi).
qed.

lemma fft_word_bound_mono
    (data : BArray2048.t) (small large : int) :
  0 <= small <= large =>
  fft_word_bound data small =>
  fft_word_bound data large.
proof.
move=> hbounds hdata.
rewrite /fft_word_bound.
move=> i hi.
have [hre him] := hdata i hi.
split; smt().
qed.

lemma symmetric_product_bound
    (x y xbound ybound : int) :
  0 <= xbound =>
  0 <= ybound =>
  -xbound <= x <= xbound =>
  -ybound <= y <= ybound =>
  -(xbound * ybound) <= x * y <= xbound * ybound.
proof.
move=> hxb hyb hx hy.
case (0 <= x) => hx0.
+ case (0 <= y) => hy0.
  + have hxy0 : 0 <= x * y by
      exact (IntOrder.mulr_ge0 x y hx0 hy0).
    have hxyb : x * y <= xbound * ybound by
      apply IntOrder.ler_pmul; smt().
    smt().
  have hny0 : 0 <= -y by smt().
  have hxny : x * (-y) <= xbound * ybound by
    apply IntOrder.ler_pmul; smt().
  have hxy0 : x * y <= 0 by
    have := IntOrder.mulr_ge0 x (-y) hx0 hny0; smt().
  smt().
have hnx0 : 0 <= -x by smt().
case (0 <= y) => hy0.
+ have hnxy : (-x) * y <= xbound * ybound by
    apply IntOrder.ler_pmul; smt().
  have hxy0 : x * y <= 0 by
    have := IntOrder.mulr_ge0 (-x) y hnx0 hy0; smt().
  smt().
have hny0 : 0 <= -y by smt().
have hnxny : (-x) * (-y) <= xbound * ybound by
  apply IntOrder.ler_pmul; smt().
have hxy0 : 0 <= x * y by
  have := IntOrder.mulr_ge0 (-x) (-y) hnx0 hny0; smt().
smt().
qed.

lemma q16_round_scaled_bound (z bound : int) :
  0 <= bound =>
  -(65536 * bound) <= z <= 65536 * bound =>
  -bound <= KeygenM23FixedPointSemantics.q16_round z <= bound.
proof.
move=> hbound hz.
have herr := KeygenM23FixedPointSemantics.q16_round_error z.
move: herr.
rewrite /KeygenM23FixedPointSemantics.q16_scale
        /KeygenM23FixedPointSemantics.q16_half.
smt().
qed.

lemma mulrnd16_int_root_bound (root value bound : int) :
  0 <= bound =>
  -65536 <= root <= 65536 =>
  -bound <= value <= bound =>
  -bound <=
    KeygenM23FixedPointSemantics.mulrnd16_int root value
  <= bound.
proof.
move=> hbound hroot hvalue.
have hproduct :=
  symmetric_product_bound root value 65536 bound _ _ hroot hvalue.
+ smt().
+ exact hbound.
rewrite /KeygenM23FixedPointSemantics.mulrnd16_int.
apply (q16_round_scaled_bound (root * value) bound hbound).
smt().
qed.

lemma mulrnd16_safe_from_root_bound
    (root value : W32.t) (bound : int) :
  0 <= bound <= 286654464 =>
  -65536 <= W32.to_sint root <= 65536 =>
  -bound <= W32.to_sint value <= bound =>
  KeygenM23SingularBoundary.mulrnd16_safe root value.
proof.
move=> hbound hroot hvalue.
have hproduct :=
  symmetric_product_bound
    (W32.to_sint root) (W32.to_sint value)
    65536 bound _ _ hroot hvalue.
+ smt().
+ smt().
have hround :=
  mulrnd16_int_root_bound
    (W32.to_sint root) (W32.to_sint value) bound
    _ hroot hvalue.
+ smt().
rewrite /KeygenM23SingularBoundary.mulrnd16_safe
        /KeygenM23SingularBoundary.s64_fits
        /KeygenM23SingularBoundary.s32_fits /=.
do split; smt().
qed.

lemma fft_butterfly_safe_from_word_bounds
    (ureal uimag oreal oimag rreal rimag : W32.t)
    (bound : int) :
  0 <= bound <= 286654464 =>
  -bound <= W32.to_sint ureal <= bound =>
  -bound <= W32.to_sint uimag <= bound =>
  -bound <= W32.to_sint oreal <= bound =>
  -bound <= W32.to_sint oimag <= bound =>
  -65536 <= W32.to_sint rreal <= 65536 =>
  -65536 <= W32.to_sint rimag <= 65536 =>
  KeygenM23SingularBoundary.fft_butterfly_safe
    ureal uimag oreal oimag rreal rimag.
proof.
move=> hbound hur hui hor hoi hrr hri.
have hs_rr_or :=
  mulrnd16_safe_from_root_bound rreal oreal bound hbound hrr hor.
have hs_ri_oi :=
  mulrnd16_safe_from_root_bound rimag oimag bound hbound hri hoi.
have hs_rr_oi :=
  mulrnd16_safe_from_root_bound rreal oimag bound hbound hrr hoi.
have hs_ri_or :=
  mulrnd16_safe_from_root_bound rimag oreal bound hbound hri hor.
have hb_rr_or :=
  mulrnd16_int_root_bound
    (W32.to_sint rreal) (W32.to_sint oreal) bound
    _ hrr hor.
+ smt().
have hb_ri_oi :=
  mulrnd16_int_root_bound
    (W32.to_sint rimag) (W32.to_sint oimag) bound
    _ hri hoi.
+ smt().
have hb_rr_oi :=
  mulrnd16_int_root_bound
    (W32.to_sint rreal) (W32.to_sint oimag) bound
    _ hrr hoi.
+ smt().
have hb_ri_or :=
  mulrnd16_int_root_bound
    (W32.to_sint rimag) (W32.to_sint oreal) bound
    _ hri hor.
+ smt().
rewrite /KeygenM23SingularBoundary.fft_butterfly_safe /=.
split.
+ exact hs_rr_or.
split.
+ exact hs_ri_oi.
split.
+ exact hs_rr_oi.
split.
+ exact hs_ri_or.
split.
+ rewrite /KeygenM23SingularBoundary.s32_fits; smt().
split.
+ rewrite /KeygenM23SingularBoundary.s32_fits; smt().
split.
+ rewrite /KeygenM23SingularBoundary.s32_fits; smt().
split.
+ rewrite /KeygenM23SingularBoundary.s32_fits; smt().
split.
+ rewrite /KeygenM23SingularBoundary.s32_fits; smt().
rewrite /KeygenM23SingularBoundary.s32_fits; smt().
qed.

lemma fft_butterfly_safe_at_from_bound
    (data roots : BArray2048.t) (even odd twid bound : int) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  0 <= bound <= 286654464 =>
  fft_word_bound data bound =>
  fft_root_word_bound roots =>
  fft_butterfly_safe_at data roots even odd twid.
proof.
move=> heven hodd htwid hbound hdata hroots.
have [her hei] := hdata even heven.
have [hor hoi] := hdata odd hodd.
have [hrr hri] := hroots twid htwid.
rewrite /fft_butterfly_safe_at.
exact
  (fft_butterfly_safe_from_word_bounds
    (fft_real_word data even) (fft_imag_word data even)
    (fft_real_word data odd) (fft_imag_word data odd)
    (fft_real_word roots twid) (fft_imag_word roots twid)
    bound hbound her hei hor hoi hrr hri).
qed.

lemma actual_fft_root_word_bound :
  fft_root_word_bound KeygenMode2ParentTarget.jfft_roots.
proof.
rewrite /fft_root_word_bound /fft_word_bound.
move=> i hi.
rewrite /fft_real_word /fft_imag_word.
split.
+ have hr :=
    KeygenM23FFTTableCertificate.jfft_roots_signed_bound
      (2 * i) _.
  + smt().
  exact hr.
+ have him :=
    KeygenM23FFTTableCertificate.jfft_roots_signed_bound
      (2 * i + 1) _.
  + smt().
  exact him.
qed.

lemma q16_decode_scaled_int_eq (out coefficient root : int) :
  out%r / 65536%r = coefficient%r * (root%r / 65536%r) =>
  out = coefficient * root.
proof.
move=> hdecode.
have hscale : 65536%r <> 0%r by smt().
have hdiv :
  out%r / 65536%r =
  (coefficient * root)%r / 65536%r.
+ rewrite fromintM hdecode.
  ring.
have hcross :=
  iffLR _ _
    (RField.eqf_div
      out%r 65536%r (coefficient * root)%r 65536%r
      hscale hscale)
    hdiv.
have hreal : out%r = (coefficient * root)%r.
+ exact (RField.mulIf (65536%r) hscale _ _ hcross).
by rewrite -eq_fromint.
qed.

lemma actual_fft_init_word_bound2
    (data : BArray2048.t) (xp : BArray1024.t) :
  fft_coefficient_bound xp 2 =>
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_init_and_bitrev
      data xp
      KeygenMode2ParentTarget.jfft_roots
      KeygenMode2ParentTarget.jfft_brv8)
    131072.
proof.
move=> hcoeff.
rewrite /fft_word_bound.
move=> i hi.
have hsrc := KeygenM23IdealFFTSchedule.bsrev8_range i.
have hsrc_bounds : 0 <= bsrev 8 i < 256 by
  move: hsrc; rewrite mem_range; smt().
have hc := hcoeff (bsrev 8 i) hsrc_bounds.
have [hrr hri] :=
  actual_fft_root_word_bound (bsrev 8 i) hsrc_bounds.
have hdecode :=
  actual_fft_init_and_bitrev_decode_bound2 data xp i hi hcoeff.
have hre := congr1 creal _ _ hdecode.
have him := congr1 cimag _ _ hdecode.
rewrite /fft_decode_at /fft_real_word /fft_imag_word
        /q16_decode_word /q16_decode_int /creal
        /fft_table_twist /cscale_int /cscale
        /fft_root_decode_at /= in hre.
rewrite /fft_decode_at /fft_real_word /fft_imag_word
        /q16_decode_word /q16_decode_int /cimag
        /fft_table_twist /cscale_int /cscale
        /fft_root_decode_at /= in him.
have hre_int :
  W32.to_sint
    (fft_real_word
      (KeygenM23SingularFFTSpec.fft_init_and_bitrev
        data xp
        KeygenMode2ParentTarget.jfft_roots
        KeygenMode2ParentTarget.jfft_brv8)
      i) =
  W32.to_sint (BArray1024.get32 xp (bsrev 8 i)) *
  W32.to_sint
    (fft_real_word KeygenMode2ParentTarget.jfft_roots (bsrev 8 i)).
+ apply q16_decode_scaled_int_eq.
  move: hre.
  by rewrite /fft_real_word.
have him_int :
  W32.to_sint
    (fft_imag_word
      (KeygenM23SingularFFTSpec.fft_init_and_bitrev
        data xp
        KeygenMode2ParentTarget.jfft_roots
        KeygenMode2ParentTarget.jfft_brv8)
      i) =
  W32.to_sint (BArray1024.get32 xp (bsrev 8 i)) *
  W32.to_sint
    (fft_imag_word KeygenMode2ParentTarget.jfft_roots (bsrev 8 i)).
+ apply q16_decode_scaled_int_eq.
  move: him.
  by rewrite /fft_imag_word.
have hproduct_r :=
  symmetric_product_bound
    (W32.to_sint (BArray1024.get32 xp (bsrev 8 i)))
    (W32.to_sint
      (fft_real_word KeygenMode2ParentTarget.jfft_roots (bsrev 8 i)))
    2 65536 _ _ hc hrr.
+ smt().
+ smt().
have hproduct_i :=
  symmetric_product_bound
    (W32.to_sint (BArray1024.get32 xp (bsrev 8 i)))
    (W32.to_sint
      (fft_imag_word KeygenMode2ParentTarget.jfft_roots (bsrev 8 i)))
    2 65536 _ _ hc hri.
+ smt().
+ smt().
rewrite hre_int him_int.
rewrite /= in hproduct_r.
rewrite /= in hproduct_i.
split.
+ exact hproduct_r.
+ exact hproduct_i.
qed.

lemma fft_decode_at_eq_to_sint
    (lhs rhs : BArray2048.t) (i : int) :
  fft_decode_at lhs i = fft_decode_at rhs i =>
  W32.to_sint (fft_real_word lhs i) =
    W32.to_sint (fft_real_word rhs i) /\
  W32.to_sint (fft_imag_word lhs i) =
    W32.to_sint (fft_imag_word rhs i).
proof.
move=> heq.
have hre := congr1 creal _ _ heq.
have him := congr1 cimag _ _ heq.
rewrite /fft_decode_at /fft_real_word /fft_imag_word
        /q16_decode_word /q16_decode_int /creal /cimag /= in hre.
rewrite /fft_decode_at /fft_real_word /fft_imag_word
        /q16_decode_word /q16_decode_int /creal /cimag /= in him.
split.
+ rewrite -eq_fromint.
  have hscale : 65536%r <> 0%r by smt().
  have hre' :
    (W32.to_sint (fft_real_word lhs i))%r * 65536%r =
    (W32.to_sint (fft_real_word rhs i))%r * 65536%r.
  + move: hre.
    by rewrite RField.eqf_div 1,2:hscale.
  exact (RField.mulIf (65536%r) hscale _ _ hre').
+ rewrite -eq_fromint.
  have hscale : 65536%r <> 0%r by smt().
  have him' :
    (W32.to_sint (fft_imag_word lhs i))%r * 65536%r =
    (W32.to_sint (fft_imag_word rhs i))%r * 65536%r.
  + move: him.
    by rewrite RField.eqf_div 1,2:hscale.
  exact (RField.mulIf (65536%r) hscale _ _ him').
qed.

lemma fft_butterfly_term_bound_from_word_bounds
    (oreal oimag rreal rimag : W32.t) (bound : int) :
  0 <= bound =>
  -bound <= W32.to_sint oreal <= bound =>
  -bound <= W32.to_sint oimag <= bound =>
  -65536 <= W32.to_sint rreal <= 65536 =>
  -65536 <= W32.to_sint rimag <= 65536 =>
  -2 * bound <=
    KeygenM23SingularIntegerSemantics.fft_treal_int
      oreal oimag rreal rimag
  <= 2 * bound /\
  -2 * bound <=
    KeygenM23SingularIntegerSemantics.fft_timag_int
      oreal oimag rreal rimag
  <= 2 * bound.
proof.
move=> hbound hor hoi hrr hri.
have hb_rr_or :=
  mulrnd16_int_root_bound
    (W32.to_sint rreal) (W32.to_sint oreal) bound
    hbound hrr hor.
have hb_ri_oi :=
  mulrnd16_int_root_bound
    (W32.to_sint rimag) (W32.to_sint oimag) bound
    hbound hri hoi.
have hb_rr_oi :=
  mulrnd16_int_root_bound
    (W32.to_sint rreal) (W32.to_sint oimag) bound
    hbound hrr hoi.
have hb_ri_or :=
  mulrnd16_int_root_bound
    (W32.to_sint rimag) (W32.to_sint oreal) bound
    hbound hri hor.
rewrite /KeygenM23SingularIntegerSemantics.fft_treal_int
        /KeygenM23SingularIntegerSemantics.fft_timag_int.
smt().
qed.

lemma fft_butterfly_word_bound_step
    (data roots : BArray2048.t) (even odd twid bound : int) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  even <> odd =>
  0 <= bound <= 286654464 =>
  fft_word_bound data bound =>
  fft_root_word_bound roots =>
  let output =
    KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid) in
  fft_butterfly_safe_at data roots even odd twid /\
  fft_word_bound output (3 * bound).
proof.
move=> heven hodd htwid hne hbound hdata hroots /=.
have hsafe :=
  fft_butterfly_safe_at_from_bound
    data roots even odd twid bound
    heven hodd htwid hbound hdata hroots.
have [hur hui] := hdata even heven.
have [hor hoi] := hdata odd hodd.
have [hrr hri] := hroots twid htwid.
have hterms :=
  fft_butterfly_term_bound_from_word_bounds
    (fft_real_word data odd) (fft_imag_word data odd)
    (fft_real_word roots twid) (fft_imag_word roots twid)
    bound _ hor hoi hrr hri.
+ smt().
have hsafe_scalar :
  KeygenM23SingularBoundary.fft_butterfly_safe
    (fft_real_word data even) (fft_imag_word data even)
    (fft_real_word data odd) (fft_imag_word data odd)
    (fft_real_word roots twid) (fft_imag_word roots twid).
+ exact hsafe.
have hsem :=
  KeygenM23SingularIntegerSemantics.fft_butterfly_outputs_to_sint
    (fft_real_word data even) (fft_imag_word data even)
    (fft_real_word data odd) (fft_imag_word data odd)
    (fft_real_word roots twid) (fft_imag_word roots twid)
    hsafe_scalar.
move: hsem => [hsem_er [hsem_ei [hsem_or hsem_oi]]].
have hwords :=
  fft_butterfly_words_written
    data roots even odd twid heven hodd htwid hne.
move: hwords => [hword_er [hword_ei [hword_or hword_oi]]].
split.
+ exact hsafe.
rewrite /fft_word_bound.
move=> j hj.
case (j = even) => hjeven.
+ rewrite hjeven hword_er hword_ei hsem_er hsem_ei.
  split; smt().
case (j = odd) => hjodd.
+ rewrite hjodd hword_or hword_oi hsem_or hsem_oi.
  split; smt().
have hframe :=
  fft_butterfly_decode_frame
    data roots even odd twid j
    heven hodd htwid hj hjeven hjodd.
have [hframe_r hframe_i] :=
  fft_decode_at_eq_to_sint
    (KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid))
    data j hframe.
have [hjr hji] := hdata j hj.
rewrite hframe_r hframe_i.
split; smt().
qed.

lemma fft_butterfly_word_bound_update
    (data roots : BArray2048.t)
    (even odd twid input_bound output_bound : int) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  even <> odd =>
  0 <= input_bound <= 286654464 =>
  3 * input_bound <= output_bound =>
  fft_word_bound data output_bound =>
  fft_word_bound_at data even input_bound =>
  fft_word_bound_at data odd input_bound =>
  fft_root_word_bound roots =>
  let output =
    KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid) in
  fft_butterfly_safe_at data roots even odd twid /\
  fft_word_bound output output_bound.
proof.
move=> heven hodd htwid hne hinput hgrowth hglobal.
rewrite /fft_word_bound_at.
move=> [hur hui] [hor hoi] hroots /=.
have [hrr hri] := hroots twid htwid.
have hsafe_scalar :=
  fft_butterfly_safe_from_word_bounds
    (fft_real_word data even) (fft_imag_word data even)
    (fft_real_word data odd) (fft_imag_word data odd)
    (fft_real_word roots twid) (fft_imag_word roots twid)
    input_bound hinput hur hui hor hoi hrr hri.
have hsafe : fft_butterfly_safe_at data roots even odd twid.
+ exact hsafe_scalar.
have hterms :=
  fft_butterfly_term_bound_from_word_bounds
    (fft_real_word data odd) (fft_imag_word data odd)
    (fft_real_word roots twid) (fft_imag_word roots twid)
    input_bound _ hor hoi hrr hri.
+ smt().
have hsem :=
  KeygenM23SingularIntegerSemantics.fft_butterfly_outputs_to_sint
    (fft_real_word data even) (fft_imag_word data even)
    (fft_real_word data odd) (fft_imag_word data odd)
    (fft_real_word roots twid) (fft_imag_word roots twid)
    hsafe_scalar.
move: hsem => [hsem_er [hsem_ei [hsem_or hsem_oi]]].
have hwords :=
  fft_butterfly_words_written
    data roots even odd twid heven hodd htwid hne.
move: hwords => [hword_er [hword_ei [hword_or hword_oi]]].
split.
+ exact hsafe.
rewrite /fft_word_bound.
move=> j hj.
case (j = even) => hjeven.
+ rewrite hjeven hword_er hword_ei hsem_er hsem_ei.
  split; smt().
case (j = odd) => hjodd.
+ rewrite hjodd hword_or hword_oi hsem_or hsem_oi.
  split; smt().
have hframe :=
  fft_butterfly_decode_frame
    data roots even odd twid j
    heven hodd htwid hj hjeven hjodd.
have [hframe_r hframe_i] :=
  fft_decode_at_eq_to_sint
    (KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid))
    data j hframe.
have [hjr hji] := hglobal j hj.
rewrite hframe_r hframe_i.
split.
+ exact hjr.
+ exact hji.
qed.

lemma fft_k_prefix_safe_bound
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed input_bound output_bound : int) :
  fft_k_schedule_wf n md2 stride processed =>
  0 <= input_bound <= 286654464 =>
  3 * input_bound <= output_bound =>
  fft_word_bound data output_bound =>
  fft_k_input_word_bound
    data n md2 stride processed input_bound =>
  fft_root_word_bound roots =>
  fft_k_prefix_safe data roots n md2 stride processed /\
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_k_prefix
      data roots n md2 stride processed)
    output_bound.
proof.
move=> hwf hinput hgrowth hglobal hlocal hroots.
have hgeneral :
  forall p, 0 <= p =>
    fft_k_schedule_wf n md2 stride p =>
    fft_k_input_word_bound data n md2 stride p input_bound =>
    fft_k_prefix_safe data roots n md2 stride p /\
    fft_word_bound
      (KeygenM23SingularFFTSpec.fft_k_prefix
        data roots n md2 stride p)
      output_bound.
+ apply intind.
  + move=> _ _.
    split.
    + rewrite /fft_k_prefix_safe.
      move=> k hk.
      smt().
    by rewrite KeygenM23SingularFFTSpec.fft_k_prefix0.
  + move=> p hp0 ih hwfS hlocalS.
    have hwfP := fft_k_schedule_wf_prev n md2 stride p hp0 hwfS.
    have hlocalP :
      fft_k_input_word_bound data n md2 stride p input_bound.
    + move: hlocalS.
      rewrite /fft_k_input_word_bound.
      move=> h k hk.
      apply h.
      smt().
    have [hsafeP hboundP] := ih hwfP hlocalP.
    have hp : 0 <= p < p + 1 by smt().
    have [hbase_even hbase_odd] := hlocalS p hp.
    have heven :=
      fft_k_even_index_bounds n md2 stride (p + 1) p hwfS hp.
    have hodd :=
      fft_k_odd_index_bounds n md2 stride (p + 1) p hwfS hp.
    have htwid :=
      fft_k_twid_index_bounds n md2 stride (p + 1) p hwfS hp.
    have hne :=
      fft_k_even_odd_neq n md2 stride (p + 1) p hwfS hp.
    have hdecode_even :=
      fft_k_prefix_decode
        data roots n md2 stride p (fft_k_even_index n p)
        hwfP heven hsafeP.
    have hpending_even :=
      fft_k_prefix_decode_at_pending_even
        data roots n md2 stride p hp0 hwfS.
    have heq_even :
      fft_decode_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        (fft_k_even_index n p) =
      fft_decode_at data (fft_k_even_index n p) by
      rewrite hdecode_even hpending_even.
    have [heq_er heq_ei] :=
      fft_decode_at_eq_to_sint
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        data (fft_k_even_index n p) heq_even.
    have hcurrent_even :
      fft_word_bound_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        (fft_k_even_index n p) input_bound.
    + move: hbase_even.
      rewrite /fft_word_bound_at heq_er heq_ei.
      done.
    have hdecode_odd :=
      fft_k_prefix_decode
        data roots n md2 stride p (fft_k_odd_index n md2 p)
        hwfP hodd hsafeP.
    have hpending_odd :=
      fft_k_prefix_decode_at_pending_odd
        data roots n md2 stride p hp0 hwfS.
    have heq_odd :
      fft_decode_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        (fft_k_odd_index n md2 p) =
      fft_decode_at data (fft_k_odd_index n md2 p) by
      rewrite hdecode_odd hpending_odd.
    have [heq_or heq_oi] :=
      fft_decode_at_eq_to_sint
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        data (fft_k_odd_index n md2 p) heq_odd.
    have hcurrent_odd :
      fft_word_bound_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        (fft_k_odd_index n md2 p) input_bound.
    + move: hbase_odd.
      rewrite /fft_word_bound_at heq_or heq_oi.
      done.
    have hstep :=
      fft_butterfly_word_bound_update
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        roots
        (fft_k_even_index n p)
        (fft_k_odd_index n md2 p)
        (fft_k_twid_index stride p)
        input_bound output_bound
        heven hodd htwid hne hinput hgrowth hboundP
        hcurrent_even hcurrent_odd hroots.
    move: hstep => [hsafe_step hbound_step].
    split.
    + rewrite /fft_k_prefix_safe.
      move=> k hk.
      case (k < p) => hkp.
      + apply hsafeP.
        smt().
      have -> : k = p by smt().
      exact hsafe_step.
    rewrite KeygenM23SingularFFTSpec.fft_k_prefixS 1:hp0.
    rewrite /KeygenM23SingularFFTSpec.fft_k_step /=.
    rewrite fft_k_odd_wordE fft_k_even_wordE fft_k_twid_wordE.
    exact hbound_step.
have hprocessed : 0 <= processed by
  move: hwf; rewrite /fft_k_schedule_wf; smt().
exact (hgeneral processed hprocessed hwf hlocal).
qed.

lemma fft_round_word_bound0 :
  fft_round_word_bound 0 = 131072.
proof. by rewrite /fft_round_word_bound expr0. qed.

lemma fft_round_word_boundS (round : int) :
  0 <= round =>
  fft_round_word_bound (round + 1) =
    3 * fft_round_word_bound round.
proof.
move=> hround.
rewrite /fft_round_word_bound exprSr 1:hround.
ring.
qed.

lemma fft_round_word_bound_8 :
  fft_round_word_bound 8 = 859963392.
proof. by rewrite /fft_round_word_bound /=. qed.

lemma fft_round_word_bound_exec (round : int) :
  0 <= round < 8 =>
  0 <= fft_round_word_bound round <= 286654464.
proof.
move=> hround.
have hcases :
     round = 0 \/ round = 1 \/ round = 2 \/ round = 3
  \/ round = 4 \/ round = 5 \/ round = 6 \/ round = 7 by smt().
elim hcases => [->|hcases]; first by rewrite /fft_round_word_bound /=.
elim hcases => [->|hcases]; first by rewrite /fft_round_word_bound /=.
elim hcases => [->|hcases]; first by rewrite /fft_round_word_bound /=.
elim hcases => [->|hcases]; first by rewrite /fft_round_word_bound /=.
elim hcases => [->|hcases]; first by rewrite /fft_round_word_bound /=.
elim hcases => [->|hcases]; first by rewrite /fft_round_word_bound /=.
elim hcases => [->|->]; by rewrite /fft_round_word_bound /=.
qed.

lemma fft_round_word_bound_all (round : int) :
  0 <= round <= 8 =>
  0 <= fft_round_word_bound round < 2147483648.
proof.
move=> hround.
case (round < 8) => hexec.
+ have h := fft_round_word_bound_exec round _; smt().
have -> : round = 8 by smt().
rewrite fft_round_word_bound_8.
smt().
qed.

end KeygenM23SingularFFTBounds.
