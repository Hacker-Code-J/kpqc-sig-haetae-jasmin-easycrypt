require import AllCore IntDiv List Ring StdOrder Real BitEncoding.

from Jasmin require import JModel_x86.

import RField RealOrder.
import SLH64.
import BitReverse.

require import BArray512 BArray1024 BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularBoundary
  KeygenM23SingularFFTSpec
  KeygenM23SingularIntegerSemantics
  KeygenM23FFTTableCertificate
  KeygenM23RootTableTargetBridge
  KeygenMode2ParentTarget.

import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule.

theory KeygenM23SingularFFTInitBridge.

(* Signed Q16 decoding is kept explicit at this boundary.  In particular,
   none of the statements below silently interprets a wrapped W32 operation
   as an integer operation. *)
op q16_decode_int (z : int) : real =
  z%r / 65536%r.

op q16_decode_word (w : W32.t) : real =
  q16_decode_int (W32.to_sint w).

op fft_decode_at (data : BArray2048.t) (i : int) : complex =
  (q16_decode_word (BArray2048.get32 data (2 * i)),
   q16_decode_word (BArray2048.get32 data (2 * i + 1))).

op fft_decode (data : BArray2048.t) : cvector =
  fun i => fft_decode_at data i.

op fft_vector_close
    (eps : real) (data : BArray2048.t) (target : cvector) : bool =
  forall i, 0 <= i < 256 =>
    cclose eps (fft_decode_at data i) (target i).

op fft_root_decode_at (roots : BArray2048.t) (i : int) : complex =
  fft_decode_at roots i.

op fft_coefficient_vector (xp : BArray1024.t) : cvector =
  fun i => cof_int (W32.to_sint (BArray1024.get32 xp i)).

op fft_coefficient_bound
    (xp : BArray1024.t) (bound : int) : bool =
  forall i, 0 <= i < 256 =>
    -bound <= W32.to_sint (BArray1024.get32 xp i) <= bound.

op fft_table_twist
    (xp : BArray1024.t) (roots : BArray2048.t) (i : int) : complex =
  cscale_int
    (W32.to_sint (BArray1024.get32 xp i))
    (fft_root_decode_at roots i).

op fft_table_twist_vector
    (xp : BArray1024.t) (roots : BArray2048.t) : cvector =
  fun i => fft_table_twist xp roots i.

op fft_init_cell_safe
    (xp : BArray1024.t) (roots : BArray2048.t) (i : int) : bool =
  KeygenM23SingularBoundary.fft_init_product_safe
    (BArray1024.get32 xp i)
    (BArray2048.get32 roots (2 * i)) /\
  KeygenM23SingularBoundary.fft_init_product_safe
    (BArray1024.get32 xp i)
    (BArray2048.get32 roots (2 * i + 1)).

op fft_init_prefix_safe
    (xp : BArray1024.t) (roots : BArray2048.t)
    (processed : int) : bool =
  forall i, 0 <= i < processed => fft_init_cell_safe xp roots i.

lemma fft_init_shift_index (i : int) :
  0 <= i < 256 =>
  W64.to_uint
    (W64.of_int i `<<` W8.of_int 1) = 2 * i.
proof.
move=> hi.
rewrite W64.shl_shlw 1:/# W64.shlMP 1:/#.
rewrite W64.of_uintK /=.
by rewrite modz_small 1:/#; ring.
qed.

lemma fft_init_shift_index_succ (i : int) :
  0 <= i < 256 =>
  W64.to_uint
    ((W64.of_int i `<<` W8.of_int 1) + W64.one) =
  2 * i + 1.
proof.
move=> hi.
rewrite W64.to_uintD_small.
+ rewrite fft_init_shift_index 1:hi W64.to_uint1.
  smt().
+ by rewrite fft_init_shift_index 1:hi W64.to_uint1.
qed.

lemma fft_real_word_index_bounds (i : int) :
  0 <= i < 256 =>
  0 <= 2 * i /\ 4 * (2 * i + 1) <= 2048.
proof. smt(). qed.

lemma fft_imag_word_index_bounds (i : int) :
  0 <= i < 256 =>
  0 <= 2 * i + 1 /\ 4 * (2 * i + 1 + 1) <= 2048.
proof. smt(). qed.

lemma coefficient2_product_s32 (coefficient root : int) :
  -2 <= coefficient <= 2 =>
  -65536 <= root <= 65536 =>
  KeygenM23SingularBoundary.s32_fits (coefficient * root).
proof.
move=> hcoefficient hroot.
rewrite /KeygenM23SingularBoundary.s32_fits.
have hcases :
  coefficient = -2 \/
  coefficient = -1 \/
  coefficient = 0 \/
  coefficient = 1 \/
  coefficient = 2 by smt().
elim hcases => [hcase | hcases].
+ rewrite hcase; smt().
elim hcases => [hcase | hcases].
+ rewrite hcase; smt().
elim hcases => [hcase | hcases].
+ rewrite hcase; smt().
elim hcases => [hcase | hcase].
+ rewrite hcase; smt().
rewrite hcase; smt().
qed.

lemma fft_init_shift_brv (w : W16.t) :
  W64.to_uint
    (zeroextu64 w `<<` W8.of_int 1) =
  2 * W16.to_uint w.
proof.
rewrite /zeroextu64 W64.shl_shlw 1:/# W64.shlMP 1:/#.
rewrite W64.of_uintK /=.
have hw : 0 <= W16.to_uint w < 65536 by
  smt(W16.to_uint_cmp).
by rewrite modz_small 1:/#; ring.
qed.

lemma fft_init_shift_brv_succ (w : W16.t) :
  W64.to_uint
    ((zeroextu64 w `<<` W8.of_int 1) + W64.one) =
  2 * W16.to_uint w + 1.
proof.
rewrite W64.to_uintD_small.
+ rewrite fft_init_shift_brv W64.to_uint1.
  have hw : 0 <= W16.to_uint w < 65536 by
    smt(W16.to_uint_cmp).
  smt().
+ by rewrite fft_init_shift_brv W64.to_uint1.
qed.

lemma q16_decode_int0 :
  q16_decode_int 0 = 0%r.
proof. by rewrite /q16_decode_int. qed.

lemma q16_decode_wordE (w : W32.t) :
  q16_decode_word w = (W32.to_sint w)%r / 65536%r.
proof. by rewrite /q16_decode_word /q16_decode_int. qed.

lemma fft_decode_atE (data : BArray2048.t) (i : int) :
  creal (fft_decode_at data i) =
    (W32.to_sint (BArray2048.get32 data (2 * i)))%r / 65536%r /\
  cimag (fft_decode_at data i) =
    (W32.to_sint (BArray2048.get32 data (2 * i + 1)))%r / 65536%r.
proof.
by rewrite /fft_decode_at /q16_decode_word /q16_decode_int
           /creal /cimag /=.
qed.

lemma fft_table_twistE
    (xp : BArray1024.t) (roots : BArray2048.t) (i : int) :
  fft_table_twist xp roots i =
  cmul (fft_coefficient_vector xp i) (fft_root_decode_at roots i).
proof.
rewrite /fft_table_twist /fft_coefficient_vector /cscale_int /cof_int.
by rewrite cmul_of_real.
qed.

lemma fft_init_step_decode_written
    (data : BArray2048.t) (xp : BArray1024.t)
    (roots : BArray2048.t) (i : int) :
  0 <= i < 256 =>
  fft_init_cell_safe xp roots i =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_init_step
      xp roots KeygenMode2ParentTarget.jfft_brv8 data i)
    (bsrev 8 i) =
  fft_table_twist xp roots i.
proof.
move=> hi hsafe.
have hbrv :=
  KeygenM23FFTTableCertificate.jfft_brv8_exact i hi.
have hbrange : 0 <= bsrev 8 i < 256.
+ move: (KeygenM23IdealFFTSchedule.bsrev8_range i).
  by rewrite mem_range.
have [hreal0 hrealmax] :=
  fft_real_word_index_bounds (bsrev 8 i) hbrange.
have [himag0 himagmax] :=
  fft_imag_word_index_bounds (bsrev 8 i) hbrange.
move: hsafe => [hsafe_r hsafe_i].
rewrite /KeygenM23SingularFFTSpec.fft_init_step /=.
rewrite fft_init_shift_brv fft_init_shift_brv_succ.
rewrite hbrv.
rewrite fft_init_shift_index 1:hi.
rewrite fft_init_shift_index_succ 1:hi.
rewrite /fft_decode_at.
rewrite BArray2048.get_set32E 1:himag0 1:himagmax /=.
rewrite BArray2048.get_set32E 1:hreal0 1:hrealmax /=.
rewrite BArray2048.get_set32E 1:himag0 1:himagmax /=.
rewrite ifF 1:/#.
rewrite /fft_table_twist /fft_root_decode_at /fft_decode_at
        /cscale_int /cscale /creal /cimag /=.
rewrite /q16_decode_word /q16_decode_int.
rewrite
  (KeygenM23SingularIntegerSemantics.fft_init_product_to_sint
    (BArray1024.get32 xp i)
    (BArray2048.get32 roots (2 * i)) hsafe_r).
rewrite
  (KeygenM23SingularIntegerSemantics.fft_init_product_to_sint
    (BArray1024.get32 xp i)
    (BArray2048.get32 roots (2 * i + 1)) hsafe_i).
split; ring.
qed.

lemma fft_init_step_decode_frame
    (data : BArray2048.t) (xp : BArray1024.t)
    (roots : BArray2048.t) (i j : int) :
  0 <= i < 256 =>
  0 <= j < 256 =>
  i <> j =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_init_step
      xp roots KeygenMode2ParentTarget.jfft_brv8 data i)
    (bsrev 8 j) =
  fft_decode_at data (bsrev 8 j).
proof.
move=> hi hj hij.
have hbri :=
  KeygenM23FFTTableCertificate.jfft_brv8_exact i hi.
have hbrange : 0 <= bsrev 8 i < 256.
+ move: (KeygenM23IdealFFTSchedule.bsrev8_range i).
  by rewrite mem_range.
have [hreal0 hrealmax] :=
  fft_real_word_index_bounds (bsrev 8 i) hbrange.
have [himag0 himagmax] :=
  fft_imag_word_index_bounds (bsrev 8 i) hbrange.
have hbrne : bsrev 8 i <> bsrev 8 j.
+ apply/negP => heq.
  have hi_range : i \in range 0 256 by
    rewrite mem_range; smt().
  have hj_range : j \in range 0 256 by
    rewrite mem_range; smt().
  have hi_involutive :=
    KeygenM23IdealFFTSchedule.bsrev8_involutive i hi_range.
  have hj_involutive :=
    KeygenM23IdealFFTSchedule.bsrev8_involutive j hj_range.
  have h := congr1 (bsrev 8) _ _ heq.
  rewrite hi_involutive hj_involutive in h.
  move: hij.
  by rewrite h.
rewrite /KeygenM23SingularFFTSpec.fft_init_step /=.
rewrite fft_init_shift_brv fft_init_shift_brv_succ hbri.
rewrite fft_init_shift_index 1:hi.
rewrite fft_init_shift_index_succ 1:hi.
rewrite /fft_decode_at.
rewrite BArray2048.get_set32E 1:himag0 1:himagmax.
rewrite BArray2048.get_set32E 1:hreal0 1:hrealmax.
rewrite BArray2048.get_set32E 1:himag0 1:himagmax.
rewrite BArray2048.get_set32E 1:hreal0 1:hrealmax.
by rewrite !ifF 1:/# 1:/# 1:/# 1:/#.
qed.

lemma fft_init_prefix_decode
    (data : BArray2048.t) (xp : BArray1024.t)
    (roots : BArray2048.t) (processed i : int) :
  0 <= processed <= 256 =>
  0 <= i < 256 =>
  fft_init_prefix_safe xp roots processed =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_init_prefix
      data xp roots KeygenMode2ParentTarget.jfft_brv8 processed)
    (bsrev 8 i) =
  if i < processed
  then fft_table_twist xp roots i
  else fft_decode_at data (bsrev 8 i).
proof.
move=> [hprocessed0 hprocessed256] hi.
have hgeneral :
  forall n,
    0 <= n =>
    n <= 256 =>
    fft_init_prefix_safe xp roots n =>
    fft_decode_at
      (KeygenM23SingularFFTSpec.fft_init_prefix
        data xp roots KeygenMode2ParentTarget.jfft_brv8 n)
      (bsrev 8 i) =
    if i < n
    then fft_table_twist xp roots i
    else fft_decode_at data (bsrev 8 i).
+ apply intind.
  + move=> _ _.
    by rewrite KeygenM23SingularFFTSpec.fft_init_prefix0 ifF 1:/#.
  + move=> n hn0 ih hn1 hsafe.
    have hn256 : n < 256 by smt().
    have hcell : fft_init_cell_safe xp roots n.
    + move: hsafe.
      rewrite /fft_init_prefix_safe.
      move=> h.
      have hnrange : 0 <= n < n + 1 by smt().
      exact (h n hnrange).
    have hsafe_n : fft_init_prefix_safe xp roots n.
    + rewrite /fft_init_prefix_safe.
      move=> j hj.
      move: hsafe.
      rewrite /fft_init_prefix_safe.
      move=> h.
      have hjrange : 0 <= j < n + 1 by smt().
      exact (h j hjrange).
    rewrite
      KeygenM23SingularFFTSpec.fft_init_prefixS 1:hn0.
    case (i = n) => hin.
    + rewrite hin
        (fft_init_step_decode_written
          (KeygenM23SingularFFTSpec.fft_init_prefix
            data xp roots KeygenMode2ParentTarget.jfft_brv8 n)
          xp roots n)
        1:/# 1:hcell.
      by rewrite ifT 1:/#.
    rewrite
      (fft_init_step_decode_frame
        (KeygenM23SingularFFTSpec.fft_init_prefix
          data xp roots KeygenMode2ParentTarget.jfft_brv8 n)
        xp roots n i)
      1:/# 1:hi 1:/#.
    have hnle256 : n <= 256 by smt().
    rewrite (ih hnle256 hsafe_n).
    case (i < n) => hinlt; smt().
exact (hgeneral processed hprocessed0 hprocessed256).
qed.

lemma actual_fft_init_cell_safe_bound2
    (xp : BArray1024.t) (i : int) :
  0 <= i < 256 =>
  fft_coefficient_bound xp 2 =>
  fft_init_cell_safe
    xp KeygenMode2ParentTarget.jfft_roots i.
proof.
move=> hi hbound.
have hc :
  -2 <= W32.to_sint (BArray1024.get32 xp i) <= 2.
+ exact (hbound i hi).
have hr :=
  KeygenM23FFTTableCertificate.jfft_roots_signed_bound
    (2 * i) _.
+ smt().
have him :=
  KeygenM23FFTTableCertificate.jfft_roots_signed_bound
    (2 * i + 1) _.
+ smt().
rewrite /fft_init_cell_safe
        /KeygenM23SingularBoundary.fft_init_product_safe.
split.
+ exact
    (coefficient2_product_s32
      (W32.to_sint (BArray1024.get32 xp i))
      (W32.to_sint
        (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * i)))
      hc hr).
exact
  (coefficient2_product_s32
    (W32.to_sint (BArray1024.get32 xp i))
    (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * i + 1)))
    hc him).
qed.

lemma actual_fft_init_prefix_safe_bound2
    (xp : BArray1024.t) :
  fft_coefficient_bound xp 2 =>
  fft_init_prefix_safe
    xp KeygenMode2ParentTarget.jfft_roots 256.
proof.
move=> hbound.
rewrite /fft_init_prefix_safe.
move=> i hi.
exact (actual_fft_init_cell_safe_bound2 xp i hi hbound).
qed.

lemma fft_init_and_bitrev_decode
    (data : BArray2048.t) (xp : BArray1024.t)
    (roots : BArray2048.t) (i : int) :
  0 <= i < 256 =>
  fft_init_prefix_safe xp roots 256 =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_init_and_bitrev
      data xp roots KeygenMode2ParentTarget.jfft_brv8)
    i =
  fft_table_twist xp roots (bsrev 8 i).
proof.
move=> hi hsafe.
have hsrc := KeygenM23IdealFFTSchedule.bsrev8_range i.
have hi_range : i \in range 0 256 by
  rewrite mem_range; smt().
have hi_involutive :=
  KeygenM23IdealFFTSchedule.bsrev8_involutive i hi_range.
have hsrc_lt : bsrev 8 i < 256.
+ move: hsrc.
  rewrite mem_range.
  smt().
have h :=
  fft_init_prefix_decode
    data xp roots 256 (bsrev 8 i) _ _ hsafe.
+ smt().
+ by rewrite mem_range in hsrc.
rewrite /KeygenM23SingularFFTSpec.fft_init_and_bitrev
        ifT 1:/# hi_involutive in h.
exact h.
qed.

lemma actual_fft_init_and_bitrev_decode_bound2
    (data : BArray2048.t) (xp : BArray1024.t) (i : int) :
  0 <= i < 256 =>
  fft_coefficient_bound xp 2 =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_init_and_bitrev
      data xp
      KeygenMode2ParentTarget.jfft_roots
      KeygenMode2ParentTarget.jfft_brv8)
    i =
  fft_table_twist
    xp KeygenMode2ParentTarget.jfft_roots (bsrev 8 i).
proof.
move=> hi hbound.
apply (fft_init_and_bitrev_decode
  data xp KeygenMode2ParentTarget.jfft_roots i hi).
exact (actual_fft_init_prefix_safe_bound2 xp hbound).
qed.

lemma actual_fft_init_and_bitrev_table_bitrev_bound2
    (data : BArray2048.t) (xp : BArray1024.t) (i : int) :
  0 <= i < 256 =>
  fft_coefficient_bound xp 2 =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_init_and_bitrev
      data xp
      KeygenMode2ParentTarget.jfft_roots
      KeygenMode2ParentTarget.jfft_brv8)
    i =
  ideal_bitrev8
    (fft_table_twist_vector
      xp KeygenMode2ParentTarget.jfft_roots)
    i.
proof.
move=> hi hbound.
rewrite /ideal_bitrev8 /fft_table_twist_vector.
exact
  (actual_fft_init_and_bitrev_decode_bound2
    data xp i hi hbound).
qed.

lemma actual_root_decode_close (i : int) :
  0 <= i < 256 =>
  cclose (1%r / 131072%r)
    (fft_root_decode_at KeygenMode2ParentTarget.jfft_roots i)
    (ideal_root i).
proof.
move=> hi.
have h :=
  KeygenM23RootTableTargetBridge.jfft_roots_q16_coordinate_error i hi.
move: h => [hre him].
rewrite /cclose /fft_root_decode_at /fft_decode_at
        /q16_decode_word /q16_decode_int /creal /cimag /=.
have hre_close :
  `|(W32.to_sint
       (BArray2048.get32
         KeygenMode2ParentTarget.jfft_roots (2 * i)))%r /
       65536%r - creal (ideal_root i)|
  < 1%r / 131072%r.
+ have heq :
    (W32.to_sint
       (BArray2048.get32
         KeygenMode2ParentTarget.jfft_roots (2 * i)))%r /
       65536%r - creal (ideal_root i) =
    -(creal (ideal_root i) -
       (W32.to_sint
         (BArray2048.get32
           KeygenMode2ParentTarget.jfft_roots (2 * i)))%r /
         65536%r) by ring.
  by rewrite heq normrN.
have him_close :
  `|(W32.to_sint
       (BArray2048.get32
         KeygenMode2ParentTarget.jfft_roots (2 * i + 1)))%r /
       65536%r - cimag (ideal_root i)|
  < 1%r / 131072%r.
+ have heq :
    (W32.to_sint
       (BArray2048.get32
         KeygenMode2ParentTarget.jfft_roots (2 * i + 1)))%r /
       65536%r - cimag (ideal_root i) =
    -(cimag (ideal_root i) -
       (W32.to_sint
         (BArray2048.get32
           KeygenMode2ParentTarget.jfft_roots (2 * i + 1)))%r /
         65536%r) by ring.
  by rewrite heq normrN.
split.
+ apply ltrW.
  exact hre_close.
apply ltrW.
exact him_close.
qed.

lemma actual_table_twist_close (xp : BArray1024.t) (i : int) :
  0 <= i < 256 =>
  cclose
    (`|(W32.to_sint (BArray1024.get32 xp i))%r| *
       (1%r / 131072%r))
    (fft_table_twist
      xp KeygenMode2ParentTarget.jfft_roots i)
    (twist256 (fft_coefficient_vector xp) i).
proof.
move=> hi.
rewrite fft_table_twistE /twist256 /fft_coefficient_vector
        /cof_int cmul_of_real.
exact
  (cclose_scale
    (W32.to_sint (BArray1024.get32 xp i))%r
    (1%r / 131072%r)
    (fft_root_decode_at KeygenMode2ParentTarget.jfft_roots i)
    (ideal_root i)
    (actual_root_decode_close i hi)).
qed.

lemma actual_table_twist_close_bounded
    (xp : BArray1024.t) (bound : real) (i : int) :
  0 <= i < 256 =>
  `|(W32.to_sint (BArray1024.get32 xp i))%r| <= bound =>
  cclose (bound / 131072%r)
    (fft_table_twist
      xp KeygenMode2ParentTarget.jfft_roots i)
    (twist256 (fft_coefficient_vector xp) i).
proof.
move=> hi hbound.
have hclose := actual_table_twist_close xp i hi.
rewrite /cclose in hclose.
rewrite /cclose.
move: hclose => [hre him].
have hdelta : 0%r <= 1%r / 131072%r by
  apply divr_ge0; smt().
have hmul :
  `|(W32.to_sint (BArray1024.get32 xp i))%r| *
      (1%r / 131072%r) <=
  bound / 131072%r.
+ have heq :
    bound / 131072%r =
    bound * (1%r / 131072%r) by ring.
  rewrite heq.
  apply (ler_wpmul2r (1%r / 131072%r)).
  + exact hdelta.
  exact hbound.
split.
+ exact (ler_trans _ _ _ hre hmul).
exact (ler_trans _ _ _ him hmul).
qed.

lemma actual_fft_init_and_bitrev_close_bound2
    (data : BArray2048.t) (xp : BArray1024.t) (i : int) :
  0 <= i < 256 =>
  fft_coefficient_bound xp 2 =>
  cclose (1%r / 65536%r)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_init_and_bitrev
        data xp
        KeygenMode2ParentTarget.jfft_roots
        KeygenMode2ParentTarget.jfft_brv8)
      i)
    (ideal_bitrev8
      (twist256 (fft_coefficient_vector xp))
      i).
proof.
move=> hi hbound.
have hsrc := KeygenM23IdealFFTSchedule.bsrev8_range i.
have hcint :
  -2 <=
    W32.to_sint
      (BArray1024.get32 xp (bsrev 8 i))
  <= 2.
+ apply hbound.
  by rewrite mem_range in hsrc.
have hcreal :
  `|(W32.to_sint
      (BArray1024.get32 xp (bsrev 8 i)))%r| <= 2%r.
+ rewrite ler_norml.
  smt().
have hclose :=
  actual_table_twist_close_bounded
    xp 2%r (bsrev 8 i) _ hcreal.
+ by rewrite mem_range in hsrc.
rewrite
  (actual_fft_init_and_bitrev_decode_bound2
    data xp i hi hbound)
  /ideal_bitrev8.
exact hclose.
qed.

lemma actual_fft_init_and_bitrev_vector_close_bound2
    (data : BArray2048.t) (xp : BArray1024.t) :
  fft_coefficient_bound xp 2 =>
  fft_vector_close (1%r / 65536%r)
    (KeygenM23SingularFFTSpec.fft_init_and_bitrev
      data xp
      KeygenMode2ParentTarget.jfft_roots
      KeygenMode2ParentTarget.jfft_brv8)
    (ideal_bitrev8
      (twist256 (fft_coefficient_vector xp))).
proof.
move=> hbound.
rewrite /fft_vector_close.
move=> i hi.
exact
  (actual_fft_init_and_bitrev_close_bound2
    data xp i hi hbound).
qed.

end KeygenM23SingularFFTInitBridge.
