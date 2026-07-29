require import AllCore IntDiv Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23FixedPointSemantics
  KeygenM23SingularSpec
  KeygenM23SingularBoundary
  KeygenM23SingularFFTSpec
  KeygenM23SingularIntegerSemantics
  KeygenM23SingularFFTInitBridge.

import
  KeygenM23ComplexReal
  KeygenM23SingularFFTInitBridge.

theory KeygenM23SingularFFTButterflyBridge.

op fft_real_word (data : BArray2048.t) (i : int) : W32.t =
  BArray2048.get32 data (2 * i).

op fft_imag_word (data : BArray2048.t) (i : int) : W32.t =
  BArray2048.get32 data (2 * i + 1).

op fft_butterfly_treal_word_at
    (data roots : BArray2048.t) (odd twid : int) : W32.t =
  KeygenM23SingularSpec.mulrnd16_word
    (fft_real_word roots twid) (fft_real_word data odd) -
  KeygenM23SingularSpec.mulrnd16_word
    (fft_imag_word roots twid) (fft_imag_word data odd).

op fft_butterfly_timag_word_at
    (data roots : BArray2048.t) (odd twid : int) : W32.t =
  KeygenM23SingularSpec.mulrnd16_word
    (fft_real_word roots twid) (fft_imag_word data odd) +
  KeygenM23SingularSpec.mulrnd16_word
    (fft_imag_word roots twid) (fft_real_word data odd).

op fft_butterfly_safe_at
    (data roots : BArray2048.t) (even odd twid : int) : bool =
  KeygenM23SingularBoundary.fft_butterfly_safe
    (fft_real_word data even)
    (fft_imag_word data even)
    (fft_real_word data odd)
    (fft_imag_word data odd)
    (fft_real_word roots twid)
    (fft_imag_word roots twid).

op fft_butterfly_term_decode_at
    (data roots : BArray2048.t) (odd twid : int) : complex =
  (q16_decode_int
     (KeygenM23SingularIntegerSemantics.fft_treal_int
       (fft_real_word data odd)
       (fft_imag_word data odd)
       (fft_real_word roots twid)
       (fft_imag_word roots twid)),
   q16_decode_int
     (KeygenM23SingularIntegerSemantics.fft_timag_int
       (fft_real_word data odd)
       (fft_imag_word data odd)
       (fft_real_word roots twid)
       (fft_imag_word roots twid))).

op fft_butterfly_even_decode_at
    (data roots : BArray2048.t) (even odd twid : int) : complex =
  cadd
    (fft_decode_at data even)
    (fft_butterfly_term_decode_at data roots odd twid).

op fft_butterfly_odd_decode_at
    (data roots : BArray2048.t) (even odd twid : int) : complex =
  csub
    (fft_decode_at data even)
    (fft_butterfly_term_decode_at data roots odd twid).

op fft_butterfly_exact_term_at
    (data roots : BArray2048.t) (odd twid : int) : complex =
  cmul (fft_decode_at roots twid) (fft_decode_at data odd).

op fft_butterfly_exact_even_at
    (data roots : BArray2048.t) (even odd twid : int) : complex =
  cadd
    (fft_decode_at data even)
    (fft_butterfly_exact_term_at data roots odd twid).

op fft_butterfly_exact_odd_at
    (data roots : BArray2048.t) (even odd twid : int) : complex =
  csub
    (fft_decode_at data even)
    (fft_butterfly_exact_term_at data roots odd twid).

lemma fft_butterfly_words_written
    (data roots : BArray2048.t) (even odd twid : int) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  even <> odd =>
  let output =
    KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid) in
  fft_real_word output even =
    fft_real_word data even +
      fft_butterfly_treal_word_at data roots odd twid /\
  fft_imag_word output even =
    fft_imag_word data even +
      fft_butterfly_timag_word_at data roots odd twid /\
  fft_real_word output odd =
    fft_real_word data even -
      fft_butterfly_treal_word_at data roots odd twid /\
  fft_imag_word output odd =
    fft_imag_word data even -
      fft_butterfly_timag_word_at data roots odd twid.
proof.
move=> heven hodd htwid hne /=.
have [her0 hermax] :=
  fft_real_word_index_bounds even heven.
have [hei0 heimax] :=
  fft_imag_word_index_bounds even heven.
have [hor0 hormax] :=
  fft_real_word_index_bounds odd hodd.
have [hoi0 hoimax] :=
  fft_imag_word_index_bounds odd hodd.
rewrite /KeygenM23SingularFFTSpec.fft_butterfly /=.
rewrite
  (fft_init_shift_index even heven)
  (fft_init_shift_index_succ even heven)
  (fft_init_shift_index odd hodd)
  (fft_init_shift_index_succ odd hodd)
  (fft_init_shift_index twid htwid)
  (fft_init_shift_index_succ twid htwid).
rewrite /fft_real_word /fft_imag_word
        /fft_butterfly_treal_word_at
        /fft_butterfly_timag_word_at.
do split.
+ rewrite BArray2048.get_set32E 1:hoi0 1:hoimax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hor0 1:hormax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hei0 1:heimax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:her0 1:hermax.
  by rewrite ifT 1:/#.
+ rewrite BArray2048.get_set32E 1:hoi0 1:hoimax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hor0 1:hormax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hei0 1:heimax.
  by rewrite ifT 1:/#.
+ rewrite BArray2048.get_set32E 1:hoi0 1:hoimax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hor0 1:hormax.
  by rewrite ifT 1:/#.
+ rewrite BArray2048.get_set32E 1:hoi0 1:hoimax.
  by rewrite ifT 1:/#.
qed.

lemma fft_butterfly_decode_written
    (data roots : BArray2048.t) (even odd twid : int) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  even <> odd =>
  fft_butterfly_safe_at data roots even odd twid =>
  let output =
    KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid) in
  fft_decode_at output even =
    fft_butterfly_even_decode_at data roots even odd twid /\
  fft_decode_at output odd =
    fft_butterfly_odd_decode_at data roots even odd twid.
proof.
move=> heven hodd htwid hne hsafe /=.
have hwords :=
  fft_butterfly_words_written
    data roots even odd twid heven hodd htwid hne.
move: hwords => [her [hei [hor hoi]]].
have houtputs :=
  KeygenM23SingularIntegerSemantics.fft_butterfly_outputs_to_sint
    (fft_real_word data even)
    (fft_imag_word data even)
    (fft_real_word data odd)
    (fft_imag_word data odd)
    (fft_real_word roots twid)
    (fft_imag_word roots twid)
    hsafe.
move: houtputs => [der [dei [dor doi]]].
split.
+ apply complex_ext.
  + rewrite /fft_decode_at /fft_butterfly_even_decode_at
            /fft_butterfly_term_decode_at
            /q16_decode_word /q16_decode_int
            /fft_real_word /fft_imag_word
            /cadd /creal /cimag /=.
    rewrite /fft_real_word /fft_imag_word in her.
    rewrite /fft_real_word /fft_imag_word in der.
    rewrite her der fromintD.
    ring.
  + rewrite /fft_decode_at /fft_butterfly_even_decode_at
            /fft_butterfly_term_decode_at
            /q16_decode_word /q16_decode_int
            /fft_real_word /fft_imag_word
            /cadd /creal /cimag /=.
    rewrite /fft_real_word /fft_imag_word in hei.
    rewrite /fft_real_word /fft_imag_word in dei.
    rewrite hei dei fromintD.
    ring.
+ apply complex_ext.
  + rewrite /fft_decode_at /fft_butterfly_odd_decode_at
            /fft_butterfly_term_decode_at
            /q16_decode_word /q16_decode_int
            /fft_real_word /fft_imag_word
            /csub /cadd /cneg /creal /cimag /=.
    rewrite /fft_real_word /fft_imag_word in hor.
    rewrite /fft_real_word /fft_imag_word in dor.
    rewrite hor dor fromintB.
    ring.
  + rewrite /fft_decode_at /fft_butterfly_odd_decode_at
            /fft_butterfly_term_decode_at
            /q16_decode_word /q16_decode_int
            /fft_real_word /fft_imag_word
            /csub /cadd /cneg /creal /cimag /=.
    rewrite /fft_real_word /fft_imag_word in hoi.
    rewrite /fft_real_word /fft_imag_word in doi.
    rewrite hoi doi fromintB.
    ring.
qed.

lemma fft_butterfly_decode_frame
    (data roots : BArray2048.t) (even odd twid j : int) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  0 <= j < 256 =>
  j <> even =>
  j <> odd =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid))
    j =
  fft_decode_at data j.
proof.
move=> heven hodd htwid hj hje hjo.
have [her0 hermax] :=
  fft_real_word_index_bounds even heven.
have [hei0 heimax] :=
  fft_imag_word_index_bounds even heven.
have [hor0 hormax] :=
  fft_real_word_index_bounds odd hodd.
have [hoi0 hoimax] :=
  fft_imag_word_index_bounds odd hodd.
rewrite /KeygenM23SingularFFTSpec.fft_butterfly /=.
rewrite
  (fft_init_shift_index even heven)
  (fft_init_shift_index_succ even heven)
  (fft_init_shift_index odd hodd)
  (fft_init_shift_index_succ odd hodd)
  (fft_init_shift_index twid htwid)
  (fft_init_shift_index_succ twid htwid).
rewrite /fft_decode_at.
apply complex_ext.
+ rewrite /creal /cimag /=.
  rewrite BArray2048.get_set32E 1:hoi0 1:hoimax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hor0 1:hormax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hei0 1:heimax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:her0 1:hermax.
  by rewrite ifF 1:/#.
+ rewrite /creal /cimag /=.
  rewrite BArray2048.get_set32E 1:hoi0 1:hoimax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hor0 1:hormax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:hei0 1:heimax.
  rewrite ifF 1:/#.
  rewrite BArray2048.get_set32E 1:her0 1:hermax.
  by rewrite ifF 1:/#.
qed.

lemma q16_mulrnd16_decode_error (x y : int) :
  `|q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int x y) -
     q16_decode_int x * q16_decode_int y|
  <= 1%r / 131072%r.
proof.
have h :=
  KeygenM23FixedPointSemantics.q16_round_error (x * y).
rewrite /KeygenM23FixedPointSemantics.q16_half
        /KeygenM23FixedPointSemantics.q16_scale in h.
move: h => [hlz huz].
have hl :
  (-32768)%r <
    (KeygenM23FixedPointSemantics.q16_round (x * y) * 65536 -
      x * y)%r.
+ by rewrite lt_fromint.
have hu :
    (KeygenM23FixedPointSemantics.q16_round (x * y) * 65536 -
      x * y)%r
  <= 32768%r.
+ by rewrite le_fromint.
rewrite /q16_decode_int
        /KeygenM23FixedPointSemantics.mulrnd16_int.
have heq :
    (KeygenM23FixedPointSemantics.q16_round (x * y))%r / 65536%r -
      x%r / 65536%r * (y%r / 65536%r) =
    (KeygenM23FixedPointSemantics.q16_round (x * y) * 65536 -
      x * y)%r / 4294967296%r.
+ rewrite fromintB !fromintM.
  field; trivial.
rewrite heq ler_norml.
split; smt().
qed.

lemma q16_decode_intD (x y : int) :
  q16_decode_int (x + y) =
    q16_decode_int x + q16_decode_int y.
proof.
rewrite /q16_decode_int fromintD.
ring.
qed.

lemma q16_decode_intB (x y : int) :
  q16_decode_int (x - y) =
    q16_decode_int x - q16_decode_int y.
proof.
rewrite /q16_decode_int fromintB.
ring.
qed.

lemma fft_butterfly_term_rounding_close
    (data roots : BArray2048.t) (odd twid : int) :
  cclose (1%r / 65536%r)
    (fft_butterfly_term_decode_at data roots odd twid)
    (fft_butterfly_exact_term_at data roots odd twid).
proof.
have hrr :=
  q16_mulrnd16_decode_error
    (W32.to_sint (fft_real_word roots twid))
    (W32.to_sint (fft_real_word data odd)).
have hri :=
  q16_mulrnd16_decode_error
    (W32.to_sint (fft_imag_word roots twid))
    (W32.to_sint (fft_imag_word data odd)).
have hro :=
  q16_mulrnd16_decode_error
    (W32.to_sint (fft_real_word roots twid))
    (W32.to_sint (fft_imag_word data odd)).
have hir :=
  q16_mulrnd16_decode_error
    (W32.to_sint (fft_imag_word roots twid))
    (W32.to_sint (fft_real_word data odd)).
rewrite /fft_butterfly_term_decode_at
        /fft_butterfly_exact_term_at
        /fft_decode_at
        /KeygenM23SingularIntegerSemantics.fft_treal_int
        /KeygenM23SingularIntegerSemantics.fft_timag_int
        /cclose /cmul /creal /cimag
        /q16_decode_word /=.
rewrite q16_decode_intB q16_decode_intD.
split.
+ have heq :
    q16_decode_int
      (KeygenM23FixedPointSemantics.mulrnd16_int
        (W32.to_sint (fft_real_word roots twid))
        (W32.to_sint (fft_real_word data odd))) -
    q16_decode_int
      (KeygenM23FixedPointSemantics.mulrnd16_int
        (W32.to_sint (fft_imag_word roots twid))
        (W32.to_sint (fft_imag_word data odd))) -
    (q16_decode_int (W32.to_sint (fft_real_word roots twid)) *
       q16_decode_int (W32.to_sint (fft_real_word data odd)) -
     q16_decode_int (W32.to_sint (fft_imag_word roots twid)) *
       q16_decode_int (W32.to_sint (fft_imag_word data odd))) =
    (q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int
         (W32.to_sint (fft_real_word roots twid))
         (W32.to_sint (fft_real_word data odd))) -
     q16_decode_int (W32.to_sint (fft_real_word roots twid)) *
       q16_decode_int (W32.to_sint (fft_real_word data odd))) +
    -(q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int
         (W32.to_sint (fft_imag_word roots twid))
         (W32.to_sint (fft_imag_word data odd))) -
      q16_decode_int (W32.to_sint (fft_imag_word roots twid)) *
        q16_decode_int (W32.to_sint (fft_imag_word data odd))) by ring.
  rewrite heq.
  have hnorm :=
    ler_norm_add
      (q16_decode_int
         (KeygenM23FixedPointSemantics.mulrnd16_int
           (W32.to_sint (fft_real_word roots twid))
           (W32.to_sint (fft_real_word data odd))) -
       q16_decode_int (W32.to_sint (fft_real_word roots twid)) *
         q16_decode_int (W32.to_sint (fft_real_word data odd)))
      (-(q16_decode_int
         (KeygenM23FixedPointSemantics.mulrnd16_int
           (W32.to_sint (fft_imag_word roots twid))
           (W32.to_sint (fft_imag_word data odd))) -
       q16_decode_int (W32.to_sint (fft_imag_word roots twid)) *
         q16_decode_int (W32.to_sint (fft_imag_word data odd)))).
  rewrite normrN in hnorm.
  have heps :
    1%r / 131072%r + 1%r / 131072%r =
      1%r / 65536%r by ring.
  smt().
+ have heq :
    q16_decode_int
      (KeygenM23FixedPointSemantics.mulrnd16_int
        (W32.to_sint (fft_real_word roots twid))
        (W32.to_sint (fft_imag_word data odd))) +
    q16_decode_int
      (KeygenM23FixedPointSemantics.mulrnd16_int
        (W32.to_sint (fft_imag_word roots twid))
        (W32.to_sint (fft_real_word data odd))) -
    (q16_decode_int (W32.to_sint (fft_real_word roots twid)) *
       q16_decode_int (W32.to_sint (fft_imag_word data odd)) +
     q16_decode_int (W32.to_sint (fft_imag_word roots twid)) *
       q16_decode_int (W32.to_sint (fft_real_word data odd))) =
    (q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int
         (W32.to_sint (fft_real_word roots twid))
         (W32.to_sint (fft_imag_word data odd))) -
     q16_decode_int (W32.to_sint (fft_real_word roots twid)) *
       q16_decode_int (W32.to_sint (fft_imag_word data odd))) +
    (q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int
         (W32.to_sint (fft_imag_word roots twid))
         (W32.to_sint (fft_real_word data odd))) -
     q16_decode_int (W32.to_sint (fft_imag_word roots twid)) *
       q16_decode_int (W32.to_sint (fft_real_word data odd))) by ring.
  rewrite heq.
  have hnorm :=
    ler_norm_add
      (q16_decode_int
         (KeygenM23FixedPointSemantics.mulrnd16_int
           (W32.to_sint (fft_real_word roots twid))
           (W32.to_sint (fft_imag_word data odd))) -
       q16_decode_int (W32.to_sint (fft_real_word roots twid)) *
         q16_decode_int (W32.to_sint (fft_imag_word data odd)))
      (q16_decode_int
         (KeygenM23FixedPointSemantics.mulrnd16_int
           (W32.to_sint (fft_imag_word roots twid))
           (W32.to_sint (fft_real_word data odd))) -
       q16_decode_int (W32.to_sint (fft_imag_word roots twid)) *
         q16_decode_int (W32.to_sint (fft_real_word data odd))).
  have heps :
    1%r / 131072%r + 1%r / 131072%r =
      1%r / 65536%r by ring.
  smt().
qed.

lemma fft_butterfly_decode_close
    (data roots : BArray2048.t) (even odd twid : int) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  even <> odd =>
  fft_butterfly_safe_at data roots even odd twid =>
  let output =
    KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid) in
  cclose (1%r / 65536%r)
    (fft_decode_at output even)
    (fft_butterfly_exact_even_at data roots even odd twid) /\
  cclose (1%r / 65536%r)
    (fft_decode_at output odd)
    (fft_butterfly_exact_odd_at data roots even odd twid).
proof.
move=> heven hodd htwid hne hsafe /=.
have hdecode :=
  fft_butterfly_decode_written
    data roots even odd twid
    heven hodd htwid hne hsafe.
move: hdecode => [heven_decode hodd_decode].
have hterm :=
  fft_butterfly_term_rounding_close data roots odd twid.
have hzero :
  cclose 0%r
    (fft_decode_at data even)
    (fft_decode_at data even).
+ by rewrite /cclose !subrr !normr0.
split.
+ rewrite heven_decode
           /fft_butterfly_even_decode_at
           /fft_butterfly_exact_even_at.
  have h :=
    cclose_add
      0%r (1%r / 65536%r)
      (fft_decode_at data even)
      (fft_decode_at data even)
      (fft_butterfly_term_decode_at data roots odd twid)
      (fft_butterfly_exact_term_at data roots odd twid)
      hzero hterm.
  by rewrite add0r in h.
+ rewrite hodd_decode
           /fft_butterfly_odd_decode_at
           /fft_butterfly_exact_odd_at.
  have h :=
    cclose_sub
      0%r (1%r / 65536%r)
      (fft_decode_at data even)
      (fft_decode_at data even)
      (fft_butterfly_term_decode_at data roots odd twid)
      (fft_butterfly_exact_term_at data roots odd twid)
      hzero hterm.
  by rewrite add0r in h.
qed.

end KeygenM23SingularFFTButterflyBridge.
