require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

require import BArray8192 BArray32768 Array256
               Fq GFq Rq NTT_Fq NTTFullSpec
               KeygenM23MatrixSpec.

theory KeygenM23ArithmeticSpec.

import Zq.

(* Algebraic views of the active mode-2 word regions.  Bases and matrix
   coordinates are expressed in 32-bit words, matching the extracted parent
   procedures. *)
op wide_poly (a : BArray8192.t) (base : int) : Rq.poly =
  Array256.init (fun j =>
    NTT_Fq.word_to_coeff (BArray8192.get32 a (base + j))).

op matrix_poly
    (m : BArray32768.t) (row col : int) : Rq.poly =
  Array256.init (fun j =>
    NTT_Fq.word_to_coeff
      (BArray32768.get32 m
        ((row * KeygenM23MatrixSpec.mode2_cols_i + col) *
           KeygenM23MatrixSpec.poly_words_i + j))).

op wide_slice_bound
    (a : BArray8192.t) (base sz : int) : bool =
  forall j,
    0 <= j < KeygenM23MatrixSpec.poly_words_i =>
    Fq.bw32 (BArray8192.get32 a (base + j)) sz.

op wide_slice_repr_bound
    (a : BArray8192.t) (base : int) (p : Rq.poly) (sz : int) : bool =
  p = wide_poly a base /\ wide_slice_bound a base sz.

op matrix_active_bound16 (m : BArray32768.t) : bool =
  forall row col j,
    0 <= row < KeygenM23MatrixSpec.mode2_rows_i =>
    0 <= col < KeygenM23MatrixSpec.mode2_cols_i =>
    0 <= j < KeygenM23MatrixSpec.poly_words_i =>
    Fq.bw32
      (BArray32768.get32 m
        ((row * KeygenM23MatrixSpec.mode2_cols_i + col) *
           KeygenM23MatrixSpec.poly_words_i + j))
      16.

(* This is the exact source-level accumulator value after its three mode-2
   columns.  Each scalar product is Montgomery-reduced once. *)
op pointwise_row_words
    (m : BArray32768.t) (v : BArray8192.t) (row : int) : Rq.poly =
  Array256.init (fun j =>
      NTT_Fq.word_to_coeff
        (BArray32768.get32 m
          ((row * KeygenM23MatrixSpec.mode2_cols_i + 0) *
             KeygenM23MatrixSpec.poly_words_i + j))
      * NTT_Fq.word_to_coeff
          (BArray8192.get32 v
            (0 * KeygenM23MatrixSpec.poly_words_i + j))
      * inv NTT_Fq.R
    +
      NTT_Fq.word_to_coeff
        (BArray32768.get32 m
          ((row * KeygenM23MatrixSpec.mode2_cols_i + 1) *
             KeygenM23MatrixSpec.poly_words_i + j))
      * NTT_Fq.word_to_coeff
          (BArray8192.get32 v
            (1 * KeygenM23MatrixSpec.poly_words_i + j))
      * inv NTT_Fq.R
    +
      NTT_Fq.word_to_coeff
        (BArray32768.get32 m
          ((row * KeygenM23MatrixSpec.mode2_cols_i + 2) *
             KeygenM23MatrixSpec.poly_words_i + j))
      * NTT_Fq.word_to_coeff
          (BArray8192.get32 v
            (2 * KeygenM23MatrixSpec.poly_words_i + j))
      * inv NTT_Fq.R).

op pointwise_row_ntt
    (m : BArray32768.t) (p0 p1 p2 : Rq.poly)
    (row : int) : Rq.poly =
  Array256.init (fun j =>
      (matrix_poly m row 0).[j]
        * (NTTFullSpec.full_ntt p0).[j] * inv NTT_Fq.R
    + (matrix_poly m row 1).[j]
        * (NTTFullSpec.full_ntt p1).[j] * inv NTT_Fq.R
    + (matrix_poly m row 2).[j]
        * (NTTFullSpec.full_ntt p2).[j] * inv NTT_Fq.R).

op output_row
    (m : BArray32768.t) (p0 p1 p2 : Rq.poly)
    (row : int) : Rq.poly =
  NTT_Fq.array256_mont
    (NTTFullSpec.full_invntt
      (pointwise_row_ntt m p0 p1 p2 row)).

op mode2_input_repr_bound16
    (s : BArray8192.t) (p0 p1 p2 : Rq.poly) : bool =
  wide_slice_repr_bound s 0 p0 16 /\
  wide_slice_repr_bound s KeygenM23MatrixSpec.poly_words_i p1 16 /\
  wide_slice_repr_bound s
    (2 * KeygenM23MatrixSpec.poly_words_i) p2 16.

op mode2_ntt_repr_bound24
    (s : BArray8192.t) (p0 p1 p2 : Rq.poly) : bool =
  wide_slice_repr_bound s 0 (NTTFullSpec.full_ntt p0) 24 /\
  wide_slice_repr_bound s KeygenM23MatrixSpec.poly_words_i
    (NTTFullSpec.full_ntt p1) 24 /\
  wide_slice_repr_bound s
    (2 * KeygenM23MatrixSpec.poly_words_i)
    (NTTFullSpec.full_ntt p2) 24.

op mode2_pointwise_repr_bound18
    (b : BArray8192.t) (m : BArray32768.t)
    (v : BArray8192.t) : bool =
  wide_slice_repr_bound b 0 (pointwise_row_words m v 0) 18 /\
  wide_slice_repr_bound b KeygenM23MatrixSpec.poly_words_i
    (pointwise_row_words m v 1) 18.

op mode2_output_repr_bound16
    (b : BArray8192.t) (m : BArray32768.t)
    (p0 p1 p2 : Rq.poly) : bool =
  wide_slice_repr_bound b 0 (output_row m p0 p1 p2 0) 16 /\
  wide_slice_repr_bound b KeygenM23MatrixSpec.poly_words_i
    (output_row m p0 p1 p2 1) 16.

lemma wide_poly_get a base j :
  0 <= j < KeygenM23MatrixSpec.poly_words_i =>
  (wide_poly a base).[j] =
    NTT_Fq.word_to_coeff (BArray8192.get32 a (base + j)).
proof.
move=> hj.
rewrite /KeygenM23MatrixSpec.poly_words_i in hj.
by rewrite /wide_poly Array256.initiE 1:/#.
qed.

lemma matrix_poly_get m row col j :
  0 <= j < KeygenM23MatrixSpec.poly_words_i =>
  (matrix_poly m row col).[j] =
    NTT_Fq.word_to_coeff
      (BArray32768.get32 m
        ((row * KeygenM23MatrixSpec.mode2_cols_i + col) *
           KeygenM23MatrixSpec.poly_words_i + j)).
proof.
move=> hj.
rewrite /KeygenM23MatrixSpec.poly_words_i in hj.
by rewrite /matrix_poly Array256.initiE 1:/#.
qed.

lemma wide_slice_repr_bound_self a base sz :
  wide_slice_bound a base sz =>
  wide_slice_repr_bound a base (wide_poly a base) sz.
proof.
by rewrite /wide_slice_repr_bound.
qed.

lemma wide_poly_prefix_eq lft rgt words base :
  KeygenM23MatrixSpec.word_prefix_eq lft rgt words =>
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <= words =>
  wide_poly lft base = wide_poly rgt base.
proof.
move=> hprefix hbase.
apply/Array256.ext_eq => j hj.
have hj' : 0 <= j < KeygenM23MatrixSpec.poly_words_i.
+ by rewrite /KeygenM23MatrixSpec.poly_words_i; exact hj.
rewrite /wide_poly !Array256.initiE 1:/# 1:/# /=.
have hidx : 0 <= base + j < words by smt().
have hget :=
  KeygenM23MatrixSpec.word_prefix_eq_get32
    lft rgt words (base + j) hprefix hidx.
by rewrite hget.
qed.

lemma wide_slice_bound_prefix_eq lft rgt words base sz :
  KeygenM23MatrixSpec.word_prefix_eq lft rgt words =>
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <= words =>
  wide_slice_bound lft base sz =>
  wide_slice_bound rgt base sz.
proof.
move=> hprefix hbase.
rewrite /wide_slice_bound.
move=> hbound j hj.
have hidx : 0 <= base + j < words by smt().
have hget :=
  KeygenM23MatrixSpec.word_prefix_eq_get32
    lft rgt words (base + j) hprefix hidx.
by rewrite -hget; apply hbound.
qed.

lemma wide_slice_repr_bound_prefix_eq
    lft rgt words base p sz :
  KeygenM23MatrixSpec.word_prefix_eq lft rgt words =>
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <= words =>
  wide_slice_repr_bound lft base p sz =>
  wide_slice_repr_bound rgt base p sz.
proof.
move=> hprefix hbase.
rewrite /wide_slice_repr_bound.
move=> [hrepr hbound].
split.
+ rewrite hrepr.
  exact (wide_poly_prefix_eq lft rgt words base hprefix hbase).
exact
  (wide_slice_bound_prefix_eq
     lft rgt words base sz hprefix hbase hbound).
qed.

lemma mode2_input_repr_bound16_prefix_eq
    lft rgt p0 p1 p2 :
  KeygenM23MatrixSpec.word_prefix_eq
    lft rgt KeygenM23MatrixSpec.mode2_s1_words_i =>
  mode2_input_repr_bound16 lft p0 p1 p2 =>
  mode2_input_repr_bound16 rgt p0 p1 p2.
proof.
move=> hprefix.
rewrite /mode2_input_repr_bound16.
move=> [h0 [h1 h2]].
split.
+ apply
    (wide_slice_repr_bound_prefix_eq
       lft rgt KeygenM23MatrixSpec.mode2_s1_words_i
       0 p0 16 hprefix).
  + rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
            /KeygenM23MatrixSpec.mode2_cols_i
            /KeygenM23MatrixSpec.poly_words_i /=.
    trivial.
  exact h0.
split.
+ apply
    (wide_slice_repr_bound_prefix_eq
       lft rgt KeygenM23MatrixSpec.mode2_s1_words_i
       KeygenM23MatrixSpec.poly_words_i p1 16 hprefix).
  + rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
            /KeygenM23MatrixSpec.mode2_cols_i
            /KeygenM23MatrixSpec.poly_words_i /=.
    trivial.
  exact h1.
apply
  (wide_slice_repr_bound_prefix_eq
     lft rgt KeygenM23MatrixSpec.mode2_s1_words_i
     (2 * KeygenM23MatrixSpec.poly_words_i) p2 16 hprefix).
+ rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
          /KeygenM23MatrixSpec.mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i /=.
  trivial.
exact h2.
qed.

lemma pointwise_row_words_get m v row j :
  0 <= j < KeygenM23MatrixSpec.poly_words_i =>
  (pointwise_row_words m v row).[j] =
      NTT_Fq.word_to_coeff
        (BArray32768.get32 m
          ((row * KeygenM23MatrixSpec.mode2_cols_i + 0) *
             KeygenM23MatrixSpec.poly_words_i + j))
      * NTT_Fq.word_to_coeff
          (BArray8192.get32 v
            (0 * KeygenM23MatrixSpec.poly_words_i + j))
      * inv NTT_Fq.R
    +
      NTT_Fq.word_to_coeff
        (BArray32768.get32 m
          ((row * KeygenM23MatrixSpec.mode2_cols_i + 1) *
             KeygenM23MatrixSpec.poly_words_i + j))
      * NTT_Fq.word_to_coeff
          (BArray8192.get32 v
            (1 * KeygenM23MatrixSpec.poly_words_i + j))
      * inv NTT_Fq.R
    +
      NTT_Fq.word_to_coeff
        (BArray32768.get32 m
          ((row * KeygenM23MatrixSpec.mode2_cols_i + 2) *
             KeygenM23MatrixSpec.poly_words_i + j))
      * NTT_Fq.word_to_coeff
          (BArray8192.get32 v
            (2 * KeygenM23MatrixSpec.poly_words_i + j))
      * inv NTT_Fq.R.
proof.
move=> hj.
rewrite /KeygenM23MatrixSpec.poly_words_i in hj.
by rewrite /pointwise_row_words Array256.initiE 1:/#.
qed.

lemma pointwise_row_words_ntt m v p0 p1 p2 row :
  mode2_ntt_repr_bound24 v p0 p1 p2 =>
  pointwise_row_words m v row =
    pointwise_row_ntt m p0 p1 p2 row.
proof.
rewrite /mode2_ntt_repr_bound24 /wide_slice_repr_bound.
move=> [[hp0 _] [[hp1 _] [hp2 _]]].
apply/Array256.ext_eq => j hj.
have hj' : 0 <= j < KeygenM23MatrixSpec.poly_words_i.
+ by rewrite /KeygenM23MatrixSpec.poly_words_i; exact hj.
have hv0 := wide_poly_get v 0 j hj'.
have hv1 :=
  wide_poly_get v KeygenM23MatrixSpec.poly_words_i j hj'.
have hv2 :=
  wide_poly_get v
    (2 * KeygenM23MatrixSpec.poly_words_i) j hj'.
rewrite -hp0 in hv0.
rewrite -hp1 in hv1.
rewrite -hp2 in hv2.
rewrite pointwise_row_words_get 1:hj'.
rewrite /pointwise_row_ntt Array256.initiE 1:/#.
rewrite /=.
have hm0 := matrix_poly_get m row 0 j hj'.
have hm1 := matrix_poly_get m row 1 j hj'.
have hm2 := matrix_poly_get m row 2 j hj'.
rewrite hm0 hm1 hm2.
rewrite /KeygenM23MatrixSpec.poly_words_i /= in hv1.
rewrite /KeygenM23MatrixSpec.poly_words_i /= in hv2.
rewrite -hv0 -hv1 -hv2.
have hidx0 :
    row * KeygenM23MatrixSpec.mode2_cols_i *
      KeygenM23MatrixSpec.poly_words_i + j =
    (row * KeygenM23MatrixSpec.mode2_cols_i + 0) *
      KeygenM23MatrixSpec.poly_words_i + j by ring.
by rewrite hidx0.
qed.

lemma mode2_pointwise_words_ntt
    b m v p0 p1 p2 :
  mode2_ntt_repr_bound24 v p0 p1 p2 =>
  mode2_pointwise_repr_bound18 b m v =>
  wide_slice_repr_bound b 0
      (pointwise_row_ntt m p0 p1 p2 0) 18 /\
  wide_slice_repr_bound b KeygenM23MatrixSpec.poly_words_i
      (pointwise_row_ntt m p0 p1 p2 1) 18.
proof.
move=> hntt.
rewrite /mode2_pointwise_repr_bound18.
move=> [hrow0 hrow1].
have heq0 := pointwise_row_words_ntt m v p0 p1 p2 0 hntt.
have heq1 := pointwise_row_words_ntt m v p0 p1 p2 1 hntt.
by rewrite -heq0 -heq1.
qed.

lemma mode2_output_words_ntt
    b m v p0 p1 p2 :
  mode2_ntt_repr_bound24 v p0 p1 p2 =>
  wide_slice_repr_bound b 0
      (NTT_Fq.array256_mont
        (NTTFullSpec.full_invntt (pointwise_row_words m v 0))) 16 /\
  wide_slice_repr_bound b KeygenM23MatrixSpec.poly_words_i
      (NTT_Fq.array256_mont
        (NTTFullSpec.full_invntt (pointwise_row_words m v 1))) 16 =>
  mode2_output_repr_bound16 b m p0 p1 p2.
proof.
move=> hntt [hrow0 hrow1].
have heq0 := pointwise_row_words_ntt m v p0 p1 p2 0 hntt.
have heq1 := pointwise_row_words_ntt m v p0 p1 p2 1 hntt.
rewrite /mode2_output_repr_bound16 /output_row.
by rewrite -heq0 -heq1.
qed.

end KeygenM23ArithmeticSpec.
