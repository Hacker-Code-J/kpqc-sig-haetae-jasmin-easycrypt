require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8192 BArray32768 VerifyUnpackMode2Target.

theory VerifyUnpackV3AssemblyPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

op mode2_rows : int = 2.
op mode2_cols : int = 4.
op poly_words : int = 256.
op row_stride : int = mode2_cols * poly_words.
op mode2_vec_words : int = mode2_rows * poly_words.
op mode2_doubled_words : int =
  mode2_rows * (mode2_cols - 1) * poly_words.
op mode2_mat_words : int = mode2_rows * mode2_cols * poly_words.

op vec_idx (row j : int) : int = row * poly_words + j.

op mat_idx (row col j : int) : int =
  (row * mode2_cols + col) * poly_words + j.

op firstcol_slot_idx (i : int) : int =
  (i %/ poly_words) * row_stride + (i %% poly_words).

op double_slot_idx (i : int) : int =
  (i %/ ((mode2_cols - 1) * poly_words)) * row_stride +
  poly_words +
  (i %% ((mode2_cols - 1) * poly_words)).

(* This is the exact word-level arithmetic order used before the first-column NTT:
   first double b1, subtract from the first column, then double again. *)
op mode2_pre_ntt_word (a b1 : W32.t) : W32.t =
  ((a - (b1 `<<` (W8.of_int 1))) `<<` (W8.of_int 1)).

op vec_double_prefix
    (before after : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 after i =
      (BArray8192.get32 before i `<<` (W8.of_int 1)).

op vec_tail_frame
    (before after : BArray8192.t) (start : int) : bool =
  forall i, start <= i < BArray8192.size %/ 4 =>
    BArray8192.get32 after i = BArray8192.get32 before i.

lemma mode2_row_strideE :
  row_stride = 1024.
proof. rewrite /row_stride /mode2_cols /poly_words. ring. qed.

lemma mode2_vec_wordsE :
  mode2_vec_words = 512.
proof. rewrite /mode2_vec_words /mode2_rows /poly_words. ring. qed.

lemma mode2_doubled_wordsE :
  mode2_doubled_words = 1536.
proof.
rewrite /mode2_doubled_words /mode2_rows /mode2_cols /poly_words.
ring.
qed.

lemma mode2_mat_wordsE :
  mode2_mat_words = 2048.
proof. rewrite /mode2_mat_words /mode2_rows /mode2_cols /poly_words. ring. qed.

lemma mat_idx_row_major row col j :
  mat_idx row col j = row * row_stride + col * poly_words + j.
proof.
rewrite /mat_idx /row_stride.
ring.
qed.

lemma vec_idx_row_major row j :
  vec_idx row j = row * poly_words + j.
proof. by rewrite /vec_idx. qed.

lemma firstcol_slot_idxE row j :
  0 <= row < mode2_rows =>
  0 <= j < poly_words =>
  firstcol_slot_idx (vec_idx row j) = mat_idx row 0 j.
proof.
move=> hrow hj.
rewrite /firstcol_slot_idx /vec_idx /mat_idx /row_stride
        /mode2_cols /poly_words.
have : row * 256 + j = 256 * row + j by ring.
smt(@IntDiv).
qed.

lemma double_slot_idxE row col j :
  0 <= row < mode2_rows =>
  1 <= col < mode2_cols =>
  0 <= j < poly_words =>
  double_slot_idx (row * 768 + (col - 1) * 256 + j) = mat_idx row col j.
proof.
move=> hrow hcol hj.
rewrite /double_slot_idx /mat_idx /row_stride
        /mode2_cols /poly_words.
have :
    row * 768 + (col - 1) * 256 + j =
    768 * row + 256 * (col - 1) + j by ring.
smt(@IntDiv).
qed.

lemma firstcol_slot_idx_bound i :
  0 <= i < mode2_vec_words =>
  0 <= firstcol_slot_idx i < mode2_mat_words.
proof.
rewrite /firstcol_slot_idx /mode2_vec_words /mode2_mat_words
        /row_stride /mode2_cols /mode2_rows /poly_words.
smt(@IntDiv).
qed.

lemma double_slot_idx_bound i :
  0 <= i < mode2_doubled_words =>
  0 <= double_slot_idx i < mode2_mat_words.
proof.
rewrite /double_slot_idx /mode2_doubled_words /mode2_mat_words
        /row_stride /mode2_cols /mode2_rows /poly_words.
smt(@IntDiv).
qed.

lemma firstcol_slot_idx_neq_double_slot i n :
  0 <= i < mode2_vec_words =>
  0 <= n < mode2_doubled_words =>
  firstcol_slot_idx i <> double_slot_idx n.
proof.
rewrite /firstcol_slot_idx /double_slot_idx /mode2_vec_words
        /mode2_doubled_words /row_stride /mode2_cols
        /mode2_rows /poly_words.
smt(@IntDiv).
qed.

lemma vec_double_prefix_zero before after :
  vec_double_prefix before after 0.
proof. rewrite /vec_double_prefix; smt(). qed.

lemma vec_double_prefix_step before after n value :
  0 <= n < mode2_vec_words =>
  value = (BArray8192.get32 before n `<<` (W8.of_int 1)) =>
  vec_double_prefix before after n =>
  vec_double_prefix before (BArray8192.set32 after n value) (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /vec_double_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
  by apply hprefix; smt().
qed.

lemma vec_tail_frame_step before after n value :
  0 <= n < BArray8192.size %/ 4 =>
  vec_tail_frame before after n =>
  vec_tail_frame before (BArray8192.set32 after n value) (n + 1).
proof.
move=> hn hframe.
rewrite /vec_tail_frame => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
rewrite ifF 1:/#.
apply hframe; smt().
qed.

lemma polyvec_double_mode2_word_exact (v0 : BArray8192.t) :
  hoare [Verify._polyvec_double :
    vp = v0 /\ count = W64.of_int mode2_vec_words
    ==>
    vec_double_prefix v0 res mode2_vec_words /\
    vec_tail_frame v0 res mode2_vec_words].
proof.
proc.
while
  (count = W64.of_int mode2_vec_words /\
   0 <= W64.to_uint i <= mode2_vec_words /\
   vec_double_prefix v0 vp (W64.to_uint i) /\
   vec_tail_frame v0 vp (W64.to_uint i)).
+ auto => /> &hr hi0 hile hprefix hframe hguard.
  have hlt : W64.to_uint i{hr} < mode2_vec_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /mode2_vec_words
            /mode2_rows /poly_words /=.
    smt(W64.to_uint_cmp).
  have hnext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hcurrent :
      BArray8192.get32 vp{hr} (W64.to_uint i{hr}) =
      BArray8192.get32 v0 (W64.to_uint i{hr}).
  + rewrite /vec_tail_frame in hframe.
    apply hframe.
    move: hlt.
    rewrite /BArray8192.size /mode2_vec_words
            /mode2_rows /poly_words /=.
    smt().
  split; first by rewrite hnext; smt().
  split.
  + rewrite hnext.
    apply (vec_double_prefix_step v0 vp{hr} (W64.to_uint i{hr})).
    * smt(W64.to_uint_cmp).
    * by rewrite hcurrent.
    * exact hprefix.
  + rewrite hnext.
    apply (vec_tail_frame_step v0 vp{hr} (W64.to_uint i{hr})).
    * rewrite /BArray8192.size; smt(W64.to_uint_cmp).
    * exact hframe.
+ auto => />.
  split.
  + exact (vec_double_prefix_zero v0 v0).
  + rewrite /vec_tail_frame; trivial.
+ move=> i0 vp0 hdone hi0 hile hprefix hframe.
  have hieq : W64.to_uint i0 = mode2_vec_words.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /mode2_vec_words
            /mode2_rows /poly_words /=.
    smt(W64.to_uint_cmp).
  by rewrite -hieq.
qed.

end VerifyUnpackV3AssemblyPostFreeze.
