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

lemma firstcol_slot_idx_inj i j :
  0 <= i < mode2_vec_words =>
  0 <= j < mode2_vec_words =>
  firstcol_slot_idx i = firstcol_slot_idx j =>
  i = j.
proof.
rewrite /firstcol_slot_idx /mode2_vec_words /row_stride
        /mode2_cols /mode2_rows /poly_words.
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

op mat_firstcol_frame
    (before after : BArray32768.t) : bool =
  forall i, 0 <= i < mode2_vec_words =>
    BArray32768.get32 after (firstcol_slot_idx i) =
      BArray32768.get32 before (firstcol_slot_idx i).

lemma mat_firstcol_frame_refl before :
  mat_firstcol_frame before before.
proof. rewrite /mat_firstcol_frame; trivial. qed.

lemma mat_firstcol_frame_set_double before after n value :
  0 <= n < mode2_doubled_words =>
  mat_firstcol_frame before after =>
  mat_firstcol_frame before
    (BArray32768.set32 after (double_slot_idx n) value).
proof.
move=> hn hframe.
rewrite /mat_firstcol_frame => i hi.
rewrite BArray32768.get_set32E.
+ have hbound := firstcol_slot_idx_bound i hi.
  rewrite /BArray32768.size.
  smt().
+ have hbound := double_slot_idx_bound n hn.
  rewrite /BArray32768.size.
  smt().
rewrite ifF.
+ have hneq := firstcol_slot_idx_neq_double_slot i n hi hn.
  smt().
exact (hframe i hi).
qed.

lemma actual_mat_double_index_uint row_off col_off j row col :
  0 <= row < mode2_rows =>
  1 <= col < mode2_cols =>
  0 <= W64.to_uint j < poly_words =>
  W64.to_uint row_off = row_stride * row =>
  W64.to_uint col_off = poly_words * col =>
  W64.to_uint (row_off + col_off + j) =
    mat_idx row col (W64.to_uint j).
proof.
move=> hrow hcol hj hrowoff hcoloff.
have hsum :
    W64.to_uint (row_off + col_off) =
    W64.to_uint row_off + W64.to_uint col_off.
+ rewrite W64.to_uintD_small.
  + rewrite hrowoff hcoloff.
    rewrite /row_stride /mode2_cols /poly_words /mode2_rows.
    smt(W64.to_uint_cmp).
  trivial.
rewrite W64.to_uintD_small.
+ rewrite hsum hrowoff hcoloff.
  rewrite /row_stride /mode2_cols /poly_words /mode2_rows.
  smt(W64.to_uint_cmp).
rewrite hsum hrowoff hcoloff /mat_idx /row_stride.
ring.
qed.

lemma polymatkl_double_mode2_firstcol_frame (mp0 : BArray32768.t) :
  hoare [Verify._polymatkl_double :
    mp = mp0 /\ rows = W64.of_int mode2_rows /\
    cols = W64.of_int mode2_cols
    ==>
    mat_firstcol_frame mp0 res].
proof.
proc.
while
  (rows = W64.of_int mode2_rows /\
   cols = W64.of_int mode2_cols /\
   0 <= W64.to_uint row <= mode2_rows /\
   W64.to_uint row_off = row_stride * W64.to_uint row /\
   mat_firstcol_frame mp0 mp).
+ wp.
  while
    (rows = W64.of_int mode2_rows /\
     cols = W64.of_int mode2_cols /\
     0 <= W64.to_uint row < mode2_rows /\
     W64.to_uint row_off = row_stride * W64.to_uint row /\
     1 <= W64.to_uint col <= mode2_cols /\
     W64.to_uint col_off = poly_words * W64.to_uint col /\
     mat_firstcol_frame mp0 mp).
  + wp.
    while
      (rows = W64.of_int mode2_rows /\
       cols = W64.of_int mode2_cols /\
       0 <= W64.to_uint row < mode2_rows /\
       W64.to_uint row_off = row_stride * W64.to_uint row /\
       1 <= W64.to_uint col < mode2_cols /\
       W64.to_uint col_off = poly_words * W64.to_uint col /\
       0 <= W64.to_uint j <= poly_words /\
       mat_firstcol_frame mp0 mp).
    + auto => /> &hr hrow0 hrowlt hrowoff hcol1 hcollt hcoloff
              hj0 hjle hframe hguard.
      have hjlt : W64.to_uint j{hr} < poly_words.
      + move: hguard.
        rewrite W64.ultE W64.of_uintK /poly_words /=.
        smt(W64.to_uint_cmp).
      have hnext :
          W64.to_uint (j{hr} + W64.one) = W64.to_uint j{hr} + 1.
      + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      have hrow : 0 <= W64.to_uint row{hr} < mode2_rows by smt().
      have hcol : 1 <= W64.to_uint col{hr} < mode2_cols by smt().
      have hj : 0 <= W64.to_uint j{hr} < poly_words by smt().
      have hidx := actual_mat_double_index_uint
        row_off{hr} col_off{hr} j{hr}
        (W64.to_uint row{hr}) (W64.to_uint col{hr})
        hrow hcol hj hrowoff hcoloff.
      have hn :
          0 <= W64.to_uint row{hr} * 768 +
                 (W64.to_uint col{hr} - 1) * 256 +
                 W64.to_uint j{hr} < mode2_doubled_words.
      + move: hrow0 hrowlt hcol1 hcollt hj0 hjlt.
        rewrite /mode2_rows /mode2_cols /poly_words
                /mode2_doubled_words.
        smt(W64.to_uint_cmp).
      have hslot := double_slot_idxE
        (W64.to_uint row{hr}) (W64.to_uint col{hr}) (W64.to_uint j{hr})
        hrow hcol hj.
      split; first by rewrite hnext; smt(W64.to_uint_cmp).
      rewrite hidx -hslot.
      exact (mat_firstcol_frame_set_double mp0 mp{hr} _ _ hn hframe).
    + wp.
      skip => &hr /=.
      move=> /> hrow0 hrowlt hrowoff hcol1 hcolle hcoloff hframe hguard.
      have hcollt : W64.to_uint col{hr} < mode2_cols.
      + move: hguard.
        rewrite W64.ultE W64.of_uintK /mode2_cols /=.
        smt(W64.to_uint_cmp).
      split; first exact hcollt.
    + move=> j0 mp1 hdone hj0 hjle hframe1.
      have hjdone : W64.to_uint j0 = poly_words.
      + move: hdone.
        rewrite W64.ultE W64.of_uintK /poly_words /=.
        smt(W64.to_uint_cmp).
      have hcolnext :
          W64.to_uint (col{hr} + W64.one) = W64.to_uint col{hr} + 1.
      + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      have hcoloffnext :
          W64.to_uint (col_off{hr} + W64.of_int 256) =
          W64.to_uint col_off{hr} + 256.
      + rewrite W64.to_uintD_small.
        * rewrite W64.of_uintK /= hcoloff.
          rewrite /poly_words /mode2_cols.
          smt(W64.to_uint_cmp).
        rewrite W64.of_uintK /=.
        trivial.
      rewrite hcoloffnext hcolnext hcoloff /poly_words.
      smt(W64.to_uint_cmp).
  + wp.
    skip => &hr /=.
    move=> /> hrow0 hrowle hrowoff hframe hguard.
    have hrowlt : W64.to_uint row{hr} < mode2_rows.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_rows /=.
      smt(W64.to_uint_cmp).
    split; first exact hrowlt.
  + move=> col0 col_off0 mp1 hdone hrowlt_exit
           hcol1 hcolle hcoloff hframe1.
    have hcoldone : W64.to_uint col0 = mode2_cols.
    + move: hdone.
      rewrite W64.ultE W64.of_uintK /mode2_cols /=.
      smt(W64.to_uint_cmp).
    have hrownext :
        W64.to_uint (row{hr} + W64.one) = W64.to_uint row{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hrowoffnext :
        W64.to_uint (row_off{hr} + col_off0) =
        W64.to_uint row_off{hr} + W64.to_uint col_off0.
    + rewrite W64.to_uintD_small.
      * rewrite hcoloff hcoldone hrowoff.
        rewrite /row_stride /mode2_cols /poly_words /mode2_rows.
        smt(W64.to_uint_cmp).
      trivial.
    split.
    + split; first by rewrite hrownext; smt(W64.to_uint_cmp).
      move=> _; rewrite hrownext; smt().
    rewrite hrowoffnext hrownext hrowoff hcoloff hcoldone
            /row_stride /mode2_cols /poly_words.
    ring.
+ wp.
  skip => &hr /=.
  move=> />.
qed.

op sub_firstcol_prefix
    (before : BArray8192.t) (mat : BArray32768.t)
    (after : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 after i =
      BArray32768.get32 mat (firstcol_slot_idx i) -
      BArray8192.get32 before i.

lemma sub_firstcol_prefix_zero before mat after :
  sub_firstcol_prefix before mat after 0.
proof. rewrite /sub_firstcol_prefix; smt(). qed.

lemma sub_firstcol_prefix_step before mat after n value :
  0 <= n < mode2_vec_words =>
  value =
    BArray32768.get32 mat (firstcol_slot_idx n) -
    BArray8192.get32 before n =>
  sub_firstcol_prefix before mat after n =>
  sub_firstcol_prefix before mat
    (BArray8192.set32 after n value) (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /sub_firstcol_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
  by apply hprefix; smt().
qed.

lemma vec_tail_frame_refl before start :
  vec_tail_frame before before start.
proof. rewrite /vec_tail_frame; trivial. qed.

lemma polyvec_sub_left_inplace_mode2_word_exact
    (bp0 : BArray8192.t) (matp0 : BArray32768.t) :
  hoare [Verify.__polyvec_sub_left_inplace :
    bp = bp0 /\
    matp = matp0 /\
    l = W64.of_int mode2_cols /\
    rows = W64.of_int mode2_rows
    ==>
    sub_firstcol_prefix bp0 matp0 res mode2_vec_words /\
    vec_tail_frame bp0 res mode2_vec_words].
proof.
proc.
while
  (matp = matp0 /\
   l = W64.of_int mode2_cols /\
   rows = W64.of_int mode2_rows /\
   stride = W64.of_int row_stride /\
   0 <= W64.to_uint row <= mode2_rows /\
   W64.to_uint bpidx = poly_words * W64.to_uint row /\
   W64.to_uint rowbase = row_stride * W64.to_uint row /\
   sub_firstcol_prefix bp0 matp0 bp (W64.to_uint bpidx) /\
   vec_tail_frame bp0 bp (W64.to_uint bpidx)).
+ wp.
  while
    (matp = matp0 /\
     l = W64.of_int mode2_cols /\
     rows = W64.of_int mode2_rows /\
     stride = W64.of_int row_stride /\
     0 <= W64.to_uint row < mode2_rows /\
     W64.to_uint rowbase = row_stride * W64.to_uint row /\
     0 <= W64.to_uint j <= poly_words /\
     W64.to_uint bpidx = poly_words * W64.to_uint row + W64.to_uint j /\
     W64.to_uint matidx = row_stride * W64.to_uint row + W64.to_uint j /\
     sub_firstcol_prefix bp0 matp0 bp (W64.to_uint bpidx) /\
     vec_tail_frame bp0 bp (W64.to_uint bpidx)).
  + auto => /> &hr hrow0 hrowlt hrowbase
                 hj0 hjle hbpidx hmatidx hprefix hframe hguard.
    have hjlt : W64.to_uint j{hr} < poly_words.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /poly_words /=.
      smt(W64.to_uint_cmp).
    have hbpcur :
        BArray8192.get32 bp{hr} (W64.to_uint bpidx{hr}) =
        BArray8192.get32 bp0 (W64.to_uint bpidx{hr}).
    + rewrite /vec_tail_frame in hframe.
      apply hframe.
      rewrite /mode2_vec_words /mode2_rows /poly_words /=.
      rewrite hbpidx.
      smt(W64.to_uint_cmp).
    have hslot :
        firstcol_slot_idx (W64.to_uint bpidx{hr}) =
        W64.to_uint matidx{hr}.
    + rewrite hbpidx hmatidx /firstcol_slot_idx
              /row_stride /mode2_cols /poly_words.
      smt(@IntDiv W64.to_uint_cmp).
    have hj_next :
        W64.to_uint (j{hr} + W64.one) = W64.to_uint j{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt(W64.to_uint_cmp).
    have hbpidx_next :
        W64.to_uint (bpidx{hr} + W64.one) = W64.to_uint bpidx{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      rewrite hbpidx.
      rewrite /mode2_vec_words /mode2_rows /poly_words /=.
      smt(W64.to_uint_cmp).
    have hmatidx_next :
        W64.to_uint (matidx{hr} + W64.one) = W64.to_uint matidx{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      rewrite hmatidx /row_stride /mode2_cols /poly_words /=.
      smt(W64.to_uint_cmp).
    split; first by rewrite hj_next; smt(W64.to_uint_cmp).
    split; first by rewrite hbpidx_next hbpidx hj_next; ring.
    split; first by rewrite hmatidx_next hmatidx hj_next; ring.
    split.
    * rewrite hbpidx_next.
      apply (sub_firstcol_prefix_step bp0 matp0 bp{hr}
               (W64.to_uint bpidx{hr})).
      + rewrite hbpidx /mode2_vec_words /mode2_rows /poly_words /=.
        smt(W64.to_uint_cmp).
      + by rewrite hslot hbpcur.
      + exact hprefix.
    * rewrite hbpidx_next.
      apply (vec_tail_frame_step bp0 bp{hr} (W64.to_uint bpidx{hr})).
      + rewrite /BArray8192.size hbpidx /mode2_rows /poly_words /=.
        smt(W64.to_uint_cmp).
      + exact hframe.
  + auto => />.
  + auto => />.
+ auto => />.
+ auto => /> &hr hrow0 hrowle hbpidx hrowbase hprefix hframe
                   hguard.
  have hrowlt : W64.to_uint row{hr} < mode2_rows.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /mode2_rows /=.
    smt(W64.to_uint_cmp).
  split; first exact hrowlt.
  move=> bp1 bpidx0 j0 matidx0 hdone hrowlt1 hj0 hjle
         hbpidx1 hmatidx hprefix1 hframe1.
  have hjdone : W64.to_uint j0 = poly_words.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /poly_words /=.
    smt(W64.to_uint_cmp).
  have hrownext :
      W64.to_uint (row{hr} + W64.one) = W64.to_uint row{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hrowbase_next :
      W64.to_uint (rowbase{hr} + W64.of_int row_stride) =
      W64.to_uint rowbase{hr} + row_stride.
  + rewrite W64.to_uintD_small.
    * rewrite W64.of_uintK /= hrowbase
              /row_stride /mode2_cols /poly_words /mode2_rows.
      smt(W64.to_uint_cmp).
    rewrite W64.of_uintK /=.
    trivial.
  split.
  + split; first by rewrite hrownext; smt(W64.to_uint_cmp).
    move=> _; rewrite hrownext; smt().
  split.
  + rewrite hbpidx1 hjdone hrownext /poly_words.
    ring.
  rewrite hrowbase_next hrowbase hrownext.
  ring.
+ wp.
  skip => &hr /=.
  move=> />.
+ split; first exact (sub_firstcol_prefix_zero bp{hr} matp{hr} bp{hr}).
+ move=> bp1 bpidx0 row0 rowbase0 hdone hstride hrow0 hrowle
         hbpidx hrowbase hprefix hframe.
  have hbpidx_eq :
      W64.to_uint bpidx0 = poly_words * W64.to_uint row0
    by exact hbpidx.
  have hrowdone : W64.to_uint row0 = mode2_rows.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /mode2_rows /=.
    smt(W64.to_uint_cmp).
  have hbpdone : W64.to_uint bpidx0 = mode2_vec_words.
  + rewrite hbpidx_eq hrowdone
            /mode2_vec_words /mode2_rows /poly_words.
    ring.
  split.
  + by rewrite -hbpdone.
  + by rewrite -hbpdone.
qed.

op mat_firstcol_install_prefix
    (vec : BArray8192.t) (mat : BArray32768.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray32768.get32 mat (firstcol_slot_idx i) =
      BArray8192.get32 vec i.

op mat_firstcol_install_frame
    (before after : BArray32768.t) (n : int) : bool =
  forall idx, 0 <= idx < BArray32768.size %/ 4 =>
    (forall i, 0 <= i < n => idx <> firstcol_slot_idx i) =>
    BArray32768.get32 after idx = BArray32768.get32 before idx.

lemma mat_firstcol_install_prefix_zero vec mat :
  mat_firstcol_install_prefix vec mat 0.
proof. rewrite /mat_firstcol_install_prefix; smt(). qed.

lemma mat_firstcol_install_prefix_step vec mat n value :
  0 <= n < mode2_vec_words =>
  value = BArray8192.get32 vec n =>
  mat_firstcol_install_prefix vec mat n =>
  mat_firstcol_install_prefix vec
    (BArray32768.set32 mat (firstcol_slot_idx n) value) (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /mat_firstcol_install_prefix => i hi.
rewrite BArray32768.get_set32E.
+ have hbound := firstcol_slot_idx_bound i.
  rewrite /BArray32768.size.
  smt().
+ have hbound := firstcol_slot_idx_bound n hn.
  rewrite /BArray32768.size.
  smt().
case (i = n) => heq.
+ by subst i.
rewrite ifF.
+ have hinj := firstcol_slot_idx_inj i n.
  smt().
by apply hprefix; smt().
qed.

lemma mat_firstcol_install_frame_step before after n value :
  0 <= n < mode2_vec_words =>
  mat_firstcol_install_frame before after n =>
  mat_firstcol_install_frame before
    (BArray32768.set32 after (firstcol_slot_idx n) value) (n + 1).
proof.
move=> hn hframe.
rewrite /mat_firstcol_install_frame => idx hidx houtside.
rewrite BArray32768.get_set32E.
+ rewrite /BArray32768.size in hidx.
  smt().
+ have hbound := firstcol_slot_idx_bound n hn.
  rewrite /BArray32768.size in hbound.
  smt().
rewrite ifF.
+ have hnnext : 0 <= n < n + 1 by smt().
  have hnnot := houtside n hnnext.
  smt().
apply hframe.
+ exact hidx.
move=> i hi.
have hinext : 0 <= i < n + 1 by smt().
exact (houtside i hinext).
qed.

lemma actual_firstcol_mat_index_uint row_off j row :
  0 <= row < mode2_rows =>
  0 <= W64.to_uint j < poly_words =>
  W64.to_uint row_off = row_stride * row =>
  W64.to_uint (row_off + j) =
    firstcol_slot_idx (poly_words * row + W64.to_uint j).
proof.
move=> hrow hj hrowoff.
rewrite W64.to_uintD_small.
+ rewrite hrowoff /row_stride /mode2_cols /mode2_rows /poly_words.
  smt(W64.to_uint_cmp).
rewrite hrowoff /firstcol_slot_idx /row_stride
        /mode2_cols /mode2_rows /poly_words.
smt(@IntDiv W64.to_uint_cmp).
qed.

lemma actual_firstcol_vec_index_uint src_off j row :
  0 <= row < mode2_rows =>
  0 <= W64.to_uint j < poly_words =>
  W64.to_uint src_off = poly_words * row =>
  W64.to_uint (src_off + j) = poly_words * row + W64.to_uint j.
proof.
move=> hrow hj hsrcoff.
rewrite W64.to_uintD_small.
+ rewrite hsrcoff /mode2_rows /poly_words.
  smt(W64.to_uint_cmp).
by rewrite hsrcoff.
qed.

lemma polymat_set_first_column_mode2_word_exact
    (mp0 : BArray32768.t) (vp0 : BArray8192.t) :
  hoare [Verify._polymat_set_first_column :
    mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int mode2_rows /\
    cols = W64.of_int mode2_cols
    ==>
    mat_firstcol_install_prefix vp0 res mode2_vec_words /\
    mat_firstcol_install_frame mp0 res mode2_vec_words].
proof.
proc.
while
  (vp = vp0 /\
   rows = W64.of_int mode2_rows /\
   cols = W64.of_int mode2_cols /\
   stride = W64.of_int row_stride /\
   0 <= W64.to_uint row <= mode2_rows /\
   W64.to_uint row_off = row_stride * W64.to_uint row /\
   W64.to_uint src_off = poly_words * W64.to_uint row /\
   mat_firstcol_install_prefix vp0 mp (W64.to_uint src_off) /\
   mat_firstcol_install_frame mp0 mp (W64.to_uint src_off)).
+ wp.
  while
    (vp = vp0 /\
     rows = W64.of_int mode2_rows /\
     cols = W64.of_int mode2_cols /\
     stride = W64.of_int row_stride /\
     0 <= W64.to_uint row < mode2_rows /\
     W64.to_uint row_off = row_stride * W64.to_uint row /\
     W64.to_uint src_off = poly_words * W64.to_uint row /\
     0 <= W64.to_uint j <= poly_words /\
     mat_firstcol_install_prefix vp0 mp
       (poly_words * W64.to_uint row + W64.to_uint j) /\
     mat_firstcol_install_frame mp0 mp
       (poly_words * W64.to_uint row + W64.to_uint j)).
  + auto => /> &hr hrow0 hrowlt hrowoff hsrcoff
                 hj0 hjle hprefix hframe hguard.
    have hjlt : W64.to_uint j{hr} < poly_words.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /poly_words /=.
      smt(W64.to_uint_cmp).
    have hn :
        0 <= poly_words * W64.to_uint row{hr} + W64.to_uint j{hr} <
          mode2_vec_words.
    + rewrite /mode2_vec_words /mode2_rows /poly_words.
      smt(W64.to_uint_cmp).
    have hrowrange :
        0 <= W64.to_uint row{hr} < mode2_rows by smt().
    have hjrange :
        0 <= W64.to_uint j{hr} < poly_words by smt().
    have hmidx := actual_firstcol_mat_index_uint
      row_off{hr} j{hr} (W64.to_uint row{hr})
      hrowrange hjrange hrowoff.
    have hvidx := actual_firstcol_vec_index_uint
      src_off{hr} j{hr} (W64.to_uint row{hr})
      hrowrange hjrange hsrcoff.
    have hjnext :
        W64.to_uint (j{hr} + W64.one) = W64.to_uint j{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hnnext :
        poly_words * W64.to_uint row{hr} +
          (W64.to_uint j{hr} + 1) =
        (poly_words * W64.to_uint row{hr} + W64.to_uint j{hr}) + 1
      by ring.
    split; first by rewrite hjnext; smt(W64.to_uint_cmp).
    split.
    * rewrite hjnext hnnext hmidx hvidx.
      apply (mat_firstcol_install_prefix_step vp0 mp{hr}
               (poly_words * W64.to_uint row{hr} + W64.to_uint j{hr})).
      + exact hn.
      + trivial.
      + exact hprefix.
    * rewrite hjnext hnnext hmidx.
      apply (mat_firstcol_install_frame_step mp0 mp{hr}
               (poly_words * W64.to_uint row{hr} + W64.to_uint j{hr})).
      + exact hn.
      + exact hframe.
  + auto => />.
  + auto => /> &hr hrow0 hrowle hrowoff hsrcoff hprefix hframe hguard.
    have hrowlt : W64.to_uint row{hr} < mode2_rows.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_rows /=.
      smt(W64.to_uint_cmp).
    split; first by smt(W64.to_uint_cmp).
    move=> j0 mp1 hdone hrowlt1 hj0 hjle hprefix1 hframe1.
    have hjdone : W64.to_uint j0 = poly_words.
    + move: hdone.
      rewrite W64.ultE W64.of_uintK /poly_words /=.
      smt(W64.to_uint_cmp).
    have hrownext :
        W64.to_uint (row{hr} + W64.one) = W64.to_uint row{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hrowoffnext :
        W64.to_uint (row_off{hr} + W64.of_int row_stride) =
          W64.to_uint row_off{hr} + row_stride.
    + rewrite W64.to_uintD_small.
      * rewrite W64.of_uintK /= hrowoff
                /row_stride /mode2_cols /mode2_rows /poly_words.
        smt(W64.to_uint_cmp).
      by rewrite W64.of_uintK /=.
    have hsrcoffnext :
        W64.to_uint (src_off{hr} + W64.of_int 256) =
          W64.to_uint src_off{hr} + poly_words.
    + rewrite W64.to_uintD_small.
      * rewrite hsrcoff /mode2_rows /poly_words.
        smt(W64.to_uint_cmp).
      by rewrite W64.of_uintK /poly_words /=.
    have hcompleted :
        poly_words * W64.to_uint row{hr} + W64.to_uint j0 =
          W64.to_uint (src_off{hr} + W64.of_int 256).
    + rewrite hjdone hsrcoffnext hsrcoff.
      ring.
    split.
    + split; first by rewrite hrownext; smt(W64.to_uint_cmp).
      move=> _; rewrite hrownext; smt().
    split.
    + rewrite hrowoffnext hrowoff hrownext.
      ring.
    split.
    + rewrite hsrcoffnext hsrcoff hrownext.
      ring.
    split.
    + by rewrite -hcompleted.
    + by rewrite -hcompleted.
+ auto => />.
  split; first exact (mat_firstcol_install_prefix_zero vp0 mp0).
  rewrite /mat_firstcol_install_frame.
  trivial.
+ move=> mp1 row0 row_off0 src_off0 hdone hstride
         hrow0 hrowle hrowoff hsrcoff hprefix hframe.
  have hrowdone : W64.to_uint row0 = mode2_rows.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /mode2_rows /=.
    smt(W64.to_uint_cmp).
  have hsrcdone : W64.to_uint src_off0 = mode2_vec_words.
  + rewrite hsrcoff hrowdone
            /mode2_vec_words /mode2_rows /poly_words.
    ring.
  by rewrite -hsrcdone.
qed.

end VerifyUnpackV3AssemblyPostFreeze.
