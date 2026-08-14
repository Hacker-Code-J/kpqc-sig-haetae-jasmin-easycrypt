require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray32768 Fq KeygenUniformXofLeafSpec
  VerifyUnpackMode2Target VerifyUnpackV3AssemblyPostFreeze
  VerifyUnpackV3ExpandBoundsPostFreeze
  VerifyUnpackV3MatrixProfilePostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3MatDoubleBoundsPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

op mat_double_bound17_prefix (mat : BArray32768.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    Fq.bw32 (BArray32768.get32 mat (double_slot_idx i)) 17.

op mat_double_frame
    (before after : BArray32768.t) (n : int) : bool =
  forall idx, 0 <= idx < BArray32768.size %/ 4 =>
    (forall i, 0 <= i < n => idx <> double_slot_idx i) =>
    BArray32768.get32 after idx = BArray32768.get32 before idx.

op mat_double_firstcol_bound16
    (before after : BArray32768.t) : bool =
  forall i, 0 <= i < mode2_vec_words =>
    BArray32768.get32 after (firstcol_slot_idx i) =
      BArray32768.get32 before (firstcol_slot_idx i) /\
    Fq.bw32 (BArray32768.get32 after (firstcol_slot_idx i)) 16.

op mat_double_nonfirst_bound17 (mat : BArray32768.t) : bool =
  forall i, 0 <= i < mode2_doubled_words =>
    Fq.bw32 (BArray32768.get32 mat (double_slot_idx i)) 17.

op mat_double_preinstall_profile
    (before after : BArray32768.t) : bool =
  (forall row j,
     0 <= row < mode2_rows =>
     0 <= j < poly_words =>
     BArray32768.get32 after (mat_idx row 0 j) =
       BArray32768.get32 before (mat_idx row 0 j) /\
     Fq.bw32 (BArray32768.get32 after (mat_idx row 0 j)) 16) /\
  (forall row col j,
     0 <= row < mode2_rows =>
     1 <= col < mode2_cols =>
     0 <= j < poly_words =>
     Fq.bw32 (BArray32768.get32 after (mat_idx row col j)) 17).

lemma double_slot_idx_inj i j :
  0 <= i < mode2_doubled_words =>
  0 <= j < mode2_doubled_words =>
  double_slot_idx i = double_slot_idx j =>
  i = j.
proof.
rewrite /double_slot_idx /mode2_doubled_words /row_stride
        /mode2_cols /mode2_rows /poly_words.
smt(@IntDiv).
qed.

lemma mat_double_bound17_prefix_zero mat :
  mat_double_bound17_prefix mat 0.
proof. rewrite /mat_double_bound17_prefix; smt(). qed.

lemma mat_double_frame_zero before :
  mat_double_frame before before 0.
proof. rewrite /mat_double_frame; smt(). qed.

lemma mat_double_bound17_prefix_step mat n value :
  0 <= n < mode2_doubled_words =>
  Fq.bw32 value 17 =>
  mat_double_bound17_prefix mat n =>
  mat_double_bound17_prefix
    (BArray32768.set32 mat (double_slot_idx n) value) (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /mat_double_bound17_prefix => i hi.
rewrite BArray32768.get_set32E.
+ have hbound := double_slot_idx_bound i.
  rewrite /BArray32768.size.
  smt().
+ have hbound := double_slot_idx_bound n hn.
  rewrite /BArray32768.size.
  smt().
case (i = n) => heq.
+ by subst i.
rewrite ifF.
+ have hinj := double_slot_idx_inj i n.
  smt().
apply hprefix.
smt().
qed.

lemma mat_double_frame_step before after n value :
  0 <= n < mode2_doubled_words =>
  mat_double_frame before after n =>
  mat_double_frame before
    (BArray32768.set32 after (double_slot_idx n) value) (n + 1).
proof.
move=> hn hframe.
rewrite /mat_double_frame => idx hidx houtside.
rewrite BArray32768.get_set32E.
+ rewrite /BArray32768.size in hidx.
  smt().
+ have hbound := double_slot_idx_bound n hn.
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

lemma expanded_mode2_prefix_bound_word
    (mat : BArray32768.t) idx :
  VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mat =>
  0 <= idx < mode2_mat_words =>
  W32.to_uint (BArray32768.get32 mat idx) < 64513.
proof.
rewrite /VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound
        /KeygenUniformXofLeafSpec.bounded_prefix32768
        /VerifyUnpackV3ExpandBoundsPostFreeze.mode2_matrix_words
        /KeygenUniformXofLeafSpec.uniform_q_i.
move=> hbound hidx.
have hidx2048 : 0 <= idx < 2048.
+ by rewrite mode2_mat_wordsE in hidx.
have hb := hbound idx hidx2048.
by rewrite add0z in hb.
qed.

lemma expanded_mode2_word_bound16 (a : W32.t) :
  0 <= W32.to_uint a < 64513 =>
  Fq.bw32 a 16.
proof.
move=> ha.
have hsint : W32.to_sint a = W32.to_uint a.
+ apply W32.to_sint_unsigned.
   rewrite W32.to_sintE /W32.smod.
   have hcmp := W32.to_uint_cmp a.
   smt().
rewrite /Fq.bw32 hsint.
have hcmp := W32.to_uint_cmp a.
smt().
qed.

lemma expanded_mode2_word_shift_bound17 (a : W32.t) :
  0 <= W32.to_uint a < 64513 =>
  Fq.bw32 (a `<<` (W8.of_int 1)) 17.
proof.
move=> ha.
have hshiftu :
    W32.to_uint (a `<<` (W8.of_int 1)) =
    W32.to_uint a * 2.
+ rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
   rewrite (modz_small (W32.to_uint a * 2) W32.modulus).
   + have hcmp := W32.to_uint_cmp a.
     smt().
   have hcmp := W32.to_uint_cmp a.
   smt().
have hsint :
    W32.to_sint (a `<<` (W8.of_int 1)) =
    W32.to_uint (a `<<` (W8.of_int 1)).
+ apply W32.to_sint_unsigned.
   rewrite W32.to_sintE /W32.smod hshiftu.
   have hcmp := W32.to_uint_cmp a.
   smt().
rewrite /Fq.bw32 hsint hshiftu.
have hcmp := W32.to_uint_cmp a.
smt().
qed.

lemma polymatkl_double_mode2_bound17_frame
    (mp0 : BArray32768.t) :
  hoare [Verify._polymatkl_double :
    mp = mp0 /\
    rows = W64.of_int mode2_rows /\
    cols = W64.of_int mode2_cols /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mp0
    ==>
    mat_firstcol_frame mp0 res /\
    mat_double_bound17_prefix res mode2_doubled_words /\
    mat_double_frame mp0 res mode2_doubled_words].
proof.
proc.
while
  (rows = W64.of_int mode2_rows /\
   cols = W64.of_int mode2_cols /\
   VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mp0 /\
   0 <= W64.to_uint row <= mode2_rows /\
   W64.to_uint row_off = row_stride * W64.to_uint row /\
   mat_firstcol_frame mp0 mp /\
   mat_double_bound17_prefix mp (W64.to_uint row * 768) /\
   mat_double_frame mp0 mp (W64.to_uint row * 768)).
+ wp.
   while
    (rows = W64.of_int mode2_rows /\
     cols = W64.of_int mode2_cols /\
     VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mp0 /\
     0 <= W64.to_uint row < mode2_rows /\
     W64.to_uint row_off = row_stride * W64.to_uint row /\
     1 <= W64.to_uint col <= mode2_cols /\
     W64.to_uint col_off = poly_words * W64.to_uint col /\
     mat_firstcol_frame mp0 mp /\
     mat_double_bound17_prefix
       mp (W64.to_uint row * 768 + (W64.to_uint col - 1) * 256) /\
     mat_double_frame
       mp0 mp (W64.to_uint row * 768 + (W64.to_uint col - 1) * 256)).
  + wp.
    while
      (rows = W64.of_int mode2_rows /\
       cols = W64.of_int mode2_cols /\
       VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mp0 /\
       0 <= W64.to_uint row < mode2_rows /\
       W64.to_uint row_off = row_stride * W64.to_uint row /\
       1 <= W64.to_uint col < mode2_cols /\
       W64.to_uint col_off = poly_words * W64.to_uint col /\
       0 <= W64.to_uint j <= poly_words /\
       mat_firstcol_frame mp0 mp /\
       mat_double_bound17_prefix
         mp
         (W64.to_uint row * 768 +
          (W64.to_uint col - 1) * 256 +
          W64.to_uint j) /\
       mat_double_frame
         mp0 mp
         (W64.to_uint row * 768 +
          (W64.to_uint col - 1) * 256 +
          W64.to_uint j)).
    + auto => /> &hr hexpand hrow0 hrowlt hrowoff
                     hcol1 hcollt hcoloff hj0 hjle
                     hfirst hprefix hframe hguard.
      have hjlt : W64.to_uint j{hr} < poly_words.
      + move: hguard.
        rewrite W64.ultE W64.of_uintK /poly_words /=.
        smt(W64.to_uint_cmp).
      have hnext :
          W64.to_uint (j{hr} + W64.one) =
          W64.to_uint j{hr} + 1.
      + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      have hrow : 0 <= W64.to_uint row{hr} < mode2_rows by smt().
      have hcol : 1 <= W64.to_uint col{hr} < mode2_cols by smt().
      have hj : 0 <= W64.to_uint j{hr} < poly_words by smt().
      pose n :=
        W64.to_uint row{hr} * 768 +
        (W64.to_uint col{hr} - 1) * 256 +
        W64.to_uint j{hr}.
      have hn : 0 <= n < mode2_doubled_words.
      + move: hrow0 hrowlt hcol1 hcollt hj0 hjlt.
        rewrite /n /mode2_rows /mode2_cols
                /poly_words /mode2_doubled_words.
        smt(W64.to_uint_cmp).
      have hidx := actual_mat_double_index_uint
        row_off{hr} col_off{hr} j{hr}
        (W64.to_uint row{hr}) (W64.to_uint col{hr})
        hrow hcol hj hrowoff hcoloff.
      have hslot := double_slot_idxE
        (W64.to_uint row{hr}) (W64.to_uint col{hr}) (W64.to_uint j{hr})
        hrow hcol hj.
      have hcur :
          BArray32768.get32 mp{hr} (double_slot_idx n) =
          BArray32768.get32 mp0 (double_slot_idx n).
      + rewrite /mat_double_frame in hframe.
        apply hframe.
        * have hbound := double_slot_idx_bound n hn.
          rewrite /BArray32768.size in hbound.
          smt().
        move=> i hi.
        have hinj := double_slot_idx_inj i n.
        smt().
      have hraw :
          W32.to_uint (BArray32768.get32 mp0 (double_slot_idx n)) < 64513.
      + apply (expanded_mode2_prefix_bound_word mp0 (double_slot_idx n)).
        * exact hexpand.
        * exact (double_slot_idx_bound n hn).
      have hnew :
          Fq.bw32
            (BArray32768.get32 mp{hr} (double_slot_idx n)
             `<<` (W8.of_int 1)) 17.
      + rewrite hcur.
        apply expanded_mode2_word_shift_bound17.
        have hcmp :=
          W32.to_uint_cmp (BArray32768.get32 mp0 (double_slot_idx n)).
        smt().
      split; first by rewrite hnext; smt(W64.to_uint_cmp).
      split.
      + rewrite hidx -hslot.
        exact (mat_firstcol_frame_set_double mp0 mp{hr} _ _ hn hfirst).
      split.
      + rewrite hnext /n.
        rewrite hidx -hslot.
        rewrite /mat_double_bound17_prefix => i hi.
        rewrite BArray32768.get_set32E.
        * have hbound := double_slot_idx_bound i.
          rewrite /BArray32768.size.
          smt().
        * have hbound := double_slot_idx_bound n hn.
          rewrite /BArray32768.size.
          smt().
        case (i = n) => heq.
        * by subst i.
        rewrite ifF.
        * have hinj := double_slot_idx_inj i n.
          smt().
        apply hprefix.
        smt().
      + rewrite hnext /n.
        rewrite hidx -hslot.
        rewrite /mat_double_frame => idx hidxw houtside.
        rewrite BArray32768.get_set32E.
        * rewrite /BArray32768.size in hidxw.
          rewrite /BArray32768.size.
          smt().
        * have hbound := double_slot_idx_bound n hn.
          rewrite /BArray32768.size in hbound.
          smt().
        rewrite ifF.
        * have hnnext :
              0 <= n <
              W64.to_uint row{hr} * 768 +
              (W64.to_uint col{hr} - 1) * 256 +
              (W64.to_uint j{hr} + 1).
          + rewrite /n.
            smt().
          have hnnot := houtside n hnnext.
          smt().
        apply hframe.
        * exact hidxw.
        move=> i hi.
        have hinext :
            0 <= i <
            W64.to_uint row{hr} * 768 +
            (W64.to_uint col{hr} - 1) * 256 +
            (W64.to_uint j{hr} + 1) by smt().
        exact (houtside i hinext).
    + wp.
      skip => &hr /=.
      move=> /> hexpand hrow0 hrowlt hrowoff hcol1 hcolle hcoloff
                 hfirst hprefix hframe hguard.
      have hcollt : W64.to_uint col{hr} < mode2_cols.
      + move: hguard.
        rewrite W64.ultE W64.of_uintK /mode2_cols /=.
        smt(W64.to_uint_cmp).
      split; first exact hcollt.
    + move=> j0 mp1 hdone hj0 hjle hfirst1 hprefix1 hframe1.
      have hjdone : W64.to_uint j0 = poly_words.
      + move: hdone.
        rewrite W64.ultE W64.of_uintK /poly_words /=.
        smt(W64.to_uint_cmp).
      have hcolnext :
          W64.to_uint (col{hr} + W64.one) =
          W64.to_uint col{hr} + 1.
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
      rewrite hjdone hcolnext hcoloffnext hcoloff.
      rewrite /poly_words /mode2_cols.
      smt(W64.to_uint_cmp).
  + wp.
    skip => &hr /=.
    move=> /> hexpand hrow0 hrowle hrowoff hfirst hprefix hframe hguard.
    have hrowlt : W64.to_uint row{hr} < mode2_rows.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_rows /=.
      smt(W64.to_uint_cmp).
    split; first exact hrowlt.
  + move=> col0 col_off0 mp1 hdone hrowlt_exit
           hcol1 hcolle hcoloff hfirst1 hprefix1 hframe1.
    have hcoldone : W64.to_uint col0 = mode2_cols.
    + move: hdone.
      rewrite W64.ultE W64.of_uintK /mode2_cols /=.
      smt(W64.to_uint_cmp).
    have hrownext :
        W64.to_uint (row{hr} + W64.one) =
        W64.to_uint row{hr} + 1.
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
    have hprocessed :
        W64.to_uint row{hr} * 768 +
          (W64.to_uint col0 - 1) * 256 =
        W64.to_uint (row{hr} + W64.one) * 768.
    + rewrite hrownext hcoldone /mode2_cols.
      ring.
    split.
    + split; first by rewrite hrownext; smt(W64.to_uint_cmp).
      move=> _; rewrite hrownext; smt(W64.to_uint_cmp).
    split.
    + rewrite hrowoffnext hrownext hrowoff hcoloff hcoldone
              /row_stride /mode2_cols /poly_words.
      ring.
    split.
    + rewrite -hprocessed.
      exact hprefix1.
    rewrite -hprocessed.
    exact hframe1.
+ wp.
  skip => &hr /=.
  move=> /> hexpand.
  split.
  + exact (mat_double_bound17_prefix_zero mp{hr}).
  move=> mp1 row0 row_off0 hdone hrow0 hrowle hrowoff
         hfirst hprefix hframe.
  have hrowdone : W64.to_uint row0 = mode2_rows.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /mode2_rows /=.
    smt(W64.to_uint_cmp).
  split.
  + move: hprefix.
    rewrite hrowdone /mode2_rows /mode2_doubled_words.
    trivial.
  move: hframe.
  rewrite hrowdone /mode2_rows /mode2_doubled_words.
  trivial.
qed.

lemma mat_double_firstcol_bound16_of_expand_frame
    (before after : BArray32768.t) :
  VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound before =>
  mat_firstcol_frame before after =>
  mat_double_firstcol_bound16 before after.
proof.
move=> hexpand hframe i hi.
split.
+ exact (hframe i hi).
have hraw :=
  VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound_firstcol
    before hexpand i hi.
rewrite hframe 1:hi.
apply expanded_mode2_word_bound16.
have hcmp :=
  W32.to_uint_cmp (BArray32768.get32 before (firstcol_slot_idx i)).
smt().
qed.

lemma mat_double_nonfirst_bound17_of_prefix after :
  mat_double_bound17_prefix after mode2_doubled_words =>
  mat_double_nonfirst_bound17 after.
proof.
rewrite /mat_double_nonfirst_bound17 /mat_double_bound17_prefix.
trivial.
qed.

lemma unpack_matrix_nonfirst_bound17_of_prefix after :
  mat_double_bound17_prefix after mode2_doubled_words =>
  VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17 after.
proof.
rewrite /VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
        /mat_double_bound17_prefix.
trivial.
qed.

lemma mat_double_preinstall_profile_of_bounds
    (before after : BArray32768.t) :
  mat_double_firstcol_bound16 before after =>
  mat_double_nonfirst_bound17 after =>
  mat_double_preinstall_profile before after.
proof.
move=> hfirst hnonfirst.
split.
+ move=> row j hrow hj.
   have hslot :=
     firstcol_slot_idxE row j hrow hj.
   have hvec :
       0 <= vec_idx row j < mode2_vec_words.
   + rewrite /vec_idx /mode2_vec_words /mode2_rows /poly_words.
     smt().
   move: (hfirst (vec_idx row j) hvec).
   by rewrite hslot.
move=> row col j hrow hcol hj.
have hn :
    0 <= row * 768 + (col - 1) * 256 + j < mode2_doubled_words.
+ rewrite /mode2_doubled_words /mode2_rows /mode2_cols /poly_words.
   smt().
have hslot := double_slot_idxE row col j hrow hcol hj.
move: (hnonfirst (row * 768 + (col - 1) * 256 + j) hn).
by rewrite hslot.
qed.

lemma verify_unpack_v3_mat_double_mixed_bounds
    (mp0 : BArray32768.t) :
  hoare [Verify._polymatkl_double :
    mp = mp0 /\
    rows = W64.of_int mode2_rows /\
    cols = W64.of_int mode2_cols /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mp0
    ==>
    mat_firstcol_frame mp0 res /\
    VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17 res /\
    mat_double_firstcol_bound16 mp0 res /\
    mat_double_preinstall_profile mp0 res].
proof.
conseq
  (polymatkl_double_mode2_bound17_frame mp0).
+ auto.
move=> &m hpre result [hfirst [hprefix hframe]].
have hfirst16 :=
  mat_double_firstcol_bound16_of_expand_frame mp0 result _ hfirst.
+ move: hpre => />.
have hnonfirst :=
  unpack_matrix_nonfirst_bound17_of_prefix result hprefix.
have hprofile :=
  mat_double_preinstall_profile_of_bounds
    mp0 result hfirst16 (mat_double_nonfirst_bound17_of_prefix result hprefix).
by auto.
qed.

end VerifyUnpackV3MatDoubleBoundsPostFreeze.
