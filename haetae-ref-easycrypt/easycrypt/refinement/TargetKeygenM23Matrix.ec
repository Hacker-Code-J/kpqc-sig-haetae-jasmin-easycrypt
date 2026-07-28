require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenMode2ParentTarget KeygenM23MatrixSpec.

theory TargetKeygenM23Matrix.

module Parent = KeygenMode2ParentTarget.M.

lemma kp_copy_vec_mode2_correct
    (rp0 ap0 : BArray8192.t) :
  hoare [Parent._kp_copy_vec :
    rp = rp0 /\ ap = ap0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_s1_words_i
    ==>
    KeygenM23MatrixSpec.word_prefix_eq
      res ap0 KeygenM23MatrixSpec.mode2_s1_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      rp0 res KeygenM23MatrixSpec.mode2_s1_words_i].
proof.
proc.
while
  (ap = ap0 /\
   count = W64.of_int KeygenM23MatrixSpec.mode2_s1_words_i /\
   KeygenM23MatrixSpec.copy_prefix_state
     rp0 ap0 rp (W64.to_uint i)
     KeygenM23MatrixSpec.mode2_s1_words_i).
+ auto => /> &hr hi0 hle hcap hprefix hframe hguard.
  have hstate :
      KeygenM23MatrixSpec.copy_prefix_state
        rp0 ap0 rp{hr} (W64.to_uint i{hr})
        KeygenM23MatrixSpec.mode2_s1_words_i.
  + rewrite /KeygenM23MatrixSpec.copy_prefix_state
            /KeygenM23MatrixSpec.copy_index_bounds.
    do split.
    + exact hi0.
    + exact hle.
    + exact hprefix.
    + exact hframe.
  have hilt :
      W64.to_uint i{hr} <
        KeygenM23MatrixSpec.mode2_s1_words_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_s1_words_i
            /KeygenM23MatrixSpec.mode2_cols_i
            /KeygenM23MatrixSpec.poly_words_i /=.
    trivial.
  have hstep :
      KeygenM23MatrixSpec.copy_prefix_state
        rp0 ap0
        (BArray8192.set32
          rp{hr} (W64.to_uint i{hr})
          (BArray8192.get32 ap0 (W64.to_uint i{hr})))
        (W64.to_uint i{hr} + 1)
        KeygenM23MatrixSpec.mode2_s1_words_i.
  + apply (KeygenM23MatrixSpec.copy_prefix_state_step
             rp0 ap0 rp{hr} (W64.to_uint i{hr})
             KeygenM23MatrixSpec.mode2_s1_words_i);
      [exact hstate | exact hilt].
  have hsucc :
      W64.to_uint (i{hr} + W64.one) =
        W64.to_uint i{hr} + 1.
  + clear hprefix hframe hstate.
    rewrite W64.to_uintD_small 1:/#.
    trivial.
  rewrite hsucc.
  exact hstep.
auto => />.
split.
+ by rewrite /KeygenM23MatrixSpec.word_prefix_eq; smt().
+ move=> i0 rp1 hdone hi0 hle hcap hprefix hframe.
  have hieq :
      W64.to_uint i0 = KeygenM23MatrixSpec.mode2_s1_words_i.
  + clear hi0 hcap hprefix hframe.
    move: hle hdone.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_s1_words_i
            /KeygenM23MatrixSpec.mode2_cols_i
            /KeygenM23MatrixSpec.poly_words_i /=.
    smt(W64.to_uint_cmp).
  by rewrite -hieq.
qed.

lemma kp_copy_vec_mode2_scratch_independent :
  equiv [Parent._kp_copy_vec ~ Parent._kp_copy_vec :
    ={ap, count} /\
    count{1} =
      W64.of_int KeygenM23MatrixSpec.mode2_s1_words_i
    ==>
    KeygenM23MatrixSpec.word_prefix_eq
      res{1} res{2} KeygenM23MatrixSpec.mode2_s1_words_i].
proof.
proc.
while
  (={ap, count, i} /\
   count{1} =
     W64.of_int KeygenM23MatrixSpec.mode2_s1_words_i /\
   KeygenM23MatrixSpec.word_prefix_eq
     rp{1} rp{2} (W64.to_uint i{1})).
+ auto => /> &1 &2 hprefix hguard.
  have hibound :
      0 <= W64.to_uint i{2} <
        KeygenM23MatrixSpec.array_words_i.
  + clear hprefix.
    move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.array_words_i
            /KeygenM23MatrixSpec.mode2_s1_words_i
            /KeygenM23MatrixSpec.mode2_cols_i
            /KeygenM23MatrixSpec.poly_words_i
            /BArray8192.size /=.
    smt(W64.to_uint_cmp).
  have hstep :
      KeygenM23MatrixSpec.word_prefix_eq
        (BArray8192.set32 rp{1} (W64.to_uint i{2})
          (BArray8192.get32 ap{2} (W64.to_uint i{2})))
        (BArray8192.set32 rp{2} (W64.to_uint i{2})
          (BArray8192.get32 ap{2} (W64.to_uint i{2})))
        (W64.to_uint i{2} + 1).
  + apply (KeygenM23MatrixSpec.word_prefix_eq_extend_same_set32
             rp{1} rp{2} (W64.to_uint i{2})
             (BArray8192.get32 ap{2} (W64.to_uint i{2})));
      [exact hibound | exact hprefix].
  have hsucc :
      W64.to_uint (i{2} + W64.one) =
        W64.to_uint i{2} + 1.
  + clear hprefix hstep.
    rewrite W64.to_uintD_small 1:/#.
    trivial.
  by rewrite hsucc.
auto => />.
move=> &1 &2.
split.
+ by rewrite /KeygenM23MatrixSpec.word_prefix_eq; smt().
+ move=> rpL iR rpR hdoneL hdoneR hprefix.
  rewrite /KeygenM23MatrixSpec.word_prefix_eq in hprefix.
  rewrite /KeygenM23MatrixSpec.word_prefix_eq.
  move=> j hj.
  apply hprefix.
  move: hdoneL.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23MatrixSpec.mode2_s1_words_i
          /KeygenM23MatrixSpec.mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i /=.
  smt().
qed.

lemma kp_copy_vec_ll :
  islossless Parent._kp_copy_vec.
proof.
proc.
while (W64.to_uint i <= W64.to_uint count)
      (W64.to_uint count - W64.to_uint i).
+ move=> z.
  auto => /> &hr hi hguard.
  rewrite W64.ultE in hguard.
  have hcount := W64.to_uint_cmp count{hr}.
  move: hcount => [_ hcount].
  have hsmall :
      W64.to_uint i{hr} + W64.to_uint W64.one < W64.modulus.
  + rewrite W64.to_uint1 ltzE.
    apply (lez_trans (W64.to_uint count{hr} + 1)).
    + rewrite lez_add2r -ltzE.
      exact hguard.
    + by rewrite -ltzE.
  rewrite W64.to_uintD_small 1:hsmall W64.to_uint1.
  split.
  + by rewrite -ltzE.
  + rewrite ltzE.
    have hident :
        W64.to_uint count{hr} - (W64.to_uint i{hr} + 1) + 1 =
        W64.to_uint count{hr} - W64.to_uint i{hr} by ring.
    by rewrite hident.
auto => />.
move=> &hr.
split.
+ have hcount := W64.to_uint_cmp count{hr}.
  by move: hcount => [hcount _].
+ move=> i0 hle hvariant.
  move: hvariant; rewrite subz_le0 => hge.
  by rewrite W64.ultE ltzNge hge.
qed.

lemma kp_copy_vec_mode2_ll
    (rp0 ap0 : BArray8192.t) :
  phoare [Parent._kp_copy_vec :
    rp = rp0 /\ ap = ap0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_s1_words_i
    ==> true] = 1%r.
proof.
conseq kp_copy_vec_ll => //=.
qed.

lemma fqmul_ll :
  islossless Parent.__fqmul.
proof.
proc.
islossless.
qed.

lemma polymat_pointwise_mode2_ll :
  phoare [Parent._polymat_pointwise_acc :
    rows = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    cols = W64.of_int KeygenM23MatrixSpec.mode2_cols_i
    ==> true] = 1%r.
proof.
proc.
while
  (rows = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
   cols = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
   W64.to_uint row <= KeygenM23MatrixSpec.mode2_rows_i)
  (KeygenM23MatrixSpec.mode2_rows_i - W64.to_uint row).
+ move=> z.
  wp.
  while
    (cols = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
     W64.to_uint col <= KeygenM23MatrixSpec.mode2_cols_i)
    (KeygenM23MatrixSpec.mode2_cols_i - W64.to_uint col).
  + move=> z0.
    wp.
    while
      (W64.to_uint j <= KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23MatrixSpec.poly_words_i - W64.to_uint j).
    + move=> z1.
      wp.
      call fqmul_ll.
      auto => /> &hr hj hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23MatrixSpec.poly_words_i /= in hguard.
      rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt().
    auto => /> &hr hcol hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_cols_i /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  wp.
  while
    (W64.to_uint j <= KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23MatrixSpec.poly_words_i - W64.to_uint j).
  + move=> z0.
    auto => /> &hr hj hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.poly_words_i /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  auto => /> &hr hrow hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23MatrixSpec.mode2_rows_i /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  move=> j0.
  split.
  + move=> hjle hvariant.
    move: hvariant; rewrite subz_le0 => hjge.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.poly_words_i /= ltzNge.
    exact hjge.
  + move=> hjdone hjle col0.
    split.
    + move=> hcolle hvariant.
      move: hvariant; rewrite subz_le0 => hcolge.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23MatrixSpec.mode2_cols_i /= ltzNge.
      exact hcolge.
    + move=> hcoldone hcolle.
      smt().
auto => /> row0 hrow hvariant.
rewrite W64.ultE W64.of_uintK
        /KeygenM23MatrixSpec.mode2_rows_i /=.
smt(W64.to_uint_cmp).
qed.

lemma polyvec_ntt_mode2_ll :
  phoare [Parent._polyvec_ntt :
    count = W64.of_int KeygenM23MatrixSpec.mode2_cols_i
    ==> true] = 1%r.
proof.
proc.
while
  (count = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
   W64.to_uint poly <= KeygenM23MatrixSpec.mode2_cols_i)
  (KeygenM23MatrixSpec.mode2_cols_i - W64.to_uint poly).
+ move=> z.
  wp.
  while
    (count = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
     W64.to_uint poly < KeygenM23MatrixSpec.mode2_cols_i /\
     KeygenM23MatrixSpec.m23_fwd_len_schedule (W64.to_uint len))
    (W64.to_uint len).
  + move=> z0.
    wp.
    while
      (count = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
       W64.to_uint poly < KeygenM23MatrixSpec.mode2_cols_i /\
       KeygenM23MatrixSpec.m23_fwd_len_schedule (W64.to_uint len) /\
       0 < W64.to_uint len /\
       KeygenM23MatrixSpec.m23_fwd_block_start
         (W64.to_uint len) (W64.to_uint start) /\
       W64.to_uint start <= KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23MatrixSpec.poly_words_i - W64.to_uint start).
    + move=> z1.
      wp.
      while
        (count = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
         W64.to_uint poly < KeygenM23MatrixSpec.mode2_cols_i /\
         KeygenM23MatrixSpec.m23_fwd_len_schedule (W64.to_uint len) /\
         0 < W64.to_uint len /\
         KeygenM23MatrixSpec.m23_fwd_block_start
           (W64.to_uint len) (W64.to_uint start) /\
         W64.to_uint start < KeygenM23MatrixSpec.poly_words_i /\
         W64.to_uint start <= W64.to_uint j /\
         W64.to_uint j <= W64.to_uint cmp /\
         W64.to_uint cmp =
           W64.to_uint start + W64.to_uint len /\
         W64.to_uint start + 2 * W64.to_uint len <=
           KeygenM23MatrixSpec.poly_words_i)
        (W64.to_uint cmp - W64.to_uint j).
      + move=> z2.
        wp.
        call fqmul_ll.
        auto => /> &hr hpoly hsched hlen hblock hstart
                    hjlo hjhi hcmp hcap hguard.
        have hjlt : W64.to_uint j{hr} < W64.to_uint cmp{hr}.
        + by move: hguard; rewrite W64.ultE.
        rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        smt().
      auto => /> &hr hpoly hsched hlen hblock hstartle hguard.
      have hstartlt :
          W64.to_uint start{hr} < KeygenM23MatrixSpec.poly_words_i.
      + move: hguard.
        rewrite W64.ultE W64.of_uintK
                /KeygenM23MatrixSpec.poly_words_i /=.
        trivial.
      have hcap :=
        KeygenM23MatrixSpec.m23_fwd_block_active_bound
          (W64.to_uint len{hr}) (W64.to_uint start{hr})
          hsched hlen hblock hstartlt.
      have hsum :
          W64.to_uint (start{hr} + len{hr}) =
            W64.to_uint start{hr} + W64.to_uint len{hr}.
      + rewrite W64.to_uintD_small 1:/#.
        trivial.
      split.
      + do split.
        + exact hstartlt.
        + rewrite hsum; smt(W64.to_uint_cmp).
        + exact hsum.
        + exact hcap.
      move=> j0.
      split.
      + move=> hstartlt0 hjlo hjhi hcmp hcap0 hvariant.
        move: hvariant; rewrite subz_le0 => hjge.
        rewrite W64.ultE ltzNge.
        exact hjge.
      + move=> hdone hstartlt0 hjlo hjhi hcmp hcap0.
        have hjge :
            W64.to_uint (start{hr} + len{hr}) <= W64.to_uint j0.
        + move: hdone.
          rewrite W64.ultE ltzNge.
          trivial.
        have hjeq :
            W64.to_uint j0 =
              W64.to_uint start{hr} + W64.to_uint len{hr} by
          rewrite -hcmp; smt().
        have hnew :
            W64.to_uint (j0 + len{hr}) =
              W64.to_uint j0 + W64.to_uint len{hr}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        have hstep :=
          KeygenM23MatrixSpec.m23_fwd_block_start_step
            (W64.to_uint len{hr}) (W64.to_uint start{hr})
            hsched hlen hblock hstartlt0.
        rewrite hnew hjeq.
        split.
        + have -> :
              W64.to_uint start{hr} + W64.to_uint len{hr} +
                W64.to_uint len{hr} =
              W64.to_uint start{hr} + 2 * W64.to_uint len{hr}
            by ring.
          split; [exact hstep | exact hcap0].
        smt().
    auto => /> &hr hpoly hsched hguard.
    have hpos : 0 < W64.to_uint len{hr}.
    + by move: hguard; rewrite W64.ultE W64.to_uint0.
    split.
    + split.
      + exact hpos.
      + exact
          (KeygenM23MatrixSpec.m23_fwd_block_start_zero
             (W64.to_uint len{hr}) hsched hpos).
    move=> start0.
    split.
    + move=> hpos0 hblock hstartle hvariant.
      move: hvariant; rewrite subz_le0 => hstartge.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23MatrixSpec.poly_words_i /= ltzNge.
      smt().
    + move=> hdone hpos0 hblock hstartle.
      have hshift :
          W64.to_uint (len{hr} `>>` W8.one) =
            W64.to_uint len{hr} %/ 2.
      + by rewrite W64.shr_div_le 1:/# /=.
      rewrite hshift.
      split.
      + exact
          (KeygenM23MatrixSpec.m23_fwd_len_schedule_shr1
             (W64.to_uint len{hr}) hsched).
      + move: hsched hpos0.
        rewrite /KeygenM23MatrixSpec.m23_fwd_len_schedule.
        by move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]]; smt().
  auto => /> &hr hpolyle hguard.
  have hpolylt :
      W64.to_uint poly{hr} < KeygenM23MatrixSpec.mode2_cols_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_cols_i /=.
    trivial.
  split; first exact hpolylt.
  move=> len0.
  split.
  + move=> hpolylt0 hsched hvariant.
    rewrite W64.ultE W64.to_uint0 ltzNge.
    smt(W64.to_uint_cmp).
  + move=> hdone hpolylt0 hsched.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
auto => /> poly0 hle hvariant.
move: hvariant; rewrite subz_le0 => hge.
rewrite W64.ultE W64.of_uintK
        /KeygenM23MatrixSpec.mode2_cols_i /= ltzNge.
exact hge.
qed.

lemma polyvec_invntt_mode2_ll :
  phoare [Parent._polyvec_invntt :
    count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i
    ==> true] = 1%r.
proof.
proc.
while
  (count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
   W64.to_uint poly <= KeygenM23MatrixSpec.mode2_rows_i)
  (KeygenM23MatrixSpec.mode2_rows_i - W64.to_uint poly).
+ move=> z.
  wp.
  while
    (count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint poly < KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint j <= KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23MatrixSpec.poly_words_i - W64.to_uint j).
  + move=> z0.
    wp.
    call fqmul_ll.
    auto => /> &hr hpoly hj hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.poly_words_i /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  wp.
  while
    (count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint poly < KeygenM23MatrixSpec.mode2_rows_i /\
     KeygenM23MatrixSpec.ntt_stage_len (W64.to_uint len) /\
     1 <= W64.to_uint len <= KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23MatrixSpec.poly_words_i - W64.to_uint len).
  + move=> z0.
    wp.
    while
      (count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
       W64.to_uint poly < KeygenM23MatrixSpec.mode2_rows_i /\
       KeygenM23MatrixSpec.ntt_stage_len (W64.to_uint len) /\
       1 <= W64.to_uint len <
         KeygenM23MatrixSpec.poly_words_i /\
       W64.to_uint start <= KeygenM23MatrixSpec.poly_words_i /\
       exists block,
         0 <= block /\
         W64.to_uint start = 2 * block * W64.to_uint len)
      (KeygenM23MatrixSpec.poly_words_i - W64.to_uint start).
    + move=> z1.
      wp.
      while
        (count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
         W64.to_uint poly < KeygenM23MatrixSpec.mode2_rows_i /\
         KeygenM23MatrixSpec.ntt_stage_len (W64.to_uint len) /\
         1 <= W64.to_uint len <
           KeygenM23MatrixSpec.poly_words_i /\
         W64.to_uint start <
           KeygenM23MatrixSpec.poly_words_i /\
         W64.to_uint start <= W64.to_uint j /\
         W64.to_uint j <= W64.to_uint cmp /\
         W64.to_uint cmp =
           W64.to_uint start + W64.to_uint len /\
         W64.to_uint start + 2 * W64.to_uint len <=
           KeygenM23MatrixSpec.poly_words_i /\
         exists block,
           0 <= block /\
           W64.to_uint start = 2 * block * W64.to_uint len)
        (W64.to_uint cmp - W64.to_uint j).
      + move=> z2.
        wp.
        call fqmul_ll.
        auto => /> &hr hpoly hsched hlen1 hlenlt hstart
                    hjlo hjhi hcmp hcap block hblock hrepr hguard.
        have hjlt : W64.to_uint j{hr} < W64.to_uint cmp{hr}.
        + by move: hguard; rewrite W64.ultE.
        rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        smt().
      auto => /> &hr hpoly hsched hlen1 hlenlt hstartle
                  block hblock hrepr hguard.
      have hstartlt :
          W64.to_uint start{hr} < KeygenM23MatrixSpec.poly_words_i.
      + move: hguard.
        rewrite W64.ultE W64.of_uintK
                /KeygenM23MatrixSpec.poly_words_i /=.
        trivial.
      have hnext :=
        KeygenM23MatrixSpec.ntt_block_next_bound
          (W64.to_uint len{hr}) block hsched hlenlt hblock.
      have hactive :
          2 * block * W64.to_uint len{hr} <
            KeygenM23MatrixSpec.poly_words_i by
        rewrite -hrepr; exact hstartlt.
      have hnext256 :
          2 * (block + 1) * W64.to_uint len{hr} <=
            KeygenM23MatrixSpec.poly_words_i.
      + apply hnext.
        rewrite /KeygenM23MatrixSpec.poly_words_i in hactive.
        exact hactive.
      have hcap :
          W64.to_uint start{hr} + 2 * W64.to_uint len{hr} <=
            KeygenM23MatrixSpec.poly_words_i.
      + rewrite hrepr.
        have -> :
            2 * block * W64.to_uint len{hr} +
              2 * W64.to_uint len{hr} =
            2 * (block + 1) * W64.to_uint len{hr}
          by ring.
        exact hnext256.
      have hsum :
          W64.to_uint (start{hr} + len{hr}) =
            W64.to_uint start{hr} + W64.to_uint len{hr}.
      + rewrite W64.to_uintD_small 1:/#.
        trivial.
      split.
      + do split.
        + exact hstartlt.
        + rewrite hsum; smt(W64.to_uint_cmp).
        + exact hsum.
        + exact hcap.
      move=> j0.
      split.
      + move=> hstartlt0 hjlo hjhi hcmp hcap0 hvariant.
        move: hvariant; rewrite subz_le0 => hjge.
        rewrite W64.ultE ltzNge.
        exact hjge.
      + move=> hdone hstartlt0 hjlo hjhi hcmp hcap0.
        have hjge :
            W64.to_uint (start{hr} + len{hr}) <= W64.to_uint j0.
        + move: hdone.
          rewrite W64.ultE ltzNge.
          trivial.
        have hjeq :
            W64.to_uint j0 =
              W64.to_uint start{hr} + W64.to_uint len{hr} by
          rewrite -hcmp; smt().
        have hnew :
            W64.to_uint (j0 + len{hr}) =
              W64.to_uint j0 + W64.to_uint len{hr}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        rewrite hnew hjeq.
        split.
        + split.
          + smt().
          + exists (block + 1).
            split; first smt().
            rewrite hrepr.
            ring.
        smt().
    auto => /> &hr hpoly hsched hlen1 hlenle hguard.
    have hlenlt :
        W64.to_uint len{hr} < KeygenM23MatrixSpec.poly_words_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23MatrixSpec.poly_words_i /=.
      trivial.
    split.
    + split; first exact hlenlt.
      exists 0.
      trivial.
    move=> start0.
    split.
    + move=> hlenlt0 hstartle block hblock hrepr hvariant.
      move: hvariant; rewrite subz_le0 => hstartge.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23MatrixSpec.poly_words_i /= ltzNge.
      smt().
    + move=> hdone hlenlt0 hstartle block hblock hrepr.
      have hlennew :
          W64.to_uint (len{hr} `<<` W8.one) =
            2 * W64.to_uint len{hr}.
      + rewrite /(`<<`) W64.to_uint_shl 1:/# /=.
        rewrite modz_small; smt(W64.to_uint_cmp).
      have hschednew :
          KeygenM23MatrixSpec.ntt_stage_len
            (2 * W64.to_uint len{hr}).
      + exact
          (KeygenM23MatrixSpec.ntt_stage_len_double
             (W64.to_uint len{hr}) hsched hlenlt).
      rewrite hlennew.
      split.
      + split; first exact hschednew.
        split; first smt().
        move=> _.
        move: hschednew.
        rewrite /KeygenM23MatrixSpec.ntt_stage_len.
        by move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]]; smt().
      smt().
  auto => /> &hr hpolyle hguard.
  have hpolylt :
      W64.to_uint poly{hr} < KeygenM23MatrixSpec.mode2_rows_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_rows_i /=.
    trivial.
  split; first exact hpolylt.
  move=> len0.
  split.
  + move=> hpolylt0 hsched hlen1 hlenle hvariant.
    move: hvariant; rewrite subz_le0 => hlenge.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.poly_words_i /= ltzNge.
    exact hlenge.
  + move=> hlendone hpolylt0 hsched hlen1 hlenle j0.
    split.
    + move=> hjle hvariant.
      move: hvariant; rewrite subz_le0 => hjge.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23MatrixSpec.poly_words_i /= ltzNge.
      exact hjge.
    + move=> hjdone hjle.
      rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt().
auto => /> poly0 hle hvariant.
move: hvariant; rewrite subz_le0 => hge.
rewrite W64.ultE W64.of_uintK
        /KeygenM23MatrixSpec.mode2_rows_i /= ltzNge.
exact hge.
qed.

lemma kp_m23_matrix_mode2_ll :
  phoare [Parent._kp_m23_matrix :
    rows = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    cols = W64.of_int KeygenM23MatrixSpec.mode2_cols_i
    ==> true] = 1%r.
proof.
proc.
call polyvec_invntt_mode2_ll.
wp.
call polymat_pointwise_mode2_ll.
wp.
call polyvec_ntt_mode2_ll.
call kp_copy_vec_ll.
auto => />.
qed.

(* The following relational lemmas expose only active-prefix dependence.
   They are schedule/footprint claims about the actual extracted loops, not
   mathematical NTT or matrix-product correctness statements. *)
lemma polyvec_ntt_mode2_prefix_equiv :
  equiv [Parent._polyvec_ntt ~ Parent._polyvec_ntt :
    ={count} /\
    count{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
    KeygenM23MatrixSpec.word_prefix_eq
      xp{1} xp{2} KeygenM23MatrixSpec.mode2_s1_words_i
    ==>
    KeygenM23MatrixSpec.word_prefix_eq
      res{1} res{2} KeygenM23MatrixSpec.mode2_s1_words_i].
proof.
proc.
inline Parent.__fqmul Parent.__montgomery_reduce.
wp.
while
  (={zetasp, poly, base, count} /\
   count{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
   W64.to_uint poly{1} <= KeygenM23MatrixSpec.mode2_cols_i /\
   W64.to_uint base{1} =
     KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
   KeygenM23MatrixSpec.word_prefix_eq
     xp{1} xp{2} KeygenM23MatrixSpec.mode2_s1_words_i).
  + wp.
    while
      (={zetasp, poly, base, count, zetasctr, len} /\
       count{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
       W64.to_uint poly{1} < KeygenM23MatrixSpec.mode2_cols_i /\
       W64.to_uint base{1} =
         KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
       KeygenM23MatrixSpec.m23_fwd_len_schedule
         (W64.to_uint len{1}) /\
       KeygenM23MatrixSpec.word_prefix_eq
         xp{1} xp{2} KeygenM23MatrixSpec.mode2_s1_words_i).
    + wp.
      while
        (={zetasp, poly, base, count, zetasctr, len, start} /\
         count{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
         W64.to_uint poly{1} < KeygenM23MatrixSpec.mode2_cols_i /\
         W64.to_uint base{1} =
           KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
         KeygenM23MatrixSpec.m23_fwd_len_schedule
           (W64.to_uint len{1}) /\
         0 < W64.to_uint len{1} /\
         KeygenM23MatrixSpec.m23_fwd_block_start
           (W64.to_uint len{1}) (W64.to_uint start{1}) /\
         KeygenM23MatrixSpec.word_prefix_eq
           xp{1} xp{2} KeygenM23MatrixSpec.mode2_s1_words_i).
      + wp.
        while
          (={zetasp, poly, base, count, zetasctr, len, start,
              zeta_0, j, cmp} /\
           count{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
           W64.to_uint poly{1} < KeygenM23MatrixSpec.mode2_cols_i /\
           W64.to_uint base{1} =
             KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
           KeygenM23MatrixSpec.m23_fwd_len_schedule
             (W64.to_uint len{1}) /\
           0 < W64.to_uint len{1} /\
           KeygenM23MatrixSpec.m23_fwd_block_start
             (W64.to_uint len{1}) (W64.to_uint start{1}) /\
           W64.to_uint start{1} <
             KeygenM23MatrixSpec.poly_words_i /\
           W64.to_uint cmp{1} =
             W64.to_uint start{1} + W64.to_uint len{1} /\
           W64.to_uint start{1} <= W64.to_uint j{1} /\
           W64.to_uint j{1} <= W64.to_uint cmp{1} /\
           KeygenM23MatrixSpec.word_prefix_eq
             xp{1} xp{2} KeygenM23MatrixSpec.mode2_s1_words_i).
        + wp.
          skip => /> &1 &2 hpoly hbase hsched hlen hblock hstart
                      hcmp hjlo hjhi hprefix hguard.
          rewrite W64.ultE in hguard.
          have hcap :=
            KeygenM23MatrixSpec.m23_fwd_block_active_bound
              (W64.to_uint len{2}) (W64.to_uint start{2})
              hsched hlen hblock hstart.
          rewrite /KeygenM23MatrixSpec.poly_words_i in hcap.
          rewrite /KeygenM23MatrixSpec.poly_words_i in hstart.
          rewrite /KeygenM23MatrixSpec.poly_words_i in hbase.
          rewrite /KeygenM23MatrixSpec.mode2_cols_i in hpoly.
          have hpoly0 := W64.to_uint_cmp poly{2}.
          have hbase0 := W64.to_uint_cmp base{2}.
          have hj0 := W64.to_uint_cmp j{2}.
          have hlen0 := W64.to_uint_cmp len{2}.
          have hjlt :
              W64.to_uint j{2} <
                W64.to_uint start{2} + W64.to_uint len{2}
            by smt().
          have hj256 : W64.to_uint j{2} < 256 by smt().
          have hjlen256 :
              W64.to_uint j{2} + W64.to_uint len{2} < 256
            by smt().
          have hbase512 : W64.to_uint base{2} <= 512 by smt().
          have hjlen_word :
              W64.to_uint (j{2} + len{2}) =
                W64.to_uint j{2} + W64.to_uint len{2}.
          + rewrite W64.to_uintD_small 1:/#.
            trivial.
          have hidx_word :
              W64.to_uint (base{2} + j{2}) =
                W64.to_uint base{2} + W64.to_uint j{2}.
          + rewrite W64.to_uintD_small 1:/#.
            trivial.
          have hidx2_word :
              W64.to_uint (base{2} + (j{2} + len{2})) =
                W64.to_uint base{2} + W64.to_uint j{2} +
                  W64.to_uint len{2}.
          + rewrite W64.to_uintD_small 1:/# hjlen_word.
            ring.
          have hj1_word :
              W64.to_uint (j{2} + W64.one) =
                W64.to_uint j{2} + 1.
          + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
            trivial.
          have hidx_bound :
              0 <= W64.to_uint (base{2} + j{2}) <
                KeygenM23MatrixSpec.mode2_s1_words_i.
          + rewrite hidx_word
                    /KeygenM23MatrixSpec.mode2_s1_words_i
                    /KeygenM23MatrixSpec.mode2_cols_i
                    /KeygenM23MatrixSpec.poly_words_i.
            smt().
          have hidx2_bound :
              0 <= W64.to_uint (base{2} + (j{2} + len{2})) <
                KeygenM23MatrixSpec.mode2_s1_words_i.
          + rewrite hidx2_word
                    /KeygenM23MatrixSpec.mode2_s1_words_i
                    /KeygenM23MatrixSpec.mode2_cols_i
                    /KeygenM23MatrixSpec.poly_words_i.
            smt().
          have hs_eq :=
            KeygenM23MatrixSpec.word_prefix_eq_get32
              xp{1} xp{2} KeygenM23MatrixSpec.mode2_s1_words_i
              (W64.to_uint (base{2} + j{2}))
              hprefix hidx_bound.
          have hcoeff_eq :=
            KeygenM23MatrixSpec.word_prefix_eq_get32
              xp{1} xp{2} KeygenM23MatrixSpec.mode2_s1_words_i
              (W64.to_uint (base{2} + (j{2} + len{2})))
              hprefix hidx2_bound.
          split.
          + rewrite hj1_word.
            smt().
          split.
          + rewrite hj1_word.
            smt().
          apply KeygenM23MatrixSpec.word_prefix_eq_set32_same.
          + exact hidx_bound.
          + rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
                    /KeygenM23MatrixSpec.mode2_cols_i
                    /KeygenM23MatrixSpec.poly_words_i
                    /KeygenM23MatrixSpec.array_words_i
                    /BArray8192.size /=.
            trivial.
          + apply KeygenM23MatrixSpec.word_prefix_eq_set32_same.
            * exact hidx2_bound.
            * rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
                      /KeygenM23MatrixSpec.mode2_cols_i
                      /KeygenM23MatrixSpec.poly_words_i
                      /KeygenM23MatrixSpec.array_words_i
                      /BArray8192.size /=.
              trivial.
            * exact hprefix.
            * by rewrite hs_eq hcoeff_eq.
          + by rewrite hs_eq hcoeff_eq.
        wp.
        skip => /> &1 &2 hpoly hbase hsched hlen hblock hprefix hguard.
        rewrite W64.ultE W64.of_uintK /= in hguard.
        have hstart_poly :
            W64.to_uint start{2} < KeygenM23MatrixSpec.poly_words_i.
        + by rewrite /KeygenM23MatrixSpec.poly_words_i.
        have hcap :=
          KeygenM23MatrixSpec.m23_fwd_block_active_bound
            (W64.to_uint len{2}) (W64.to_uint start{2})
            hsched hlen hblock hstart_poly.
        have hstartlen_word :
            W64.to_uint (start{2} + len{2}) =
              W64.to_uint start{2} + W64.to_uint len{2}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        split.
        + split.
          + exact hstart_poly.
          split.
          + exact hstartlen_word.
          + rewrite hstartlen_word.
            have hlen0 := W64.to_uint_cmp len{2}.
            smt().
        move=> xpL jR xpR hdoneL hdoneR hstart' hcmpword
                hjlo hjhi hprefix'.
        rewrite W64.ultE in hdoneR.
        have hj_eq :
            W64.to_uint jR = W64.to_uint (start{2} + len{2})
          by smt().
        have hjsum_word :
            W64.to_uint (jR + len{2}) =
              W64.to_uint jR + W64.to_uint len{2}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        have hstep :=
          KeygenM23MatrixSpec.m23_fwd_block_start_step
            (W64.to_uint len{2}) (W64.to_uint start{2})
            hsched hlen hblock hstart'.
        rewrite hjsum_word hj_eq hcmpword.
        have -> :
            W64.to_uint start{2} + W64.to_uint len{2} +
              W64.to_uint len{2} =
            W64.to_uint start{2} + 2 * W64.to_uint len{2}
          by ring.
        exact hstep.
      wp.
      skip => /> &1 &2 hpoly hbase hsched hprefix hguard.
      have hpos : 0 < W64.to_uint len{2}.
      + by move: hguard; rewrite W64.ultE W64.to_uint0.
      split.
      + split.
        + exact hpos.
        + exact (KeygenM23MatrixSpec.m23_fwd_block_start_zero
                   (W64.to_uint len{2}) hsched hpos).
      move=> xpL startR xpR hdoneL hdoneR hpos' hblock' hprefix'.
      have hshift :
          W64.to_uint (len{2} `>>` W8.one) =
            W64.to_uint len{2} %/ 2.
      + by rewrite W64.shr_div_le 1:/# /=.
      rewrite hshift.
      exact (KeygenM23MatrixSpec.m23_fwd_len_schedule_shr1
               (W64.to_uint len{2}) hsched).
    wp.
    skip => /> &1 &2 hpolyle hbase hprefix hguard.
    have hpolylt :
        W64.to_uint poly{2} < KeygenM23MatrixSpec.mode2_cols_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23MatrixSpec.mode2_cols_i /=.
      trivial.
    split.
    + exact hpolylt.
    move=> xpL lenR xpR hdoneL hdoneR hpolylt' hsched hprefix'.
    rewrite /KeygenM23MatrixSpec.poly_words_i in hbase.
    rewrite /KeygenM23MatrixSpec.mode2_cols_i in hpolylt'.
    have hpoly1 :
        W64.to_uint (poly{2} + W64.one) =
          W64.to_uint poly{2} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hbase256 :
        W64.to_uint (base{2} + W64.of_int 256) =
          W64.to_uint base{2} + 256.
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
      trivial.
    split.
    + rewrite hpoly1 /KeygenM23MatrixSpec.mode2_cols_i.
      smt().
    + rewrite hbase256 hpoly1
              /KeygenM23MatrixSpec.poly_words_i.
      rewrite hbase.
      ring.
  by wp; skip.
qed.

lemma fqmul_equiv :
  equiv [Parent.__fqmul ~ Parent.__fqmul : ={a, b} ==> ={res}].
proof.
proc.
inline Parent.__montgomery_reduce.
sim.
qed.

lemma invntt_inner_entry
    (start len zetasctr : W64.t) (z0 : int) :
  KeygenM23MatrixSpec.ntt_stage_len (W64.to_uint len) =>
  1 <= W64.to_uint len =>
  W64.to_uint len <= 128 =>
  0 <= z0 =>
  z0 <= 255 =>
  z0 * W64.to_uint len = 256 * (W64.to_uint len - 1) =>
  z0 <= W64.to_uint zetasctr =>
  W64.to_uint zetasctr <= 255 =>
  W64.to_uint start =
    2 * (W64.to_uint zetasctr - z0) * W64.to_uint len =>
  W64.to_uint start < 256 =>
  W64.to_uint start < 256 /\
  W64.to_uint start <= W64.to_uint (start + len) /\
  W64.to_uint (start + len) =
    W64.to_uint start + W64.to_uint len /\
  W64.to_uint start + 2 * W64.to_uint len <= 256 /\
  exists z0x,
    0 <= z0x <= 255 /\
    z0x * W64.to_uint len = 256 * (W64.to_uint len - 1) /\
    z0x + 1 <= W64.to_uint (zetasctr + W64.one) <= 255 /\
    W64.to_uint start =
      2 * (W64.to_uint (zetasctr + W64.one) - 1 - z0x) *
        W64.to_uint len /\
    W64.to_uint start + 2 * W64.to_uint len =
      2 * (W64.to_uint (zetasctr + W64.one) - z0x) *
        W64.to_uint len.
proof.
move=> hsched hlen1 hlen128 hz00 hz0255 hzrel hzlow hzup
        hstartrel hstartlt.
have hlenlt : W64.to_uint len < 256 by smt().
have hblock0 : 0 <= W64.to_uint zetasctr - z0 by smt().
have hactive :
    2 * (W64.to_uint zetasctr - z0) * W64.to_uint len < 256 by
  rewrite -hstartrel; exact hstartlt.
have hnextcap :=
  KeygenM23MatrixSpec.ntt_block_next_bound
    (W64.to_uint len) (W64.to_uint zetasctr - z0)
    hsched hlenlt hblock0 hactive.
have hznext :=
  KeygenM23MatrixSpec.invntt_counter_next_bound
    (W64.to_uint len) z0 (W64.to_uint zetasctr - z0)
    hsched hlenlt hz00 hzrel hblock0 hactive.
have hzsucc :
    W64.to_uint (zetasctr + W64.one) =
      W64.to_uint zetasctr + 1 by
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
have hsum :
    W64.to_uint (start + len) =
      W64.to_uint start + W64.to_uint len by
  rewrite W64.to_uintD_small 1:/#.
have hmono :
    W64.to_uint start <= W64.to_uint (start + len) by
  rewrite hsum; smt().
have hcap :
    W64.to_uint start + 2 * W64.to_uint len <= 256.
+ rewrite hstartrel.
  have -> :
      2 * (W64.to_uint zetasctr - z0) * W64.to_uint len +
        2 * W64.to_uint len =
      2 * (W64.to_uint zetasctr - z0 + 1) * W64.to_uint len
    by ring.
  exact hnextcap.
have hzrange :
    z0 + 1 <= W64.to_uint (zetasctr + W64.one) <= 255 by
  rewrite hzsucc; smt().
have hcurrent :
    W64.to_uint start =
      2 * (W64.to_uint (zetasctr + W64.one) - 1 - z0) *
        W64.to_uint len by
  rewrite hzsucc hstartrel; ring.
have hnext :
    W64.to_uint start + 2 * W64.to_uint len =
      2 * (W64.to_uint (zetasctr + W64.one) - z0) *
        W64.to_uint len by
  rewrite hzsucc hstartrel; ring.
have hex :
    exists z0x,
      0 <= z0x <= 255 /\
      z0x * W64.to_uint len = 256 * (W64.to_uint len - 1) /\
      z0x + 1 <= W64.to_uint (zetasctr + W64.one) <= 255 /\
      W64.to_uint start =
        2 * (W64.to_uint (zetasctr + W64.one) - 1 - z0x) *
          W64.to_uint len /\
      W64.to_uint start + 2 * W64.to_uint len =
        2 * (W64.to_uint (zetasctr + W64.one) - z0x) *
          W64.to_uint len.
+ exists z0.
  smt().
exact
  (andI _ _ hstartlt
    (andI _ _ hmono
      (andI _ _ hsum
        (andI _ _ hcap hex)))).
qed.

lemma invntt_inner_exit
    (start len zetasctr j : W64.t) (z0 : int) :
  ! (j \ult start + len) =>
  W64.to_uint start <= W64.to_uint j =>
  W64.to_uint j <= W64.to_uint (start + len) =>
  W64.to_uint (start + len) =
    W64.to_uint start + W64.to_uint len =>
  W64.to_uint start + 2 * W64.to_uint len <= 256 =>
  0 <= z0 =>
  z0 <= 255 =>
  z0 * W64.to_uint len = 256 * (W64.to_uint len - 1) =>
  z0 + 1 <= W64.to_uint zetasctr =>
  W64.to_uint zetasctr <= 255 =>
  W64.to_uint start =
    2 * (W64.to_uint zetasctr - 1 - z0) * W64.to_uint len =>
  W64.to_uint start + 2 * W64.to_uint len =
    2 * (W64.to_uint zetasctr - z0) * W64.to_uint len =>
  exists z0x,
    0 <= z0x <= 255 /\
    z0x * W64.to_uint len = 256 * (W64.to_uint len - 1) /\
    z0x <= W64.to_uint zetasctr /\
    0 <= W64.to_uint (j + len) <= 256 /\
    W64.to_uint (j + len) =
      2 * (W64.to_uint zetasctr - z0x) * W64.to_uint len /\
    2 * (W64.to_uint zetasctr - z0x) * W64.to_uint len <= 256.
proof.
move=> hdone hjlow hjhigh hsum hblock hz00 hz0255 hzrel
        hzlow hzup hstartrel hnextrel.
have hjge :
    W64.to_uint (start + len) <= W64.to_uint j by
  move: hdone; rewrite W64.ultE ltzNge.
have hjeq :
    W64.to_uint j = W64.to_uint (start + len) by smt().
have hnew :
    W64.to_uint (j + len) =
      W64.to_uint j + W64.to_uint len.
+ rewrite W64.to_uintD_small 1:/#.
  trivial.
exists z0.
smt(W64.to_uint_cmp).
qed.

lemma polyvec_invntt_mode2_prefix_equiv :
  equiv [Parent._polyvec_invntt ~ Parent._polyvec_invntt :
    ={count} /\
    count{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    KeygenM23MatrixSpec.word_prefix_eq
      xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i
    ==>
    KeygenM23MatrixSpec.word_prefix_eq
      res{1} res{2} KeygenM23MatrixSpec.mode2_b_words_i].
proof.
proc.
while
  (={zetasp, poly, base, count} /\
   count{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
   W64.to_uint poly{1} <= KeygenM23MatrixSpec.mode2_rows_i /\
   W64.to_uint base{1} =
     KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
   KeygenM23MatrixSpec.word_prefix_eq
     xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i).
+ wp.
  while
    (={zetasp, poly, base, count, zeta_0, j} /\
     count{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint poly{1} < KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
     W64.to_uint j{1} <= KeygenM23MatrixSpec.poly_words_i /\
     KeygenM23MatrixSpec.word_prefix_eq
       xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i).
  + wp.
    call fqmul_equiv.
    wp.
    skip => /> &1 &2.
    move=> hpoly hbase hj hprefix hguard.
    have hjlt : W64.to_uint j{2} < 256.
    + move: hguard.
      by rewrite W64.ultE W64.of_uintK.
    have hidx :
        W64.to_uint (base{2} + j{2}) =
          W64.to_uint base{2} + W64.to_uint j{2}.
    + rewrite W64.to_uintD_small 1:/#.
      trivial.
    have hidxbound :
        0 <= W64.to_uint (base{2} + j{2}) <
          KeygenM23MatrixSpec.mode2_b_words_i.
    + rewrite hidx /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i /=.
      smt(W64.to_uint_cmp).
    have hread :=
      KeygenM23MatrixSpec.word_prefix_eq_get32
        xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i
        (W64.to_uint (base{2} + j{2})) hprefix hidxbound.
    split; first exact hread.
    move=> _ result_R.
    split.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt().
    + apply (KeygenM23MatrixSpec.word_prefix_eq_set32_same
               xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i
               (W64.to_uint (base{2} + j{2})) result_R result_R).
      + exact hidxbound.
      + rewrite /KeygenM23MatrixSpec.mode2_b_words_i
                /KeygenM23MatrixSpec.mode2_rows_i
                /KeygenM23MatrixSpec.poly_words_i
                /KeygenM23MatrixSpec.array_words_i
                /BArray8192.size /=.
        trivial.
      + exact hprefix.
      + trivial.
  + wp.
    while
      (={zetasp, poly, base, count, zetasctr, len} /\
       count{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
       W64.to_uint poly{1} < KeygenM23MatrixSpec.mode2_rows_i /\
       W64.to_uint base{1} =
         KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
       KeygenM23MatrixSpec.ntt_stage_len (W64.to_uint len{1}) /\
       1 <= W64.to_uint len{1} <= 256 /\
       0 <= W64.to_uint zetasctr{1} <= 255 /\
       W64.to_uint zetasctr{1} * W64.to_uint len{1} =
         256 * (W64.to_uint len{1} - 1) /\
       KeygenM23MatrixSpec.word_prefix_eq
         xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i).
    + wp.
      while
        (={zetasp, poly, base, count, len, zetasctr, start} /\
         count{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
         W64.to_uint poly{1} < KeygenM23MatrixSpec.mode2_rows_i /\
         W64.to_uint base{1} =
           KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
         KeygenM23MatrixSpec.ntt_stage_len (W64.to_uint len{1}) /\
         1 <= W64.to_uint len{1} <= 128 /\
         KeygenM23MatrixSpec.word_prefix_eq
           xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i /\
         exists z0,
           0 <= z0 <= 255 /\
           z0 * W64.to_uint len{1} =
             256 * (W64.to_uint len{1} - 1) /\
           z0 <= W64.to_uint zetasctr{1} <= 255 /\
           0 <= W64.to_uint start{1} <= 256 /\
           W64.to_uint start{1} =
             2 * (W64.to_uint zetasctr{1} - z0) *
               W64.to_uint len{1} /\
           2 * (W64.to_uint zetasctr{1} - z0) *
             W64.to_uint len{1} <= 256).
      + wp.
        while
          (={zetasp, poly, base, count, len, zetasctr,
             start, zeta_0, j, cmp} /\
           count{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
           W64.to_uint poly{1} < KeygenM23MatrixSpec.mode2_rows_i /\
           W64.to_uint base{1} =
             KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
           KeygenM23MatrixSpec.ntt_stage_len (W64.to_uint len{1}) /\
           1 <= W64.to_uint len{1} <= 128 /\
           0 <= W64.to_uint start{1} < 256 /\
           W64.to_uint start{1} <= W64.to_uint j{1} <=
             W64.to_uint cmp{1} /\
           W64.to_uint cmp{1} =
             W64.to_uint start{1} + W64.to_uint len{1} /\
           W64.to_uint start{1} + 2 * W64.to_uint len{1} <= 256 /\
           KeygenM23MatrixSpec.word_prefix_eq
             xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i /\
           exists z0,
             0 <= z0 <= 255 /\
             z0 * W64.to_uint len{1} =
               256 * (W64.to_uint len{1} - 1) /\
             z0 + 1 <= W64.to_uint zetasctr{1} <= 255 /\
             W64.to_uint start{1} =
               2 * (W64.to_uint zetasctr{1} - 1 - z0) *
                 W64.to_uint len{1} /\
             W64.to_uint start{1} + 2 * W64.to_uint len{1} =
               2 * (W64.to_uint zetasctr{1} - z0) *
                 W64.to_uint len{1}).
        + wp.
          call fqmul_equiv.
          wp.
          skip => /> &1 &2.
          move=> hpoly hbase hsched hlen1 hlen128
                  hstart0 hstartlt hjlow hjhigh hcmp hblock
                  hprefix z0 hz00 hz0255 hzrel hzlow hzup
                  hstartrel hnextrel hguard.
          have hjlt : W64.to_uint j{2} < W64.to_uint cmp{2}.
          + move: hguard.
            by rewrite W64.ultE.
          have hjlen :
              W64.to_uint j{2} + W64.to_uint len{2} < 256 by smt().
          have hidx1 :
              W64.to_uint (base{2} + j{2}) =
                W64.to_uint base{2} + W64.to_uint j{2}.
          + rewrite W64.to_uintD_small 1:/#.
            trivial.
          have hoffset :
              W64.to_uint (j{2} + len{2}) =
                W64.to_uint j{2} + W64.to_uint len{2}.
          + rewrite W64.to_uintD_small 1:/#.
            trivial.
          have hidx2 :
              W64.to_uint (base{2} + (j{2} + len{2})) =
                W64.to_uint base{2} +
                  (W64.to_uint j{2} + W64.to_uint len{2}).
          + rewrite W64.to_uintD_small 1:/#.
            by rewrite hoffset.
          have hb1 :
              0 <= W64.to_uint (base{2} + j{2}) <
                KeygenM23MatrixSpec.mode2_b_words_i.
          + rewrite hidx1 hbase
                    /KeygenM23MatrixSpec.mode2_b_words_i
                    /KeygenM23MatrixSpec.mode2_rows_i
                    /KeygenM23MatrixSpec.poly_words_i /=.
            smt(W64.to_uint_cmp).
          have hb2 :
              0 <= W64.to_uint (base{2} + (j{2} + len{2})) <
                KeygenM23MatrixSpec.mode2_b_words_i.
          + rewrite hidx2 hbase
                    /KeygenM23MatrixSpec.mode2_b_words_i
                    /KeygenM23MatrixSpec.mode2_rows_i
                    /KeygenM23MatrixSpec.poly_words_i /=.
            smt(W64.to_uint_cmp).
          have hr1 :=
            KeygenM23MatrixSpec.word_prefix_eq_get32
              xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i
              (W64.to_uint (base{2} + j{2})) hprefix hb1.
          have hr2 :=
            KeygenM23MatrixSpec.word_prefix_eq_get32
              xp{1} xp{2} KeygenM23MatrixSpec.mode2_b_words_i
              (W64.to_uint (base{2} + (j{2} + len{2}))) hprefix hb2.
          rewrite hr1 hr2.
          split.
          + trivial.
          move=> _ result_R.
          split.
          + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
            smt().
          + apply
              (KeygenM23MatrixSpec.word_prefix_eq_set32_same
                (BArray8192.set32 xp{1}
                  (W64.to_uint (base{2} + j{2}))
                  (BArray8192.get32 xp{2}
                    (W64.to_uint (base{2} + j{2})) +
                   BArray8192.get32 xp{2}
                    (W64.to_uint (base{2} + (j{2} + len{2})))))
                (BArray8192.set32 xp{2}
                  (W64.to_uint (base{2} + j{2}))
                  (BArray8192.get32 xp{2}
                    (W64.to_uint (base{2} + j{2})) +
                   BArray8192.get32 xp{2}
                    (W64.to_uint (base{2} + (j{2} + len{2})))))
                KeygenM23MatrixSpec.mode2_b_words_i
                (W64.to_uint (base{2} + (j{2} + len{2})))
                result_R result_R).
            * exact hb2.
            * rewrite /KeygenM23MatrixSpec.mode2_b_words_i
                      /KeygenM23MatrixSpec.mode2_rows_i
                      /KeygenM23MatrixSpec.poly_words_i
                      /KeygenM23MatrixSpec.array_words_i
                      /BArray8192.size /=.
              trivial.
            * apply
                (KeygenM23MatrixSpec.word_prefix_eq_set32_same
                  xp{1} xp{2}
                  KeygenM23MatrixSpec.mode2_b_words_i
                  (W64.to_uint (base{2} + j{2}))
                  (BArray8192.get32 xp{2}
                    (W64.to_uint (base{2} + j{2})) +
                   BArray8192.get32 xp{2}
                    (W64.to_uint (base{2} + (j{2} + len{2}))))
                  (BArray8192.get32 xp{2}
                    (W64.to_uint (base{2} + j{2})) +
                   BArray8192.get32 xp{2}
                    (W64.to_uint (base{2} + (j{2} + len{2}))))).
              - exact hb1.
              - rewrite /KeygenM23MatrixSpec.mode2_b_words_i
                        /KeygenM23MatrixSpec.mode2_rows_i
                        /KeygenM23MatrixSpec.poly_words_i
                        /KeygenM23MatrixSpec.array_words_i
                        /BArray8192.size /=.
                trivial.
              - exact hprefix.
              - trivial.
            * trivial.
        + wp.
          skip => /> &1 &2.
          move=> hpoly hbase hsched hlen1 hlen128 hprefix
                  z0 hz00 hz0255 hzrel hzlow hzup
                  hstart0 hstart256 hstartrel hcap hguard.
          have hstartlt : W64.to_uint start{2} < 256.
          + move: hguard.
            by rewrite W64.ultE W64.of_uintK.
          split.
          + exact
              (invntt_inner_entry
                start{2} len{2} zetasctr{2} z0
                hsched hlen1 hlen128 hz00 hz0255 hzrel hzlow hzup
                hstartrel hstartlt).
          + move=> xpL jR xpR hn1 hn2 hstartltx hjlowx hjhighx
                    hcmpeq hblockx hprefx z00 hz00x hz255x hzrelx
                    hzlowx hzupx hstartrelx hnextrelx.
            exact
              (invntt_inner_exit
                start{2} len{2} (zetasctr{2} + W64.one) jR z00
                hn1 hjlowx hjhighx hcmpeq hblockx hz00x hz255x
                hzrelx hzlowx hzupx hstartrelx hnextrelx).
      + wp.
        skip => /> &1 &2.
        move=> hpoly hbase hsched hlen1 hlen256 hz0 hz255 hzrel
                hpref hguard.
        have hlenlt : W64.to_uint len{2} < 256 by
          move: hguard; rewrite W64.ultE /=; smt().
        have hlen128 : W64.to_uint len{2} <= 128 by
          have :=
            KeygenM23MatrixSpec.ntt_stage_len_active_bounds
              (W64.to_uint len{2}) hsched hlenlt;
          smt().
        split.
        + split; first exact hlen128.
          exists (W64.to_uint zetasctr{2}).
          smt().
        move=> xpL startR xpR zR hn1 hn2 hlen128x hprefx
                z0x hz0x hz255x hzrel0 hzlow hzup hstart0 hstart256
                hstartrel hcap.
        have hstartge : 256 <= W64.to_uint startR by
          move: hn1; rewrite W64.ultE /=; smt().
        have hstarteq : W64.to_uint startR = 256 by smt().
        have hlennew :
            W64.to_uint (len{2} `<<` W8.one) =
              2 * W64.to_uint len{2}.
        + rewrite /(`<<`) W64.to_uint_shl 1:/# /=.
          rewrite modz_small; smt(W64.to_uint_cmp).
        have hschednew :
            KeygenM23MatrixSpec.ntt_stage_len
              (2 * W64.to_uint len{2}) by
          apply
            (KeygenM23MatrixSpec.ntt_stage_len_double
              (W64.to_uint len{2}) hsched hlenlt).
        have hblockeq :
            2 * (W64.to_uint zR - z0x) * W64.to_uint len{2} = 256
          by smt().
        rewrite hlennew.
        split; first exact hschednew.
        split; first smt().
        split; first smt(W64.to_uint_cmp).
        have hring :
            W64.to_uint zR * (2 * W64.to_uint len{2}) =
              2 * (z0x * W64.to_uint len{2}) +
              2 * (W64.to_uint zR - z0x) * W64.to_uint len{2}
          by ring.
        rewrite hring hzrel0 hblockeq.
        ring.
    + wp.
      skip => /> &1 &2.
      move=> hpolyle hbase hpref hguard.
      have hpolylt :
          W64.to_uint poly{2} <
            KeygenM23MatrixSpec.mode2_rows_i by
        move: hguard;
        rewrite W64.ultE W64.of_uintK
                /KeygenM23MatrixSpec.mode2_rows_i /=;
        smt().
      split; first exact hpolylt.
      move=> xpL lenR xpR zR hnlen1 hnlen2 hpolyltx hsched
              hlen1 hlen256 hz0 hz255 hzrel hprefx
              xpL0 jR xpR0 hnj1 hnj2 hj256 hpref0.
      have hpsucc :
          W64.to_uint (poly{2} + W64.one) =
            W64.to_uint poly{2} + 1 by
        rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      have hbsucc :
          W64.to_uint (base{2} + W64.of_int 256) =
            W64.to_uint base{2} + 256.
      + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
        trivial.
      rewrite hpsucc hbsucc hbase
              /KeygenM23MatrixSpec.mode2_rows_i
              /KeygenM23MatrixSpec.poly_words_i /=.
      smt().
+ auto => />.
qed.

lemma polymat_pointwise_mode2_prefix_scratch_independent :
  equiv [Parent._polymat_pointwise_acc ~
         Parent._polymat_pointwise_acc :
    ={mp, rows, cols} /\
    rows{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    cols{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
    KeygenM23MatrixSpec.word_prefix_eq
      vp{1} vp{2} KeygenM23MatrixSpec.mode2_s1_words_i
    ==>
    KeygenM23MatrixSpec.word_prefix_eq
      res{1} res{2} KeygenM23MatrixSpec.mode2_b_words_i].
proof.
proc.
inline Parent.__fqmul Parent.__montgomery_reduce.
while
  (={row, row_out, row_mat, rows, cols, mp} /\
   rows{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
   cols{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
   0 <= W64.to_uint row{1} <=
     KeygenM23MatrixSpec.mode2_rows_i /\
   W64.to_uint row_out{1} =
     KeygenM23MatrixSpec.poly_words_i * W64.to_uint row{1} /\
   W64.to_uint row_mat{1} =
     KeygenM23MatrixSpec.mode2_s1_words_i * W64.to_uint row{1} /\
   KeygenM23MatrixSpec.word_prefix_eq
     vp{1} vp{2} KeygenM23MatrixSpec.mode2_s1_words_i /\
   KeygenM23MatrixSpec.word_prefix_eq
     tp{1} tp{2} (W64.to_uint row_out{1})).
+ wp.
  while
    (={row, row_out, row_mat, rows, cols, mp,
       col, col_off} /\
     rows{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     cols{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
     0 <= W64.to_uint row{1} <
       KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint row_out{1} =
       KeygenM23MatrixSpec.poly_words_i * W64.to_uint row{1} /\
     W64.to_uint row_mat{1} =
       KeygenM23MatrixSpec.mode2_s1_words_i * W64.to_uint row{1} /\
     0 <= W64.to_uint col{1} <=
       KeygenM23MatrixSpec.mode2_cols_i /\
     W64.to_uint col_off{1} =
       KeygenM23MatrixSpec.poly_words_i * W64.to_uint col{1} /\
     KeygenM23MatrixSpec.word_prefix_eq
       vp{1} vp{2} KeygenM23MatrixSpec.mode2_s1_words_i /\
     KeygenM23MatrixSpec.word_prefix_eq
       tp{1} tp{2}
       (W64.to_uint row_out{1} +
        KeygenM23MatrixSpec.poly_words_i)).
  + wp.
    while
      (={row, row_out, row_mat, rows, cols, mp,
         col, col_off, j} /\
       rows{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
       cols{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
       0 <= W64.to_uint row{1} <
         KeygenM23MatrixSpec.mode2_rows_i /\
       W64.to_uint row_out{1} =
         KeygenM23MatrixSpec.poly_words_i * W64.to_uint row{1} /\
       W64.to_uint row_mat{1} =
         KeygenM23MatrixSpec.mode2_s1_words_i * W64.to_uint row{1} /\
       0 <= W64.to_uint col{1} <
         KeygenM23MatrixSpec.mode2_cols_i /\
       W64.to_uint col_off{1} =
         KeygenM23MatrixSpec.poly_words_i * W64.to_uint col{1} /\
       0 <= W64.to_uint j{1} <= KeygenM23MatrixSpec.poly_words_i /\
       KeygenM23MatrixSpec.word_prefix_eq
         vp{1} vp{2} KeygenM23MatrixSpec.mode2_s1_words_i /\
       KeygenM23MatrixSpec.word_prefix_eq
         tp{1} tp{2}
         (W64.to_uint row_out{1} +
          KeygenM23MatrixSpec.poly_words_i)).
    + auto => /> &1 &2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12.
      split.
      + smt(W64.to_uint_cmp).
      apply (KeygenM23MatrixSpec.word_prefix_eq_set32_same).
      + rewrite W64.to_uintD_small 1:/#.
        smt(W64.to_uint_cmp).
      + rewrite /KeygenM23MatrixSpec.array_words_i
                /BArray8192.size.
        smt(W64.to_uint_cmp).
      + assumption.
      + have htp :
          BArray8192.get32 tp{1}
            (W64.to_uint (row_out{2} + j{2})) =
          BArray8192.get32 tp{2}
            (W64.to_uint (row_out{2} + j{2})).
        + apply (KeygenM23MatrixSpec.word_prefix_eq_get32
                   tp{1} tp{2}
                   (W64.to_uint row_out{2} +
                    KeygenM23MatrixSpec.poly_words_i)
                   (W64.to_uint (row_out{2} + j{2})));
            first exact h11.
          split; first smt(W64.to_uint_cmp).
          rewrite W64.to_uintD_small 1:/#.
          move: h12.
          rewrite W64.ultE W64.of_uintK /=.
          smt(W64.to_uint_cmp).
        have hvp :
          BArray8192.get32 vp{1}
            (W64.to_uint (col_off{2} + j{2})) =
          BArray8192.get32 vp{2}
            (W64.to_uint (col_off{2} + j{2})).
        + apply (KeygenM23MatrixSpec.word_prefix_eq_get32
                   vp{1} vp{2}
                   KeygenM23MatrixSpec.mode2_s1_words_i
                   (W64.to_uint (col_off{2} + j{2})));
            first exact h10.
          split; first smt(W64.to_uint_cmp).
          rewrite W64.to_uintD_small 1:/#.
          move: h12.
          rewrite W64.ultE W64.of_uintK
                  /KeygenM23MatrixSpec.mode2_s1_words_i
                  /KeygenM23MatrixSpec.mode2_cols_i
                  /KeygenM23MatrixSpec.poly_words_i /=.
          smt(W64.to_uint_cmp).
        by rewrite htp hvp.
  wp.
  wp.
  skip => />.
  move=> &1 &2 hrow0 hrowlt hrowout hrowmat
          hcol0 hcolle hcoloff hvp htp hguard.
  have hcollt :
      W64.to_uint col{2} < KeygenM23MatrixSpec.mode2_cols_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_cols_i /=.
    trivial.
  split; first exact hcollt.
  move=> tpL jR tpR hdoneL hdoneR hcollt0
          hj0 hjle hprefix.
  split.
  + split; first smt(W64.to_uint_cmp).
    move=> _.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  + clear hvp htp hprefix hdoneL hdoneR hj0 hjle.
    rewrite W64.to_uintD_small 1:/#.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1
            W64.of_uintK
            /KeygenM23MatrixSpec.poly_words_i /=.
    smt().
  wp.
  while
    (={row, row_out, row_mat, rows, cols, mp, j} /\
     rows{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     cols{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
     0 <= W64.to_uint row{1} <
       KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint row_out{1} =
       KeygenM23MatrixSpec.poly_words_i * W64.to_uint row{1} /\
     W64.to_uint row_mat{1} =
       KeygenM23MatrixSpec.mode2_s1_words_i * W64.to_uint row{1} /\
     0 <= W64.to_uint j{1} <= KeygenM23MatrixSpec.poly_words_i /\
     KeygenM23MatrixSpec.word_prefix_eq
       vp{1} vp{2} KeygenM23MatrixSpec.mode2_s1_words_i /\
     KeygenM23MatrixSpec.word_prefix_eq
       tp{1} tp{2} (W64.to_uint row_out{1} + W64.to_uint j{1})).
  + auto => /> &1 &2 hrow0 hrowlt hrowout hrowmat
                    hj0 hjle hvp htp hguard.
    have hjlt : W64.to_uint j{2} < KeygenM23MatrixSpec.poly_words_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23MatrixSpec.poly_words_i /=.
      trivial.
    have hjsucc :
        W64.to_uint (j{2} + W64.one) = W64.to_uint j{2} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hidx :
        W64.to_uint (row_out{2} + j{2}) =
        W64.to_uint row_out{2} + W64.to_uint j{2}.
    + rewrite W64.to_uintD_small 1:/#.
      trivial.
    split.
    + rewrite hjsucc.
      smt(W64.to_uint_cmp).
    + rewrite hidx hjsucc.
      have hbound :
          0 <= W64.to_uint row_out{2} + W64.to_uint j{2} <
            KeygenM23MatrixSpec.array_words_i.
      + rewrite /KeygenM23MatrixSpec.array_words_i
                /BArray8192.size.
        smt(W64.to_uint_cmp).
      have hstep :=
        KeygenM23MatrixSpec.word_prefix_eq_extend_same_set32
          tp{1} tp{2}
          (W64.to_uint row_out{2} + W64.to_uint j{2})
          W32.zero hbound htp.
      have hlen :
          W64.to_uint row_out{2} + (W64.to_uint j{2} + 1) =
          (W64.to_uint row_out{2} + W64.to_uint j{2}) + 1
        by ring.
      by rewrite hlen; exact hstep.
  wp.
  skip => />.
move=> &1 &2 hrow0 hrowle hrowout hrowmat hvp htp hrowguard.
have hrowlt :
    W64.to_uint row{2} < KeygenM23MatrixSpec.mode2_rows_i.
+ move: hrowguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23MatrixSpec.mode2_rows_i /=.
  trivial.
split; first exact hrowlt.
move=> tpL jR tpR hjdoneL hjdoneR hrowlt0
        hj0 hjle hzero.
have hjeq :
    W64.to_uint jR = KeygenM23MatrixSpec.poly_words_i.
+ move: hjdoneL.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23MatrixSpec.poly_words_i /=.
  smt(W64.to_uint_cmp).
split.
+ by rewrite -hjeq.
move=> tpL0 colR colOffR tpR0 hcoldoneL hcoldoneR
        hcol0 hcolle hcoloff hrowprefix.
have hcoleq :
    W64.to_uint colR = KeygenM23MatrixSpec.mode2_cols_i.
+ move: hcoldoneL.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23MatrixSpec.mode2_cols_i /=.
  smt(W64.to_uint_cmp).
have hrowsucc :
    W64.to_uint (row{2} + W64.one) =
    W64.to_uint row{2} + 1.
+ rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  trivial.
have houtsucc :
    W64.to_uint (row_out{2} + W64.of_int 256) =
    W64.to_uint row_out{2} + 256.
+ rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  trivial.
have hmatsucc :
    W64.to_uint (row_mat{2} + colOffR) =
    W64.to_uint row_mat{2} + W64.to_uint colOffR.
+ rewrite W64.to_uintD_small 1:/#.
  trivial.
split.
+ rewrite hrowsucc.
  smt(W64.to_uint_cmp).
split.
+ rewrite houtsucc hrowsucc
           /KeygenM23MatrixSpec.poly_words_i.
  smt().
split.
+ rewrite hmatsucc hrowsucc
           /KeygenM23MatrixSpec.mode2_s1_words_i
           /KeygenM23MatrixSpec.mode2_cols_i
           /KeygenM23MatrixSpec.poly_words_i /=.
  smt().
+ by rewrite houtsucc.
wp.
skip => />.
move=> &1 &2 hvp.
split.
+ by rewrite /KeygenM23MatrixSpec.word_prefix_eq; smt().
move=> tpL rowR rowMatR rowOutR tpR
        hdoneL hdoneR hrow0 hrowle hrowout hrowmat hprefix.
have hroweq :
    W64.to_uint rowR = KeygenM23MatrixSpec.mode2_rows_i.
+ move: hdoneL.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23MatrixSpec.mode2_rows_i /=.
  smt(W64.to_uint_cmp).
have houteq :
    W64.to_uint rowOutR = KeygenM23MatrixSpec.mode2_b_words_i.
+ rewrite hrowout hroweq
           /KeygenM23MatrixSpec.mode2_b_words_i
           /KeygenM23MatrixSpec.mode2_rows_i
           /KeygenM23MatrixSpec.poly_words_i /=.
  trivial.
by rewrite -houteq.
qed.

lemma kp_m23_matrix_mode2_active_prefix_scratch_independent :
  equiv [Parent._kp_m23_matrix ~ Parent._kp_m23_matrix :
    ={ap, s1p, rows, cols} /\
    rows{1} = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    cols{1} = W64.of_int KeygenM23MatrixSpec.mode2_cols_i
    ==>
    KeygenM23MatrixSpec.word_prefix_eq
      res{1}.`1 res{2}.`1
      KeygenM23MatrixSpec.mode2_b_words_i /\
    KeygenM23MatrixSpec.word_prefix_eq
      res{1}.`2 res{2}.`2
      KeygenM23MatrixSpec.mode2_s1_words_i].
proof.
proc.
call polyvec_invntt_mode2_prefix_equiv.
wp.
call polymat_pointwise_mode2_prefix_scratch_independent.
wp.
call polyvec_ntt_mode2_prefix_equiv.
call kp_copy_vec_mode2_scratch_independent.
auto => />.
qed.

end TargetKeygenM23Matrix.
