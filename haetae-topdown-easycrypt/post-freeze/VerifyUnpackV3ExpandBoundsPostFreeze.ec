require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray32768 VerifyUnpackMode2Target
  KeygenUniformXofLeafSpec VerifyUnpackV3AssemblyPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3ExpandBoundsPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

op mode2_m : int = 3.
op mode2_matrix_words : int = 2048.

op expanded_mode2_prefix_bound (mat : BArray32768.t) : bool =
  KeygenUniformXofLeafSpec.bounded_prefix32768
    mat 0 mode2_matrix_words.

lemma bounded_prefix32768_append_at
    (a : BArray32768.t) base_i (base ctr : W64.t) (w : W32.t) :
  W64.to_uint base = base_i =>
  0 <= base_i =>
  base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
    BArray32768.size %/ 4 =>
  W64.to_uint ctr < KeygenUniformXofLeafSpec.uniform_poly_words_i =>
  KeygenUniformXofLeafSpec.bounded_prefix32768
    a 0 (base_i + W64.to_uint ctr) =>
  W32.to_uint w < KeygenUniformXofLeafSpec.uniform_q_i =>
  KeygenUniformXofLeafSpec.bounded_prefix32768
    (BArray32768.set32 a (W64.to_uint (base + ctr)) w)
    0 (base_i + W64.to_uint (ctr + W64.one)).
proof.
move=> hbase hbase0 hcap hctr hprefix hw.
have hidx :
    W64.to_uint (base + ctr) = base_i + W64.to_uint ctr.
+ rewrite W64.to_uintD_small.
  + rewrite hbase.
    have hctru := W64.to_uint_cmp ctr.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i in hctr.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /BArray32768.size in hcap.
    smt().
  by rewrite hbase.
have hnext :
    W64.to_uint (ctr + W64.one) = W64.to_uint ctr + 1.
+ rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  trivial.
rewrite hnext.
rewrite /KeygenUniformXofLeafSpec.bounded_prefix32768 in hprefix.
rewrite /KeygenUniformXofLeafSpec.bounded_prefix32768.
move=> i hi.
rewrite BArray32768.get_set32E 1:/# 1:/# hidx.
case (base_i + W64.to_uint ctr = i) => heq.
+ by subst i.
have hiold : 0 <= i < base_i + W64.to_uint ctr by smt().
have hp := hprefix i hiold.
rewrite ifF 1:/#.
exact hp.
qed.

lemma verify_uniform_consume_prefix_extend base_i :
  hoare [Verify.__poly_uniform_consume :
    W64.to_uint base = base_i /\
    0 <= base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    KeygenUniformXofLeafSpec.bounded_prefix32768
      ap 0 (base_i + W64.to_uint ctr) /\
    0 <= W64.to_uint ctr <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i
    ==>
    0 <= W64.to_uint res.`2 <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    KeygenUniformXofLeafSpec.bounded_prefix32768
      res.`1 0 (base_i + W64.to_uint res.`2)].
proof.
proc.
while
  (W64.to_uint base = base_i /\
   0 <= base_i /\
   base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
     BArray32768.size %/ 4 /\
   KeygenUniformXofLeafSpec.bounded_prefix32768
     ap 0 (base_i + W64.to_uint ctr) /\
   0 <= W64.to_uint ctr <=
     KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ if.
  + by auto.
  sp 2.
  if.
  + by auto.
  sp 11.
  if.
  + auto => /> &hr pos0 hbase0 hcap hprefix hctr0 hctrle
                  hlive hnotfull hrem haccept.
    split.
    + apply (bounded_prefix32768_append_at
               ap{hr} (W64.to_uint base{hr})
               base{hr} ctr{hr} _).
      + trivial.
      + exact hbase0.
      + exact hcap.
      + move: hnotfull.
        rewrite W64.uleE W64.of_uintK
                /KeygenUniformXofLeafSpec.uniform_poly_words_i /=.
        smt(W64.to_uint_cmp).
      + exact hprefix.
      move: haccept.
      rewrite W32.ultE W32.of_uintK
              /KeygenUniformXofLeafSpec.uniform_q_i /=.
      trivial.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    move: hnotfull.
    rewrite W64.uleE W64.of_uintK
            /KeygenUniformXofLeafSpec.uniform_poly_words_i /=.
    smt(W64.to_uint_cmp).
  by auto.
wp.
skip => />.
qed.

lemma verify_poly_uniform_at_prefix_extend base_i :
  hoare [Verify._poly_uniform_at :
    W64.to_uint base = base_i /\
    0 <= base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    KeygenUniformXofLeafSpec.bounded_prefix32768 ap 0 base_i
    ==>
    KeygenUniformXofLeafSpec.bounded_prefix32768
      res 0 (base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i)].
proof.
proc.
while
  (W64.to_uint base = base_i /\
   0 <= base_i /\
   base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
     BArray32768.size %/ 4 /\
   KeygenUniformXofLeafSpec.bounded_prefix32768
     ap 0 (base_i + W64.to_uint ctr) /\
   0 <= W64.to_uint ctr <=
     KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ wp.
  call (verify_uniform_consume_prefix_extend base_i).
  wp.
  call (_: true).
  + by auto.
  while
    (W64.to_uint base = base_i /\
     0 <= base_i /\
     base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
       BArray32768.size %/ 4 /\
     KeygenUniformXofLeafSpec.bounded_prefix32768
       ap 0 (base_i + W64.to_uint ctr) /\
     0 <= W64.to_uint ctr <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i).
  + by auto.
  by auto.
wp.
call (verify_uniform_consume_prefix_extend base_i).
do 5! (wp; call (_: true); first by auto).
auto => /> &hr hbase0 hcap hprefix hpoly0 result
             hres0 hresle hresprefix ap0 ctr0
             hguard hbound hctr0 hctrle.
have hdone :
    W64.to_uint ctr0 =
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
+ move: hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenUniformXofLeafSpec.uniform_poly_words_i /=.
  smt(W64.to_uint_cmp).
rewrite -hdone.
exact hbound.
qed.

lemma verify_expand_with_vecA_mode2_prefix_bound
    (mat0 : BArray32768.t) seed0 :
  hoare [Verify.__polymatkl_expand_matA_with_vecA :
    matp = mat0 /\ seedp = seed0 /\
    rows = W64.of_int mode2_rows /\
    cols = W64.of_int mode2_cols /\
    m = W64.of_int mode2_m
    ==>
    expanded_mode2_prefix_bound res].
proof.
proc.
while
  (seedp = seed0 /\
   rows = W64.of_int mode2_rows /\
   cols = W64.of_int mode2_cols /\
   m = W64.of_int mode2_m /\
   0 <= W64.to_uint i <= mode2_rows /\
   W64.to_uint base =
     W64.to_uint i * mode2_cols * poly_words /\
   KeygenUniformXofLeafSpec.bounded_prefix32768
     matp 0 (W64.to_uint base)).
+ wp.
  exlim base => base_before.
  exlim i => i_before.
  seq 13 :
    (seedp = seed0 /\
     rows = W64.of_int mode2_rows /\
     cols = W64.of_int mode2_cols /\
     m = W64.of_int mode2_m /\
     0 <= W64.to_uint i < mode2_rows /\
     W64.to_uint base =
       W64.to_uint i * mode2_cols * poly_words + poly_words /\
     KeygenUniformXofLeafSpec.bounded_prefix32768
       matp 0 (W64.to_uint base)).
  + wp.
    call
      (verify_poly_uniform_at_prefix_extend
         (W64.to_uint base_before)).
    auto => /> &hr hi0 hile hbase hprefix hguard.
    have hilt : W64.to_uint i_before < mode2_rows.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_rows /=.
      smt(W64.to_uint_cmp).
    have hbase0 : 0 <= W64.to_uint base_before
      by smt(W64.to_uint_cmp).
    have hcap :
        W64.to_uint base_before +
          KeygenUniformXofLeafSpec.uniform_poly_words_i <=
        BArray32768.size %/ 4.
    + rewrite /mode2_rows in hilt.
      rewrite /mode2_cols /poly_words in hbase.
      rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
              /BArray32768.size.
      smt().
    split.
    + by split.
    move=> _ _ result hresult.
    rewrite /protect_64 /protect_ptr.
    have hbasenext :
        W64.to_uint (base_before + W64.of_int poly_words) =
          W64.to_uint base_before + poly_words.
    + rewrite W64.to_uintD_small.
      + rewrite W64.of_uintK /=.
        rewrite /mode2_cols /poly_words in hbase.
        smt(W64.to_uint_cmp).
      by rewrite W64.of_uintK /=.
    do split.
    + by move=> _.
    + by rewrite hbasenext hbase.
    rewrite hbasenext.
    exact hresult.
  while
    (seedp = seed0 /\
     rows = W64.of_int mode2_rows /\
     cols = W64.of_int mode2_cols /\
     m = W64.of_int mode2_m /\
     0 <= W64.to_uint i < mode2_rows /\
     0 <= W64.to_uint j <= mode2_m /\
     W64.to_uint base =
       (W64.to_uint i * mode2_cols + 1 + W64.to_uint j) * poly_words /\
     KeygenUniformXofLeafSpec.bounded_prefix32768
       matp 0 (W64.to_uint base)).
  + wp.
    exlim base => inner_base_before.
    exlim i => inner_i_before.
    exlim j => j_before.
    call
      (verify_poly_uniform_at_prefix_extend
         (W64.to_uint inner_base_before)).
    auto => /> &hr hi0 hilt hj0 hjle hbase hprefix hguard.
    have hjlt : W64.to_uint j_before < mode2_m.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_m /=.
      smt(W64.to_uint_cmp).
    have hjnext :
        W64.to_uint (j_before + W64.one) = W64.to_uint j_before + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hbasenext :
        W64.to_uint (inner_base_before + W64.of_int poly_words) =
          W64.to_uint inner_base_before + poly_words.
    + rewrite W64.to_uintD_small.
      + rewrite W64.of_uintK /= hbase.
        rewrite /mode2_rows /mode2_cols /mode2_m /poly_words in hi0.
        rewrite /mode2_rows /mode2_cols /mode2_m /poly_words in hilt.
        rewrite /mode2_rows /mode2_cols /mode2_m /poly_words in hj0.
        rewrite /mode2_rows /mode2_cols /mode2_m /poly_words in hjlt.
        rewrite /mode2_rows /mode2_cols /mode2_m /poly_words.
        smt(W64.to_uint_cmp).
      by rewrite W64.of_uintK /=.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /BArray32768.size /mode2_rows /mode2_cols /mode2_m
            /poly_words in hbase.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /BArray32768.size /mode2_rows /mode2_cols /mode2_m
            /poly_words in hbasenext.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /BArray32768.size /mode2_rows /mode2_cols /mode2_m
            /poly_words.
    do split; try smt(W64.to_uint_cmp).
  auto => />.
  move=> &hr hi0 hilt hbase hprefix.
  split.
  + rewrite hbase.
    ring.
  move=> base0 i0 j0 matp0 hinner hi0' hilt' hj0 hjle
         hbase' hprefix'.
  have hjdone : W64.to_uint j0 = mode2_m.
  + move: hinner.
    rewrite W64.ultE W64.of_uintK /mode2_m /=.
    smt(W64.to_uint_cmp).
  have hinext :
      W64.to_uint (i0 + W64.one) = W64.to_uint i0 + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  rewrite /mode2_rows in hilt'.
  split.
  + rewrite hinext.
    split; first smt().
    move=> _; smt().
  rewrite hinext hbase' hjdone.
  rewrite /mode2_cols /mode2_m /poly_words.
  ring.
auto => />.
split.
+ rewrite /KeygenUniformXofLeafSpec.bounded_prefix32768.
  smt().
move=> base0 i0 matp0 hguard hi0 hile hbase hprefix.
have hbase_done : W64.to_uint base0 = mode2_matrix_words.
+ rewrite /mode2_matrix_words.
  rewrite /mode2_rows /mode2_cols /poly_words in hbase.
  move: hguard.
  rewrite W64.ultE W64.of_uintK /mode2_rows /=.
  smt(W64.to_uint_cmp).
rewrite /expanded_mode2_prefix_bound /mode2_matrix_words.
smt().
qed.

lemma expanded_mode2_prefix_bound_firstcol
    (mat : BArray32768.t) :
  expanded_mode2_prefix_bound mat =>
  forall i, 0 <= i < mode2_vec_words =>
    W32.to_uint (BArray32768.get32 mat (firstcol_slot_idx i)) < 64513.
proof.
rewrite /expanded_mode2_prefix_bound
        /KeygenUniformXofLeafSpec.bounded_prefix32768
        /mode2_matrix_words
        /KeygenUniformXofLeafSpec.uniform_q_i.
move=> hbound i hi.
have hslot : 0 <= firstcol_slot_idx i < 2048.
+ rewrite /firstcol_slot_idx /mode2_rows /mode2_cols
          /mode2_vec_words /row_stride /poly_words in hi.
  rewrite /firstcol_slot_idx /mode2_rows /mode2_cols
          /mode2_vec_words /row_stride /poly_words.
  have hdiv := divz_eq i 256.
  have hmod := modz_cmp i 256 _; first smt().
  smt(@IntDiv).
have hb := hbound (firstcol_slot_idx i) hslot.
rewrite add0z in hb.
exact hb.
qed.

end VerifyUnpackV3ExpandBoundsPostFreeze.
