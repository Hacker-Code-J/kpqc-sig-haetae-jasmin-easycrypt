require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray8192 BArray32768 Fq
  KeygenM23ArithmeticSpec KeygenM23MatrixSpec
  VerifyUnpackV3AssemblyPostFreeze VerifyUnpackV3PreNttPostFreeze
  VerifyUnpackVkM23CoefficientsPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3PreNttBoundPostFreeze.

op pre_ntt_source_bound
    (vkp : BArray2752.t) (mat : BArray32768.t) : bool =
  forall i, 0 <= i < mode2_vec_words =>
    W32.to_uint
      (BArray32768.get32 mat (firstcol_slot_idx i)) < 64513 /\
    W32.to_uint
      (VerifyUnpackVkM23CoefficientsPostFreeze.unpack_vk_coeff_word vkp i)
      < 32768.

op pre_ntt_active_bound17 (a : BArray8192.t) : bool =
  forall i, 0 <= i < mode2_vec_words =>
    Fq.bw32 (BArray8192.get32 a i) 17.

lemma mode2_pre_ntt_word_bound17 (a b : W32.t) :
  0 <= W32.to_uint a < 64513 =>
  0 <= W32.to_uint b < 32768 =>
  Fq.bw32 (mode2_pre_ntt_word a b) 17.
proof.
move=> ha hb.
have heq :
    mode2_pre_ntt_word a b =
    W32.of_int (2 * (W32.to_uint a - 2 * W32.to_uint b)).
+ rewrite /mode2_pre_ntt_word /(`<<`) !W8.of_uintK /=;
  rewrite -(W32.to_uintK a) -(W32.to_uintK b).
  rewrite !W32.shlMP 1:/#.
  rewrite !W32.to_uintK_small 1:/# 1:/#.
  rewrite W32.of_intS' W32.shlMP 1:/#.
  congr; ring.
rewrite heq /Fq.bw32 W32.to_sintK_small; smt().
qed.

lemma pre_ntt_active_bound17_of_prefix_frame
    (vkp : BArray2752.t)
    (mat0 mat : BArray32768.t) (after : BArray8192.t) :
  pre_ntt_source_bound vkp mat0 =>
  VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
    vkp mat after mode2_vec_words =>
  mat_firstcol_frame mat0 mat =>
  pre_ntt_active_bound17 after.
proof.
move=> hsource hprefix hframe.
rewrite /pre_ntt_active_bound17 => i hi.
rewrite /VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix in hprefix.
rewrite hprefix 1:hi hframe 1:hi.
apply mode2_pre_ntt_word_bound17.
+ have ha := W32.to_uint_cmp
    (BArray32768.get32 mat0 (firstcol_slot_idx i)).
  have hs := hsource i hi.
  smt().
have hb := W32.to_uint_cmp
  (VerifyUnpackVkM23CoefficientsPostFreeze.unpack_vk_coeff_word vkp i).
have hs := hsource i hi.
smt().
qed.

lemma pre_ntt_active_bound17_repr_self (a : BArray8192.t) :
  pre_ntt_active_bound17 a =>
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    a 0 (KeygenM23ArithmeticSpec.wide_poly a 0) 17 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    a KeygenM23MatrixSpec.poly_words_i
      (KeygenM23ArithmeticSpec.wide_poly
        a KeygenM23MatrixSpec.poly_words_i) 17.
proof.
move=> hbound.
split.
+ apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
  rewrite /KeygenM23ArithmeticSpec.wide_slice_bound => j hj.
  apply hbound.
  rewrite /mode2_vec_words /mode2_rows /poly_words
          /KeygenM23MatrixSpec.poly_words_i in hj.
  rewrite /mode2_vec_words /mode2_rows /poly_words.
  smt().
apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
rewrite /KeygenM23ArithmeticSpec.wide_slice_bound => j hj.
apply hbound.
rewrite /mode2_vec_words /mode2_rows /poly_words
        /KeygenM23MatrixSpec.poly_words_i in hj.
rewrite /mode2_vec_words /mode2_rows /poly_words
        /KeygenM23MatrixSpec.poly_words_i.
smt().
qed.

lemma actual_verify_unpack_post_expand_pre_ntt_mode2_bound17
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [
    VerifyUnpackV3PreNttPostFreeze.ActualVerifyUnpackPostExpandPreNttMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0 /\
    pre_ntt_source_bound vkp0 mat0
    ==>
    VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
      vkp0 res.`2 res.`1 mode2_vec_words /\
    mat_firstcol_frame mat0 res.`2 /\
    pre_ntt_active_bound17 res.`1 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`1 0 (KeygenM23ArithmeticSpec.wide_poly res.`1 0) 17 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`1 KeygenM23MatrixSpec.poly_words_i
        (KeygenM23ArithmeticSpec.wide_poly
          res.`1 KeygenM23MatrixSpec.poly_words_i) 17].
proof.
conseq
  (VerifyUnpackV3PreNttPostFreeze.actual_verify_unpack_post_expand_pre_ntt_mode2_word_exact
     bp0 vkp0 mat0).
+ auto.
move=> &m hpre result [hprefix hframe].
have hsource : pre_ntt_source_bound vkp0 mat0 by
  move: hpre => />.
have hbound :=
  pre_ntt_active_bound17_of_prefix_frame
    vkp0 mat0 result.`2 result.`1 hsource hprefix hframe.
have hrepr := pre_ntt_active_bound17_repr_self result.`1 hbound.
by auto.
qed.

end VerifyUnpackV3PreNttBoundPostFreeze.
