require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray8192 BArray32768 VerifyUnpackMode2Target
  VerifyUnpackV3AssemblyPostFreeze
  VerifyUnpackVkM23CoefficientsPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3PreNttPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

op pre_ntt_prefix
    (vkp : BArray2752.t) (mat : BArray32768.t)
    (after : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 after i =
      mode2_pre_ntt_word
        (BArray32768.get32 mat (firstcol_slot_idx i))
        (VerifyUnpackVkM23CoefficientsPostFreeze.unpack_vk_coeff_word vkp i).

lemma decoder_active_wordsE :
  VerifyUnpackVkM23CoefficientsPostFreeze.mode2_active_words =
  mode2_vec_words.
proof.
rewrite /VerifyUnpackVkM23CoefficientsPostFreeze.mode2_active_words
        /VerifyUnpackV3AssemblyPostFreeze.mode2_vec_words
        /VerifyUnpackV3AssemblyPostFreeze.mode2_rows
        /VerifyUnpackV3AssemblyPostFreeze.poly_words.
ring.
qed.

lemma pre_ntt_prefix_of_actual_steps
    (decoded first_double subtracted out : BArray8192.t)
    (vkp : BArray2752.t) (mat : BArray32768.t) :
  VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
    decoded vkp mode2_vec_words =>
  vec_double_prefix decoded first_double mode2_vec_words =>
  sub_firstcol_prefix first_double mat subtracted mode2_vec_words =>
  vec_double_prefix subtracted out mode2_vec_words =>
  pre_ntt_prefix vkp mat out mode2_vec_words.
proof.
move=> hdecoded hdouble1 hsub hdouble2.
rewrite /pre_ntt_prefix => i hi.
rewrite /vec_double_prefix in hdouble1.
rewrite /vec_double_prefix in hdouble2.
rewrite /sub_firstcol_prefix in hsub.
rewrite /VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
        in hdecoded.
rewrite hdouble2 1:hi hsub 1:hi hdouble1 1:hi hdecoded 1:hi.
by rewrite /mode2_pre_ntt_word.
qed.

(* The generated matrix expansion remains outside this wrapper.  Its [matp]
   input is the expanded matrix, and the wrapper follows the exact generated
   decoder/double/subtract/double suffix up to the NTT boundary. *)
module ActualVerifyUnpackPostExpandPreNttMode2 = {
  proc run (bp : BArray8192.t, vkp : BArray2752.t,
            matp : BArray32768.t)
      : BArray8192.t * BArray32768.t = {
    bp <@ Verify.__unpack_vk_m23_coeffs
      (bp, vkp,
       W64.of_int VerifyUnpackVkM23CoefficientsPostFreeze.mode2_rows);
    matp <@ Verify._polymatkl_double
      (matp, W64.of_int mode2_rows, W64.of_int mode2_cols);
    bp <@ Verify._polyvec_double
      (bp, W64.of_int mode2_vec_words);
    bp <@ Verify.__polyvec_sub_left_inplace
      (bp, matp, W64.of_int mode2_cols, W64.of_int mode2_rows);
    bp <@ Verify._polyvec_double
      (bp, W64.of_int mode2_vec_words);
    return (bp, matp);
  }
}.

lemma actual_verify_unpack_post_expand_pre_ntt_mode2_word_exact
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [ActualVerifyUnpackPostExpandPreNttMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0
    ==>
    pre_ntt_prefix vkp0 res.`2 res.`1 mode2_vec_words /\
    mat_firstcol_frame mat0 res.`2].
proof.
proc.
seq 1 :
  (exists decoded,
     bp = decoded /\ vkp = vkp0 /\ matp = mat0 /\
     VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
       decoded vkp0 mode2_vec_words).
+ call
    (VerifyUnpackVkM23CoefficientsPostFreeze.unpack_vk_m23_coeffs_mode2_actual_exact
       bp0 vkp0).
  auto => />.
  move=> result hdecoded htail.
  exists result.
  split; first trivial.
  by rewrite -decoder_active_wordsE.
exlim bp => decoded0.
seq 1 :
  (exists doubled_mat,
     bp = decoded0 /\ vkp = vkp0 /\ matp = doubled_mat /\
     VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
       decoded0 vkp0 mode2_vec_words /\
     mat_firstcol_frame mat0 doubled_mat).
+ call (polymatkl_double_mode2_firstcol_frame mat0).
  auto => />.
  move=> &hr hdecoded result hframe.
  exists result.
  by auto.
exlim matp => doubled_mat0.
seq 1 :
  (exists first_double,
     bp = first_double /\ vkp = vkp0 /\ matp = doubled_mat0 /\
     VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
       decoded0 vkp0 mode2_vec_words /\
     mat_firstcol_frame mat0 doubled_mat0 /\
     vec_double_prefix decoded0 first_double mode2_vec_words).
+ call (polyvec_double_mode2_word_exact decoded0).
  auto => />.
  move=> &hr hdecoded hmatframe result hdouble htail.
  exists result.
  by auto.
exlim bp => first_double0.
seq 1 :
  (exists subtracted,
     bp = subtracted /\ vkp = vkp0 /\ matp = doubled_mat0 /\
     VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
       decoded0 vkp0 mode2_vec_words /\
     mat_firstcol_frame mat0 doubled_mat0 /\
     vec_double_prefix decoded0 first_double0 mode2_vec_words /\
     sub_firstcol_prefix first_double0 doubled_mat0 subtracted
       mode2_vec_words).
+ call
    (polyvec_sub_left_inplace_mode2_word_exact
      first_double0 doubled_mat0).
  auto => />.
  move=> &hr hdecoded hmatframe hdouble result hsub htail.
  exists result.
  by auto.
exlim bp => subtracted0.
call (polyvec_double_mode2_word_exact subtracted0).
auto => />.
move=> &hr hdecoded hmatframe hdouble1 hsub result hdouble2 htail.
exact (pre_ntt_prefix_of_actual_steps
  decoded0 first_double0 subtracted0 result
  vkp{hr} matp{hr} hdecoded hdouble1 hsub hdouble2).
qed.

end VerifyUnpackV3PreNttPostFreeze.
