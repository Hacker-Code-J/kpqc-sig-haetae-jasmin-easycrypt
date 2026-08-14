require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray8192 BArray32768 VerifyUnpackMode2Target
  KeygenM23ArithmeticSpec KeygenM23MatrixSpec NTTRowProductSpec
  VerifyUnpackVkM23CoefficientsPostFreeze
  VerifyUnpackV3AssemblyPostFreeze VerifyUnpackV3PreNttPostFreeze
  VerifyUnpackV3ExpandBoundsPostFreeze
  VerifyUnpackV3PreNttBoundPostFreeze
  VerifyUnpackV3PreNttTightBoundPostFreeze
  VerifyUnpackV3NttBound17PostFreeze
  VerifyUnpackV3NttTightBoundPostFreeze
  VerifyUnpackV3NttInstallPostFreeze
  VerifyUnpackV3MatrixProfilePostFreeze
  VerifyUnpackV3MatDoubleBoundsPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3PostDecodeThroughNttPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

module ActualVerifyUnpackPostDecodePreNttMode2 = {
  proc run (bp : BArray8192.t, vkp : BArray2752.t,
            matp : BArray32768.t)
      : BArray8192.t * BArray32768.t = {
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

lemma actual_verify_unpack_post_decode_pre_ntt_mode2_word_exact
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [ActualVerifyUnpackPostDecodePreNttMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0 /\
    VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
      bp0 vkp0 mode2_vec_words /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mat0
    ==>
    VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
      vkp0 res.`2 res.`1 mode2_vec_words /\
    mat_firstcol_frame mat0 res.`2 /\
    VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
      res.`2].
proof.
proc.
seq 1 :
  (exists doubled_mat,
     bp = bp0 /\ vkp = vkp0 /\ matp = doubled_mat /\
     VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
       bp0 vkp0 mode2_vec_words /\
     mat_firstcol_frame mat0 doubled_mat /\
     VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
       doubled_mat).
+ call
    (VerifyUnpackV3MatDoubleBoundsPostFreeze.verify_unpack_v3_mat_double_mixed_bounds
       mat0).
  auto => />.
  move=> result hdecoded hframe hnonfirst hfirst16 hprofile.
  smt().
exlim matp => doubled_mat0.
seq 1 :
  (exists first_double,
     bp = first_double /\ vkp = vkp0 /\ matp = doubled_mat0 /\
     VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
       bp0 vkp0 mode2_vec_words /\
     mat_firstcol_frame mat0 doubled_mat0 /\
     VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
       doubled_mat0 /\
     vec_double_prefix bp0 first_double mode2_vec_words).
+ call (polyvec_double_mode2_word_exact bp0).
  auto => />.
  move=> &hr hdecoded hmatframe hnonfirst result hdouble htail.
  exists result.
  by auto.
exlim bp => first_double0.
seq 1 :
  (exists subtracted,
     bp = subtracted /\ vkp = vkp0 /\ matp = doubled_mat0 /\
     VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
       bp0 vkp0 mode2_vec_words /\
     mat_firstcol_frame mat0 doubled_mat0 /\
     VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
       doubled_mat0 /\
     vec_double_prefix bp0 first_double0 mode2_vec_words /\
     sub_firstcol_prefix first_double0 doubled_mat0 subtracted
       mode2_vec_words).
+ call
    (polyvec_sub_left_inplace_mode2_word_exact
      first_double0 doubled_mat0).
  auto => />.
  move=> &hr hdecoded hmatframe hnonfirst hdouble result hsub htail.
  exists result.
  by auto.
exlim bp => subtracted0.
call (polyvec_double_mode2_word_exact subtracted0).
auto => />.
move=> &hr hdecoded hmatframe hnonfirst hdouble1 hsub result hdouble2 htail.
have hprefix :=
  VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix_of_actual_steps
    bp0 first_double0 subtracted0 result
    vkp{hr} matp{hr} hdecoded hdouble1 hsub hdouble2.
by auto.
qed.

lemma actual_verify_unpack_post_decode_pre_ntt_mode2_bound17
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [ActualVerifyUnpackPostDecodePreNttMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0 /\
    VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
      bp0 vkp0 mode2_vec_words /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mat0 /\
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp0 mat0
    ==>
    VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
      vkp0 res.`2 res.`1 mode2_vec_words /\
    mat_firstcol_frame mat0 res.`2 /\
    VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
      res.`2 /\
    VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
      res.`1
      (KeygenM23ArithmeticSpec.wide_poly res.`1 0)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`1 KeygenM23MatrixSpec.poly_words_i)].
proof.
conseq
  (actual_verify_unpack_post_decode_pre_ntt_mode2_word_exact
     bp0 vkp0 mat0).
+ auto.
move=> &m hpre result [hprefix [hframe hnonfirst]].
have hsource :
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound
      vkp0 mat0 by
  move: hpre => />.
have hbound :=
  VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_active_bound17_of_prefix_frame
    vkp0 mat0 result.`2 result.`1 hsource hprefix hframe.
have hrepr :=
  VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_active_bound17_repr_self
    result.`1 hbound.
rewrite
  /VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17.
by auto.
qed.

lemma actual_verify_unpack_post_decode_pre_ntt_mode2_tight_bound
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [ActualVerifyUnpackPostDecodePreNttMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0 /\
    VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
      bp0 vkp0 mode2_vec_words /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mat0 /\
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp0 mat0
    ==>
    VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
      vkp0 res.`2 res.`1 mode2_vec_words /\
    mat_firstcol_frame mat0 res.`2 /\
    VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
      res.`2 /\
    VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_input_signed131068
      res.`1].
proof.
conseq
  (actual_verify_unpack_post_decode_pre_ntt_mode2_word_exact
     bp0 vkp0 mat0).
+ auto.
move=> &m hpre result [hprefix [hframe hnonfirst]].
have hsource :
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound
      vkp0 mat0 by
  move: hpre => />.
have hbound :=
  VerifyUnpackV3PreNttTightBoundPostFreeze.pre_ntt_active_sint_bound_of_prefix_frame
    vkp0 mat0 result.`2 result.`1 hsource hprefix hframe.
have hinput :
    VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_input_signed131068
      result.`1.
+ move: hbound.
  rewrite
    /VerifyUnpackV3PreNttTightBoundPostFreeze.pre_ntt_active_sint_bound
    /VerifyUnpackV3PreNttTightBoundPostFreeze.pre_ntt_sint_limit
    /VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_input_signed131068
    /VerifyUnpackV3NttTightBoundPostFreeze.signed_bound32
    /VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_words
    /VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_polys
    /mode2_vec_words /mode2_rows /poly_words
    /KeygenM23MatrixSpec.poly_words_i.
  by auto.
by auto.
qed.

lemma actual_verify_unpack_post_decode_pre_ntt_mode2_full_tight_input
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [ActualVerifyUnpackPostDecodePreNttMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0 /\
    VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
      bp0 vkp0 mode2_vec_words /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mat0 /\
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp0 mat0
    ==>
    VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
      vkp0 res.`2 res.`1 mode2_vec_words /\
    mat_firstcol_frame mat0 res.`2 /\
    VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
      res.`2 /\
    VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
      res.`1
      (KeygenM23ArithmeticSpec.wide_poly res.`1 0)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`1 KeygenM23MatrixSpec.poly_words_i) /\
    VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_input_signed131068
      res.`1].
proof.
conseq
  (actual_verify_unpack_post_decode_pre_ntt_mode2_bound17
     bp0 vkp0 mat0)
  (actual_verify_unpack_post_decode_pre_ntt_mode2_tight_bound
     bp0 vkp0 mat0) => />.
qed.

module ActualVerifyUnpackPostDecodeThroughNttInstallMode2 = {
  proc run (bp : BArray8192.t, vkp : BArray2752.t,
            matp : BArray32768.t)
      : BArray8192.t * BArray32768.t = {
    (bp, matp) <@
      ActualVerifyUnpackPostDecodePreNttMode2.run (bp, vkp, matp);
    (bp, matp) <@
      VerifyUnpackV3NttInstallPostFreeze.ActualVerifyUnpackNttInstallMode2.run
        (bp, matp);
    return (bp, matp);
  }
}.

lemma actual_verify_unpack_post_decode_through_ntt_install_mode2_correct
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [ActualVerifyUnpackPostDecodeThroughNttInstallMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0 /\
    VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
      bp0 vkp0 mode2_vec_words /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mat0 /\
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp0 mat0
    ==>
    exists pre_ntt preinstall_mat,
      VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
        vkp0 preinstall_mat pre_ntt mode2_vec_words /\
      mat_firstcol_frame mat0 preinstall_mat /\
      VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
        preinstall_mat /\
      VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
        pre_ntt
        (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
        (KeygenM23ArithmeticSpec.wide_poly
          pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
      VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
        res.`1
        (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
        (KeygenM23ArithmeticSpec.wide_poly
          pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
      NTTRowProductSpec.vector_forward_repr
        VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_polys
        (fun col =>
          KeygenM23ArithmeticSpec.wide_poly
            res.`1 (col * KeygenM23MatrixSpec.poly_words_i))
        (fun col =>
          KeygenM23ArithmeticSpec.wide_poly
            pre_ntt (col * KeygenM23MatrixSpec.poly_words_i)) /\
      KeygenM23MatrixSpec.word_tail_frame
        pre_ntt res.`1
          VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_words /\
      mat_firstcol_install_prefix res.`1 res.`2 mode2_vec_words /\
      mat_firstcol_install_frame
        preinstall_mat res.`2 mode2_vec_words /\
      VerifyUnpackV3MatrixProfilePostFreeze.verify_unpack_mode2_matrix_repr_bound25_17
        res.`2].
proof.
proc.
seq 1 :
  (exists pre_ntt preinstall_mat,
     bp = pre_ntt /\ vkp = vkp0 /\ matp = preinstall_mat /\
     VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
       vkp0 preinstall_mat pre_ntt mode2_vec_words /\
     mat_firstcol_frame mat0 preinstall_mat /\
     VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
       preinstall_mat /\
     VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
       pre_ntt
       (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
       (KeygenM23ArithmeticSpec.wide_poly
         pre_ntt KeygenM23MatrixSpec.poly_words_i)).
+ call
    (actual_verify_unpack_post_decode_pre_ntt_mode2_bound17
       bp0 vkp0 mat0).
  auto => />.
  move=> result hprefix hframe hnonfirst hinput.
  smt().
exlim bp => pre_ntt0.
exlim matp => preinstall_mat0.
call
  (VerifyUnpackV3NttInstallPostFreeze.actual_verify_unpack_ntt_install_mode2_full_correct17
     pre_ntt0 preinstall_mat0
     (KeygenM23ArithmeticSpec.wide_poly pre_ntt0 0)
     (KeygenM23ArithmeticSpec.wide_poly
       pre_ntt0 KeygenM23MatrixSpec.poly_words_i)).
auto => />.
move=> &m hprefix hmatframe hnonfirst hinput result
        hbound hforward htail hinstall hinstallframe.
move=> hvector htailframe hinstallprefix hmatrixframe.
have hnttbound :
    VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
      hbound.`1
      (KeygenM23ArithmeticSpec.wide_poly pre_ntt0 0)
      (KeygenM23ArithmeticSpec.wide_poly
        pre_ntt0 KeygenM23MatrixSpec.poly_words_i).
+ rewrite
    /VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
    /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  by auto.
have hmatrixprofile :=
  VerifyUnpackV3MatrixProfilePostFreeze.verify_unpack_mode2_matrix_repr_bound25_17_of_install
    hbound.`1 preinstall_mat0 hbound.`2
    (KeygenM23ArithmeticSpec.wide_poly pre_ntt0 0)
    (KeygenM23ArithmeticSpec.wide_poly
      pre_ntt0 KeygenM23MatrixSpec.poly_words_i)
    hnonfirst hnttbound hinstallprefix hmatrixframe.
exists pre_ntt0 preinstall_mat0.
by auto.
qed.

lemma actual_verify_unpack_post_decode_through_ntt_install_mode2_tight20_correct
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [ActualVerifyUnpackPostDecodeThroughNttInstallMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0 /\
    VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
      bp0 vkp0 mode2_vec_words /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mat0 /\
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp0 mat0
    ==>
    exists pre_ntt preinstall_mat,
      VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
        vkp0 preinstall_mat pre_ntt mode2_vec_words /\
      mat_firstcol_frame mat0 preinstall_mat /\
      VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
        preinstall_mat /\
      VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
        pre_ntt
        (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
        (KeygenM23ArithmeticSpec.wide_poly
          pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
      VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_input_signed131068
        pre_ntt /\
      VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_output_bound20
        res.`1 /\
      VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
        res.`1
        (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
        (KeygenM23ArithmeticSpec.wide_poly
          pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
      NTTRowProductSpec.vector_forward_repr
        VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_polys
        (fun col =>
          KeygenM23ArithmeticSpec.wide_poly
            res.`1 (col * KeygenM23MatrixSpec.poly_words_i))
        (fun col =>
          KeygenM23ArithmeticSpec.wide_poly
            pre_ntt (col * KeygenM23MatrixSpec.poly_words_i)) /\
      KeygenM23MatrixSpec.word_tail_frame
        pre_ntt res.`1
          VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_words /\
      mat_firstcol_install_prefix res.`1 res.`2 mode2_vec_words /\
      mat_firstcol_install_frame
        preinstall_mat res.`2 mode2_vec_words /\
      VerifyUnpackV3MatrixProfilePostFreeze.verify_unpack_mode2_matrix_repr_bound20_17
        res.`2].
proof.
proc.
seq 1 :
  (exists pre_ntt preinstall_mat,
     bp = pre_ntt /\ vkp = vkp0 /\ matp = preinstall_mat /\
     VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
       vkp0 preinstall_mat pre_ntt mode2_vec_words /\
     mat_firstcol_frame mat0 preinstall_mat /\
     VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
       preinstall_mat /\
     VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
       pre_ntt
       (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
       (KeygenM23ArithmeticSpec.wide_poly
         pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
     VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_input_signed131068
       pre_ntt).
+ call
    (actual_verify_unpack_post_decode_pre_ntt_mode2_full_tight_input
       bp0 vkp0 mat0).
  auto => />.
  move=> result hprefix hframe hnonfirst hinput0 hinput1 hsigned.
  smt().
exlim bp => pre_ntt0.
exlim matp => preinstall_mat0.
call
  (VerifyUnpackV3NttInstallPostFreeze.actual_verify_unpack_ntt_install_mode2_full_correct_tight20
     pre_ntt0 preinstall_mat0
     (KeygenM23ArithmeticSpec.wide_poly pre_ntt0 0)
     (KeygenM23ArithmeticSpec.wide_poly
       pre_ntt0 KeygenM23MatrixSpec.poly_words_i)).
auto => />.
move=> &m hprefix hmatframe hnonfirst hinput0 hinput1 hsigned
        result htight hntt0 hntt0bound hntt1 hntt1bound
        hforward htail hinstall hinstallframe.
have hnttbound :
    VerifyUnpackV3NttTightBoundPostFreeze.verify_unpack_ntt_output_bound20
      result.`1 by
  exact htight.
have hmatrixprofile :=
  VerifyUnpackV3MatrixProfilePostFreeze.verify_unpack_mode2_matrix_repr_bound20_17_of_install
    result.`1 preinstall_mat0 result.`2
    hnonfirst hnttbound hinstall hinstallframe.
exists pre_ntt0 preinstall_mat0.
by auto.
qed.

end VerifyUnpackV3PostDecodeThroughNttPostFreeze.
