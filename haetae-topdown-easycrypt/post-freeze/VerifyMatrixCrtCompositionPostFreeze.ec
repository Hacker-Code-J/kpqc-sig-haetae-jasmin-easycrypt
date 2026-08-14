require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.
require import VerifyCoreTarget.
require import KeygenM23MatrixSpec KeygenM23ArithmeticSpec.
require import Array256 Fq GFq Rq NTT_Fq NTTFullSpec NTTRowProductSpec.
require import VerifyMatrixCrtPostFreeze VerifyCrtFreezeMode2PostFreeze.

import VerifyMatrixCrtPostFreeze VerifyCrtFreezeMode2PostFreeze.

theory VerifyMatrixCrtCompositionPostFreeze.

module Verify = VerifyCoreTarget.M.
module NttAcc = VerifyMatrixCrtPostFreeze.ActualVerifyMatrixNttAccMode2.
module CrtFreeze = VerifyCrtFreezeMode2PostFreeze.ActualVerifyCrtFreezeMode2.

module ActualVerifyMatrixCrtMode2 = {
  proc run
      (z1p : BArray8192.t, highp : BArray8192.t,
       a1p : BArray32768.t, wprimep : BArray1024.t)
      : BArray8192.t * BArray8192.t = {
    (z1p, highp) <@ Verify._verify_matrix_crt
      (z1p, highp, a1p, wprimep,
       W64.of_int verify_mode2_rows_i,
       W64.of_int verify_mode2_cols_i);
    return (z1p, highp);
  }
}.

module SequentialVerifyMatrixCrtMode2 = {
  proc run
      (z1p : BArray8192.t, highp : BArray8192.t,
       a1p : BArray32768.t, wprimep : BArray1024.t)
      : BArray8192.t * BArray8192.t = {
    (z1p, highp) <@ NttAcc.run (z1p, highp, a1p);
    z1p <@ CrtFreeze.run (z1p, highp, wprimep);
    return (z1p, highp);
  }
}.

op verify_matrix_crt_mode2_result
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (out high : BArray8192.t) : bool =
  exists transformed,
    NTTRowProductSpec.vector_forward_repr
      verify_mode2_cols_i
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          transformed (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          z10 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      high 0 (verify_mode2_coefficient_row_product a10 z10 0) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      high KeygenM23MatrixSpec.poly_words_i
        (verify_mode2_coefficient_row_product a10 z10 1) 16 /\
    crt_freeze_prefix out high wprime0 mode2_active_words /\
    coeff_tail_frame transformed out mode2_active_words /\
    KeygenM23MatrixSpec.word_tail_frame
      z10 transformed verify_mode2_vec_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      z10 out verify_mode2_vec_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      high0 high verify_mode2_out_words_i.

lemma word_tail_frame_of_coeff_tail before after coeff_start word_start :
  coeff_start <= word_start =>
  coeff_tail_frame before after coeff_start =>
  KeygenM23MatrixSpec.word_tail_frame before after word_start.
proof.
rewrite /coeff_tail_frame /KeygenM23MatrixSpec.word_tail_frame.
move=> hstart h i hi.
apply h.
split; first smt().
move: hi.
rewrite /KeygenM23MatrixSpec.array_words_i /BArray8192.size /=.
smt().
qed.

lemma sequential_verify_matrix_crt_mode2_correct
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [SequentialVerifyMatrixCrtMode2.run :
    z1p = z10 /\ highp = high0 /\
    a1p = a10 /\ wprimep = wprime0 /\
    verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3 /\
    verify_mode2_matrix_repr_bound16 a10
    ==>
    verify_matrix_crt_mode2_result
      z10 high0 a10 wprime0 res.`1 res.`2].
proof.
proc.
seq 1 :
  (a1p = a10 /\ wprimep = wprime0 /\
   NTTRowProductSpec.vector_forward_repr
     verify_mode2_cols_i
     (fun col =>
       KeygenM23ArithmeticSpec.wide_poly
         z1p (col * KeygenM23MatrixSpec.poly_words_i))
     (fun col =>
       KeygenM23ArithmeticSpec.wide_poly
         z10 (col * KeygenM23MatrixSpec.poly_words_i)) /\
   KeygenM23ArithmeticSpec.wide_slice_repr_bound
     highp 0 (verify_mode2_coefficient_row_product a10 z10 0) 16 /\
   KeygenM23ArithmeticSpec.wide_slice_repr_bound
     highp KeygenM23MatrixSpec.poly_words_i
       (verify_mode2_coefficient_row_product a10 z10 1) 16 /\
   KeygenM23MatrixSpec.word_tail_frame
     z10 z1p verify_mode2_vec_words_i /\
   KeygenM23MatrixSpec.word_tail_frame
     high0 highp verify_mode2_out_words_i).
+ call
    (verify_matrix_ntt_acc_mode2_cols4_correct
      z10 high0 a10 p0 p1 p2 p3).
  auto => />.
exlim z1p => transformed.
exlim highp => coefficient.
call
  (verify_crt_freeze_mode2_word_exact
    transformed coefficient wprime0).
auto => />.
move=> hforward hrow0_eq hrow0_bound hrow1_eq hrow1_bound
        htail_ntt htail_high
        result hcrt htail_crt.
have hrow0 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      coefficient 0
        (verify_mode2_coefficient_row_product a10 z10 0) 16.
+ rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  split; first exact hrow0_eq.
  exact hrow0_bound.
have hrow1 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      coefficient KeygenM23MatrixSpec.poly_words_i
        (verify_mode2_coefficient_row_product a10 z10 1) 16.
+ rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  split; first exact hrow1_eq.
  exact hrow1_bound.
have htail_crt_words :
    KeygenM23MatrixSpec.word_tail_frame
      transformed result verify_mode2_vec_words_i.
+ apply
    (word_tail_frame_of_coeff_tail
      transformed result mode2_active_words verify_mode2_vec_words_i).
  + rewrite /mode2_active_words /verify_mode2_vec_words_i
            /verify_mode2_cols_i /KeygenM23MatrixSpec.poly_words_i.
    trivial.
  exact htail_crt.
have htail_result :
    KeygenM23MatrixSpec.word_tail_frame
      z10 result verify_mode2_vec_words_i.
+ exact
    (KeygenM23MatrixSpec.word_tail_frame_trans
      z10 transformed result verify_mode2_vec_words_i
      htail_ntt htail_crt_words).
rewrite /verify_matrix_crt_mode2_result.
exists transformed.
split; first exact hforward.
split; first exact hrow0.
split; first exact hrow1.
split; first exact hcrt.
split; first exact htail_crt.
split; first exact htail_ntt.
split; first exact htail_result.
exact htail_high.
qed.

lemma actual_verify_matrix_crt_mode2_equiv_sequential :
  equiv [ActualVerifyMatrixCrtMode2.run ~
         SequentialVerifyMatrixCrtMode2.run :
    ={z1p, highp, a1p, wprimep} ==> ={res}].
proof.
proc.
inline Verify._verify_matrix_crt NttAcc.run CrtFreeze.run.
wp.
call (: ={vp, count} ==> ={res}).
+ by sim.
wp.
call (: ={wp_0, up, vp, count} ==> ={res}).
+ by sim.
wp.
call (: ={xp, count} ==> ={res}).
+ by sim.
wp.
call (: ={tp, mp, vp, rows, cols} ==> ={res}).
+ by sim.
wp.
call (: ={xp, count} ==> ={res}).
+ by sim.
auto => />.
qed.

lemma verify_matrix_crt_mode2_fromcrt_freeze_exact
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [ActualVerifyMatrixCrtMode2.run :
    z1p = z10 /\ highp = high0 /\
    a1p = a10 /\ wprimep = wprime0 /\
    verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3 /\
    verify_mode2_matrix_repr_bound16 a10
    ==>
    verify_matrix_crt_mode2_result
      z10 high0 a10 wprime0 res.`1 res.`2].
proof.
by conseq actual_verify_matrix_crt_mode2_equiv_sequential
  (sequential_verify_matrix_crt_mode2_correct
    z10 high0 a10 wprime0 p0 p1 p2 p3) => /#.
qed.

end VerifyMatrixCrtCompositionPostFreeze.
