require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 BArray2752 BArray8192 BArray32768
               RawVerifyApiTarget
               KeygenM23ArithmeticSpec KeygenM23MatrixSpec
               Mode2VerifyPrepareNorm
               VerifyUnpackV3AssemblyPostFreeze
               VerifyUnpackV3ExpandBoundsPostFreeze
               VerifyUnpackV3FullPostFreeze
               VerifyUnpackV3RawBoundaryPostFreeze
               VerifyMatrixCrtPostFreeze
               VerifyMatrixCrtCompositionPostFreeze
               VerifyMatrixCrtRawBoundaryPostFreeze
               VerifyUnpackMatrixCrtRawCompositionPostFreeze
               VerifyPrepareZ1RawBoundaryPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.
import Mode2VerifyPrepareNorm.
import VerifyMatrixCrtPostFreeze VerifyMatrixCrtCompositionPostFreeze.

theory VerifyUnpackPrepareMatrixCrtRawCompositionPostFreeze.

module Raw = RawVerifyApiTarget.M.
module RawPrepare =
  VerifyPrepareZ1RawBoundaryPostFreeze.RawVerifyPrepareZ1WprimeMode2.
module RawMatrixCrt =
  VerifyMatrixCrtRawBoundaryPostFreeze.RawVerifyMatrixCrtMode2.

module RawVerifyUnpackPrepareMatrixCrtMode2 = {
  proc run
      (matp : BArray32768.t, vkp : BArray2752.t, seedu : int,
       z1p highp highzp lowzp : BArray8192.t,
       wprimep cp : BArray1024.t)
      : BArray8192.t * BArray8192.t * BArray1024.t * W64.t = {
    var total : W64.t;
    matp <@ Raw._unpack_vk_m23_full
      (matp, vkp, seedu,
       W64.of_int mode2_rows,
       W64.of_int mode2_cols,
       W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m);
    (z1p, wprimep, total) <@ RawPrepare.run
      (z1p, highzp, lowzp, wprimep, cp);
    (z1p, highp) <@ RawMatrixCrt.run
      (z1p, highp, matp, wprimep);
    return (z1p, highp, wprimep, total);
  }
}.

op raw_verify_unpack_prepare_matrix_crt_mode2_result
    (vkp0 : BArray2752.t)
    (z10 high0 highz0 lowz0 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t) : bool =
  exists outbp outmat prepared_z1,
    VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
      vkp0 outbp outmat /\
    verify_prepare_z1_prefix prepared_z1 highz0 lowz0 low_words /\
    coeff_tail_frame z10 prepared_z1 low_words /\
    verify_mode2_input_repr_bound16
      prepared_z1
      (KeygenM23ArithmeticSpec.wide_poly prepared_z1 0)
      (KeygenM23ArithmeticSpec.wide_poly
        prepared_z1 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        prepared_z1 (2 * KeygenM23MatrixSpec.poly_words_i))
      (KeygenM23ArithmeticSpec.wide_poly
        prepared_z1 (3 * KeygenM23MatrixSpec.poly_words_i)) /\
    verify_prepare_wprime_prefix outw highz0 lowz0 cp0 challenge_words /\
    wprime_tail_frame wprime0 outw challenge_words /\
    total = verify_prepare_total_prefix highz0 lowz0 low_words /\
    verify_matrix_crt_mode2_result
      prepared_z1 high0 outmat outw out high.

lemma raw_verify_unpack_prepare_matrix_crt_mode2_tight20_exact
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0
    (z10 high0 highz0 lowz0 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t) :
  hoare [RawVerifyUnpackPrepareMatrixCrtMode2.run :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    z1p = z10 /\ highp = high0 /\
    highzp = highz0 /\ lowzp = lowz0 /\
    wprimep = wprime0 /\ cp = cp0 /\
    canonical_hbz_mode2 highz0 /\ canonical_signed_low lowz0
    ==>
    raw_verify_unpack_prepare_matrix_crt_mode2_result
      vkp0 z10 high0 highz0 lowz0 wprime0 cp0
      res.`1 res.`2 res.`3 res.`4].
proof.
proc.
seq 1 :
  (z1p = z10 /\ highp = high0 /\
   highzp = highz0 /\ lowzp = lowz0 /\
   wprimep = wprime0 /\ cp = cp0 /\
   canonical_hbz_mode2 highz0 /\ canonical_signed_low lowz0 /\
   (exists outbp,
     VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
       vkp0 outbp matp) /\
   verify_mode2_matrix_repr_bound20_17 matp).
+ call
    (VerifyUnpackMatrixCrtRawCompositionPostFreeze.raw_verify_unpack_mode2_tight20_matrix_crt_ready
      mat0 vkp0 seed0).
  auto => />.
seq 1 :
  (highp = high0 /\
   highzp = highz0 /\ lowzp = lowz0 /\ cp = cp0 /\
   canonical_hbz_mode2 highz0 /\ canonical_signed_low lowz0 /\
   (exists outbp,
     VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
       vkp0 outbp matp) /\
   verify_mode2_matrix_repr_bound20_17 matp /\
   verify_prepare_z1_prefix z1p highz0 lowz0 low_words /\
   coeff_tail_frame z10 z1p low_words /\
   verify_mode2_input_repr_bound16
     z1p
     (KeygenM23ArithmeticSpec.wide_poly z1p 0)
     (KeygenM23ArithmeticSpec.wide_poly
       z1p KeygenM23MatrixSpec.poly_words_i)
     (KeygenM23ArithmeticSpec.wide_poly
       z1p (2 * KeygenM23MatrixSpec.poly_words_i))
     (KeygenM23ArithmeticSpec.wide_poly
       z1p (3 * KeygenM23MatrixSpec.poly_words_i)) /\
   verify_prepare_wprime_prefix wprimep highz0 lowz0 cp0 challenge_words /\
   wprime_tail_frame wprime0 wprimep challenge_words /\
   total = verify_prepare_total_prefix highz0 lowz0 low_words).
+ call
    (VerifyPrepareZ1RawBoundaryPostFreeze.raw_verify_prepare_z1_wprime_mode2_wrapper_input_repr_bound16
      z10 highz0 lowz0 wprime0 cp0).
  auto => />.
exlim matp => unpacked0.
exlim z1p => prepared_z10.
exlim wprimep => prepared_wprime0.
call
  (VerifyMatrixCrtRawBoundaryPostFreeze.raw_verify_matrix_crt_mode2_fromcrt_freeze_mixed_exact
    prepared_z10 high0 unpacked0 prepared_wprime0
    (KeygenM23ArithmeticSpec.wide_poly prepared_z10 0)
    (KeygenM23ArithmeticSpec.wide_poly
      prepared_z10 KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      prepared_z10 (2 * KeygenM23MatrixSpec.poly_words_i))
    (KeygenM23ArithmeticSpec.wide_poly
      prepared_z10 (3 * KeygenM23MatrixSpec.poly_words_i))).
auto.
move=> &hr
  [hwprime_eq [hz1_eq [hmat_eq
  [hhigh [hhighz [hlowz [hcp [hcanon_high [hcanon_low
   [hunpack [hmatrix [hzprefix [hzframe [hinput
   [hwprefix [hwframe htotal]]]]]]]]]]]]]]]].
split.
+ split; first by rewrite hz1_eq.
  split; first exact hhigh.
  split; first by rewrite hmat_eq.
  split; first by rewrite hwprime_eq.
  split; first by rewrite hz1_eq; exact hinput.
  rewrite hmat_eq.
  exact hmatrix.
move=> _ result hcrt.
rewrite /raw_verify_unpack_prepare_matrix_crt_mode2_result.
move: hunpack => [outbp htight].
exists outbp unpacked0 prepared_z10.
split; first by rewrite hmat_eq; exact htight.
split; first by rewrite hz1_eq; exact hzprefix.
split; first by rewrite hz1_eq; exact hzframe.
split; first by rewrite hz1_eq; exact hinput.
split; first exact hwprefix.
split; first exact hwframe.
split; first exact htotal.
rewrite -hwprime_eq.
exact hcrt.
qed.

end VerifyUnpackPrepareMatrixCrtRawCompositionPostFreeze.
