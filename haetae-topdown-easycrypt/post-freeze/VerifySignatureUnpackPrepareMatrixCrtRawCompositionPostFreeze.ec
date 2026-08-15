require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8 BArray1024 BArray2752 BArray2948 BArray8192
               BArray32768
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
               VerifyPrepareZ1RawBoundaryPostFreeze
               VerifyUnpackPrepareMatrixCrtRawCompositionPostFreeze
               VerifySignatureUnpackRawBoundaryPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.
import Mode2VerifyPrepareNorm.
import VerifyMatrixCrtPostFreeze VerifyMatrixCrtCompositionPostFreeze.

theory VerifySignatureUnpackPrepareMatrixCrtRawCompositionPostFreeze.

module Raw = RawVerifyApiTarget.M.
module RawSignature =
  VerifySignatureUnpackRawBoundaryPostFreeze.RawUnpackSignatureMode2.
module RawPrepare =
  VerifyPrepareZ1RawBoundaryPostFreeze.RawVerifyPrepareZ1WprimeMode2.
module RawMatrixCrt =
  VerifyMatrixCrtRawBoundaryPostFreeze.RawVerifyMatrixCrtMode2.

module RawVerifySignatureUnpackPrepareMatrixCrtMode2 = {
  proc run
      (matp : BArray32768.t, vkp : BArray2752.t, seedu : int,
       z1p highp lowzp highzp hp : BArray8192.t,
       wprimep cp : BArray1024.t,
       badp : BArray8.t, sigp : BArray2948.t)
      : BArray32768.t * BArray1024.t * BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8.t * BArray8192.t * BArray8192.t *
        BArray1024.t * W64.t = {
    var bad : W64.t;
    var total : W64.t;

    matp <@ Raw._unpack_vk_m23_full
      (matp, vkp, seedu,
       W64.of_int mode2_rows,
       W64.of_int mode2_cols,
       W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m);

    badp <- BArray8.set64 badp 0 W64.zero;
    (cp, lowzp, highzp, hp, badp) <@ RawSignature.run
      (cp, lowzp, highzp, hp, badp, sigp);

    bad <- BArray8.get64 badp 0;
    total <- W64.zero;
    if (bad = W64.zero) {
      (z1p, wprimep, total) <@ RawPrepare.run
        (z1p, highzp, lowzp, wprimep, cp);
      (z1p, highp) <@ RawMatrixCrt.run
        (z1p, highp, matp, wprimep);
    }

    return
      (matp, cp, lowzp, highzp, hp, badp,
       z1p, highp, wprimep, total);
  }
}.

op raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
    (vkp0 : BArray2752.t)
    (z10 high0 : BArray8192.t) (wprime0 : BArray1024.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t) : bool =
  exists outbp,
    VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
      vkp0 outbp outmat /\
    Mode2VerifyPrepareNorm.canonical_challenge parsed_cp /\
    Mode2VerifyPrepareNorm.canonical_signed_low parsed_low /\
    (BArray8.get64 parsed_bad 0 = W64.zero =>
      Mode2VerifyPrepareNorm.canonical_hbz_mode2 parsed_high /\
      VerifyUnpackPrepareMatrixCrtRawCompositionPostFreeze.raw_verify_unpack_prepare_matrix_crt_mode2_result
          vkp0 z10 high0 parsed_high parsed_low wprime0 parsed_cp
          out high outw total) /\
    (BArray8.get64 parsed_bad 0 <> W64.zero =>
      out = z10 /\ high = high0 /\ outw = wprime0 /\ total = W64.zero).

lemma raw_verify_signature_unpack_prepare_matrix_crt_mode2_tight20_exact
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0
    (z10 high0 lowz0 highz0 h0 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t) :
  hoare [RawVerifySignatureUnpackPrepareMatrixCrtMode2.run :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    z1p = z10 /\ highp = high0 /\
    lowzp = lowz0 /\ highzp = highz0 /\ hp = h0 /\
    wprimep = wprime0 /\ cp = cp0 /\
    badp = bad0 /\ sigp = sig0
    ==>
    raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
      vkp0 z10 high0 wprime0
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      res.`7 res.`8 res.`9 res.`10].
proof.
proc.
seq 1 :
  (z1p = z10 /\ highp = high0 /\
   lowzp = lowz0 /\ highzp = highz0 /\ hp = h0 /\
   wprimep = wprime0 /\ cp = cp0 /\
   badp = bad0 /\ sigp = sig0 /\
   (exists outbp,
     VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
       vkp0 outbp matp) /\
   verify_mode2_matrix_repr_bound20_17 matp).
+ call
    (VerifyUnpackMatrixCrtRawCompositionPostFreeze.raw_verify_unpack_mode2_tight20_matrix_crt_ready
      mat0 vkp0 seed0).
  auto => />.
seq 1 :
  (z1p = z10 /\ highp = high0 /\
   lowzp = lowz0 /\ highzp = highz0 /\ hp = h0 /\
   wprimep = wprime0 /\ cp = cp0 /\
   badp = BArray8.set64 bad0 0 W64.zero /\ sigp = sig0 /\
   (exists outbp,
     VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
       vkp0 outbp matp) /\
   verify_mode2_matrix_repr_bound20_17 matp).
+ auto.
seq 1 :
  (z1p = z10 /\ highp = high0 /\ wprimep = wprime0 /\
   Mode2VerifyPrepareNorm.canonical_challenge cp /\
   Mode2VerifyPrepareNorm.canonical_signed_low lowzp /\
   (BArray8.get64 badp 0 = W64.zero =>
      Mode2VerifyPrepareNorm.canonical_hbz_mode2 highzp) /\
   (exists outbp,
     VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
       vkp0 outbp matp) /\
   verify_mode2_matrix_repr_bound20_17 matp).
+ call
    (VerifySignatureUnpackRawBoundaryPostFreeze.raw_unpack_signature_mode2_verify_canonical
      cp0 lowz0 highz0 (BArray8.set64 bad0 0 W64.zero) sig0).
  auto => />; smt().
sp 2.
if.
+ exlim matp => unpacked0.
  exlim cp => parsed_cp0.
  exlim lowzp => parsed_low0.
  exlim highzp => parsed_high0.
  exlim hp => parsed_h0.
  exlim badp => parsed_bad0.
  seq 1 :
    (highp = high0 /\
     matp = unpacked0 /\ cp = parsed_cp0 /\
     lowzp = parsed_low0 /\ highzp = parsed_high0 /\
     hp = parsed_h0 /\ badp = parsed_bad0 /\
     BArray8.get64 parsed_bad0 0 = W64.zero /\
     Mode2VerifyPrepareNorm.canonical_challenge parsed_cp0 /\
     Mode2VerifyPrepareNorm.canonical_signed_low parsed_low0 /\
     Mode2VerifyPrepareNorm.canonical_hbz_mode2 parsed_high0 /\
     (exists outbp,
       VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
         vkp0 outbp unpacked0) /\
     verify_mode2_matrix_repr_bound20_17 unpacked0 /\
     verify_prepare_z1_prefix z1p parsed_high0 parsed_low0 low_words /\
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
     verify_prepare_wprime_prefix
       wprimep parsed_high0 parsed_low0 parsed_cp0 challenge_words /\
     wprime_tail_frame wprime0 wprimep challenge_words /\
     total =
       verify_prepare_total_prefix parsed_high0 parsed_low0 low_words).
  + call
      (VerifyPrepareZ1RawBoundaryPostFreeze.raw_verify_prepare_z1_wprime_mode2_wrapper_input_repr_bound16
        z10 parsed_high0 parsed_low0 wprime0 parsed_cp0).
    auto => />; smt().
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
    [hwprime_eq [hz1_eq
    [hhigh [hmat [hcp [hloweq [hhighzeq [hhpeq [hbadeq
    [hbadzero [hcanoncp [hcanonlow [hcanonhigh
    [hunpack [hmatrix [hzprefix [hzframe [hinput
    [hwprefix [hwframe htotal]]]]]]]]]]]]]]]]]]]].
  split.
  + split; first by rewrite hz1_eq.
    split; first exact hhigh.
    split; first by rewrite hmat.
    split; first by rewrite hwprime_eq.
    split; first by rewrite hz1_eq; exact hinput.
    exact hmatrix.
  move=> _ result hcrt.
  rewrite /raw_verify_signature_unpack_prepare_matrix_crt_mode2_result.
  move: hunpack => [outbp htight].
  exists outbp.
  split; first by rewrite hmat; exact htight.
  split; first by rewrite hcp; exact hcanoncp.
  split; first by rewrite hloweq; exact hcanonlow.
  split.
  + move=> _.
    split; first by rewrite hhighzeq; exact hcanonhigh.
    rewrite /VerifyUnpackPrepareMatrixCrtRawCompositionPostFreeze.raw_verify_unpack_prepare_matrix_crt_mode2_result.
    exists outbp unpacked0 prepared_z10.
    split; first exact htight.
    split; first by rewrite hz1_eq hhighzeq hloweq; exact hzprefix.
    split; first by rewrite hz1_eq; exact hzframe.
    split; first by rewrite hz1_eq; exact hinput.
    split; first by rewrite hhighzeq hloweq hcp; exact hwprefix.
    split; first exact hwframe.
    split; first by rewrite hhighzeq hloweq; exact htotal.
    rewrite -hwprime_eq.
    exact hcrt.
  move=> hbad.
  rewrite hbadeq in hbad.
  smt().
+ auto => &hr hpre.
  move: hpre =>
    [[hbad_eq [htotal [hz1 [hhigh [hwprime [hcanoncp [hcanonlow
      [hcanonhigh [hunpack hmatrix]]]]]]]]] hguard].
  rewrite /raw_verify_signature_unpack_prepare_matrix_crt_mode2_result.
  move: hunpack => [outbp htight].
  exists outbp.
  split; first exact htight.
  split; first exact hcanoncp.
  split; first exact hcanonlow.
  split.
  + move=> hsuccess.
    move: hguard hsuccess hbad_eq.
    smt().
  move=> _.
  split; first exact hz1.
  split; first exact hhigh.
  split; first exact hwprime.
  exact htotal.
qed.

end VerifySignatureUnpackPrepareMatrixCrtRawCompositionPostFreeze.
