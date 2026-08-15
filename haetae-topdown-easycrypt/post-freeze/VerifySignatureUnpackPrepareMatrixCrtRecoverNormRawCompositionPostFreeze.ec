require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8 BArray1024 BArray2752 BArray2948 BArray8192
               BArray32768
               Mode2VerifyRecover Mode2VerifyPrepareNorm
               VerifySignatureUnpackPrepareMatrixCrtRawCompositionPostFreeze
               VerifyRecoverNormRawBoundaryPostFreeze.

import VerifySignatureUnpackPrepareMatrixCrtRawCompositionPostFreeze
       VerifyRecoverNormRawBoundaryPostFreeze.

theory VerifySignatureUnpackPrepareMatrixCrtRecoverNormRawCompositionPostFreeze.

module Prefix = RawVerifySignatureUnpackPrepareMatrixCrtMode2.
module RawRecover = RawSignVerifyRecoverMode2.
module RawNorm = RawSignVerifyNormRejectMode2.

module RawVerifySignatureUnpackPrepareMatrixCrtRecoverNormMode2 = {
  proc run
      (matp : BArray32768.t, vkp : BArray2752.t, seedu : int,
       z1p highp lowzp highzp hp wp_0 z2p : BArray8192.t,
       wprimep cp : BArray1024.t,
       badp : BArray8.t, sigp : BArray2948.t)
      : BArray32768.t * BArray1024.t * BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8.t * BArray8192.t * BArray8192.t *
        BArray1024.t * W64.t * BArray8192.t * BArray8192.t * W64.t = {
    var bad : W64.t;
    var reject : W64.t;
    var total : W64.t;

    (matp, cp, lowzp, highzp, hp, badp,
     z1p, highp, wprimep, total) <@ Prefix.run
      (matp, vkp, seedu,
       z1p, highp, lowzp, highzp, hp,
       wprimep, cp, badp, sigp);

    bad <- BArray8.get64 badp 0;
    reject <- W64.one;
    if (bad = W64.zero) {
      (wp_0, z2p) <@ RawRecover.run
        (wp_0, z2p, z1p, hp, wprimep);
      reject <@ RawNorm.run (z2p, total);
    }

    return
      (matp, cp, lowzp, highzp, hp, badp,
       z1p, highp, wprimep, total, wp_0, z2p, reject);
  }
}.

op raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
    (vkp0 : BArray2752.t)
    (z10 high0 : BArray8192.t) (wprime0 : BArray1024.t)
    (wp0 z20 : BArray8192.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t)
    (w z2 : BArray8192.t) (reject : W64.t) : bool =
  raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
      vkp0 z10 high0 wprime0
      outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
      out high outw total /\
  (BArray8.get64 parsed_bad 0 = W64.zero =>
    Mode2VerifyRecover.recover_w_prefix
      w out parsed_h Mode2VerifyRecover.mode2_verify_recover_count /\
    Mode2VerifyRecover.recover_z2_prefix
      z2 out parsed_h outw Mode2VerifyRecover.mode2_verify_recover_count /\
    (reject = W64.zero <=>
      Mode2VerifyPrepareNorm.verify_norm_accepts_word z2 total) /\
    (reject = W64.one <=>
      W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_bound \ult
        Mode2VerifyPrepareNorm.verify_norm_total_word z2 total)) /\
  (BArray8.get64 parsed_bad 0 <> W64.zero =>
    w = wp0 /\ z2 = z20 /\ reject = W64.one).

lemma raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_result_accepts
    (vkp0 : BArray2752.t)
    (z10 high0 : BArray8192.t) (wprime0 : BArray1024.t)
    (wp0 z20 : BArray8192.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t)
    (w z2 : BArray8192.t) (reject : W64.t) :
  raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
    vkp0 z10 high0 wprime0 wp0 z20
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total w z2 reject =>
  reject = W64.zero =>
  BArray8.get64 parsed_bad 0 = W64.zero /\
  raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
    vkp0 z10 high0 wprime0
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total /\
  Mode2VerifyRecover.recover_w_prefix
    w out parsed_h Mode2VerifyRecover.mode2_verify_recover_count /\
  Mode2VerifyRecover.recover_z2_prefix
    z2 out parsed_h outw Mode2VerifyRecover.mode2_verify_recover_count /\
  Mode2VerifyPrepareNorm.verify_norm_accepts_word z2 total.
proof.
rewrite
  /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result.
move=> [hprefix [hsuccess hfailure]] hreject.
have hbadzero : BArray8.get64 parsed_bad 0 = W64.zero.
+ case (BArray8.get64 parsed_bad 0 = W64.zero) => hbad.
  + smt().
  + move: (hfailure hbad) hreject.
    rewrite /W64.zero /W64.one /=.
    smt().
move: (hsuccess hbadzero) => [hw [hz [hnorm _]]].
split; first exact hbadzero.
split; first exact hprefix.
split; first exact hw.
split; first exact hz.
smt().
qed.

lemma raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_exact
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0
    (z10 high0 lowz0 highz0 h0 wp0 z20 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t) :
  hoare [RawVerifySignatureUnpackPrepareMatrixCrtRecoverNormMode2.run :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    z1p = z10 /\ highp = high0 /\
    lowzp = lowz0 /\ highzp = highz0 /\ hp = h0 /\
    wp_0 = wp0 /\ z2p = z20 /\
    wprimep = wprime0 /\ cp = cp0 /\
    badp = bad0 /\ sigp = sig0
    ==>
    raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
      vkp0 z10 high0 wprime0 wp0 z20
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      res.`7 res.`8 res.`9 res.`10 res.`11 res.`12 res.`13].
proof.
proc.
seq 1 :
  (wp_0 = wp0 /\ z2p = z20 /\
   raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
       vkp0 z10 high0 wprime0
       matp cp lowzp highzp hp badp z1p highp wprimep total).
+ call
    (raw_verify_signature_unpack_prepare_matrix_crt_mode2_tight20_exact
      mat0 vkp0 seed0 z10 high0 lowz0 highz0 h0
      wprime0 cp0 bad0 sig0).
  auto.
sp 2.
if.
+ seq 1 :
    (raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
         vkp0 z10 high0 wprime0
         matp cp lowzp highzp hp badp z1p highp wprimep total /\
     BArray8.get64 badp 0 = W64.zero /\
     Mode2VerifyRecover.recover_w_prefix
       wp_0 z1p hp
       Mode2VerifyRecover.mode2_verify_recover_count /\
     Mode2VerifyRecover.recover_z2_prefix
       z2p z1p hp wprimep
       Mode2VerifyRecover.mode2_verify_recover_count).
  + exlim z1p => matrix_z10.
    exlim hp => parsed_h0.
    exlim wprimep => prepared_wprime0.
    exlim wp_0 => wp00.
    exlim z2p => z200.
    call
      (raw_sign_verify_recover_w_z2_mode2_word_semantics
        wp00 z200 matrix_z10 parsed_h0 prepared_wprime0).
    auto.
  seq 1 :
    (raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
       vkp0 z10 high0 wprime0
       matp cp lowzp highzp hp badp z1p highp wprimep total /\
     BArray8.get64 badp 0 = W64.zero /\
     Mode2VerifyRecover.recover_w_prefix
       wp_0 z1p hp Mode2VerifyRecover.mode2_verify_recover_count /\
     Mode2VerifyRecover.recover_z2_prefix
       z2p z1p hp wprimep Mode2VerifyRecover.mode2_verify_recover_count /\
     (reject = W64.zero <=>
       Mode2VerifyPrepareNorm.verify_norm_accepts_word z2p total) /\
     (reject = W64.one <=>
       W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_bound \ult
         Mode2VerifyPrepareNorm.verify_norm_total_word z2p total)).
  + exlim z2p => recovered_z20.
    exlim total => prepared_total0.
    call
      (raw_sign_verify_norm_reject_mode2_word_exact
        recovered_z20 prepared_total0).
    auto.
  auto => &hr hpre.
  move: hpre =>
    [hprefix [hbad [hw [hz [hnorm0 hnorm1]]]]].
  rewrite
    /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result.
  split; first exact hprefix.
  split.
  + move=> _.
    split; first exact hw.
    split; first exact hz.
    split; first exact hnorm0.
    exact hnorm1.
  move=> hnotbad.
  smt().
+ auto => &hr hpre.
  move: hpre =>
    [[hbad_read [hreject_one [hwp_frame [hz2_frame hprefix]]]] hguard].
  rewrite
    /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result.
  split; first exact hprefix.
  split.
  + move=> hzero.
    smt().
  move=> _.
  split; first exact hwp_frame.
  split; first exact hz2_frame.
  exact hreject_one.
qed.

end VerifySignatureUnpackPrepareMatrixCrtRecoverNormRawCompositionPostFreeze.
