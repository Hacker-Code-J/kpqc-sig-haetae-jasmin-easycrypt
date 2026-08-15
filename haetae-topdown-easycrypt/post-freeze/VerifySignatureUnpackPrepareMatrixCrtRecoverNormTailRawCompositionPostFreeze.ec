require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8 BArray40 BArray1024 BArray2752 BArray2948
               BArray8192 BArray32768
               Mode2VerifyRecover Mode2VerifyPrepareNorm
               Mode2VerifyTailChallenge
               VerifySignatureUnpackPrepareMatrixCrtRawCompositionPostFreeze
               VerifySignatureUnpackPrepareMatrixCrtRecoverNormRawCompositionPostFreeze
               VerifyTailRawBoundaryPostFreeze
               VerifyActualAcceptChallengeEqualityRawPostFreeze.

import VerifySignatureUnpackPrepareMatrixCrtRawCompositionPostFreeze
       VerifySignatureUnpackPrepareMatrixCrtRecoverNormRawCompositionPostFreeze
       VerifyTailRawBoundaryPostFreeze
       VerifyActualAcceptChallengeEqualityRawPostFreeze.

theory VerifySignatureUnpackPrepareMatrixCrtRecoverNormTailRawCompositionPostFreeze.

module Prefix =
  RawVerifySignatureUnpackPrepareMatrixCrtRecoverNormMode2.
module RawTail = RawSignVerifyTailMode2.

module RawVerifySignatureUnpackPrepareMatrixCrtRecoverNormTailMode2 = {
  proc run
      (matp : BArray32768.t, vkp : BArray2752.t, seedu : int,
       z1p highp lowzp highzp hp wp_0 z2p : BArray8192.t,
       wprimep cp : BArray1024.t,
       badp : BArray8.t, sigp : BArray2948.t, descp : BArray40.t)
      : BArray32768.t * BArray1024.t * BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8.t * BArray8192.t * BArray8192.t *
        BArray1024.t * W64.t * BArray8192.t * BArray8192.t * W64.t *
        W64.t = {
    var norm_reject : W64.t;
    var reject : W64.t;
    var total : W64.t;

    (matp, cp, lowzp, highzp, hp, badp,
     z1p, highp, wprimep, total, wp_0, z2p, norm_reject) <@ Prefix.run
      (matp, vkp, seedu,
       z1p, highp, lowzp, highzp, hp,
       wp_0, z2p, wprimep, cp, badp, sigp);

    reject <- norm_reject;
    if (norm_reject = W64.zero) {
      reject <@ RawTail.run (wp_0, wprimep, cp, descp);
    }

    return
      (matp, cp, lowzp, highzp, hp, badp,
       z1p, highp, wprimep, total, wp_0, z2p, norm_reject, reject);
  }
}.

op raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
    (vkp0 : BArray2752.t)
    (z10 high0 : BArray8192.t) (wprime0 : BArray1024.t)
    (wp0 z20 : BArray8192.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t)
    (w z2 : BArray8192.t) (norm_reject reject : W64.t) : bool =
  raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
      vkp0 z10 high0 wprime0 wp0 z20
      outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
      out high outw total w z2 norm_reject /\
  (norm_reject = W64.zero =>
    exists cprime,
      reject = Mode2VerifyTailChallenge.poly_mismatch_result_word
        (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
          parsed_cp cprime Mode2VerifyTailChallenge.mode2_challenge_words)) /\
  (norm_reject <> W64.zero => reject = norm_reject).

lemma raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_result_accepts
    (vkp0 : BArray2752.t)
    (z10 high0 : BArray8192.t) (wprime0 : BArray1024.t)
    (wp0 z20 : BArray8192.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t)
    (w z2 : BArray8192.t) (norm_reject reject : W64.t) :
  raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
    vkp0 z10 high0 wprime0 wp0 z20
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total w z2 norm_reject reject =>
  reject = W64.zero =>
  norm_reject = W64.zero /\
  BArray8.get64 parsed_bad 0 = W64.zero /\
  raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
    vkp0 z10 high0 wprime0
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total /\
  Mode2VerifyRecover.recover_w_prefix
    w out parsed_h Mode2VerifyRecover.mode2_verify_recover_count /\
  Mode2VerifyRecover.recover_z2_prefix
    z2 out parsed_h outw Mode2VerifyRecover.mode2_verify_recover_count /\
  Mode2VerifyPrepareNorm.verify_norm_accepts_word z2 total /\
  exists cprime,
    Mode2VerifyTailChallenge.poly_mismatch_result_word
      (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
        parsed_cp cprime Mode2VerifyTailChallenge.mode2_challenge_words) =
      W64.zero /\
    Mode2VerifyPrepareNorm.canonical_challenge cprime /\
    forall i,
      0 <= i < Mode2VerifyTailChallenge.mode2_challenge_words =>
      BArray1024.get32 parsed_cp i = BArray1024.get32 cprime i.
proof.
rewrite
  /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result.
move=> [hprefix [htail hframe]] hreject.
have hnormzero : norm_reject = W64.zero.
+ case (norm_reject = W64.zero) => hnorm.
  + smt().
  + move: (hframe hnorm) hreject.
    smt().
move:
  (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_result_accepts
    vkp0 z10 high0 wprime0 wp0 z20
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total w z2 norm_reject
    hprefix hnormzero) => [hbad [hraw [hw [hz hnorm]]]].
move: (htail hnormzero) => [cprime hmismatch].
split; first exact hnormzero.
split; first exact hbad.
split; first exact hraw.
split; first exact hw.
split; first exact hz.
split; first exact hnorm.
exists cprime.
have hmismatch_zero :
    Mode2VerifyTailChallenge.poly_mismatch_result_word
      (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
        parsed_cp cprime Mode2VerifyTailChallenge.mode2_challenge_words) =
      W64.zero.
+ rewrite -hmismatch.
  exact hreject.
have hequal :
    forall i,
      0 <= i < Mode2VerifyTailChallenge.mode2_challenge_words =>
      BArray1024.get32 parsed_cp i = BArray1024.get32 cprime i.
+ apply
    (poly_mismatch_result_zero_words_equal
      parsed_cp cprime Mode2VerifyTailChallenge.mode2_challenge_words).
  + by rewrite /Mode2VerifyTailChallenge.mode2_challenge_words.
  + exact hmismatch_zero.
have hcanonical_parsed :
    Mode2VerifyPrepareNorm.canonical_challenge parsed_cp.
+ move: hraw.
  rewrite
    /raw_verify_signature_unpack_prepare_matrix_crt_mode2_result.
  move=> [outbp [_ [hcanonical _]]].
  exact hcanonical.
have hcanonical_cprime :
    Mode2VerifyPrepareNorm.canonical_challenge cprime.
+ apply
    (canonical_challenge_of_word_equal parsed_cp cprime).
  + exact hcanonical_parsed.
  + exact hequal.
split; first exact hmismatch_zero.
split; first exact hcanonical_cprime.
exact hequal.
qed.

lemma raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_exact
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0
    (z10 high0 lowz0 highz0 h0 wp0 z20 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t)
    (desc0 : BArray40.t) :
  hoare [RawVerifySignatureUnpackPrepareMatrixCrtRecoverNormTailMode2.run :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    z1p = z10 /\ highp = high0 /\
    lowzp = lowz0 /\ highzp = highz0 /\ hp = h0 /\
    wp_0 = wp0 /\ z2p = z20 /\
    wprimep = wprime0 /\ cp = cp0 /\
    badp = bad0 /\ sigp = sig0 /\ descp = desc0
    ==>
    raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
      vkp0 z10 high0 wprime0 wp0 z20
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      res.`7 res.`8 res.`9 res.`10 res.`11 res.`12 res.`13 res.`14].
proof.
proc.
seq 1 :
  (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
    vkp0 z10 high0 wprime0 wp0 z20
    matp cp lowzp highzp hp badp
    z1p highp wprimep total wp_0 z2p norm_reject).
+ call
    (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_exact
      mat0 vkp0 seed0 z10 high0 lowz0 highz0 h0
      wp0 z20 wprime0 cp0 bad0 sig0).
  auto.
sp 1.
if.
+ exlim cp => parsed_cp0.
  call (raw_sign_verify_tail_mode2_mismatch_word_exact parsed_cp0).
  auto.
  move=> &hr [hcp [[hreject hprefix] hzero]].
  rewrite
    /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
    -hcp /=.
  move=> result [cprime hmismatch].
  rewrite -hcp in hprefix.
  split; first exact hprefix.
  split.
  + move=> _.
    exists cprime.
    exact hmismatch.
  + move=> hnotzero.
    smt().
+ auto.
  move=> &hr [[hreject hprefix] hnotzero].
  rewrite
    /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result.
  split; first exact hprefix.
  split.
  + move=> hzero.
    smt().
  + move=> _.
    exact hreject.
qed.

lemma raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_accept_sound
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0
    (z10 high0 lowz0 highz0 h0 wp0 z20 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t)
    (desc0 : BArray40.t) :
  hoare [RawVerifySignatureUnpackPrepareMatrixCrtRecoverNormTailMode2.run :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    z1p = z10 /\ highp = high0 /\
    lowzp = lowz0 /\ highzp = highz0 /\ hp = h0 /\
    wp_0 = wp0 /\ z2p = z20 /\
    wprimep = wprime0 /\ cp = cp0 /\
    badp = bad0 /\ sigp = sig0 /\ descp = desc0
    ==>
    res.`14 = W64.zero =>
    res.`13 = W64.zero /\
    BArray8.get64 res.`6 0 = W64.zero /\
    raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
      vkp0 z10 high0 wprime0
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      res.`7 res.`8 res.`9 res.`10 /\
    Mode2VerifyRecover.recover_w_prefix
      res.`11 res.`7 res.`5 Mode2VerifyRecover.mode2_verify_recover_count /\
    Mode2VerifyRecover.recover_z2_prefix
      res.`12 res.`7 res.`5 res.`9
      Mode2VerifyRecover.mode2_verify_recover_count /\
    Mode2VerifyPrepareNorm.verify_norm_accepts_word res.`12 res.`10 /\
    exists cprime,
      Mode2VerifyTailChallenge.poly_mismatch_result_word
        (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
          res.`2 cprime Mode2VerifyTailChallenge.mode2_challenge_words) =
        W64.zero /\
      Mode2VerifyPrepareNorm.canonical_challenge cprime /\
      forall i,
        0 <= i < Mode2VerifyTailChallenge.mode2_challenge_words =>
        BArray1024.get32 res.`2 i = BArray1024.get32 cprime i].
proof.
have hexact :=
  raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_exact
    mat0 vkp0 seed0 z10 high0 lowz0 highz0 h0
    wp0 z20 wprime0 cp0 bad0 sig0 desc0.
conseq hexact => //=.
move=> &m _ result hresult hreject.
exact
  (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_result_accepts
    vkp0 z10 high0 wprime0 wp0 z20
    result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
    result.`7 result.`8 result.`9 result.`10 result.`11 result.`12
    result.`13 result.`14 hresult hreject).
qed.

end VerifySignatureUnpackPrepareMatrixCrtRecoverNormTailRawCompositionPostFreeze.
