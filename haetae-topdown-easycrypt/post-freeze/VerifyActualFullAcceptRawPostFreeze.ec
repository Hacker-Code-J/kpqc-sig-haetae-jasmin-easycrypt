require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8 BArray1024 BArray2752 BArray2948
               BArray8192 BArray32768
               RawVerifyApiTarget
               Mode2HbzCodecSpec Mode2VerifyPrepareNorm
               Mode2VerifyRecover Mode2VerifyTailChallenge
               KeygenM23ArithmeticSpec KeygenM23MatrixSpec
               VerifyUnpackV3FullPostFreeze
               VerifyHbzRansSuccessCanonicalPostFreeze
               VerifySignatureUnpackRawBoundaryPostFreeze
               VerifyPrepareZ1RawBoundaryPostFreeze
               VerifyRecoverNormRawBoundaryPostFreeze
               VerifyTailRawBoundaryPostFreeze
               VerifyUnpackMatrixCrtRawCompositionPostFreeze
               VerifyUnpackPrepareMatrixCrtRawCompositionPostFreeze
               VerifyMatrixCrtPostFreeze VerifyMatrixCrtCompositionPostFreeze
               VerifySignatureUnpackPrepareMatrixCrtRawCompositionPostFreeze
               VerifySignatureUnpackPrepareMatrixCrtRecoverNormRawCompositionPostFreeze
               VerifySignatureUnpackPrepareMatrixCrtRecoverNormTailRawCompositionPostFreeze
               VerifyActualFullFunctionalRawPostFreeze
               VerifyMatrixCrtDirectRawPostFreeze.

import Mode2VerifyPrepareNorm Mode2VerifyRecover Mode2VerifyTailChallenge
       VerifySignatureUnpackRawBoundaryPostFreeze
       VerifyUnpackV3FullPostFreeze
       VerifyPrepareZ1RawBoundaryPostFreeze
       VerifyRecoverNormRawBoundaryPostFreeze
       VerifyTailRawBoundaryPostFreeze
       VerifyUnpackMatrixCrtRawCompositionPostFreeze
       VerifyUnpackPrepareMatrixCrtRawCompositionPostFreeze
       VerifyMatrixCrtPostFreeze VerifyMatrixCrtCompositionPostFreeze
       VerifySignatureUnpackPrepareMatrixCrtRawCompositionPostFreeze
       VerifySignatureUnpackPrepareMatrixCrtRecoverNormRawCompositionPostFreeze
       VerifySignatureUnpackPrepareMatrixCrtRecoverNormTailRawCompositionPostFreeze
       VerifyActualFullFunctionalRawPostFreeze
       VerifyMatrixCrtDirectRawPostFreeze.

theory VerifyActualFullAcceptRawPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Flat = VerifyFullMode2FlatTrace.

lemma raw_unpack_sig_full_mode2_verify_canonical_direct
    (cp0 : BArray1024.t) (low0 hbz0 : BArray8192.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t) :
  hoare [Raw._unpack_sig_full :
    cp = cp0 /\ lowp = low0 /\ hbzp = hbz0 /\
    badp = bad0 /\ sigp = sig0 /\
    lcount_i = 4 /\ hb_count_i = 1024 /\
    hb_m_i = 13 /\ hb_offset_i = 6
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res.`1 /\
    Mode2VerifyPrepareNorm.canonical_signed_low res.`2 /\
    (BArray8.get64 res.`5 0 = W64.zero =>
      Mode2VerifyPrepareNorm.canonical_hbz_mode2 res.`3 /\
      Mode2VerifyPrepareNorm.coeff_tail_frame
        hbz0 res.`3 Mode2HbzCodecSpec.mode2_hbz_count)].
proof.
conseq
  VerifySignatureUnpackRawBoundaryPostFreeze.raw_unpack_sig_full_equiv_focused
  (VerifyHbzRansSuccessCanonicalPostFreeze.unpack_sig_full_mode2_verify_canonical
    cp0 low0 hbz0 bad0 sig0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists
    (cp{1}, lowp{1}, hbzp{1}, hp{1}, badp{1}, sigp{1},
     h_symbolwp{1}, h_dsymswp{1}, hb_symbolwp{1}, hb_dsymswp{1},
     lcount_i{1}, hb_count_i{1}, hb_m_i{1}, hb_offset_i{1},
     h_count_i{1}, h_m_i{1}, h_offset_i{1},
     base_hb_i{1}, base_h_i{1}, payload_limit_i{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

lemma raw_verify_signature_unpack_prepare_matrix_crt_mode2_result_of_success
    (vkp0 : BArray2752.t)
    (z10 high0 : BArray8192.t) (wprime0 : BArray1024.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (prepared_z out_z out_high : BArray8192.t)
    (prepared_w : BArray1024.t) (total : W64.t) :
  (exists (outbp : BArray8192.t),
    VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
      vkp0 outbp outmat) =>
  Mode2VerifyPrepareNorm.canonical_challenge parsed_cp =>
  Mode2VerifyPrepareNorm.canonical_signed_low parsed_low =>
  Mode2VerifyPrepareNorm.canonical_hbz_mode2 parsed_high =>
  BArray8.get64 parsed_bad 0 = W64.zero =>
  verify_prepare_z1_prefix
    prepared_z parsed_high parsed_low low_words =>
  coeff_tail_frame z10 prepared_z low_words =>
  verify_mode2_input_repr_bound16
    prepared_z
    (KeygenM23ArithmeticSpec.wide_poly prepared_z 0)
    (KeygenM23ArithmeticSpec.wide_poly
      prepared_z KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      prepared_z (2 * KeygenM23MatrixSpec.poly_words_i))
    (KeygenM23ArithmeticSpec.wide_poly
      prepared_z (3 * KeygenM23MatrixSpec.poly_words_i)) =>
  verify_prepare_wprime_prefix
    prepared_w parsed_high parsed_low parsed_cp challenge_words =>
  wprime_tail_frame wprime0 prepared_w challenge_words =>
  total = verify_prepare_total_prefix
    parsed_high parsed_low low_words =>
  verify_matrix_crt_mode2_result
    prepared_z high0 outmat prepared_w out_z out_high =>
  raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
    vkp0 z10 high0 wprime0
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out_z out_high prepared_w total.
proof.
move=> [outbp htight] hcanonical_cp hcanonical_low hcanonical_high
  hbadzero hzprefix hzframe hinput hwprefix hwframe htotal hcrt.
rewrite /raw_verify_signature_unpack_prepare_matrix_crt_mode2_result.
exists outbp.
split; first exact htight.
split; first exact hcanonical_cp.
split; first exact hcanonical_low.
split.
+ move=> _.
  split; first exact hcanonical_high.
  rewrite
    /VerifyUnpackPrepareMatrixCrtRawCompositionPostFreeze.raw_verify_unpack_prepare_matrix_crt_mode2_result.
  exists outbp outmat prepared_z.
  split; first exact htight.
  split; first exact hzprefix.
  split; first exact hzframe.
  split; first exact hinput.
  split; first exact hwprefix.
  split; first exact hwframe.
  split; first exact htotal.
  exact hcrt.
+ move=> hbad.
  smt().
qed.

lemma raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result_of_success
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
  raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
    vkp0 z10 high0 wprime0
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total =>
  BArray8.get64 parsed_bad 0 = W64.zero =>
  Mode2VerifyRecover.recover_w_prefix
    w out parsed_h Mode2VerifyRecover.mode2_verify_recover_count =>
  Mode2VerifyRecover.recover_z2_prefix
    z2 out parsed_h outw Mode2VerifyRecover.mode2_verify_recover_count =>
  (reject = W64.zero <=>
    Mode2VerifyPrepareNorm.verify_norm_accepts_word z2 total) =>
  (reject = W64.one <=>
    W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_bound \ult
      Mode2VerifyPrepareNorm.verify_norm_total_word z2 total) =>
  raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
    vkp0 z10 high0 wprime0 wp0 z20
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total w z2 reject.
proof.
move=> hprefix hbadzero hw hz hnorm0 hnorm1.
rewrite
  /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result.
split; first exact hprefix.
split.
+ move=> _.
  split; first exact hw.
  split; first exact hz.
  split; first exact hnorm0.
  exact hnorm1.
+ move=> hbad.
  smt().
qed.

lemma raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result_of_success
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
  raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
    vkp0 z10 high0 wprime0 wp0 z20
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total w z2 norm_reject =>
  norm_reject = W64.zero =>
  (exists cprime,
    reject = Mode2VerifyTailChallenge.poly_mismatch_result_word
      (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
        parsed_cp cprime Mode2VerifyTailChallenge.mode2_challenge_words)) =>
  raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
    vkp0 z10 high0 wprime0 wp0 z20
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total w z2 norm_reject reject.
proof.
move=> hprefix hnormzero [cprime htail].
rewrite
  /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result.
split; first exact hprefix.
split.
+ move=> _.
  exists cprime.
  exact htail.
+ move=> hnotzero.
  smt().
qed.

lemma verify_full_mode2_flat_trace_accept_exact
    (sig0 : BArray2948.t)
    (vkp0 : BArray2752.t) (vku0 : int)
    (desc0 : BArray40.t) :
  hoare [Flat.run :
    sigp = sig0 /\ siglen = W64.of_int 1474 /\
    vkp = vkp0 /\ vku = vku0 /\ descp = desc0
    ==>
    res.`14 = W64.zero =>
    raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
      vkp0
      witness<:BArray8192.t> witness<:BArray8192.t>
      witness<:BArray1024.t>
      witness<:BArray8192.t> witness<:BArray8192.t>
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      res.`7 res.`8 res.`9 res.`10 res.`11 res.`12 res.`13 res.`14].
proof.
proc.
sp.
if.
+ auto => />.
+ sp 10.
  seq 1 :
    ((exists (outbp : BArray8192.t),
       VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
         vkp0 outbp a1p) /\
     verify_mode2_matrix_repr_bound20_17 a1p /\
     c = witness /\ lowz = witness /\ highz = witness /\
     bad = witness /\ sigp = sig0 /\
     z1 = witness /\ wprime = witness /\ highbits = witness /\
     w = witness /\ z2 = witness /\
     b2sq_i = 163265017 /\
     k_i = 2 /\ l_i = 4 /\
     hb_count_i = 1024 /\ hb_m_i = 13 /\ hb_offset_i = 6 /\
     h_count_i = 512 /\ h_m_i = 13 /\ h_offset_i = 239 /\
     base_hb_i = 132 /\ base_h_i = 7 /\ payload_limit_i = 416 /\
     highbits_len_i = 576 /\ vkbytes_i = 992 /\ tau_i = 58 /\
     k = W64.of_int 2 /\ l = W64.of_int 4).
  + call
      (raw_verify_unpack_mode2_tight20_matrix_crt_ready
        witness vkp0 vku0).
    auto => />; smt().
  seq 21 :
    ((exists (outbp : BArray8192.t),
       VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
         vkp0 outbp a1p) /\
     verify_mode2_matrix_repr_bound20_17 a1p /\
     Mode2VerifyPrepareNorm.canonical_challenge cp /\
     Mode2VerifyPrepareNorm.canonical_signed_low lowzp /\
     (BArray8.get64 badp 0 = W64.zero =>
       Mode2VerifyPrepareNorm.canonical_hbz_mode2 highzp) /\
     z1 = witness /\ wprime = witness /\ highbits = witness /\
     w = witness /\ z2 = witness /\
     b2sq_i = 163265017 /\
     k_i = 2 /\ l_i = 4 /\
     highbits_len_i = 576 /\ vkbytes_i = 992 /\ tau_i = 58 /\
     k = W64.of_int 2 /\ l = W64.of_int 4 /\
     sigp = sig0).
  + call
      (raw_unpack_sig_full_mode2_verify_canonical_direct
        witness witness witness
        (BArray8.set64 witness 0 W64.zero) sig0).
    auto => />; smt().
  sp 5.
  if.
  + auto => />; smt().
  + exlim a1p => unpacked0.
    exlim cp => parsed_cp0.
    exlim lowzp => parsed_low0.
    exlim highzp => parsed_high0.
    exlim hp => parsed_h0.
    exlim badp => parsed_bad0.
    seq 12 :
      (a1p = unpacked0 /\ cp = parsed_cp0 /\
       lowzp = parsed_low0 /\ highzp = parsed_high0 /\
       hp = parsed_h0 /\ badp = parsed_bad0 /\
       BArray8.get64 parsed_bad0 0 = W64.zero /\
       Mode2VerifyPrepareNorm.canonical_challenge parsed_cp0 /\
       Mode2VerifyPrepareNorm.canonical_signed_low parsed_low0 /\
       Mode2VerifyPrepareNorm.canonical_hbz_mode2 parsed_high0 /\
       (exists (outbp : BArray8192.t),
         VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
           vkp0 outbp unpacked0) /\
       verify_mode2_matrix_repr_bound20_17 unpacked0 /\
       verify_prepare_z1_prefix
         z1p parsed_high0 parsed_low0 low_words /\
       coeff_tail_frame witness z1p low_words /\
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
       wprime_tail_frame witness wprimep challenge_words /\
       sqnorm2 =
         verify_prepare_total_prefix parsed_high0 parsed_low0 low_words /\
       highbits = witness /\ w = witness /\ z2 = witness /\
       b2sq_i = 163265017 /\
       k_i = 2 /\ l_i = 4 /\
       highbits_len_i = 576 /\ vkbytes_i = 992 /\ tau_i = 58 /\
       k = W64.of_int 2 /\ l = W64.of_int 4).
    + call
        (raw_verify_prepare_z1_wprime_mode2_input_repr_bound16
          witness parsed_high0 parsed_low0 witness parsed_cp0).
      auto => />; smt().
    exlim z1p => prepared_z10.
    exlim wprimep => prepared_wprime0.
    exlim sqnorm2 => prepared_total0.
    seq 9 :
      (BArray8.get64 parsed_bad0 0 = W64.zero /\
       Mode2VerifyPrepareNorm.canonical_challenge parsed_cp0 /\
       Mode2VerifyPrepareNorm.canonical_signed_low parsed_low0 /\
       Mode2VerifyPrepareNorm.canonical_hbz_mode2 parsed_high0 /\
       (exists (outbp : BArray8192.t),
         VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
           vkp0 outbp unpacked0) /\
       verify_prepare_z1_prefix
         prepared_z10 parsed_high0 parsed_low0 low_words /\
       coeff_tail_frame witness prepared_z10 low_words /\
       verify_mode2_input_repr_bound16
         prepared_z10
         (KeygenM23ArithmeticSpec.wide_poly prepared_z10 0)
         (KeygenM23ArithmeticSpec.wide_poly
           prepared_z10 KeygenM23MatrixSpec.poly_words_i)
         (KeygenM23ArithmeticSpec.wide_poly
           prepared_z10 (2 * KeygenM23MatrixSpec.poly_words_i))
         (KeygenM23ArithmeticSpec.wide_poly
           prepared_z10 (3 * KeygenM23MatrixSpec.poly_words_i)) /\
       verify_prepare_wprime_prefix
         prepared_wprime0 parsed_high0 parsed_low0 parsed_cp0 challenge_words /\
       wprime_tail_frame witness prepared_wprime0 challenge_words /\
       prepared_total0 =
         verify_prepare_total_prefix parsed_high0 parsed_low0 low_words /\
       verify_matrix_crt_mode2_result
         prepared_z10 witness unpacked0 prepared_wprime0 z1p highbitsp /\
       a1p = unpacked0 /\ lowzp = parsed_low0 /\
       highzp = parsed_high0 /\ badp = parsed_bad0 /\
       sqnorm2 = prepared_total0 /\
       cp = parsed_cp0 /\ hp = parsed_h0 /\
       wprimep = prepared_wprime0 /\
       w = witness /\ z2 = witness /\
       k = W64.of_int 2 /\ b2sq_i = 163265017 /\
       k_i = 2 /\ highbits_len_i = 576 /\
       vkbytes_i = 992 /\ tau_i = 58).
    + call
        (raw_verify_matrix_crt_mode2_direct_fromcrt_freeze_mixed_exact
          prepared_z10 witness unpacked0 prepared_wprime0
          (KeygenM23ArithmeticSpec.wide_poly prepared_z10 0)
          (KeygenM23ArithmeticSpec.wide_poly
            prepared_z10 KeygenM23MatrixSpec.poly_words_i)
          (KeygenM23ArithmeticSpec.wide_poly
            prepared_z10 (2 * KeygenM23MatrixSpec.poly_words_i))
          (KeygenM23ArithmeticSpec.wide_poly
            prepared_z10 (3 * KeygenM23MatrixSpec.poly_words_i))).
      wp.
      auto => />.
    seq 0 :
      (raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
         vkp0 witness witness witness
         unpacked0 parsed_cp0 parsed_low0 parsed_high0 parsed_h0 parsed_bad0
         z1p highbitsp prepared_wprime0 prepared_total0 /\
       BArray8.get64 parsed_bad0 0 = W64.zero /\
       a1p = unpacked0 /\ lowzp = parsed_low0 /\
       highzp = parsed_high0 /\ badp = parsed_bad0 /\
       sqnorm2 = prepared_total0 /\
       cp = parsed_cp0 /\ hp = parsed_h0 /\
       wprimep = prepared_wprime0 /\
       w = witness /\ z2 = witness /\
       k = W64.of_int 2 /\ b2sq_i = 163265017 /\
       k_i = 2 /\ highbits_len_i = 576 /\
       vkbytes_i = 992 /\ tau_i = 58).
    + auto => &hr hpre.
      move: hpre => [hbadzero hpre].
      move: hpre => [hcanonical_cp hpre].
      move: hpre => [hcanonical_low hpre].
      move: hpre => [hcanonical_high hpre].
      move: hpre => [htight hpre].
      move: hpre => [hzprefix hpre].
      move: hpre => [hzframe hpre].
      move: hpre => [hinput hpre].
      move: hpre => [hwprefix hpre].
      move: hpre => [hwframe hpre].
      move: hpre => [htotal hpre].
      move: hpre => [hcrt hpre].
      split.
      + apply
          (raw_verify_signature_unpack_prepare_matrix_crt_mode2_result_of_success
            vkp0 witness witness witness unpacked0
            parsed_cp0 parsed_low0 parsed_high0 parsed_h0 parsed_bad0
            prepared_z10 z1p{hr} highbitsp{hr}
            prepared_wprime0 prepared_total0).
        + exact htight.
        + exact hcanonical_cp.
        + exact hcanonical_low.
        + exact hcanonical_high.
        + exact hbadzero.
        + exact hzprefix.
        + exact hzframe.
        + exact hinput.
        + exact hwprefix.
        + exact hwframe.
        + exact htotal.
        + exact hcrt.
      + split; first exact hbadzero.
        exact hpre.
    + exlim z1p => matrix_z10.
      exlim highbitsp => matrix_high0.
      seq 12 :
        (raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
           vkp0 witness witness witness
           unpacked0 parsed_cp0 parsed_low0 parsed_high0 parsed_h0 parsed_bad0
           matrix_z10 matrix_high0 prepared_wprime0 prepared_total0 /\
         BArray8.get64 parsed_bad0 0 = W64.zero /\
         Mode2VerifyRecover.recover_w_prefix
           wp_0 matrix_z10 parsed_h0
           Mode2VerifyRecover.mode2_verify_recover_count /\
         Mode2VerifyRecover.recover_z2_prefix
           z2p matrix_z10 parsed_h0 prepared_wprime0
           Mode2VerifyRecover.mode2_verify_recover_count /\
         a1p = unpacked0 /\ lowzp = parsed_low0 /\
         highzp = parsed_high0 /\ badp = parsed_bad0 /\
         z1p = matrix_z10 /\ highbitsp = matrix_high0 /\
         sqnorm2 = prepared_total0 /\
         cp = parsed_cp0 /\ hp = parsed_h0 /\
         wprimep = prepared_wprime0 /\
         kcount = W64.of_int 512 /\ b2sq_i = 163265017 /\
         k_i = 2 /\ highbits_len_i = 576 /\
         vkbytes_i = 992 /\ tau_i = 58).
      + call
          (raw_sign_verify_recover_w_z2_mode2_direct
            witness witness matrix_z10 parsed_h0 prepared_wprime0).
        wp.
        auto => />; smt().
      exlim wp_0 => recovered_w0.
      exlim z2p => recovered_z20.
      seq 7 :
        (raw_verify_signature_unpack_prepare_matrix_crt_mode2_result
           vkp0 witness witness witness
           unpacked0 parsed_cp0 parsed_low0 parsed_high0 parsed_h0 parsed_bad0
           matrix_z10 matrix_high0 prepared_wprime0 prepared_total0 /\
         BArray8.get64 parsed_bad0 0 = W64.zero /\
         Mode2VerifyRecover.recover_w_prefix
           recovered_w0 matrix_z10 parsed_h0
           Mode2VerifyRecover.mode2_verify_recover_count /\
         Mode2VerifyRecover.recover_z2_prefix
           recovered_z20 matrix_z10 parsed_h0 prepared_wprime0
           Mode2VerifyRecover.mode2_verify_recover_count /\
         (reject = W64.zero <=>
           Mode2VerifyPrepareNorm.verify_norm_accepts_word
             recovered_z20 prepared_total0) /\
         (reject = W64.one <=>
           W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_bound \ult
             Mode2VerifyPrepareNorm.verify_norm_total_word
               recovered_z20 prepared_total0) /\
         a1p = unpacked0 /\ lowzp = parsed_low0 /\
         highzp = parsed_high0 /\ badp = parsed_bad0 /\
         z1p = matrix_z10 /\ highbitsp = matrix_high0 /\
         sqnorm2 = prepared_total0 /\
         wp_0 = recovered_w0 /\ z2p = recovered_z20 /\
         cp = parsed_cp0 /\ hp = parsed_h0 /\
         wprimep = prepared_wprime0 /\
         k_i = 2 /\ highbits_len_i = 576 /\
         vkbytes_i = 992 /\ tau_i = 58).
      + call
          (raw_sign_verify_norm_reject_mode2_direct
            recovered_z20 prepared_total0).
        wp.
        auto => />; smt().
      seq 0 :
        (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
           vkp0 witness witness witness witness witness
           unpacked0 parsed_cp0 parsed_low0 parsed_high0 parsed_h0 parsed_bad0
           matrix_z10 matrix_high0 prepared_wprime0 prepared_total0
           recovered_w0 recovered_z20 reject /\
         a1p = unpacked0 /\ lowzp = parsed_low0 /\
         highzp = parsed_high0 /\ badp = parsed_bad0 /\
         z1p = matrix_z10 /\ highbitsp = matrix_high0 /\
         sqnorm2 = prepared_total0 /\
         wp_0 = recovered_w0 /\ z2p = recovered_z20 /\
         cp = parsed_cp0 /\ hp = parsed_h0 /\
         wprimep = prepared_wprime0 /\
         k_i = 2 /\ highbits_len_i = 576 /\
         vkbytes_i = 992 /\ tau_i = 58).
      + auto => &hr hpre.
        move: hpre => [hprefix hpre].
        move: hpre => [hbadzero hpre].
        move: hpre => [hw hpre].
        move: hpre => [hz hpre].
        move: hpre => [hnorm0 hpre].
        move: hpre => [hnorm1 hpre].
        split.
        + apply
            (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result_of_success
              vkp0 witness witness witness witness witness
              unpacked0 parsed_cp0 parsed_low0 parsed_high0 parsed_h0 parsed_bad0
              matrix_z10 matrix_high0 prepared_wprime0 prepared_total0
              recovered_w0 recovered_z20 reject{hr}).
          + exact hprefix.
          + exact hbadzero.
          + exact hw.
          + exact hz.
          + exact hnorm0.
          + exact hnorm1.
        + exact hpre.
      + exlim reject => norm_reject0.
        sp 3.
        if.
        + seq 7 :
            (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result
               vkp0 witness witness witness witness witness
               unpacked0 parsed_cp0 parsed_low0 parsed_high0
               parsed_h0 parsed_bad0 matrix_z10 matrix_high0
               prepared_wprime0 prepared_total0
               recovered_w0 recovered_z20 norm_reject0 /\
             norm_reject0 = W64.zero /\
             (exists cprime,
               reject = Mode2VerifyTailChallenge.poly_mismatch_result_word
                 (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
                   parsed_cp0 cprime
                   Mode2VerifyTailChallenge.mode2_challenge_words)) /\
             a1p = unpacked0 /\ lowzp = parsed_low0 /\
             highzp = parsed_high0 /\ badp = parsed_bad0 /\
             z1p = matrix_z10 /\ highbitsp = matrix_high0 /\
             sqnorm2 = prepared_total0 /\
             wp_0 = recovered_w0 /\ z2p = recovered_z20 /\
             cp = parsed_cp0 /\ hp = parsed_h0 /\
             wprimep = prepared_wprime0 /\
             norm_reject = norm_reject0).
          + call
              (raw_sign_verify_tail_m23_mismatch_word_exact parsed_cp0).
            wp.
            auto => />; smt().
          seq 0 :
            (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
               vkp0 witness witness witness witness witness
               unpacked0 parsed_cp0 parsed_low0 parsed_high0
               parsed_h0 parsed_bad0 matrix_z10 matrix_high0
               prepared_wprime0 prepared_total0
               recovered_w0 recovered_z20 norm_reject0 reject /\
             a1p = unpacked0 /\ lowzp = parsed_low0 /\
             highzp = parsed_high0 /\ badp = parsed_bad0 /\
             z1p = matrix_z10 /\ highbitsp = matrix_high0 /\
             sqnorm2 = prepared_total0 /\
             wp_0 = recovered_w0 /\ z2p = recovered_z20 /\
             cp = parsed_cp0 /\ hp = parsed_h0 /\
             wprimep = prepared_wprime0 /\
             norm_reject = norm_reject0).
          + auto => &hr hpre.
            move: hpre => [hrecover hpre].
            move: hpre => [hnormzero hpre].
            move: hpre => [htail hpre].
            split.
            + apply
                (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result_of_success
                  vkp0 witness witness witness witness witness
                  unpacked0 parsed_cp0 parsed_low0 parsed_high0
                  parsed_h0 parsed_bad0 matrix_z10 matrix_high0
                  prepared_wprime0 prepared_total0
                  recovered_w0 recovered_z20 norm_reject0 reject{hr}).
              + exact hrecover.
              + exact hnormzero.
              + exact htail.
            + exact hpre.
          + auto => />.
        + auto => />; smt().
qed.

lemma actual_verify_full_mode2_accept_exact_flat_trace
    (sig0 : BArray2948.t)
    (vkp0 : BArray2752.t) (vku0 : int)
    (desc0 : BArray40.t) :
  equiv [Raw._verify_full_mode2 ~ Flat.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp} /\
    sigp{2} = sig0 /\ siglen{2} = W64.of_int 1474 /\
    vkp{2} = vkp0 /\ vku{2} = vku0 /\ descp{2} = desc0
    ==>
    ={Glob.mem} /\ res{1} = res{2}.`14 /\
    (res{1} = W64.zero =>
      raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
        vkp0
        witness<:BArray8192.t> witness<:BArray8192.t>
        witness<:BArray1024.t>
        witness<:BArray8192.t> witness<:BArray8192.t>
        res{2}.`1 res{2}.`2 res{2}.`3 res{2}.`4 res{2}.`5 res{2}.`6
        res{2}.`7 res{2}.`8 res{2}.`9 res{2}.`10 res{2}.`11 res{2}.`12
        res{2}.`13 res{2}.`14)].
proof.
conseq actual_verify_full_mode2_exact_flat_trace
  (_ : true ==> true)
  (verify_full_mode2_flat_trace_accept_exact sig0 vkp0 vku0 desc0) => //=.
qed.

end VerifyActualFullAcceptRawPostFreeze.
