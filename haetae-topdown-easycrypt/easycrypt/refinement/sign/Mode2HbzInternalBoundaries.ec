require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  HbzFullEncodeTarget HbzFullDecodeTarget
  HbzPrepareTarget HbzApplyTarget
  RansEncodeTarget RansDecodeTarget
  Mode2HbzCodecSpec
  Mode2HbzPrepare Mode2HbzApply
  Mode2RansEncodeRefinement
  Mode2RansByteStack
  Mode2RansArrayListBridge
  Mode2RansEncoderOuterRefinement
  Mode2RansDecoderCursor
  Mode2RansDecoderActualTrace
  Mode2RansDecoderTopHoare.

theory Mode2HbzInternalBoundaries.

import Mode2HbzCodecSpec
       Mode2HbzPrepare Mode2HbzApply
       Mode2RansEncodeRefinement
       Mode2RansByteStack
       Mode2RansArrayListBridge
       Mode2RansEncoderOuterRefinement
       Mode2RansDecoderCursor
       Mode2RansDecoderActualTrace
       Mode2RansDecoderTopHoare.

module FullEncode = HbzFullEncodeTarget.M.
module FullDecode = HbzFullDecodeTarget.M.
module PrepareTarget = HbzPrepareTarget.M.
module ApplyTarget = HbzApplyTarget.M.
module EncodeTarget = RansEncodeTarget.M.
module DecodeTarget = RansDecodeTarget.M.

lemma full_encode_prepare_exact_focused :
  equiv [FullEncode._encode_hb_z1_prepare ~ PrepareTarget._encode_hb_z1_prepare :
    ={symsp, badp, hp, count, mhb, offset}
    ==>
    ={res}].
proof.
proc; sim.
qed.

lemma full_rans_encode_exact_focused :
  equiv [FullEncode._rans_encode ~ EncodeTarget._rans_encode :
    ={encp, statep, symsp, esymsp, count}
    ==>
    ={res}].
proof.
proc; sim.
qed.

lemma full_rans_decode_exact_focused :
  equiv [FullDecode._rans_decode ~ DecodeTarget._rans_decode :
    ={symsp, statep, bufp, symbolwp, dsymswp}
    ==>
    ={res}].
proof.
proc; sim.
qed.

lemma full_decode_apply_exact_focused :
  equiv [FullDecode._decode_hb_z1_apply ~ ApplyTarget._decode_hb_z1_apply :
    ={hp, symsp, count, offset}
    ==>
    ={res}].
proof.
proc; sim.
qed.

lemma prepared_hbz_implies_mode2_symbol_stream
    (symbols : BArray2048.t)
    (hbz : BArray8192.t) :
  canonical_hbz_mode2 hbz /\
  prepared_hbz_prefix symbols hbz mode2_hbz_count =>
  mode2_hbz_symbol_stream symbols.
proof.
move=> [hcanon hprepared].
rewrite /mode2_hbz_symbol_stream => i hi.
have hcanon_i :
    -mode2_hbz_offset <= W32.to_sint (BArray8192.get32 hbz i) <
    mode2_hbz_alphabet - mode2_hbz_offset.
+ rewrite /canonical_hbz_mode2 in hcanon.
  exact (hcanon i hi).
have hsym :
    BArray2048.get8 symbols i =
    hbz_symbol_word (BArray8192.get32 hbz i).
+ rewrite /prepared_hbz_prefix in hprepared.
  exact (hprepared i hi).
rewrite hsym (hbz_symbol_word_uint _ hcanon_i).
exact (canonical_hbz_symbol_bounds hbz i hcanon hi).
qed.

lemma decoded_prefix_preserves_prepared_hbz
    (decoded expected : BArray2048.t)
    (hbz : BArray8192.t) :
  prepared_hbz_prefix expected hbz mode2_hbz_count /\
  decoded_symbol_prefix decoded expected mode2_hbz_count =>
  prepared_hbz_prefix decoded hbz mode2_hbz_count.
proof.
move=> [hprepared hprefix].
rewrite /prepared_hbz_prefix => i hi.
rewrite /decoded_symbol_prefix in hprefix.
rewrite (hprefix i hi).
exact (hprepared i hi).
qed.

lemma full_encode_prepare_mode2_correct
    (symbols0 : BArray2048.t)
    (bad0 : BArray8.t)
    (hbz0 : BArray8192.t) :
  hoare [FullEncode._encode_hb_z1_prepare :
    symsp = symbols0 /\ badp = bad0 /\ hp = hbz0 /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset /\
    canonical_hbz_mode2 hbz0
    ==>
    BArray8.get64 res.`2 0 = W64.zero /\
    prepared_hbz_prefix res.`1 hbz0 mode2_hbz_count /\
    byte_tail_frame symbols0 res.`1 mode2_hbz_count].
proof.
conseq full_encode_prepare_exact_focused
  (encode_hb_z1_prepare_core_mode2_correct symbols0 bad0 hbz0) => //=.
move=> &1 hpre.
exists (symsp{1}, badp{1}, hp{1}, count{1}, mhb{1}, offset{1}) => /=.
smt().
qed.

lemma full_rans_encode_trace_refinement
    (enc0 : BArray2048.t)
    (state0 : BArray16.t)
    (symbols0 : BArray2048.t) :
  hoare [FullEncode._rans_encode :
    encp = enc0 /\
    statep = state0 /\
    symsp = symbols0 /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int mode2_hbz_count /\
    mode2_hbz_symbol_stream symbols0
    ==>
    BArray16.get64 res.`2 1 <> W64.zero \/
    (BArray16.get64 res.`2 1 = W64.zero /\
     0 <= W64.to_uint (BArray16.get64 res.`2 0) <= 1020 /\
     W64.to_uint (BArray16.get64 res.`2 0) +
       size (trace_bytes (symbol_list_of_array symbols0)) =
       mode2_hbz_count /\
     segment_matches res.`1
       (W64.to_uint (BArray16.get64 res.`2 0))
       (trace_bytes (symbol_list_of_array symbols0)) /\
     prefix_frame enc0 res.`1
       (W64.to_uint (BArray16.get64 res.`2 0)))].
proof.
conseq full_rans_encode_exact_focused
  (actual_rans_encode_trace_refinement enc0 state0 symbols0) => //=.
move=> &1 hpre.
exists (encp{1}, statep{1}, symsp{1}, esymsp{1}, count{1}) => /=.
smt().
qed.

lemma full_rans_decode_trace_refinement
    (decoded0 expected_symbols buffer0 : BArray2048.t)
    (state0 : BArray24.t)
    (encoded_size : int) :
  hoare [FullDecode._rans_decode :
    symsp = decoded0 /\
    statep = state0 /\
    bufp = buffer0 /\
    symbolwp = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words /\
    dsymswp = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words /\
    actual_mode2_decoder_trace_input
      expected_symbols buffer0 state0 encoded_size
    ==>
    actual_mode2_decoder_trace_post
      decoded0 expected_symbols res encoded_size].
proof.
conseq full_rans_decode_exact_focused
  (actual_rans_decode_trace_refinement
     decoded0 expected_symbols buffer0 state0 encoded_size) => //=.
move=> &1 hpre.
exists (symsp{1}, statep{1}, bufp{1}, symbolwp{1}, dsymswp{1}) => /=.
smt().
qed.

lemma full_decode_apply_mode2_correct
    (decoded0 original0 : BArray8192.t) :
  hoare [FullDecode._decode_hb_z1_apply :
    hp = decoded0 /\
    count = W64.of_int mode2_hbz_count /\
    offset = W64.of_int mode2_hbz_offset /\
    canonical_hbz_mode2 original0 /\
    prepared_hbz_prefix symsp original0 mode2_hbz_count
    ==>
    decoded_hbz_prefix res original0 mode2_hbz_count /\
    coeff_tail_frame decoded0 res mode2_hbz_count].
proof.
conseq full_decode_apply_exact_focused
  (decode_hb_z1_apply_core_mode2_correct decoded0 original0) => //=.
move=> &1 hpre.
exists (hp{1}, symsp{1}, count{1}, offset{1}) => /=.
smt().
qed.

end Mode2HbzInternalBoundaries.
