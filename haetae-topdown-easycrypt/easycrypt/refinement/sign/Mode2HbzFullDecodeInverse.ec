require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  HbzFullDecodeTarget SignatureUnpackMode2Target
  Mode2HbzCodecSpec
  Mode2RansEncodeRefinement
  Mode2RansArrayListBridge
  Mode2RansDecoderCursor
  Mode2RansDecoderActualTrace
  Mode2RansCoreActualInverse
  Mode2HbzInternalBoundaries
  Mode2RansCoreCompositionBridge.

theory Mode2HbzFullDecodeInverse.

import Mode2HbzCodecSpec
       Mode2RansEncodeRefinement
       Mode2RansArrayListBridge
       Mode2RansDecoderCursor
       Mode2RansDecoderActualTrace
       Mode2RansCoreActualInverse
       Mode2HbzInternalBoundaries
       Mode2RansCoreCompositionBridge.

module FullDecode = HbzFullDecodeTarget.M.

lemma actual_decode_hb_z1_full_mode2_inverse
    (decoded0 : BArray8192.t)
    (bad0 : BArray8.t)
    (encoded_buffer expected_symbols : BArray2048.t)
    (original_hbz : BArray8192.t)
    (encoded_size : int) :
  hoare [FullDecode._decode_hb_z1_full :
    hp = decoded0 /\
    badp = bad0 /\
    bufp = encoded_buffer /\
    size_in = W64.of_int encoded_size /\
    symbolwp = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words /\
    dsymswp = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset /\
    canonical_hbz_mode2 original_hbz /\
    prepared_hbz_prefix expected_symbols original_hbz mode2_hbz_count /\
    mode2_hbz_symbol_stream expected_symbols /\
    encoded_size = size (mode2_trace_bytes expected_symbols) /\
    4 <= encoded_size <= mode2_hbz_count /\
    segment_matches encoded_buffer 0 (mode2_trace_bytes expected_symbols)
    ==>
    BArray8.get64 res.`2 0 = W64.zero /\
    decoded_hbz_prefix res.`1 original_hbz mode2_hbz_count /\
    coeff_tail_frame decoded0 res.`1 mode2_hbz_count].
proof.
proc.
seq 10 :
  (hp = decoded0 /\
   badp = bad0 /\
   count = W64.of_int mode2_hbz_count /\
   offset = W64.of_int mode2_hbz_offset /\
   canonical_hbz_mode2 original_hbz /\
   prepared_hbz_prefix symsp original_hbz mode2_hbz_count /\
   BArray24.get64 statep 1 = W64.zero).
+ wp.
  call (full_rans_decode_trace_refinement
          witness expected_symbols encoded_buffer
          (configured_decoder_state witness encoded_size)
          encoded_size).
  auto => &hr hpre.
  split.
  + move: hpre =>
      [hdecoded0 [hbad0 [hbuf [hsizein [hsymbolw [hdsymsw [hcount [hmhb
        [hoff [hcanon [hprepared [hstream [hsize [hbound hsegment]]]]]]]]]]]]]].
    split; first trivial.
    split.
    * rewrite /configured_decoder_state hcount hsizein hmhb.
      trivial.
    split; first exact hbuf.
    split; first exact hsymbolw.
    split; first exact hdsymsw.
    apply (actual_decoder_input_from_configured_trace
      expected_symbols encoded_buffer witness encoded_size).
    * exact hstream.
    * exact hsize.
    * exact hbound.
    * exact hsegment.
  + move=> _ result hdecode.
    move: hpre =>
      [hdecoded0 [hbad0 [_ [_ [_ [_ [hcount [_ [hoff [hcanon
        [hprepared _]]]]]]]]]]].
    rewrite /actual_mode2_decoder_trace_post in hdecode.
    move: hdecode => [hbad [_ [hprefix _]]].
    have hprepared_decoded :
        prepared_hbz_prefix result.`1 original_hbz mode2_hbz_count.
    + apply (decoded_prefix_preserves_prepared_hbz
        result.`1 expected_symbols original_hbz).
      split; first exact hprepared.
      exact hprefix.
    split; first exact hdecoded0.
    split; first exact hbad0.
    split; first exact hcount.
    split; first exact hoff.
    split; first exact hcanon.
    split; first exact hprepared_decoded.
    exact hbad.
+ sp 4.
  if.
  - wp.
    call (full_decode_apply_mode2_correct decoded0 original_hbz).
    auto => />.
  - auto => />; smt().
qed.

end Mode2HbzFullDecodeInverse.
