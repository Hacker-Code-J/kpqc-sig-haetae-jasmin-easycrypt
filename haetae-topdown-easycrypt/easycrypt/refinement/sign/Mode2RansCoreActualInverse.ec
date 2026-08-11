require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  Mode2HbzCodecSpec
  Mode2RansByteStack
  Mode2RansArrayListBridge
  Mode2RansEncodeRefinement
  Mode2RansSuffixCopy
  Mode2RansDecoderCursor
  Mode2RansActualInverse
  Mode2RansCoreCompositionBridge
  Mode2RansEncoderOuterRefinement
  Mode2RansDecoderTopHoare.

theory Mode2RansCoreActualInverse.

import Mode2HbzCodecSpec
       Mode2RansByteStack
       Mode2RansArrayListBridge
       Mode2RansEncodeRefinement
       Mode2RansSuffixCopy
       Mode2RansDecoderCursor
       Mode2RansActualInverse
       Mode2RansCoreCompositionBridge
       Mode2RansEncoderOuterRefinement
       Mode2RansDecoderTopHoare.

op mode2_trace_bytes (symbols : BArray2048.t) : int list =
  trace_bytes (symbol_list_of_array symbols).

lemma actual_rans_encode_copy_decode_inverse
    (enc_initial copied_initial decoded_initial : BArray2048.t)
    (encoder_state_initial : BArray16.t)
    (decoder_state_initial : BArray24.t)
    (expected_symbols : BArray2048.t) :
  hoare [Mode2RansActualHarness.run :
    arg = (enc_initial, copied_initial, decoded_initial,
           encoder_state_initial, decoder_state_initial,
           expected_symbols) /\
    mode2_hbz_symbol_stream expected_symbols
    ==>
    (Mode2RansActualHarness.encoder_bad <> W64.zero /\
     !Mode2RansActualHarness.decoder_ran /\
     Mode2RansActualHarness.decoder_off = W64.zero /\
     Mode2RansActualHarness.decoder_bad = W64.one /\
     res.`2 = decoded_initial /\
     res.`3 = decoder_state_initial)
    \/
    (Mode2RansActualHarness.encoder_bad = W64.zero /\
     Mode2RansActualHarness.decoder_ran /\
     Mode2RansActualHarness.decoder_count_input =
       W64.of_int mode2_hbz_count /\
     Mode2RansActualHarness.decoder_size_input =
       Mode2RansActualHarness.encoded_size /\
     Mode2RansActualHarness.decoder_alphabet_input =
       W64.of_int mode2_hbz_alphabet /\
     Mode2RansActualHarness.decoder_bad = W64.zero /\
     Mode2RansActualHarness.decoder_off =
       Mode2RansActualHarness.encoded_size /\
     decoded_symbol_prefix res.`2 expected_symbols mode2_hbz_count /\
     decoded_symbol_tail_frame decoded_initial res.`2 mode2_hbz_count /\
     actual_core_success_result
       Mode2RansActualHarness.encoder_bad
       Mode2RansActualHarness.decoder_bad
       Mode2RansActualHarness.decoder_off
       Mode2RansActualHarness.encoded_size
       Mode2RansActualHarness.decoder_ran /\
     segment_matches res.`1
       (W64.to_uint Mode2RansActualHarness.encoder_off)
       (mode2_trace_bytes expected_symbols) /\
     prefix_frame enc_initial res.`1
       (W64.to_uint Mode2RansActualHarness.encoder_off))].
proof.
proc.
seq 1 :
  (copied0 = copied_initial /\
   decoded0 = decoded_initial /\
   decoder_state0 = decoder_state_initial /\
   symbols = expected_symbols /\
   mode2_hbz_symbol_stream expected_symbols /\
   (BArray16.get64 encoder_state 1 <> W64.zero \/
    (BArray16.get64 encoder_state 1 = W64.zero /\
     0 <= W64.to_uint (BArray16.get64 encoder_state 0) <= 1020 /\
     W64.to_uint (BArray16.get64 encoder_state 0) +
       size (mode2_trace_bytes expected_symbols) = mode2_hbz_count /\
     segment_matches encoded
       (W64.to_uint (BArray16.get64 encoder_state 0))
       (mode2_trace_bytes expected_symbols) /\
     prefix_frame enc_initial encoded
       (W64.to_uint (BArray16.get64 encoder_state 0))))).
+ call (actual_rans_encode_trace_refinement
    enc_initial encoder_state_initial expected_symbols).
  auto.
+ sp 12.
  if.
  - seq 9 :
      (Mode2RansActualHarness.encoder_bad = W64.zero /\
       0 <= W64.to_uint Mode2RansActualHarness.encoder_off <= 1020 /\
       segment_matches encoded
         (W64.to_uint Mode2RansActualHarness.encoder_off)
         (mode2_trace_bytes expected_symbols) /\
       prefix_frame enc_initial encoded
         (W64.to_uint Mode2RansActualHarness.encoder_off) /\
       Mode2RansActualHarness.encoded_size =
         W64.of_int (size (mode2_trace_bytes expected_symbols)) /\
       4 <= size (mode2_trace_bytes expected_symbols) <= mode2_hbz_count /\
       mode2_hbz_symbol_stream expected_symbols /\
       segment_matches copied 0 (mode2_trace_bytes expected_symbols) /\
       decoded = decoded_initial /\
       decoder_state = configured_decoder_state decoder_state_initial
         (size (mode2_trace_bytes expected_symbols)) /\
       Mode2RansActualHarness.decoder_ran /\
       Mode2RansActualHarness.decoder_count_input =
         W64.of_int mode2_hbz_count /\
       Mode2RansActualHarness.decoder_size_input =
         Mode2RansActualHarness.encoded_size /\
       Mode2RansActualHarness.decoder_alphabet_input =
         W64.of_int mode2_hbz_alphabet).
    * wp.
      exists* encoded{hr}; elim* => encoded1.
      exists* Mode2RansActualHarness.encoder_off{hr};
        elim* => encoder_off1.
      call (copy_encoded_suffix_correct
        copied_initial encoded1 (W64.to_uint encoder_off1)
        (size (mode2_trace_bytes expected_symbols))).
      auto => &hr hpre encoded_size1.
      move: hpre => [hoff1 [hencoded1 [hstate hguard]]].
      move: hstate =>
        [hoffstate [hbadstate [hran0 [hesize0 [hcopied0 [hdecoded0
          [hdstate0 [hcount0 [hsizein0 [halpha0 [hdoff0 [hdbad0
            hinv]]]]]]]]]]]].
      move: hinv =>
        [hcopiedarg [hdecodedarg [hdstatearg [hsymbolarg
          [hstream henc]]]]].
      rewrite -hbadstate hguard /= in henc.
      move: henc => [hoff0 [hsize0 [hsegment0 hframe0]]].
      have hoff : 0 <= W64.to_uint encoder_off1 <= 1020.
        + rewrite hoff1 hoffstate; exact hoff0.
        have hsize :
            W64.to_uint encoder_off1 +
            size (mode2_trace_bytes expected_symbols) = mode2_hbz_count.
        + rewrite hoff1 hoffstate; exact hsize0.
        have hsegment :
            segment_matches encoded1 (W64.to_uint encoder_off1)
              (mode2_trace_bytes expected_symbols).
        + rewrite hencoded1 hoff1 hoffstate; exact hsegment0.
        have hframe :
            prefix_frame enc_initial encoded1 (W64.to_uint encoder_off1).
        + rewrite hencoded1 hoff1 hoffstate; exact hframe0.
        have hsizew := encoder_success_size_word_bridge encoder_off1
          (size (mode2_trace_bytes expected_symbols)) hoff hsize.
        move: hsizew => [hencuint [hencword [hnbound [hsum hoffw]]]].
        split.
        + split; first by rewrite hcopied0 hcopiedarg.
          split; first by rewrite hencoded1.
          split; first by rewrite hoff1.
          split.
          * change
              (W64.of_int mode2_hbz_count -
                 Mode2RansActualHarness.encoder_off{hr} =
               W64.of_int (size (mode2_trace_bytes expected_symbols))).
            rewrite -hoff1.
            exact hencword.
          split; first smt().
          split; first exact (size_ge0 (mode2_trace_bytes expected_symbols)).
          rewrite /mode2_hbz_capacity; smt().
        + move=> hcallpre result [hslice hsuffix].
        move: hcallpre =>
          [hcpre [hepre [hopre [hsizepre [hoffpre [hnpre hcappre]]]]]].
        have hcopied := copied_suffix_is_exact_trace encoded1 result
          (W64.to_uint encoder_off1) (mode2_trace_bytes expected_symbols)
          hsegment hslice.
        split; first exact hguard.
        split; first by rewrite -hoff1.
        split; first by rewrite -hencoded1 -hoff1.
        split; first by rewrite -hencoded1 -hoff1.
        split.
        + change
            (W64.of_int mode2_hbz_count -
               Mode2RansActualHarness.encoder_off{hr} =
             W64.of_int (size (mode2_trace_bytes expected_symbols))).
          rewrite -hoff1.
          exact hencword.
        split; first exact hnbound.
        split; first exact hstream.
        split; first exact hcopied.
        split; first by rewrite hdecoded0 hdecodedarg.
        rewrite hdstate0 hdstatearg hsizepre
                /configured_decoder_state; trivial.
    * wp.
      exists* copied{hr}; elim* => copied1.
      exists* decoder_state{hr}; elim* => decoder_state1.
      call (actual_rans_decode_trace_refinement
        decoded_initial expected_symbols copied1
        (configured_decoder_state decoder_state_initial
          (size (mode2_trace_bytes expected_symbols)))
        (size (mode2_trace_bytes expected_symbols))).
      auto => &hr hpre.
      split.
      + move: hpre => [hstate1 [hcopied1 hcut]].
        move: hcut =>
          [hbad [hoff [hsegment [hframe [hsizew [hbound [hstream
            [hcopied [hdecoded [hstate [hran [hcount
              [hsizein halpha]]]]]]]]]]]]].
        split; first exact hdecoded.
        split; first exact hstate.
        split.
        + rewrite hcopied1.
          trivial.
        have hcopied_snapshot :
            segment_matches copied1 0 (mode2_trace_bytes expected_symbols).
        + rewrite hcopied1; exact hcopied.
        apply (actual_decoder_input_from_configured_trace
          expected_symbols copied1 decoder_state_initial
          (size (mode2_trace_bytes expected_symbols))).
        + exact hstream.
        + trivial.
        + exact hbound.
        + exact hcopied_snapshot.
      + move=> _ result hdec.
      move: hpre => [hstate1 [hcopied1 hcut]].
      move: hcut =>
        [hbad [hoff [hsegment [hframe [hsizew [hbound [hstream
          [hcopied [hdecoded [hstate [hran [hcount
            [hsizein halpha]]]]]]]]]]]]].
      rewrite /actual_mode2_decoder_trace_post in hdec.
      move: hdec => [hdbad [hdoff [hprefix htail]]].
      right.
      split; first exact hbad.
      split; first exact hran.
      split; first exact hcount.
      split; first exact hsizein.
      split; first exact halpha.
      split; first exact hdbad.
      split.
      + rewrite hsizew.
        exact hdoff.
      split; first exact hprefix.
      split; first exact htail.
      split.
      + rewrite /actual_core_success_result; smt().
      split; first exact hsegment.
      exact hframe.
  - auto.
qed.

end Mode2RansCoreActualInverse.
