require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  HbzFullEncodeTarget
  SignaturePackMode2Target
  Mode2HbzCodecSpec Mode2HbzInternalBoundaries
  Mode2RansEncodeRefinement
  Mode2RansArrayListBridge
  Mode2RansSuffixCopy Mode2RansCoreCompositionBridge
  Mode2RansCoreActualInverse.

theory Mode2HbzFullEncodeTrace.

import Mode2HbzCodecSpec Mode2RansSuffixCopy
       Mode2HbzInternalBoundaries
       Mode2RansEncodeRefinement
       Mode2RansArrayListBridge
       Mode2RansCoreCompositionBridge
       Mode2RansCoreActualInverse.

module Focus = HbzFullEncodeTarget.M.

lemma actual_encode_hb_z1_full_mode2_trace
    (out_initial : BArray2048.t)
    (hbz0 : BArray8192.t) :
  hoare [Focus._encode_hb_z1_full :
    outp = out_initial /\
    hp = hbz0 /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset /\
    canonical_hbz_mode2 hbz0
    ==>
    (res.`2 = W64.zero /\
     res.`1 = out_initial /\
     exists prepared_symbols,
       prepared_hbz_prefix prepared_symbols hbz0 mode2_hbz_count /\
       mode2_hbz_symbol_stream prepared_symbols)
    \/
    (res.`2 <> W64.zero /\
     4 <= W64.to_uint res.`2 <= mode2_hbz_count /\
     exists prepared_symbols,
       prepared_hbz_prefix prepared_symbols hbz0 mode2_hbz_count /\
       mode2_hbz_symbol_stream prepared_symbols /\
       res.`2 =
         W64.of_int (size (mode2_trace_bytes prepared_symbols)) /\
       4 <= size (mode2_trace_bytes prepared_symbols) <=
         mode2_hbz_count /\
       segment_matches res.`1 0 (mode2_trace_bytes prepared_symbols) /\
       suffix_frame out_initial res.`1 (W64.to_uint res.`2))].
proof.
proc.
seq 13 :
  (exists prepared_symbols,
     outp = out_initial /\
     hp = hbz0 /\
     esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
     count = W64.of_int mode2_hbz_count /\
     mhb = W64.of_int mode2_hbz_alphabet /\
     offset = W64.of_int mode2_hbz_offset /\
     canonical_hbz_mode2 hbz0 /\
     symsp = prepared_symbols /\
     BArray8.get64 badp 0 = W64.zero /\
     prepared_hbz_prefix prepared_symbols hbz0 mode2_hbz_count /\
     mode2_hbz_symbol_stream prepared_symbols).
+ wp.
   call (Mode2HbzInternalBoundaries.full_encode_prepare_mode2_correct
     witness witness hbz0).
   auto => &hr hpre.
   split.
   + move: hpre =>
       [hout [hhp [hesyms [hcount [hmhb [hoffset hcanon]]]]]].
     split; first trivial.
     split; first trivial.
     split; first exact hhp.
     split; first exact hcount.
     split; first exact hmhb.
     split; first exact hoffset.
     exact hcanon.
   + move=> _ result hprepare.
   move: hpre =>
     [hout [hhp [hesyms [hcount [hmhb [hoffset hcanon]]]]]].
   move: hprepare => [hbad [hprepared htail]].
   exists result.`1.
   split; first exact hout.
   split; first exact hhp.
   split; first exact hesyms.
   split; first exact hcount.
   split; first exact hmhb.
   split; first exact hoffset.
   split; first exact hcanon.
   split; first trivial.
   split; first exact hbad.
   split; first exact hprepared.
   apply (Mode2HbzInternalBoundaries.prepared_hbz_implies_mode2_symbol_stream
     result.`1 hbz0).
   split; first exact hcanon.
   exact hprepared.
+ sp 4.
   if.
   - auto => />; rewrite /protect_64; smt().
   - seq 2 :
       (exists prepared_symbols,
          outp = out_initial /\
          hp = hbz0 /\
          esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
          count = W64.of_int mode2_hbz_count /\
          mhb = W64.of_int mode2_hbz_alphabet /\
          offset = W64.of_int mode2_hbz_offset /\
          canonical_hbz_mode2 hbz0 /\
          symsp = prepared_symbols /\
          prepared_hbz_prefix prepared_symbols hbz0 mode2_hbz_count /\
          mode2_hbz_symbol_stream prepared_symbols /\
          (BArray16.get64 statep 1 <> W64.zero \/
           (BArray16.get64 statep 1 = W64.zero /\
            0 <= W64.to_uint (BArray16.get64 statep 0) <= 1020 /\
            W64.to_uint (BArray16.get64 statep 0) +
              size (mode2_trace_bytes prepared_symbols) =
              mode2_hbz_count /\
            segment_matches encp
              (W64.to_uint (BArray16.get64 statep 0))
              (mode2_trace_bytes prepared_symbols)))).
     * sp 1.
       exists* encp{hr}, statep{hr}, symsp{hr};
         elim* => enc0 state0 prepared_symbols.
       move=> ms0 prepared_symbols0.
       call (Mode2HbzInternalBoundaries.full_rans_encode_trace_refinement
         enc0 state0 prepared_symbols).
       auto => &hr hpost.
       smt().
     * sp 4.
       if.
       - auto => />; rewrite /protect_64; smt().
       - sp 7.
         exists* encp{hr}, off{hr}; elim* => encoded1 off1.
         move=> ms0 prepared_symbols.
         call (copy_encoded_suffix_correct
           out_initial encoded1 (W64.to_uint off1)
           (size (mode2_trace_bytes prepared_symbols))).
         auto => &hr hpost.
         move: hpost =>
           [hcaptured [hms_call [hoff_call [hsize_call [hcore hnotb]]]]].
         move: hcaptured => [hencoded1 hoff1eq].
         move: hcore => [hms [hbadv [hb [hout [hhp [hesyms [hcount
           [hmhb [hoffset [hcanon [hsymsp [hprepared [hstream hrans]]]]]]]]]]]]].
         move: hrans => [hrans_bad | [hzero [hoff [hsize hsegment]]]].
         + smt().
         + have hsizew := encoder_success_size_word_bridge
             (BArray16.get64 statep{hr} 0)
             (size (mode2_trace_bytes prepared_symbols)) hoff hsize.
           move: hsizew => [hsizeu [hsizeword [hbound [hsum hoffw]]]].
           have hoff1_state :
               off1 = BArray16.get64 statep{hr} 0 by
             rewrite hoff1eq hoff_call.
           have hsize_call_word :
               size{hr} =
                 W64.of_int (size (mode2_trace_bytes prepared_symbols)) by
             rewrite hsize_call hcount hsizeword.
           split.
           * split; first exact hout.
             split; first by rewrite hencoded1.
             split; first by rewrite hoff_call -hoff1_state.
             split; first exact hsize_call_word.
             split; first by have := W64.to_uint_cmp off1; smt().
             split; first exact (size_ge0 (mode2_trace_bytes prepared_symbols)).
             rewrite /mode2_hbz_capacity; smt().
           * move=> _ result hcopy.
             move: hcopy => [hslice hframe].
             have hsegment1 :
                 segment_matches encoded1 (W64.to_uint off1)
                   (mode2_trace_bytes prepared_symbols) by
               rewrite hencoded1 hoff1_state; exact hsegment.
             have hcopied := copied_suffix_is_exact_trace encoded1 result
               (W64.to_uint off1) (mode2_trace_bytes prepared_symbols)
               hsegment1 hslice.
             have hresult_sizeu :
                 W64.to_uint size{hr} =
                   size (mode2_trace_bytes prepared_symbols) by
               rewrite hsize_call hcount hsizeu.
             have hresult_nz : size{hr} <> W64.zero by
               smt(W64.to_uint0).
             right.
             split; first exact hresult_nz.
             split; first by rewrite hresult_sizeu.
             exists prepared_symbols.
             split; first exact hprepared.
             split; first exact hstream.
             split; first exact hsize_call_word.
             split; first exact hbound.
             split; first exact hcopied.
             rewrite hresult_sizeu.
             exact hframe.
qed.

end Mode2HbzFullEncodeTrace.
