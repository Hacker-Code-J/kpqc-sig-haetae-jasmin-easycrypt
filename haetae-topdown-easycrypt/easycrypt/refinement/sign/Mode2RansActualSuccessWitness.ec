require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansEncodeTarget
  HbzFullEncodeTarget
  SignaturePackMode2Target
  Mode2HbzCodecSpec
  Mode2RansByteStack
  Mode2RansArrayListBridge
  Mode2RansEncodeRefinement
  Mode2RansSuffixCopy
  Mode2RansCoreCompositionBridge
  Mode2RansCoreActualInverse
  Mode2RansEncoderActualTraceClosure
  Mode2HbzFullDecodeInverse
  Mode2HbzFullActualInverse
  Mode2HbzActualBoundary
  Mode2HbzInternalBoundaries
  Mode2HbzSignatureBoundaryLift
  Mode2RansAllSixBudget.

theory Mode2RansActualSuccessWitness.

import Mode2HbzCodecSpec
       Mode2RansByteStack
       Mode2RansArrayListBridge
       Mode2RansEncodeRefinement
       Mode2RansSuffixCopy
       Mode2RansCoreCompositionBridge
       Mode2RansCoreActualInverse
       Mode2RansEncoderActualTraceClosure
       Mode2HbzFullDecodeInverse
       Mode2HbzFullActualInverse
       Mode2HbzActualBoundary
       Mode2HbzInternalBoundaries
       Mode2HbzSignatureBoundaryLift
       Mode2RansAllSixBudget.

module Encode = RansEncodeTarget.M.
module Focus = HbzFullEncodeTarget.M.
module Pack = SignaturePackMode2Target.M.

lemma all_six_prefix_stream symbols :
  all_six_prefix symbols mode2_hbz_count =>
  mode2_hbz_symbol_stream symbols.
proof.
move=> hprefix i hi.
rewrite /all_six_prefix in hprefix.
rewrite (hprefix i hi) W8.of_uintK /mode2_hbz_alphabet /=.
smt().
qed.

lemma all_six_prefix_symbol_list_eq symbols :
  all_six_prefix symbols mode2_hbz_count =>
  symbol_list_of_array symbols = all_six_symbol_list.
proof.
move=> hprefix.
rewrite all_six_symbol_listE.
exact (all_six_prefix_symbol_list symbols hprefix).
qed.

lemma all_six_prefix_trace_bytes_eq symbols :
  all_six_prefix symbols mode2_hbz_count =>
  trace_bytes (symbol_list_of_array symbols) =
  mode2_trace_bytes all_six_symbols.
proof.
move=> hprefix.
rewrite /mode2_trace_bytes.
rewrite (all_six_prefix_symbol_list_eq symbols hprefix).
trivial.
qed.

lemma all_six_prefix_normalization_budget symbols :
  all_six_prefix symbols mode2_hbz_count =>
  size (encode_trace (symbol_list_of_array symbols)).`2 <= 1020.
proof.
move=> hprefix.
rewrite (all_six_prefix_symbol_list symbols hprefix).
have hbudget := all_six_normalization_budget mode2_hbz_count _.
+ rewrite /mode2_hbz_count.
   smt().
rewrite /mode2_hbz_count in hbudget.
smt().
qed.

lemma prepared_all_six_symbols_zero_hbz :
  prepared_hbz_prefix all_six_symbols zero_hbz mode2_hbz_count.
proof.
rewrite /prepared_hbz_prefix => i hi.
rewrite /all_six_symbols BArray2048.initiE 1:/#.
rewrite zero_hbz_get32 1:hi hbz_symbol_word_zero.
trivial.
qed.

lemma actual_rans_encode_all_six_success
    (enc0 : BArray2048.t)
    (state0 : BArray16.t)
    (symbols0 : BArray2048.t) :
  hoare [Encode._rans_encode :
    encp = enc0 /\
    statep = state0 /\
    symsp = symbols0 /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int 1024 /\
    all_six_prefix symbols0 mode2_hbz_count
    ==>
    BArray16.get64 res.`2 1 = W64.zero /\
    0 <= W64.to_uint (BArray16.get64 res.`2 0) <= 1020 /\
    4 <= 1024 - W64.to_uint (BArray16.get64 res.`2 0) <= 1024 /\
    segment_matches res.`1
      (W64.to_uint (BArray16.get64 res.`2 0))
      (mode2_trace_bytes all_six_symbols) /\
    W64.to_uint (BArray16.get64 res.`2 0) +
      size (mode2_trace_bytes all_six_symbols) = 1024 /\
    prefix_frame enc0 res.`1
      (W64.to_uint (BArray16.get64 res.`2 0))].
proof.
conseq (actual_rans_encode_trace_closure_strong enc0 state0 symbols0) => //=.
+ move=> &m [henc [hstate [hsym [hesym [hcount hallsix]]]]].
  split; first exact henc.
  split; first exact hstate.
  split; first exact hsym.
  split; first exact hesym.
  split.
  - rewrite /mode2_hbz_count.
    exact hcount.
  exact (all_six_prefix_stream symbols0 hallsix).
+ move=> &m [_ [_ [_ [_ [_ hallsix]]]]] result hpost.
  have hbudget :
      size (encode_trace (symbol_list_of_array symbols0)).`2 <= 1020.
  - exact (all_six_prefix_normalization_budget symbols0 hallsix).
  have htraceeq :
      trace_bytes (symbol_list_of_array symbols0) =
      mode2_trace_bytes all_six_symbols.
  - exact (all_six_prefix_trace_bytes_eq symbols0 hallsix).
  move: hpost => [htrace hfailure].
  move: htrace => [hbad | [hzero [hoff [hsize [hsegment [hcursor hframe]]]]]].
  - have htoo :
        1020 < size (encode_trace (symbol_list_of_array symbols0)).`2 by
      exact (hfailure hbad).
    smt().
  - split; first exact hzero.
    split; first exact hoff.
    split.
    * rewrite /mode2_hbz_count in hsize.
      exact hsize.
    split.
    * rewrite htraceeq in hsegment.
      exact hsegment.
    split.
    * rewrite htraceeq in hcursor.
      exact hcursor.
    exact hframe.
qed.

lemma full_rans_encode_all_six_success
    (enc0 : BArray2048.t)
    (state0 : BArray16.t)
    (symbols0 : BArray2048.t) :
  hoare [Focus._rans_encode :
    encp = enc0 /\
    statep = state0 /\
    symsp = symbols0 /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int 1024 /\
    all_six_prefix symbols0 mode2_hbz_count
    ==>
    BArray16.get64 res.`2 1 = W64.zero /\
    0 <= W64.to_uint (BArray16.get64 res.`2 0) <= 1020 /\
    4 <= 1024 - W64.to_uint (BArray16.get64 res.`2 0) <= 1024 /\
    segment_matches res.`1
      (W64.to_uint (BArray16.get64 res.`2 0))
      (mode2_trace_bytes all_six_symbols) /\
    W64.to_uint (BArray16.get64 res.`2 0) +
      size (mode2_trace_bytes all_six_symbols) = 1024 /\
    prefix_frame enc0 res.`1
      (W64.to_uint (BArray16.get64 res.`2 0))].
proof.
conseq full_rans_encode_exact_focused
  (actual_rans_encode_all_six_success enc0 state0 symbols0) => //=.
move=> &1 hpre.
exists (encp{1}, statep{1}, symsp{1}, esymsp{1}, count{1}) => /=.
smt().
qed.

lemma actual_encode_hb_z1_full_zero_success
    (out_initial : BArray2048.t) :
  hoare [Focus._encode_hb_z1_full :
    outp = out_initial /\
    hp = zero_hbz /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int 1024 /\
    mhb = W64.of_int 13 /\
    offset = W64.of_int 6
    ==>
    res.`2 <> W64.zero /\
    4 <= W64.to_uint res.`2 <= 1024 /\
    res.`2 = W64.of_int (size (mode2_trace_bytes all_six_symbols)) /\
    segment_matches res.`1 0 (mode2_trace_bytes all_six_symbols) /\
    suffix_frame out_initial res.`1 (W64.to_uint res.`2) /\
    exists prepared_symbols,
      prepared_hbz_prefix prepared_symbols zero_hbz mode2_hbz_count /\
      all_six_prefix prepared_symbols mode2_hbz_count /\
      res.`2 = W64.of_int (size (mode2_trace_bytes prepared_symbols)) /\
      segment_matches res.`1 0 (mode2_trace_bytes prepared_symbols)].
proof.
proc.
seq 13 :
  (exists prepared_symbols,
     outp = out_initial /\
     hp = zero_hbz /\
     esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
     count = W64.of_int 1024 /\
     mhb = W64.of_int 13 /\
     offset = W64.of_int 6 /\
     symsp = prepared_symbols /\
     BArray8.get64 badp 0 = W64.zero /\
     prepared_hbz_prefix prepared_symbols zero_hbz mode2_hbz_count /\
     all_six_prefix prepared_symbols mode2_hbz_count).
+ wp.
   call (full_encode_prepare_mode2_correct witness witness zero_hbz).
   auto => &hr hpre.
   move: hpre =>
     [hout [hhp [hesyms [hcount [hmhb hoffset]]]]].
   split.
   - split; first trivial.
     split; first trivial.
     split; first exact hhp.
     split; first exact hcount.
     split; first exact hmhb.
     split; first exact hoffset.
     exact zero_hbz_canonical.
   move=> _ result hprepare.
   move: hprepare => [hbad [hprepared _]].
   exists result.`1.
   split; first exact hout.
   split; first exact hhp.
   split; first exact hesyms.
   split; first exact hcount.
   split; first exact hmhb.
   split; first exact hoffset.
   split; first trivial.
   split; first exact hbad.
   split; first exact hprepared.
   exact (prepared_zero_hbz_is_all_six _ hprepared).
+ sp 4.
   if.
   - auto => />; rewrite /protect_64; smt().
   - seq 2 :
       (exists prepared_symbols,
          outp = out_initial /\
          hp = zero_hbz /\
          esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
          count = W64.of_int 1024 /\
          mhb = W64.of_int 13 /\
          offset = W64.of_int 6 /\
          symsp = prepared_symbols /\
          prepared_hbz_prefix prepared_symbols zero_hbz mode2_hbz_count /\
          all_six_prefix prepared_symbols mode2_hbz_count /\
          BArray16.get64 statep 1 = W64.zero /\
          0 <= W64.to_uint (BArray16.get64 statep 0) <= 1020 /\
          4 <= 1024 - W64.to_uint (BArray16.get64 statep 0) <= 1024 /\
          segment_matches encp
            (W64.to_uint (BArray16.get64 statep 0))
            (mode2_trace_bytes all_six_symbols) /\
          W64.to_uint (BArray16.get64 statep 0) +
            size (mode2_trace_bytes all_six_symbols) = 1024).
     * sp 1.
       exists* encp{hr}, statep{hr}, symsp{hr};
         elim* => enc0 state0 prepared_symbols.
       move=> ms0 prepared_symbols0.
       call (full_rans_encode_all_six_success enc0 state0 prepared_symbols).
       auto => &hr hpost.
       move: hpost => [[henc [hstate hsym0]] [hms [hcore hnotb]]].
       move: hcore => [_ [_ [_ hcore]]].
       move: hcore =>
         [hout [hhp [hesyms [hcount [hmhb [hoffset hcore]]]]]].
       move: hcore => [hsym [_ [hprepared hallsix]]].
       split.
       - split; first by rewrite -henc.
         split; first by rewrite -hstate.
         split; first by rewrite -hsym0.
         split; first exact hesyms.
         split; first exact hcount.
         rewrite hsym0 hsym.
         exact hallsix.
       move=> _ result
         [hzero [hoff [hbound [hsegment [hcursor _]]]]].
       exists prepared_symbols0.
       split; first exact hout.
       split; first exact hhp.
       split; first exact hesyms.
       split; first exact hcount.
       split; first exact hmhb.
       split; first exact hoffset.
       split; first exact hsym.
       split; first exact hprepared.
       split; first exact hallsix.
       split; first exact hzero.
       split; first exact hoff.
       split; first exact hbound.
       split; first exact hsegment.
       exact hcursor.
     * sp 4.
       if.
       - auto => />; rewrite /protect_64; smt().
       - sp 7.
         exists* encp{hr}, off{hr}; elim* => encoded1 off1.
         move=> ms0 prepared_symbols.
         call (copy_encoded_suffix_correct
           out_initial encoded1 (W64.to_uint off1)
           (size (mode2_trace_bytes all_six_symbols))).
         auto => &hr hpost.
         move: hpost =>
           [hcaptured [hms_call [hoff_call [hsize_call [hcore hnotb]]]]].
         move: hcaptured => [hencoded1 hoff1eq].
         move: hcore => [hms hcore].
         move: hcore => [hbadv hcore].
         move: hcore => [hb hcore].
         move: hcore => [hout hcore].
         move: hcore => [hhp hcore].
         move: hcore => [hesyms hcore].
         move: hcore => [hcount hcore].
         move: hcore => [hmhb hcore].
         move: hcore => [hoffset hcore].
         move: hcore => [hsymsp hcore].
         move: hcore => [hprepared hcore].
         move: hcore => [hallsix hcore].
         move: hcore => [hzero hcore].
         move: hcore => [hoff hcore].
         move: hcore => [hbound hcore].
         move: hcore => [hsegment hcursor].
         have hoff1_state :
             off1 = BArray16.get64 statep{hr} 0 by
           rewrite hoff1eq hoff_call.
         have hsizew := encoder_success_size_word_bridge
           (BArray16.get64 statep{hr} 0)
           (size (mode2_trace_bytes all_six_symbols)) hoff hcursor.
         move: hsizew =>
           [hsizeu [hsizeword [hsizebound [hsum hoffw]]]].
         have hsize_call_word :
             size{hr} =
               W64.of_int (size (mode2_trace_bytes all_six_symbols)) by
           rewrite hsize_call hcount hsizeword.
         have htraceeqprep :
             mode2_trace_bytes prepared_symbols =
             mode2_trace_bytes all_six_symbols by
           exact (all_six_prefix_trace_bytes_eq prepared_symbols hallsix).
         split.
         - split; first exact hout.
           split; first by rewrite hencoded1.
           split; first by rewrite hoff_call -hoff1_state.
           split; first exact hsize_call_word.
           split; first by have := W64.to_uint_cmp off1; smt().
           split; first exact (size_ge0 (mode2_trace_bytes all_six_symbols)).
           rewrite /mode2_hbz_capacity; smt().
         move=> _ result hcopy.
         move: hcopy => [hslice hsuffix].
         have hsegment1 :
             segment_matches encoded1 (W64.to_uint off1)
               (mode2_trace_bytes all_six_symbols) by
           rewrite hencoded1 hoff1eq hoff_call; exact hsegment.
         have hcopied := copied_suffix_is_exact_trace encoded1 result
           (W64.to_uint off1) (mode2_trace_bytes all_six_symbols)
           hsegment1 hslice.
         have hresult_sizeu :
             W64.to_uint size{hr} =
               size (mode2_trace_bytes all_six_symbols) by
           rewrite hsize_call hcount hsizeu.
         split; first by smt(W64.to_uint0).
         split; first by rewrite hresult_sizeu; exact hsizebound.
         split; first exact hsize_call_word.
         split; first exact hcopied.
         split.
         + rewrite hresult_sizeu.
           exact hsuffix.
         exists prepared_symbols.
         split; first exact hprepared.
         split; first exact hallsix.
         split.
         + rewrite htraceeqprep.
           exact hsize_call_word.
         rewrite htraceeqprep.
         exact hcopied.
qed.

lemma signature_pack_hbz_zero_success_mode2
    (out_initial : BArray2048.t) :
  hoare [Pack._encode_hb_z1_full :
    outp = out_initial /\
    hp = zero_hbz /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int 1024 /\
    mhb = W64.of_int 13 /\
    offset = W64.of_int 6
    ==>
    res.`2 <> W64.zero /\
    4 <= W64.to_uint res.`2 <= 1024 /\
    res.`2 = W64.of_int (size (mode2_trace_bytes all_six_symbols)) /\
    segment_matches res.`1 0 (mode2_trace_bytes all_six_symbols) /\
    suffix_frame out_initial res.`1 (W64.to_uint res.`2)].
proof.
conseq pack_target_encode_hb_z1_full_exact_focused
  (actual_encode_hb_z1_full_zero_success out_initial) => //=.
move=> &1 hpre.
exists (outp{1}, hp{1}, esymsp{1}, count{1}, mhb{1}, offset{1}) => /=.
smt().
qed.

lemma actual_hbz_full_encode_decode_zero_success_mode2
    (out0 : BArray2048.t)
    (decoded0 : BArray8192.t)
    (bad0 : BArray8.t) :
  hoare [HbzFullActualHarness.run :
    arg = (out0, zero_hbz, decoded0, bad0)
    ==>
    res.`2 <> W64.zero /\
    4 <= W64.to_uint res.`2 <= 1024 /\
    HbzFullActualHarness.decoder_ran /\
    BArray8.get64 res.`5 0 = W64.zero /\
    decoded_hbz_prefix res.`4 zero_hbz mode2_hbz_count /\
    coeff_tail_frame decoded0 res.`4 mode2_hbz_count /\
    suffix_frame out0 res.`1 (W64.to_uint res.`2) /\
    res.`2 = W64.of_int (size (mode2_trace_bytes all_six_symbols)) /\
    segment_matches res.`1 0 (mode2_trace_bytes all_six_symbols)].
proof.
proc.
sp 4.
seq 1 :
  (decoded = decoded0 /\
   bad = bad0 /\
   !HbzFullActualHarness.decoder_ran /\
   size <> W64.zero /\
   4 <= W64.to_uint size <= 1024 /\
   size = W64.of_int (size (mode2_trace_bytes all_six_symbols)) /\
   segment_matches encoded 0 (mode2_trace_bytes all_six_symbols) /\
   suffix_frame out0 encoded (W64.to_uint size)).
+ call (actual_encode_hb_z1_full_zero_success out0).
   auto.
+ if.
   - sp 1.
     exists* decoded{hr}, bad{hr}, encoded{hr}, size{hr};
       elim* => decoded1 bad1 encoded1 size1.
     move=> hguard.
     call (actual_decode_hb_z1_full_mode2_inverse
       decoded1 bad1 encoded1 all_six_symbols zero_hbz
       (size (mode2_trace_bytes all_six_symbols))).
     + auto => &hr hpre.
       split.
       * have hcanon := zero_hbz_canonical.
         have hprepared := prepared_all_six_symbols_zero_hbz.
         have hstream := all_six_symbols_stream.
         have htracebound := all_six_mode2_trace_total_bounds.
         smt().
       move=> _ result hdecode.
       move: hdecode => [hbad0 [hdecoded0 htail]].
       smt().
   - auto => &hr hpost; smt().
qed.

lemma signature_pack_unpack_hbz_zero_success_mode2
    (out0 : BArray2048.t)
    (decoded0 : BArray8192.t)
    (bad0 : BArray8.t) :
  hoare [SignaturePackUnpackHbzFullHarness.run :
    arg = (out0, zero_hbz, decoded0, bad0)
    ==>
    res.`2 <> W64.zero /\
    4 <= W64.to_uint res.`2 <= 1024 /\
    SignaturePackUnpackHbzFullHarness.decoder_ran /\
    BArray8.get64 res.`5 0 = W64.zero /\
    decoded_hbz_prefix res.`4 zero_hbz mode2_hbz_count /\
    coeff_tail_frame decoded0 res.`4 mode2_hbz_count /\
    suffix_frame out0 res.`1 (W64.to_uint res.`2) /\
    res.`2 = W64.of_int (size (mode2_trace_bytes all_six_symbols)) /\
    segment_matches res.`1 0 (mode2_trace_bytes all_six_symbols)].
proof.
conseq signature_pack_unpack_hbz_full_actual_exact
  (actual_hbz_full_encode_decode_zero_success_mode2 out0 decoded0 bad0)
  => //=.
move=> &1 harg.
exists (out0, zero_hbz, decoded0, bad0) => /=.
smt().
qed.

end Mode2RansActualSuccessWitness.
