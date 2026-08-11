require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  HbzFullEncodeTarget HbzFullDecodeTarget
  SignaturePackMode2Target SignatureUnpackMode2Target
  Mode2HbzCodecSpec
  Mode2RansEncodeRefinement
  Mode2HbzFullEncodeTrace Mode2HbzFullDecodeInverse
  Mode2RansArrayListBridge
  Mode2RansSuffixCopy
  Mode2RansCoreActualInverse.

theory Mode2HbzFullActualInverse.

import Mode2HbzCodecSpec
       Mode2RansEncodeRefinement
       Mode2HbzFullEncodeTrace Mode2HbzFullDecodeInverse
       Mode2RansArrayListBridge
       Mode2RansSuffixCopy
       Mode2RansCoreActualInverse.

module HbzFullEncode = HbzFullEncodeTarget.M.
module HbzFullDecode = HbzFullDecodeTarget.M.

module HbzFullActualHarness = {
  var decoder_ran : bool

  proc run(out0 : BArray2048.t,
           hbz0 : BArray8192.t,
           decoded0 : BArray8192.t,
           bad0 : BArray8.t) :
      BArray2048.t * W64.t * bool * BArray8192.t * BArray8.t = {
    var encoded : BArray2048.t;
    var size : W64.t;
    var decoded : BArray8192.t;
    var bad : BArray8.t;

    encoded <- out0;
    decoded <- decoded0;
    bad <- bad0;
    decoder_ran <- false;
    (encoded, size) <@ HbzFullEncode._encode_hb_z1_full(
      encoded, hbz0,
      SignaturePackMode2Target.jmode2_hb_z1_esyms,
      W64.of_int mode2_hbz_count,
      W64.of_int mode2_hbz_alphabet,
      W64.of_int mode2_hbz_offset);

    if (size <> W64.zero) {
      decoder_ran <- true;
      (decoded, bad) <@ HbzFullDecode._decode_hb_z1_full(
        decoded, bad, encoded, size,
        SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words,
        SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words,
        W64.of_int mode2_hbz_count,
        W64.of_int mode2_hbz_alphabet,
        W64.of_int mode2_hbz_offset);
    }

    return (encoded, size, decoder_ran, decoded, bad);
  }
}.

lemma actual_hbz_full_encode_decode_inverse_mode2
    (out0 : BArray2048.t)
    (hbz0 decoded0 : BArray8192.t)
    (bad0 : BArray8.t) :
  hoare [HbzFullActualHarness.run :
    arg = (out0, hbz0, decoded0, bad0) /\
    canonical_hbz_mode2 hbz0
    ==>
    (res.`2 = W64.zero /\
     !HbzFullActualHarness.decoder_ran /\
     res.`1 = out0 /\
     res.`4 = decoded0 /\
     res.`5 = bad0)
    \/
    (res.`2 <> W64.zero /\
     4 <= W64.to_uint res.`2 <= mode2_hbz_count /\
     HbzFullActualHarness.decoder_ran /\
     BArray8.get64 res.`5 0 = W64.zero /\
     decoded_hbz_prefix res.`4 hbz0 mode2_hbz_count /\
     coeff_tail_frame decoded0 res.`4 mode2_hbz_count /\
     suffix_frame out0 res.`1 (W64.to_uint res.`2) /\
     exists prepared_symbols,
       prepared_hbz_prefix prepared_symbols hbz0 mode2_hbz_count /\
       mode2_hbz_symbol_stream prepared_symbols /\
       res.`2 =
         W64.of_int (size (mode2_trace_bytes prepared_symbols)) /\
       segment_matches res.`1 0 (mode2_trace_bytes prepared_symbols))].
proof.
proc.
sp 4.
seq 1 :
  (decoded = decoded0 /\
   bad = bad0 /\
   !HbzFullActualHarness.decoder_ran /\
   canonical_hbz_mode2 hbz0 /\
   ((size = W64.zero /\
     encoded = out0 /\
     exists prepared_symbols,
       prepared_hbz_prefix prepared_symbols hbz0 mode2_hbz_count /\
       mode2_hbz_symbol_stream prepared_symbols)
    \/
    (size <> W64.zero /\
     4 <= W64.to_uint size <= mode2_hbz_count /\
     exists prepared_symbols,
       prepared_hbz_prefix prepared_symbols hbz0 mode2_hbz_count /\
       mode2_hbz_symbol_stream prepared_symbols /\
       size =
         W64.of_int (size (mode2_trace_bytes prepared_symbols)) /\
       4 <= size (mode2_trace_bytes prepared_symbols) <=
         mode2_hbz_count /\
       segment_matches encoded 0 (mode2_trace_bytes prepared_symbols) /\
       suffix_frame out0 encoded (W64.to_uint size)))).
+ call (actual_encode_hb_z1_full_mode2_trace out0 hbz0).
   auto.
+ if.
   - sp 1.
     exists* decoded{hr}, bad{hr}, encoded{hr}, size{hr};
       elim* => decoded1 bad1 encoded1 size1.
     move=> hguard prepared_symbols prepared_symbols0.
     call (actual_decode_hb_z1_full_mode2_inverse
       decoded1 bad1 encoded1 prepared_symbols hbz0
       (size (mode2_trace_bytes prepared_symbols))).
     + auto => &hr hpre.
       smt().
   - auto => &hr hpost; smt().
qed.

end Mode2HbzFullActualInverse.
