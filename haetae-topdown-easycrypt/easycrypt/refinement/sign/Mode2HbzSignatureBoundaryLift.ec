require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  SignaturePackMode2Target SignatureUnpackMode2Target
  Mode2HbzCodecSpec
  Mode2RansEncodeRefinement Mode2RansArrayListBridge
  Mode2RansCoreActualInverse
  Mode2RansSuffixCopy
  Mode2HbzActualBoundary Mode2HbzFullEncodeTrace
  Mode2HbzFullDecodeInverse Mode2HbzFullActualInverse.

theory Mode2HbzSignatureBoundaryLift.

import Mode2HbzCodecSpec
       Mode2RansEncodeRefinement Mode2RansArrayListBridge
       Mode2RansCoreActualInverse
       Mode2RansSuffixCopy
       Mode2HbzActualBoundary Mode2HbzFullEncodeTrace
       Mode2HbzFullDecodeInverse Mode2HbzFullActualInverse.

module Pack = SignaturePackMode2Target.M.
module Unpack = SignatureUnpackMode2Target.M.

module SignaturePackUnpackHbzFullHarness = {
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
    (encoded, size) <@ Pack._encode_hb_z1_full(
      encoded, hbz0,
      SignaturePackMode2Target.jmode2_hb_z1_esyms,
      W64.of_int mode2_hbz_count,
      W64.of_int mode2_hbz_alphabet,
      W64.of_int mode2_hbz_offset);

    if (size <> W64.zero) {
      decoder_ran <- true;
      (decoded, bad) <@ Unpack._decode_hb_z1_full(
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

lemma signature_pack_unpack_hbz_full_actual_exact :
  equiv [SignaturePackUnpackHbzFullHarness.run ~ HbzFullActualHarness.run :
    ={arg}
    ==>
    ={res} /\
    SignaturePackUnpackHbzFullHarness.decoder_ran{1} =
      HbzFullActualHarness.decoder_ran{2}].
proof.
proc.
seq 5 5 :
  (={out0, hbz0, decoded0, bad0, encoded, size, decoded, bad} /\
   !SignaturePackUnpackHbzFullHarness.decoder_ran{1} /\
   !HbzFullActualHarness.decoder_ran{2}).
+ wp.
   call pack_target_encode_hb_z1_full_exact_focused.
   auto.
  + if.
    - auto.
    - sp 1 1.
      call unpack_target_decode_hb_z1_full_exact_focused.
      auto.
    - auto.
      smt().
qed.

lemma signature_pack_unpack_hbz_full_inverse_mode2
    (out0 : BArray2048.t)
    (hbz0 decoded0 : BArray8192.t)
    (bad0 : BArray8.t) :
  hoare [SignaturePackUnpackHbzFullHarness.run :
    arg = (out0, hbz0, decoded0, bad0) /\
    canonical_hbz_mode2 hbz0
    ==>
    (res.`2 = W64.zero /\
     !SignaturePackUnpackHbzFullHarness.decoder_ran /\
     res.`1 = out0 /\
     res.`4 = decoded0 /\
     res.`5 = bad0)
    \/
    (res.`2 <> W64.zero /\
     4 <= W64.to_uint res.`2 <= mode2_hbz_count /\
     SignaturePackUnpackHbzFullHarness.decoder_ran /\
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
conseq signature_pack_unpack_hbz_full_actual_exact
  (actual_hbz_full_encode_decode_inverse_mode2 out0 hbz0 decoded0 bad0)
  => //=.
move=> &1 [harg hcanon].
exists (out0{1}, hbz0{1}, decoded0{1}, bad0{1}) => /=.
smt().
qed.

end Mode2HbzSignatureBoundaryLift.
