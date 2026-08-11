require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansEncodeTarget
  Mode2HbzCodecSpec Mode2RansArrayListBridge Mode2RansByteStack
  Mode2RansEncodeRefinement
  Mode2RansEncoderActualTraceClosure.

theory Mode2RansEncoderOuterRefinement.

import Mode2HbzCodecSpec Mode2RansArrayListBridge Mode2RansByteStack
       Mode2RansEncodeRefinement
       Mode2RansEncoderActualTraceClosure.

module Encode = RansEncodeTarget.M.

lemma actual_rans_encode_trace_refinement
    (enc0 : BArray2048.t)
    (state0 : BArray16.t)
    (symbols0 : BArray2048.t) :
  hoare [Encode._rans_encode :
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
conseq (actual_rans_encode_trace_closure enc0 state0 symbols0) => //=.
move=> &m _ result hpost.
elim hpost => hbad; first by left.
right.
move: hbad => [hzero [hoff [_ [hsegment [hcursor hframe]]]]].
split; first exact hzero.
split; first exact hoff.
split; first exact hcursor.
split; first exact hsegment.
exact hframe.
qed.

end Mode2RansEncoderOuterRefinement.
