require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  Mode2HbzCodecSpec Mode2RansByteStack Mode2RansEncodeRefinement
  Mode2RansArrayListBridge Mode2RansEncoderTailInvariant
  Mode2RansEncoderSerialization
  Mode2RansEncoderSerializationComposition.

theory Mode2RansEncoderFinalization.

import Mode2HbzCodecSpec Mode2RansByteStack Mode2RansEncodeRefinement
       Mode2RansArrayListBridge Mode2RansEncoderTailInvariant
       Mode2RansEncoderSerialization
       Mode2RansEncoderSerializationComposition.

lemma encoder_outer_tail_finalize_success
    (enc0 symbols0 encp : BArray2048.t) (x : W32.t) (off : W64.t) :
  encoder_outer_tail_inv enc0 symbols0 encp 0 x off =>
  let start = W64.to_uint off - 4 in
    0 <= start <= 1020 /\
    4 <= mode2_hbz_count - start <= mode2_hbz_count /\
    segment_matches
      (actual_store_w32_le encp start x) start
      (trace_bytes (symbol_list_of_array symbols0)) /\
    start + size (trace_bytes (symbol_list_of_array symbols0)) =
      mode2_hbz_count /\
    prefix_frame enc0 (actual_store_w32_le encp start x) start.
proof.
move=> hout.
rewrite /encoder_outer_tail_inv in hout.
move: hout => [hi [hx [hcursor [hsegment [hframe hofflo]]]]].
rewrite /symbol_suffix drop0 in hx.
rewrite /symbol_suffix drop0 in hcursor.
rewrite /symbol_suffix drop0 in hsegment.
have hsize : 0 <= size (encode_trace (symbol_list_of_array symbols0)).`2 by
  exact (List.size_ge0 (encode_trace (symbol_list_of_array symbols0)).`2).
have hoffhi : W64.to_uint off <= mode2_hbz_count by smt().
have hstart :
    0 <= W64.to_uint off - 4 /\
    W64.to_uint off - 4 + 4 <= mode2_hbz_capacity.
+ rewrite /mode2_hbz_capacity /mode2_hbz_count.
  smt().
have hsegment4 :
    segment_matches encp (W64.to_uint off - 4 + 4)
      (encode_trace (symbol_list_of_array symbols0)).`2.
+ have -> : W64.to_uint off - 4 + 4 = W64.to_uint off by ring.
  exact hsegment.
have hframe4 :
    prefix_frame enc0 encp (W64.to_uint off - 4 + 4).
+ have -> : W64.to_uint off - 4 + 4 = W64.to_uint off by ring.
  exact hframe.
have hserialized := actual_store_w32_le_prepend_trace_bytes
  enc0 encp (W64.to_uint off - 4) x
  (symbol_list_of_array symbols0)
  hstart hx hsegment4 hframe4.
move: hserialized => [hfull hprefix].
split.
+ smt().
split.
+ rewrite /mode2_hbz_count.
  smt().
split; first exact hfull.
split.
+ rewrite /trace_bytes /serialize32_le /= in hcursor.
  rewrite /trace_bytes /serialize32_le /=.
  smt().
exact hprefix.
qed.

end Mode2RansEncoderFinalization.
