require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  Mode2HbzCodecSpec Mode2RansByteStack Mode2RansArrayListBridge
  Mode2RansEncoderTailInvariant Mode2RansEncoderSerializationComposition
  Mode2RansEncoderFinalization.

theory Mode2RansEncoderGeneratedFinalization.

import Mode2HbzCodecSpec Mode2RansByteStack Mode2RansArrayListBridge
       Mode2RansEncoderTailInvariant Mode2RansEncoderSerializationComposition
       Mode2RansEncoderFinalization.

lemma generated_encoder_final_offset_uint (off : W64.t) :
  4 <= W64.to_uint off =>
  W64.to_uint (off - W64.of_int 4) = W64.to_uint off - 4.
proof.
move=> hoff.
rewrite W64.to_uintB.
+ rewrite W64.uleE W64.of_uintK /=.
  smt().
rewrite W64.of_uintK /=.
trivial.
qed.

lemma generated_encoder_outer_finalize_success
    (enc0 symbols0 encp : BArray2048.t) (x : W32.t) (off : W64.t) :
  encoder_outer_tail_inv enc0 symbols0 encp 0 x off =>
  let returned_off = off - W64.of_int 4 in
  0 <= W64.to_uint returned_off <= 1020 /\
  4 <= mode2_hbz_count - W64.to_uint returned_off <= mode2_hbz_count /\
  segment_matches
    (generated_store_w32_le encp returned_off x)
    (W64.to_uint returned_off)
    (trace_bytes (symbol_list_of_array symbols0)) /\
  W64.to_uint returned_off +
    size (trace_bytes (symbol_list_of_array symbols0)) = mode2_hbz_count /\
  prefix_frame enc0
    (generated_store_w32_le encp returned_off x)
    (W64.to_uint returned_off).
proof.
move=> hout.
have hfinal := encoder_outer_tail_finalize_success
  enc0 symbols0 encp x off hout.
have hoff : 4 <= W64.to_uint off.
+ move: hout.
  rewrite /encoder_outer_tail_inv.
  smt().
have hreturned := generated_encoder_final_offset_uint off hoff.
have hfit :
    0 <= W64.to_uint (off - W64.of_int 4) /\
    W64.to_uint (off - W64.of_int 4) + 4 <= mode2_hbz_capacity.
+ rewrite hreturned /mode2_hbz_capacity /mode2_hbz_count.
  move: hfinal.
  smt().
have hstore := generated_store_w32_le_eq_actual encp
  (off - W64.of_int 4) x hfit.
rewrite /=.
rewrite hstore hreturned.
exact hfinal.
qed.

end Mode2RansEncoderGeneratedFinalization.
