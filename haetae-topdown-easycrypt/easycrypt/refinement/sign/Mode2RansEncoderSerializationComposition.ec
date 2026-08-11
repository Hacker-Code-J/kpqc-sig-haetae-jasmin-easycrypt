require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2HbzCodecSpec Mode2RansByteStack
  Mode2RansArrayListBridge Mode2RansEncoderSerialization.

theory Mode2RansEncoderSerializationComposition.

import Mode2HbzCodecSpec Mode2RansByteStack
       Mode2RansArrayListBridge Mode2RansEncoderSerialization.

op generated_store_w32_le
    (a : BArray2048.t) (off : W64.t) (x : W32.t) : BArray2048.t =
  let a = BArray2048.set8 a (W64.to_uint off) (truncateu8 x) in
  let idx = off + W64.one in
  let x1 = x `>>` W8.of_int 8 in
  let a = BArray2048.set8 a (W64.to_uint idx) (truncateu8 x1) in
  let idx = idx + W64.one in
  let x2 = x1 `>>` W8.of_int 8 in
  let a = BArray2048.set8 a (W64.to_uint idx) (truncateu8 x2) in
  let idx = idx + W64.one in
  let x3 = x2 `>>` W8.of_int 8 in
  BArray2048.set8 a (W64.to_uint idx) (truncateu8 x3).

lemma generated_store_w32_le_eq_actual a off x :
  0 <= W64.to_uint off /\
  W64.to_uint off + 4 <= mode2_hbz_capacity =>
  generated_store_w32_le a off x =
    actual_store_w32_le a (W64.to_uint off) x.
proof.
move=> hoff.
rewrite /generated_store_w32_le /actual_store_w32_le /=.
rewrite !W64.to_uintD_small 1:/# 1:/# 1:/# !W64.to_uint1.
trivial.
qed.

lemma actual_store_w32_le_serialized_segment a start x :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  segment_matches
    (actual_store_w32_le a start x)
    start
    (serialize32_le (W32.to_uint x)).
proof.
move=> hstart.
rewrite /segment_matches /serialize32_le /=.
split; first smt().
split; first smt().
move=> k hk.
exact (actual_store_w32_le_get_inside a start x k hstart hk).
qed.

lemma actual_store_w32_le_tail_segment a start x tail :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  segment_matches a (start + 4) tail =>
  segment_matches (actual_store_w32_le a start x) (start + 4) tail.
proof.
move=> hstart htail.
rewrite /segment_matches in htail.
move: htail => [htail0 [htailcap hbytes]].
rewrite /segment_matches.
split; first exact htail0.
split; first exact htailcap.
move=> k hk.
have hj : 0 <= start + 4 + k < mode2_hbz_capacity by smt().
have hout : start + 4 <= start + 4 + k by smt().
rewrite (actual_store_w32_le_get_outside
  a start x (start + 4 + k) hstart hj _).
+ right; exact hout.
exact (hbytes k hk).
qed.

lemma actual_store_w32_le_prepend_segment a start x tail :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  segment_matches a (start + 4) tail =>
  segment_matches
    (actual_store_w32_le a start x)
    start
    (serialize32_le (W32.to_uint x) ++ tail).
proof.
move=> hstart htail.
have hhead := actual_store_w32_le_serialized_segment a start x hstart.
have htail' := actual_store_w32_le_tail_segment a start x tail
  hstart htail.
have hcat := segment_matches_cat
  (actual_store_w32_le a start x)
  start (serialize32_le (W32.to_uint x)) tail hhead _.
+ rewrite /serialize32_le /=.
  exact htail'.
exact hcat.
qed.

lemma actual_store_w32_le_prepend_trace enc0 a start x tail :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  segment_matches a (start + 4) tail =>
  prefix_frame enc0 a (start + 4) =>
  segment_matches
    (actual_store_w32_le a start x)
    start
    (serialize32_le (W32.to_uint x) ++ tail) /\
  prefix_frame enc0 (actual_store_w32_le a start x) start.
proof.
move=> hstart htail hframe.
split.
+ exact (actual_store_w32_le_prepend_segment a start x tail
    hstart htail).
+ exact (actual_store_w32_le_prefix_frame enc0 a start x
    hstart hframe).
qed.

lemma actual_store_w32_le_prepend_trace_bytes
    enc0 a start x symbols :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  W32.to_uint x = (encode_trace symbols).`1 =>
  segment_matches a (start + 4) (encode_trace symbols).`2 =>
  prefix_frame enc0 a (start + 4) =>
  segment_matches
    (actual_store_w32_le a start x)
    start
    (trace_bytes symbols) /\
  prefix_frame enc0 (actual_store_w32_le a start x) start.
proof.
move=> hstart hx htail hframe.
have h := actual_store_w32_le_prepend_trace
  enc0 a start x (encode_trace symbols).`2 hstart htail hframe.
move: h => [hsegment hprefix].
split; last exact hprefix.
rewrite /trace_bytes -encode_trace_bytes_segments -hx.
exact hsegment.
qed.

lemma encoder_serialization_composition_satisfiable :
  exists enc0 a start x symbols,
    0 <= start /\ start + 4 <= mode2_hbz_capacity /\
    W32.to_uint x = (encode_trace symbols).`1 /\
    segment_matches a (start + 4) (encode_trace symbols).`2 /\
    prefix_frame enc0 a (start + 4).
proof.
exists witness witness 0 (W32.of_int rans_initial_state) [].
rewrite /encode_trace /= W32.to_uint_small.
+ rewrite /rans_initial_state; smt().
rewrite /mode2_hbz_capacity.
split; first smt().
split; first trivial.
split.
+ apply segment_matches_nil; smt().
+ exact (prefix_frame_refl witness 4).
qed.

end Mode2RansEncoderSerializationComposition.
