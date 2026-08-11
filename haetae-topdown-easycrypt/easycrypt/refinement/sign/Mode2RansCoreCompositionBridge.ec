require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  Mode2HbzCodecSpec Mode2RansByteStack
  Mode2RansArrayListBridge Mode2RansEncodeRefinement
  Mode2RansDecodeRefinement
  Mode2RansSuffixCopy Mode2RansDecoderCursor
  Mode2RansDecoderCursorSteps Mode2RansDecoderActualTrace.

theory Mode2RansCoreCompositionBridge.

import Mode2HbzCodecSpec Mode2RansByteStack
       Mode2RansArrayListBridge Mode2RansDecodeRefinement
       Mode2RansEncodeRefinement
       Mode2RansSuffixCopy Mode2RansDecoderCursor
       Mode2RansDecoderCursorSteps Mode2RansDecoderActualTrace.

op configured_decoder_state
    (state0 : BArray24.t) (encoded_size : int) : BArray24.t =
  BArray24.set64
    (BArray24.set64
      (BArray24.set64 state0 0 (W64.of_int mode2_hbz_count))
      1 (W64.of_int encoded_size))
    2 (W64.of_int mode2_hbz_alphabet).

lemma flatten_segment_nth (segments : int list list) i k :
  0 <= i < size segments =>
  0 <= k < size (nth [] segments i) =>
  nth 0 (flatten segments)
    (size (flatten (take i segments)) + k) =
  nth 0 (nth [] segments i) k.
proof.
move=> hi hk.
rewrite size_flatten.
exact (nth_flatten [] 0 segments i k hi hk).
qed.

lemma trace_bytes_trace_segment_nth symbols i k :
  0 <= i < size symbols =>
  0 <= k < size (nth [] (trace_segments symbols) i) =>
  nth 0 (trace_bytes symbols) (decoder_cursor symbols i + k) =
  nth 0 (nth [] (trace_segments symbols) i) k.
proof.
move=> hi hk.
have hcursor := decoder_cursor_prefix_size symbols i _; first smt().
have hsegidx : 0 <= i < size (trace_segments symbols).
+ rewrite trace_segments_size.
  exact hi.
have hflat := flatten_segment_nth
  (trace_segments symbols) i k hsegidx hk.
have hge4 : 4 <= decoder_cursor symbols i + k.
+ have hp := size_ge0 (flatten (take i (trace_segments symbols))).
  move: hcursor hk.
  smt().
have hflat_goal :
    nth 0 (flatten (trace_segments symbols))
      (decoder_cursor symbols i + k - 4) =
    nth 0 (nth [] (trace_segments symbols) i) k.
+ rewrite hcursor.
  have -> :
      4 + size (flatten (take i (trace_segments symbols))) + k - 4 =
      size (flatten (take i (trace_segments symbols))) + k by ring.
  exact hflat.
rewrite /trace_bytes nth_cat.
case (decoder_cursor symbols i + k <
      size (serialize32_le (encode_trace symbols).`1)) => hleft.
+ have hser : size (serialize32_le (encode_trace symbols).`1) = 4 by
    rewrite /serialize32_le /=.
  smt().
+ simplify.
  have hser : size (serialize32_le (encode_trace symbols).`1) = 4 by
    rewrite /serialize32_le /=.
  rewrite hser.
  exact hflat_goal.
qed.

lemma copied_suffix_is_exact_trace
    (encoded copied : BArray2048.t)
    (off : int) (trace : int list) :
  segment_matches encoded off trace =>
  slice_eq encoded copied off (size trace) =>
  segment_matches copied 0 trace.
proof.
move=> hencoded hslice.
rewrite /segment_matches in hencoded.
move: hencoded => [hoff [hcap hbytes]].
rewrite /segment_matches.
split; first smt().
split; first smt().
move=> k hk.
rewrite /slice_eq in hslice.
have hcopy := hslice k hk.
have htrace := hbytes k hk.
rewrite hcopy.
exact htrace.
qed.

lemma segment_matches_implies_exact_decoder_segment_input
    (expected_symbols buffer0 : BArray2048.t) :
  segment_matches buffer0 0
    (trace_bytes (symbol_list_of_array expected_symbols)) =>
  exact_decoder_segment_input
    (symbol_list_of_array expected_symbols) buffer0.
proof.
move=> hsegment.
rewrite /exact_decoder_segment_input /decoder_segment_at.
move=> i off hi hoff.
pose syms := symbol_list_of_array expected_symbols.
pose k := off - decoder_cursor syms i.
have hi' : 0 <= i < size syms.
+ rewrite /syms symbol_list_of_array_size.
  exact hi.
have hk : 0 <= k < size (nth [] (trace_segments syms) i).
+ rewrite /k /syms.
  move: hoff.
  smt().
have htrace := trace_bytes_trace_segment_nth syms i k hi' hk.
rewrite (_ : decoder_cursor syms i + k = off) in htrace.
+ rewrite /k; ring.
have hofftrace : 0 <= off < size (trace_bytes syms).
+ have hfinal := decoder_cursor_segment_before_final syms i off hi' _.
  - rewrite /decoder_segment_at.
    exact hoff.
  have hstart := decoder_cursor_bounds syms i _; first smt().
  smt().
rewrite -htrace /syms /k.
move: (segment_matches_nth buffer0 0
  (trace_bytes (symbol_list_of_array expected_symbols))
  off hsegment hofftrace).
rewrite add0z.
trivial.
qed.

lemma segment_matches_implies_decoder_word_reads
    (expected_symbols buffer0 : BArray2048.t)
    (i off : W64.t) :
  segment_matches buffer0 0
    (trace_bytes (symbol_list_of_array expected_symbols)) =>
  0 <= W64.to_uint i < mode2_hbz_count =>
  decoder_word_cursor expected_symbols i <= W64.to_uint off <
    decoder_word_cursor expected_symbols i +
      size (decoder_word_segment expected_symbols i) =>
  decoder_read_byte_eq expected_symbols buffer0 i off.
proof.
move=> hsegment hi hoff.
have hexact := segment_matches_implies_exact_decoder_segment_input
  expected_symbols buffer0 hsegment.
rewrite /exact_decoder_segment_input in hexact.
rewrite /decoder_read_byte_eq /decoder_word_segment
        /decoder_word_index /decoder_word_cursor.
exact (hexact (W64.to_uint i) (W64.to_uint off) hi hoff).
qed.

lemma actual_decoder_input_from_copied_trace
    (expected_symbols copied0 : BArray2048.t)
    (state0 : BArray24.t) (encoded_size : int) :
  mode2_hbz_symbol_stream expected_symbols =>
  encoded_size = size (trace_bytes (symbol_list_of_array expected_symbols)) =>
  4 <= encoded_size <= mode2_hbz_count =>
  segment_matches copied0 0
    (trace_bytes (symbol_list_of_array expected_symbols)) =>
  mode2_decode_state state0 encoded_size =>
  actual_mode2_decoder_trace_input
    expected_symbols copied0 state0 encoded_size.
proof.
move=> hstream hsize hbound hsegment hstate.
move: hstate => [hcount [hsizew hm]].
rewrite /actual_mode2_decoder_trace_input.
split; first exact hstream.
split; first exact hsize.
split; first exact hbound.
split.
+ rewrite hsizew.
  exact (mode2_encoded_size_w64_exact encoded_size hbound).
split; first exact hsegment.
split.
+ move=> i off hi hoff.
  exact (segment_matches_implies_decoder_word_reads
    expected_symbols copied0 i off hsegment hi hoff).
split; first exact hcount.
split; first exact hsizew.
exact hm.
qed.

lemma configured_decoder_state_fields state0 encoded_size :
  4 <= encoded_size <= mode2_hbz_count =>
  mode2_decode_state (configured_decoder_state state0 encoded_size)
    encoded_size.
proof.
move=> _.
rewrite /configured_decoder_state /mode2_decode_state /=.
trivial.
qed.

lemma actual_decoder_input_from_configured_trace
    (expected_symbols copied0 : BArray2048.t)
    (state0 : BArray24.t) (encoded_size : int) :
  mode2_hbz_symbol_stream expected_symbols =>
  encoded_size = size (trace_bytes (symbol_list_of_array expected_symbols)) =>
  4 <= encoded_size <= mode2_hbz_count =>
  segment_matches copied0 0
    (trace_bytes (symbol_list_of_array expected_symbols)) =>
  actual_mode2_decoder_trace_input
    expected_symbols copied0
    (configured_decoder_state state0 encoded_size) encoded_size.
proof.
move=> hstream hsize hbound hsegment.
apply (actual_decoder_input_from_copied_trace
  expected_symbols copied0 (configured_decoder_state state0 encoded_size)
  encoded_size hstream hsize hbound hsegment).
exact (configured_decoder_state_fields state0 encoded_size hbound).
qed.

lemma encoder_success_size_word_bridge offw n :
  0 <= W64.to_uint offw <= 1020 =>
  W64.to_uint offw + n = mode2_hbz_count =>
  W64.to_uint (W64.of_int mode2_hbz_count - offw) = n /\
  W64.of_int mode2_hbz_count - offw = W64.of_int n /\
  4 <= n <= mode2_hbz_count /\
  W64.to_uint offw +
    W64.to_uint (W64.of_int mode2_hbz_count - offw) = mode2_hbz_count /\
  offw = W64.of_int (W64.to_uint offw).
proof.
move=> hoff hsum.
have hoffrange : 0 <= W64.to_uint offw < W64.modulus by
  exact (W64.to_uint_cmp offw).
have hoffw : offw = W64.of_int (W64.to_uint offw).
+ apply W64.to_uint_eq.
  rewrite W64.to_uint_small 1:hoffrange.
  trivial.
have hle : offw \ule W64.of_int mode2_hbz_count.
+ rewrite hoffw W64.uleE W64.of_uintK /mode2_hbz_count /=.
  smt().
have huint :
    W64.to_uint (W64.of_int mode2_hbz_count - offw) =
    mode2_hbz_count - W64.to_uint offw.
+ rewrite W64.to_uintB 1:hle W64.of_uintK /mode2_hbz_count /=.
  trivial.
have hn : n = mode2_hbz_count - W64.to_uint offw by smt().
have hboundn : 4 <= n <= mode2_hbz_count by smt().
split; first by rewrite huint hn.
split.
+ apply (mode2_w64_word_from_encoded_size
    (W64.of_int mode2_hbz_count - offw) n hboundn).
  rewrite huint hn.
  trivial.
split; first exact hboundn.
split; first by rewrite huint; smt().
exact hoffw.
qed.

lemma core_composition_preconditions_satisfiable :
  exists symbols,
    mode2_hbz_symbol_stream symbols.
proof.
exists (BArray2048.init (fun _ => W8.zero)).
rewrite /mode2_hbz_symbol_stream.
move=> i hi.
rewrite BArray2048.initiE 1:/# W8.to_uint0 /mode2_hbz_alphabet.
smt().
qed.

end Mode2RansCoreCompositionBridge.
