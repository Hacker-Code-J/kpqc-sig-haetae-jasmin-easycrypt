require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansDecodeTarget SignatureUnpackMode2Target
  Mode2HbzCodecSpec Mode2RansByteStack
  Mode2RansEncodeRefinement
  Mode2RansArrayListBridge Mode2RansDecodeRefinement Mode2RansNormalization
  Mode2RansDecoderCursor Mode2RansDecoderWordStep
  Mode2RansDecoderNormalization Mode2RansDecoderCursorSteps
  Mode2RansDecoderActualWord Mode2RansDecoderGeneratedStep.

theory Mode2RansDecoderActualTrace.

import Mode2HbzCodecSpec Mode2RansByteStack
       Mode2RansEncodeRefinement
       Mode2RansArrayListBridge Mode2RansDecodeRefinement Mode2RansNormalization
       Mode2RansDecoderCursor Mode2RansDecoderWordStep
       Mode2RansDecoderNormalization Mode2RansDecoderCursorSteps
       Mode2RansDecoderActualWord Mode2RansDecoderGeneratedStep.

module Decode = RansDecodeTarget.M.

lemma truncateu32_zeroextu64_id (x : W32.t) :
  truncateu32 (zeroextu64 x) = x.
proof.
apply W32.to_uint_eq.
rewrite W2u32.to_uint_truncateu32 W2u32.to_uint_zeroextu64.
rewrite modz_small.
+ exact (W32.to_uint_cmp x).
+ trivial.
qed.

lemma index_lt_to_le i n : 0 <= i < n => 0 <= i <= n.
proof. smt(). qed.

lemma int_sub_self_zero (x : int) : x - x = 0.
proof. ring. qed.

lemma int_add_zero_right (x : int) : x + 0 = x.
proof. ring. qed.

lemma int_sub_self_between_zero (x n : int) :
  0 <= n => 0 <= x - x <= n.
proof. smt(). qed.

lemma int_lt_le_trans (x y z : int) : x < y => y <= z => x < z.
proof. smt(). qed.

lemma mode2_encoded_size_w64_exact encoded_size :
  4 <= encoded_size <= mode2_hbz_count =>
  W64.to_uint (W64.of_int encoded_size) = encoded_size.
proof.
move=> hsize.
have hrange : 0 <= encoded_size < W64.modulus.
+ have hm64 : W64.modulus = 18446744073709551616 by trivial.
  move: hsize.
  rewrite hm64 /mode2_hbz_count.
  smt().
exact (W64.to_uint_small encoded_size hrange).
qed.

lemma mode2_w64_word_from_encoded_size (w : W64.t) encoded_size :
  4 <= encoded_size <= mode2_hbz_count =>
  W64.to_uint w = encoded_size =>
  w = W64.of_int encoded_size.
proof.
move=> hbound huint.
apply W64.to_uint_eq.
have hexact := mode2_encoded_size_w64_exact encoded_size hbound.
smt().
qed.

lemma w64_ult_from_uint_bound wleft wright n :
  W64.to_uint wright = n =>
  W64.to_uint wleft < n =>
  wleft \ult wright.
proof.
move=> hright hlt.
rewrite W64.ultE hright.
exact hlt.
qed.

lemma mode2_encoded_size_ult_all encoded_size :
  4 <= encoded_size <= mode2_hbz_count =>
  forall w, W64.to_uint w < encoded_size =>
    w \ult W64.of_int encoded_size.
proof.
move=> hsize w hlt.
exact (w64_ult_from_uint_bound w (W64.of_int encoded_size) encoded_size
  (mode2_encoded_size_w64_exact encoded_size hsize) hlt).
qed.

lemma decoder_cursor_self_interval expected j :
  0 <=
    decoder_cursor (symbol_list_of_array expected) j -
      decoder_cursor (symbol_list_of_array expected) j <=
    size (decoder_segment_at (symbol_list_of_array expected) j).
proof.
have hn := size_ge0
  (decoder_segment_at (symbol_list_of_array expected) j).
smt().
qed.

lemma decoder_cursor_plus_zero expected j :
  decoder_cursor (symbol_list_of_array expected) j =
  decoder_cursor (symbol_list_of_array expected) j + 0.
proof. ring. qed.

lemma decoder_cursor_self_zero expected j :
  decoder_cursor (symbol_list_of_array expected) j -
    decoder_cursor (symbol_list_of_array expected) j = 0.
proof. ring. qed.

lemma decoder_segment_state_at expected j :
  mode2_hbz_symbol_stream expected =>
  0 <= j < mode2_hbz_count =>
  decoder_segment_at (symbol_list_of_array expected) j =
    mode2_normalization_bytes
      (decoder_state_at (symbol_list_of_array expected) (j + 1))
      (W8.to_uint (BArray2048.get8 expected j)).
proof.
move=> hstream hj.
rewrite (decoder_state_at_symbol_suffix expected (j + 1) _); first smt().
exact (decoder_segment_symbol_suffix expected j hstream hj).
qed.

op exact_decoder_segment_input
    (syms : int list) (buffer0 : BArray2048.t) : bool =
  forall i off,
    0 <= i < mode2_hbz_count =>
    decoder_cursor syms i <= off <
      decoder_cursor syms i + size (decoder_segment_at syms i) =>
    W8.to_uint (BArray2048.get8 buffer0 off) =
      nth 0 (decoder_segment_at syms i) (off - decoder_cursor syms i).

op decoder_word_cursor (expected_symbols : BArray2048.t) (i : W64.t) : int =
  decoder_cursor (symbol_list_of_array expected_symbols) (W64.to_uint i).

op decoder_word_segment
    (expected_symbols : BArray2048.t) (i : W64.t) : int list =
  decoder_segment_at
    (symbol_list_of_array expected_symbols) (W64.to_uint i).

op decoder_word_index
    (expected_symbols : BArray2048.t) (i off : W64.t) : int =
  W64.to_uint off - decoder_word_cursor expected_symbols i.

op decoder_read_byte_eq
    (expected_symbols buffer : BArray2048.t) (i off : W64.t) : bool =
  W8.to_uint (BArray2048.get8 buffer (W64.to_uint off)) =
    nth 0 (decoder_word_segment expected_symbols i)
      (decoder_word_index expected_symbols i off).

op actual_mode2_decoder_trace_input
    (expected_symbols buffer0 : BArray2048.t)
    (state0 : BArray24.t) (encoded_size : int) : bool =
  mode2_hbz_symbol_stream expected_symbols /\
  encoded_size = size (trace_bytes (symbol_list_of_array expected_symbols)) /\
  4 <= encoded_size <= mode2_hbz_count /\
  W64.to_uint (BArray24.get64 state0 1) = encoded_size /\
  segment_matches buffer0 0
    (trace_bytes (symbol_list_of_array expected_symbols)) /\
  (forall (i off : W64.t),
    0 <= W64.to_uint i < mode2_hbz_count =>
    decoder_word_cursor expected_symbols i <= W64.to_uint off <
      decoder_word_cursor expected_symbols i +
        size (decoder_word_segment expected_symbols i) =>
    decoder_read_byte_eq expected_symbols buffer0 i off) /\
  BArray24.get64 state0 0 = W64.of_int mode2_hbz_count /\
  BArray24.get64 state0 1 = W64.of_int encoded_size /\
  BArray24.get64 state0 2 = W64.of_int mode2_hbz_alphabet.

lemma actual_decoder_input_read_byte
    expected_symbols buffer0 state0 encoded_size i off :
  actual_mode2_decoder_trace_input
    expected_symbols buffer0 state0 encoded_size =>
  0 <= W64.to_uint i < mode2_hbz_count =>
  decoder_word_cursor expected_symbols i <= W64.to_uint off <
    decoder_word_cursor expected_symbols i +
      size (decoder_word_segment expected_symbols i) =>
  decoder_read_byte_eq expected_symbols buffer0 i off.
proof.
move=> hinput hi hoff.
rewrite /actual_mode2_decoder_trace_input in hinput.
move: hinput => [_ [_ [_ [_ [_ [hbytes _]]]]]].
exact (hbytes i off hi hoff).
qed.

op generated_decoder_parse32 (buffer : BArray2048.t) : W32.t =
  (((zeroextu32 (BArray2048.get8 buffer 0) `|`
      (zeroextu32 (BArray2048.get8 buffer 1) `<<` W8.of_int 8)) `|`
      (zeroextu32 (BArray2048.get8 buffer 2) `<<` W8.of_int 16)) `|`
      (zeroextu32 (BArray2048.get8 buffer 3) `<<` W8.of_int 24)).

op decoder_outer_trace_live
    (decoded0 expected_symbols buffer0 : BArray2048.t)
    (state0 : BArray24.t) (encoded_size : int)
    (symsp : BArray2048.t) (statep : BArray24.t)
    (bufp symbolwp : BArray2048.t) (dsymswp : BArray528.t)
    (count size_in m bad i off : W64.t) (x : W32.t) : bool =
  let syms = symbol_list_of_array expected_symbols in
  actual_mode2_decoder_trace_input
    expected_symbols buffer0 state0 encoded_size /\
  statep = state0 /\
  bufp = buffer0 /\
  symbolwp = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words /\
  dsymswp = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words /\
  count = W64.of_int mode2_hbz_count /\
  size_in = BArray24.get64 state0 1 /\
  m = W64.of_int mode2_hbz_alphabet /\
  bad = W64.zero /\
  0 <= W64.to_uint i <= mode2_hbz_count /\
  x = W32.of_int (decoder_state_at syms (W64.to_uint i)) /\
  W64.to_uint off = decoder_cursor syms (W64.to_uint i) /\
  decoded_symbol_prefix symsp expected_symbols (W64.to_uint i) /\
  decoded_symbol_tail_frame decoded0 symsp (W64.to_uint i).

op decoder_trace_bindings
    (expected_symbols buffer0 : BArray2048.t)
    (state0 : BArray24.t) (encoded_size : int)
    (statep : BArray24.t) (bufp symbolwp : BArray2048.t)
    (dsymswp : BArray528.t) (count size_in m bad : W64.t) : bool =
  actual_mode2_decoder_trace_input
    expected_symbols buffer0 state0 encoded_size /\
  statep = state0 /\
  bufp = buffer0 /\
  symbolwp = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words /\
  dsymswp = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words /\
  count = W64.of_int mode2_hbz_count /\
  size_in = BArray24.get64 state0 1 /\
  m = W64.of_int mode2_hbz_alphabet /\
  bad = W64.zero.

op decoder_inner_math
    (expected_symbols : BArray2048.t)
    (i off again : W64.t) (x : W32.t) : bool =
  let syms = symbol_list_of_array expected_symbols in
  let j = W64.to_uint i in
  let s = W8.to_uint (BArray2048.get8 expected_symbols j) in
  let tail_state = decoder_state_at syms (j + 1) in
  let segment = decoder_segment_at syms j in
  let k = W64.to_uint off - decoder_cursor syms j in
  0 <= j < mode2_hbz_count /\
  segment = mode2_normalization_bytes tail_state s /\
  0 <= k <= size segment /\
  W64.to_uint off = decoder_cursor syms j + k /\
  x = W32.of_int (decoder_replay_prefix tail_state s k) /\
  (again = W64.zero => k = size segment).

lemma decoder_inner_math_components expected i off again x :
  0 <= W64.to_uint i < mode2_hbz_count =>
  decoder_segment_at (symbol_list_of_array expected) (W64.to_uint i) =
    mode2_normalization_bytes
      (decoder_state_at (symbol_list_of_array expected) (W64.to_uint i + 1))
      (W8.to_uint (BArray2048.get8 expected (W64.to_uint i))) =>
  0 <= W64.to_uint off -
      decoder_cursor (symbol_list_of_array expected) (W64.to_uint i) <=
    size (decoder_segment_at
      (symbol_list_of_array expected) (W64.to_uint i)) =>
  W64.to_uint off =
    decoder_cursor (symbol_list_of_array expected) (W64.to_uint i) +
      (W64.to_uint off -
       decoder_cursor (symbol_list_of_array expected) (W64.to_uint i)) =>
  x = W32.of_int
    (decoder_replay_prefix
      (decoder_state_at (symbol_list_of_array expected) (W64.to_uint i + 1))
      (W8.to_uint (BArray2048.get8 expected (W64.to_uint i)))
      (W64.to_uint off -
       decoder_cursor (symbol_list_of_array expected) (W64.to_uint i))) =>
  (again = W64.zero =>
    W64.to_uint off -
      decoder_cursor (symbol_list_of_array expected) (W64.to_uint i) =
    size (decoder_segment_at
      (symbol_list_of_array expected) (W64.to_uint i))) =>
  decoder_inner_math expected i off again x.
proof.
move=> hj hsegment hk hoff hx hagain.
rewrite /decoder_inner_math /=.
split; first exact hj.
split; first exact hsegment.
split; first exact hk.
split; first exact hoff.
split; first exact hx.
exact hagain.
qed.

op decoder_inner_trace_live
    (decoded0 expected_symbols buffer0 : BArray2048.t)
    (state0 : BArray24.t) (encoded_size : int)
    (symsp : BArray2048.t) (statep : BArray24.t)
    (bufp symbolwp : BArray2048.t) (dsymswp : BArray528.t)
    (count size_in m bad i off again : W64.t) (x : W32.t) : bool =
  decoder_trace_bindings expected_symbols buffer0 state0 encoded_size
    statep bufp symbolwp dsymswp count size_in m bad /\
  decoder_inner_math expected_symbols i off again x /\
  decoded_symbol_prefix symsp expected_symbols (W64.to_uint i + 1) /\
  decoded_symbol_tail_frame decoded0 symsp (W64.to_uint i + 1).

lemma decoder_inner_trace_live_components
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off again x :
  decoder_trace_bindings expected_symbols buffer0 state0 encoded_size
    statep bufp symbolwp dsymswp count size_in m bad =>
  decoder_inner_math expected_symbols i off again x =>
  decoded_symbol_prefix symsp expected_symbols (W64.to_uint i + 1) =>
  decoded_symbol_tail_frame decoded0 symsp (W64.to_uint i + 1) =>
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off again x.
proof.
move=> hbindings hmath hprefix htail.
rewrite /decoder_inner_trace_live.
split; first exact hbindings.
split; first exact hmath.
split; first exact hprefix.
exact htail.
qed.

lemma decoded_symbol_tail_frame_weaken before after small large :
  small <= large =>
  decoded_symbol_tail_frame before after small =>
  decoded_symbol_tail_frame before after large.
proof.
rewrite /decoded_symbol_tail_frame => hle hframe i hi.
apply hframe; smt().
qed.

lemma decoder_lane01_disjoint (b0 b1 : W8.t) :
  zeroextu32 b0 `&` (zeroextu32 b1 `<<` W8.of_int 8) = W32.zero.
proof.
apply W32.wordP => bit hbit.
rewrite W32.andwE /(`<<`) W32.shlwE.
rewrite W8.of_uintK /= !W4u8.zeroextu32_bit.
smt().
qed.

lemma decoder_lane012_disjoint (b0 b1 b2 : W8.t) :
  (zeroextu32 b0 `|` (zeroextu32 b1 `<<` W8.of_int 8)) `&`
    (zeroextu32 b2 `<<` W8.of_int 16) = W32.zero.
proof.
apply W32.wordP => bit hbit.
rewrite W32.andwE W32.orwE /(`<<`) W32.shlwE.
rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
smt().
qed.

lemma decoder_lane0123_disjoint (b0 b1 b2 b3 : W8.t) :
  ((zeroextu32 b0 `|` (zeroextu32 b1 `<<` W8.of_int 8)) `|`
    (zeroextu32 b2 `<<` W8.of_int 16)) `&`
    (zeroextu32 b3 `<<` W8.of_int 24) = W32.zero.
proof.
apply W32.wordP => bit hbit.
rewrite W32.andwE !W32.orwE /(`<<`) W32.shlwE.
rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
smt().
qed.

lemma w8_uint_lt_256 (b : W8.t) : W8.to_uint b < 256.
proof.
have h := W8.to_uint_cmp b.
move: h.
simplify.
smt().
qed.

lemma generated_decoder_parse32_uint buffer :
  W32.to_uint (generated_decoder_parse32 buffer) =
  parse32_le
    [W8.to_uint (BArray2048.get8 buffer 0);
     W8.to_uint (BArray2048.get8 buffer 1);
     W8.to_uint (BArray2048.get8 buffer 2);
     W8.to_uint (BArray2048.get8 buffer 3)].
proof.
rewrite /generated_decoder_parse32 /parse32_le /byte_radix /=.
rewrite W32.to_uint_orw_disjoint.
+ exact (decoder_lane0123_disjoint
    (BArray2048.get8 buffer 0) (BArray2048.get8 buffer 1)
    (BArray2048.get8 buffer 2) (BArray2048.get8 buffer 3)).
rewrite W32.to_uint_orw_disjoint.
+ exact (decoder_lane012_disjoint
    (BArray2048.get8 buffer 0) (BArray2048.get8 buffer 1)
    (BArray2048.get8 buffer 2)).
rewrite W32.to_uint_orw_disjoint.
+ exact (decoder_lane01_disjoint
    (BArray2048.get8 buffer 0) (BArray2048.get8 buffer 1)).
rewrite W4u8.to_uint_zeroextu32.
rewrite !W32.to_uint_shl 1:/# 1:/# 1:/#.
rewrite !W4u8.to_uint_zeroextu32 !W8.of_uintK /=.
have hb1 := w8_uint_lt_256 (BArray2048.get8 buffer 1).
have hb2 := w8_uint_lt_256 (BArray2048.get8 buffer 2).
have hb3 := w8_uint_lt_256 (BArray2048.get8 buffer 3).
have hb1l := W8.to_uint_cmp (BArray2048.get8 buffer 1).
have hb2l := W8.to_uint_cmp (BArray2048.get8 buffer 2).
have hb3l := W8.to_uint_cmp (BArray2048.get8 buffer 3).
rewrite !modz_small 1:/# 1:/# 1:/#.
ring.
qed.

lemma generated_decoder_parse32_from_trace buffer expected_symbols :
  mode2_hbz_symbol_stream expected_symbols =>
  segment_matches buffer 0
    (trace_bytes (symbol_list_of_array expected_symbols)) =>
  generated_decoder_parse32 buffer =
    W32.of_int
      (decoder_state_at (symbol_list_of_array expected_symbols) 0).
proof.
move=> hstream hsegment.
have hcan := mode2_stream_canonical_list expected_symbols hstream.
have hparse := decoder_parse32_from_trace buffer
  (symbol_list_of_array expected_symbols) hcan hsegment.
have hbound := encode_trace_state_bounds
  (symbol_list_of_array expected_symbols) hcan.
apply W32.to_uint_eq.
rewrite generated_decoder_parse32_uint hparse decoder_state_start.
rewrite W32.to_uint_small.
+ have hm : W32.modulus = 4294967296 by trivial.
  smt().
trivial.
qed.

lemma decoder_state_at_mode2_bounds expected_symbols i :
  mode2_hbz_symbol_stream expected_symbols =>
  0 <= i <= mode2_hbz_count =>
  rans_initial_state <=
    decoder_state_at (symbol_list_of_array expected_symbols) i < 2147483648.
proof.
move=> hstream hi.
case (i = mode2_hbz_count) => hlast.
+ rewrite hlast.
  have hsize := symbol_list_of_array_size expected_symbols.
  rewrite -hsize decoder_state_final /rans_initial_state.
  smt().
+ have hstrict : 0 <= i < mode2_hbz_count by smt().
  rewrite /decoder_state_at.
  rewrite (trace_states_nth_drop
    (symbol_list_of_array expected_symbols) i _).
  - rewrite symbol_list_of_array_size; exact hstrict.
  rewrite -/symbol_suffix.
  exact (encode_trace_state_bounds
    (symbol_suffix expected_symbols i)
    (canonical_symbol_suffix expected_symbols i hstream _)); smt().
qed.

lemma decoder_state_at_word_exact expected_symbols i :
  mode2_hbz_symbol_stream expected_symbols =>
  0 <= i <= mode2_hbz_count =>
  W32.to_uint
    (W32.of_int
      (decoder_state_at (symbol_list_of_array expected_symbols) i)) =
  decoder_state_at (symbol_list_of_array expected_symbols) i.
proof.
move=> hstream hi.
have hb := decoder_state_at_mode2_bounds expected_symbols i hstream hi.
rewrite W32.to_uint_small.
+ have hm : W32.modulus = 4294967296 by trivial.
  smt().
trivial.
qed.

lemma generated_decoder_parse32_mode2_bounds buffer expected_symbols :
  mode2_hbz_symbol_stream expected_symbols =>
  segment_matches buffer 0
    (trace_bytes (symbol_list_of_array expected_symbols)) =>
  rans_initial_state <= W32.to_uint (generated_decoder_parse32 buffer) <
    2147483648.
proof.
move=> hstream hsegment.
have hparse := generated_decoder_parse32_from_trace
  buffer expected_symbols hstream hsegment.
have hbound := decoder_state_at_mode2_bounds expected_symbols 0
  hstream _; first smt().
have hword := decoder_state_at_word_exact expected_symbols 0
  hstream _; first smt().
rewrite hparse hword.
exact hbound.
qed.

lemma generated_decoder_parse32_no_low_reject buffer expected_symbols :
  mode2_hbz_symbol_stream expected_symbols =>
  segment_matches buffer 0
    (trace_bytes (symbol_list_of_array expected_symbols)) =>
  !(zeroextu64 (generated_decoder_parse32 buffer) \ult
    W64.of_int rans_initial_state).
proof.
move=> hstream hsegment.
have hbound := generated_decoder_parse32_mode2_bounds
  buffer expected_symbols hstream hsegment.
rewrite W64.ultE W2u32.to_uint_zeroextu64 W64.of_uintK.
rewrite /rans_initial_state.
smt().
qed.

lemma generated_decoder_parse32_no_high_reject buffer expected_symbols :
  mode2_hbz_symbol_stream expected_symbols =>
  segment_matches buffer 0
    (trace_bytes (symbol_list_of_array expected_symbols)) =>
  !((W64.one `<<` W8.of_int 31) \ule
    zeroextu64 (generated_decoder_parse32 buffer)).
proof.
move=> hstream hsegment.
have hbound := generated_decoder_parse32_mode2_bounds
  buffer expected_symbols hstream hsegment.
rewrite W64.uleE W2u32.to_uint_zeroextu64.
rewrite /(`<<`) W64.to_uint_shl 1:/# W64.to_uint1 W8.of_uintK /=.
smt().
qed.

lemma decoder_outer_generated_low_word
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  W64.to_uint i < mode2_hbz_count =>
  W32.to_uint (generated_decoder_lookup_word x `&` W32.of_int 65535) =
    W8.to_uint (BArray2048.get8 expected_symbols (W64.to_uint i)).
proof.
move=> hlive hi.
have hcopy := hlive.
rewrite /decoder_outer_trace_live /= in hcopy.
move: hcopy =>
  [hinput [_ [_ [_ [_ [_ [_ [_ [_ [hib [hx [_ [_ _]]]]]]]]]]]]].
have hstream : mode2_hbz_symbol_stream expected_symbols by
  move: hinput; rewrite /actual_mode2_decoder_trace_input; smt().
rewrite hx.
apply (generated_decoder_low_word_expected
  expected_symbols (W64.to_uint i) hstream).
have hi0 := W64.to_uint_cmp i.
smt().
qed.

lemma decoder_outer_guard_index
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x cond :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  cond = (i \ult count) =>
  cond =>
  W64.to_uint i < mode2_hbz_count.
proof.
move=> hlive hguard hcond.
have hcopy := hlive.
rewrite /decoder_outer_trace_live /= in hcopy.
move: hcopy => [_ [_ [_ [_ [_ [hcount _]]]]]].
have hcount_uint : W64.to_uint count = mode2_hbz_count.
+ rewrite hcount W64.of_uintK.
  have hsmall : 0 <= mode2_hbz_count < W64.modulus.
  - rewrite /mode2_hbz_count.
    have hm : W64.modulus = 18446744073709551616 by trivial.
    smt().
  rewrite modz_small; exact hsmall.
move: hcond.
rewrite hguard W64.ultE hcount_uint.
trivial.
qed.

lemma decoder_outer_generated_symbol_word
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  W64.to_uint i < mode2_hbz_count =>
  W64.to_uint
    (zeroextu64
      (generated_decoder_lookup_word x `&` W32.of_int 65535)) =
  W8.to_uint (BArray2048.get8 expected_symbols (W64.to_uint i)).
proof.
move=> hlive hi.
rewrite W2u32.to_uint_zeroextu64.
exact (decoder_outer_generated_low_word
  decoded0 expected_symbols buffer0 state0 encoded_size
  symsp statep bufp symbolwp dsymswp count size_in m bad i off x
  hlive hi).
qed.

lemma decoder_outer_loaded_symbol_below_m
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x tmp64 :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  W64.to_uint i < mode2_hbz_count =>
  tmp64 = zeroextu64
    (generated_decoder_lookup_word_from symbolwp x `&` W32.of_int 65535) =>
  !(m \ule tmp64).
proof.
move=> hlive hi htmp.
have hcopy := hlive.
rewrite /decoder_outer_trace_live /= in hcopy.
move: hcopy =>
  [hinput [_ [_ [htable [_ [_ [_ [hm _]]]]]]]].
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy => [hstream _].
have hs := hstream (W64.to_uint i) _.
+ have hi0 := W64.to_uint_cmp i.
  smt().
have hfrom := generated_decoder_lookup_word_from_mode2 symbolwp x htable.
have hword := decoder_outer_generated_symbol_word
  decoded0 expected_symbols buffer0 state0 encoded_size
  symsp statep bufp symbolwp dsymswp count size_in m bad i off x
  hlive hi.
have htmp_uint :
    W64.to_uint tmp64 =
    W8.to_uint (BArray2048.get8 expected_symbols (W64.to_uint i)).
+ rewrite htmp hfrom.
  exact hword.
rewrite W64.uleE hm W64.of_uintK /= /mode2_hbz_alphabet.
move: hs htmp_uint.
smt().
qed.

lemma decoder_outer_loaded_symbol_byte_bound
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x tmp64 :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  W64.to_uint i < mode2_hbz_count =>
  tmp64 = zeroextu64
    (generated_decoder_lookup_word_from symbolwp x `&` W32.of_int 65535) =>
  W64.to_uint tmp64 < W8.modulus.
proof.
move=> hlive hi htmp.
have hcopy := hlive.
rewrite /decoder_outer_trace_live /= in hcopy.
move: hcopy =>
  [_ [_ [_ [htable _]]]].
have hfrom := generated_decoder_lookup_word_from_mode2 symbolwp x htable.
have hword := decoder_outer_generated_symbol_word
  decoded0 expected_symbols buffer0 state0 encoded_size
  symsp statep bufp symbolwp dsymswp count size_in m bad i off x
  hlive hi.
have heq :
    W64.to_uint tmp64 =
    W8.to_uint (BArray2048.get8 expected_symbols (W64.to_uint i)).
+ rewrite htmp hfrom.
  exact hword.
have [_ hbyte] := W8.to_uint_cmp
  (BArray2048.get8 expected_symbols (W64.to_uint i)).
rewrite heq.
exact hbyte.
qed.

lemma generated_decoder_word_update_at_trace expected_symbols i x :
  mode2_hbz_symbol_stream expected_symbols =>
  0 <= i < mode2_hbz_count =>
  x = W32.of_int
    (decoder_state_at (symbol_list_of_array expected_symbols) i) =>
  generated_decoder_word_update x (BArray2048.get8 expected_symbols i) =
    W32.of_int
      (decoder_replay_prefix
        (decoder_state_at (symbol_list_of_array expected_symbols) (i + 1))
        (W8.to_uint (BArray2048.get8 expected_symbols i)) 0).
proof.
move=> hstream hi hx.
pose s := W8.to_uint (BArray2048.get8 expected_symbols i).
pose tail := symbol_suffix expected_symbols (i + 1).
have hs : 0 <= s < mode2_hbz_alphabet by
  rewrite /s; exact (hstream i hi).
have htailcan : canonical_symbol_list tail.
+ rewrite /tail.
  apply (canonical_symbol_suffix expected_symbols (i + 1) hstream).
  smt().
have hstate_bound := decoder_state_at_mode2_bounds expected_symbols i
  hstream _; first smt().
have hstate_word := decoder_state_at_word_exact expected_symbols i
  hstream _; first smt().
have hslot := decoder_state_expected_slot_interval expected_symbols i
  hstream hi.
have hword := generated_decoder_word_update_matches x
  (BArray2048.get8 expected_symbols i) _ _ _.
+ rewrite /s in hs; smt().
+ rewrite hx hstate_word; exact hstate_bound.
+ rewrite hx hstate_word; exact hslot.
have hcur_suffix := decoder_state_at_symbol_suffix expected_symbols i _;
  first smt().
have hnext_suffix := decoder_state_at_symbol_suffix expected_symbols (i + 1) _;
  first smt().
have hcons := symbol_suffix_cons expected_symbols i hi.
have hdecode := trace_head_decodes_to_reduced s tail hs htailcan.
rewrite /s /tail in hdecode.
rewrite -hcons in hdecode.
rewrite -hcur_suffix -hnext_suffix in hdecode.
rewrite hword decoder_replay_zero.
rewrite hx hstate_word.
congr.
exact hdecode.
qed.

lemma decoder_outer_to_inner_trace
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  W64.to_uint i < mode2_hbz_count =>
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size
    (BArray2048.set8 symsp (W64.to_uint i)
      (BArray2048.get8 expected_symbols (W64.to_uint i)))
    statep bufp symbolwp dsymswp count size_in m bad i off W64.one
    (generated_decoder_word_update x
      (BArray2048.get8 expected_symbols (W64.to_uint i))).
proof.
move=> houter hi.
have hcopy := houter.
rewrite /decoder_outer_trace_live /= in hcopy.
move: hcopy =>
  [hinput [hstate [hbuf [htable [hdtable [hcount [hsize [hm
   [hbad [hib [hx [hoff [hprefix htail]]]]]]]]]]]]].
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy =>
  [hstream [hencsize [hsizebound [_ [hglobal [hsegs
   [hstate_count [hstate_size hstate_m]]]]]]]].
pose j := W64.to_uint i.
pose s := W8.to_uint (BArray2048.get8 expected_symbols j).
pose syms := symbol_list_of_array expected_symbols.
pose tail_state := decoder_state_at syms (j + 1).
have hj : 0 <= j < mode2_hbz_count by
  rewrite /j; have := W64.to_uint_cmp i; smt().
have hs : 0 <= s < mode2_hbz_alphabet by
  rewrite /s /j; exact (hstream (W64.to_uint i) hj).
have hprefix' := decoded_symbol_prefix_step symsp expected_symbols j hj hprefix.
have htail_weaken := decoded_symbol_tail_frame_weaken
  decoded0 symsp j (j + 1) _ htail; first smt().
have htail' := decoded_symbol_tail_frame_set_before
  decoded0 symsp (j + 1) j
  (BArray2048.get8 expected_symbols j) _ htail_weaken; first smt().
have hbindings :
    decoder_trace_bindings expected_symbols buffer0 state0 encoded_size
      statep bufp symbolwp dsymswp count size_in m bad.
+ rewrite /decoder_trace_bindings.
  split; first exact hinput.
  split; first exact hstate.
  split; first exact hbuf.
  split; first exact htable.
  split; first exact hdtable.
  split; first exact hcount.
  split; first exact hsize.
  split; first exact hm.
  exact hbad.
have hmath :
    decoder_inner_math expected_symbols i off W64.one
      (generated_decoder_word_update x
        (BArray2048.get8 expected_symbols j)).
+ have hsegment2 := decoder_segment_state_at expected_symbols j hstream hj.
  have hk0 :
      0 <= W64.to_uint off -
          decoder_cursor (symbol_list_of_array expected_symbols)
            (W64.to_uint i) <=
        size (decoder_segment_at (symbol_list_of_array expected_symbols)
          (W64.to_uint i)).
  - rewrite hoff.
    exact (decoder_cursor_self_interval expected_symbols j).
  have hoff0 :
      W64.to_uint off =
        decoder_cursor (symbol_list_of_array expected_symbols)
          (W64.to_uint i) +
        (W64.to_uint off -
          decoder_cursor (symbol_list_of_array expected_symbols)
            (W64.to_uint i)).
  - rewrite hoff (decoder_cursor_self_zero expected_symbols j).
    exact (decoder_cursor_plus_zero expected_symbols j).
  have hx0 :
      generated_decoder_word_update x
        (BArray2048.get8 expected_symbols j) =
      W32.of_int
        (decoder_replay_prefix
          (decoder_state_at (symbol_list_of_array expected_symbols)
            (W64.to_uint i + 1))
          (W8.to_uint
            (BArray2048.get8 expected_symbols (W64.to_uint i)))
          (W64.to_uint off -
            decoder_cursor (symbol_list_of_array expected_symbols)
              (W64.to_uint i))).
  - rewrite hoff (decoder_cursor_self_zero expected_symbols j).
    exact (generated_decoder_word_update_at_trace
      expected_symbols j x hstream hj hx).
  have hagain0 :
      W64.one = W64.zero =>
      W64.to_uint off -
        decoder_cursor (symbol_list_of_array expected_symbols)
          (W64.to_uint i) =
      size (decoder_segment_at (symbol_list_of_array expected_symbols)
        (W64.to_uint i)).
  - move=> honezero.
    have hcontra : W64.to_uint W64.one = W64.to_uint W64.zero by
      rewrite honezero.
    rewrite W64.to_uint1 W64.to_uint0 in hcontra.
    smt().
  exact (decoder_inner_math_components expected_symbols i off W64.one
    (generated_decoder_word_update x
      (BArray2048.get8 expected_symbols j))
    hj hsegment2 hk0 hoff0 hx0 hagain0).
have hresult := decoder_inner_trace_live_components
  decoded0 expected_symbols buffer0 state0 encoded_size
  (BArray2048.set8 symsp j (BArray2048.get8 expected_symbols j))
  statep bufp symbolwp dsymswp count size_in m bad i off W64.one
  (generated_decoder_word_update x (BArray2048.get8 expected_symbols j))
  hbindings hmath hprefix' htail'.
rewrite /j in hresult.
exact hresult.
qed.

lemma decoder_outer_to_inner_trace_loaded
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  W64.to_uint i < mode2_hbz_count =>
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size
    (BArray2048.set8 symsp (W64.to_uint i)
      (generated_decoder_symbol_from symbolwp x))
    statep bufp symbolwp dsymswp count size_in m bad i off W64.one
    (generated_decoder_word_update_from dsymswp x
      (generated_decoder_symbol_from symbolwp x)).
proof.
move=> houter hi.
have hcopy := houter.
rewrite /decoder_outer_trace_live /= in hcopy.
move: hcopy =>
  [hinput [_ [_ [hsymbol_table [hdsyms_table [_ [_ [_ [_ [_ [hx _]]]]]]]]]]].
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy => [hstream _].
have hi0 : 0 <= W64.to_uint i < mode2_hbz_count.
+ have hu := W64.to_uint_cmp i; smt().
have hsymbol :
    generated_decoder_symbol_from symbolwp x =
    BArray2048.get8 expected_symbols (W64.to_uint i).
+ rewrite (generated_decoder_symbol_from_mode2 symbolwp x hsymbol_table).
  rewrite hx.
  exact (generated_decoder_symbol_expected expected_symbols
    (W64.to_uint i) hstream hi0).
have hupdate :
    generated_decoder_word_update_from dsymswp x
      (generated_decoder_symbol_from symbolwp x) =
    generated_decoder_word_update x
      (BArray2048.get8 expected_symbols (W64.to_uint i)).
+ rewrite (generated_decoder_word_update_from_mode2 dsymswp x
      (generated_decoder_symbol_from symbolwp x) hdsyms_table).
  rewrite hsymbol.
  trivial.
rewrite hupdate hsymbol.
exact (decoder_outer_to_inner_trace
  decoded0 expected_symbols buffer0 state0 encoded_size
  symsp statep bufp symbolwp dsymswp count size_in m bad i off x
  houter hi).
qed.

lemma decoder_outer_to_inner_trace_actual_loaded
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x tmp64 :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  W64.to_uint i < mode2_hbz_count =>
  tmp64 = zeroextu64
    (generated_decoder_lookup_word_from symbolwp x `&` W32.of_int 65535) =>
  W64.to_uint tmp64 < W8.modulus =>
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size
    (BArray2048.set8 symsp (W64.to_uint i) (truncateu8 tmp64))
    statep bufp symbolwp dsymswp count size_in m bad i off W64.one
    (let packed = BArray528.get32 dsymswp (W64.to_uint tmp64) in
     (((x `>>` W8.of_int 10) * (packed `>>` W8.of_int 16)) +
       (x `&` W32.of_int 1023)) -
       (packed `&` W32.of_int 65535)).
proof.
move=> houter hi htmp htmp_bound.
have hloaded := decoder_outer_to_inner_trace_loaded
  decoded0 expected_symbols buffer0 state0 encoded_size
  symsp statep bufp symbolwp dsymswp count size_in m bad i off x
  houter hi.
have hsymbol :
    truncateu8 tmp64 = generated_decoder_symbol_from symbolwp x.
+ rewrite htmp /generated_decoder_symbol_from.
  trivial.
have hindex :
    W64.to_uint tmp64 =
    W8.to_uint (generated_decoder_symbol_from symbolwp x).
+ rewrite -hsymbol W8u8.to_uint_truncateu8.
  rewrite modz_small.
  - have [htmp0 _] := W64.to_uint_cmp tmp64.
    rewrite /absz W8.ge0_modulus /=.
    split; first exact htmp0.
    move=> _; exact htmp_bound.
  - trivial.
have hpacked :
    BArray528.get32 dsymswp (W64.to_uint tmp64) =
    BArray528.get32 dsymswp
      (W8.to_uint (generated_decoder_symbol_from symbolwp x)).
+ rewrite hindex.
  trivial.
rewrite hpacked hsymbol.
rewrite /generated_decoder_word_update_from in hloaded.
exact hloaded.
qed.

lemma decoder_inner_math_guard_exact
    expected_symbols i off again x :
  mode2_hbz_symbol_stream expected_symbols =>
  decoder_inner_math expected_symbols i off again x =>
  (W32.to_uint x < rans_initial_state <=>
   decoder_word_index expected_symbols i off <
     size (decoder_word_segment expected_symbols i)).
proof.
move=> hstream hmath.
rewrite /decoder_inner_math /= in hmath.
move: hmath => [hj [hsegment [hk [_ [hx _]]]]].
pose j := W64.to_uint i.
pose s := W8.to_uint (BArray2048.get8 expected_symbols j).
pose tail_state := decoder_state_at
  (symbol_list_of_array expected_symbols) (j + 1).
pose k := W64.to_uint off -
  decoder_cursor (symbol_list_of_array expected_symbols) j.
have hs : 0 <= s < mode2_hbz_alphabet by
  rewrite /s /j; exact (hstream (W64.to_uint i) hj).
have htb := decoder_state_at_mode2_bounds expected_symbols (j + 1)
  hstream _; first smt().
have hlen := mode2_normalization_bytes_size s tail_state hs htb.
have hkb : 0 <= k <= mode2_normalization_len tail_state s by
  move: hk hsegment hlen; rewrite /j /s /tail_state /k; smt().
have hrb := decoder_replay_prefix_bounds s tail_state k hs htb hkb.
have hxuint : W32.to_uint x = decoder_replay_prefix tail_state s k.
+ rewrite hx W32.to_uint_small.
  - have hm32 : W32.modulus = 4294967296 by trivial.
    smt().
  trivial.
have hguard := decoder_replay_guard_exact s tail_state k hs htb hkb.
rewrite hxuint.
move: hguard hsegment hlen.
rewrite /decoder_word_index /decoder_word_cursor /decoder_word_segment
  /j /s /tail_state /k.
smt().
qed.

lemma decoder_inner_generated_guard_exact
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off again x :
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off again x =>
  (W32.to_uint x < rans_initial_state <=>
   decoder_word_index expected_symbols i off <
     size (decoder_word_segment expected_symbols i)).
proof.
move=> hlive.
have hcopy := hlive.
rewrite /decoder_inner_trace_live in hcopy.
move: hcopy => [hbindings [hmath _]].
rewrite /decoder_trace_bindings in hbindings.
move: hbindings => [hinput _].
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy => [hstream _].
exact (decoder_inner_math_guard_exact
  expected_symbols i off again x hstream hmath).
qed.

lemma decoder_inner_math_read_region expected_symbols i off again x :
  decoder_inner_math expected_symbols i off again x =>
  decoder_word_index expected_symbols i off <
    size (decoder_word_segment expected_symbols i) =>
  decoder_word_cursor expected_symbols i <= W64.to_uint off <
    decoder_word_cursor expected_symbols i +
      size (decoder_word_segment expected_symbols i).
proof.
move=> hmath hkstrict.
rewrite /decoder_inner_math /= in hmath.
move: hmath => [_ [_ [hk [hoff _]]]].
move: hk hoff hkstrict.
rewrite /decoder_word_index /decoder_word_cursor /decoder_word_segment.
smt().
qed.

lemma decoder_inner_math_read_byte
    expected_symbols buffer0 state0 encoded_size i off again x :
  actual_mode2_decoder_trace_input
    expected_symbols buffer0 state0 encoded_size =>
  decoder_inner_math expected_symbols i off again x =>
  decoder_word_index expected_symbols i off <
    size (decoder_word_segment expected_symbols i) =>
  decoder_read_byte_eq expected_symbols buffer0 i off.
proof.
move=> hinput hmath hkstrict.
have hmath_copy := hmath.
rewrite /decoder_inner_math /= in hmath_copy.
move: hmath_copy => [hj _].
have hregion := decoder_inner_math_read_region
  expected_symbols i off again x hmath hkstrict.
exact (actual_decoder_input_read_byte
  expected_symbols buffer0 state0 encoded_size i off
  hinput hj hregion).
qed.

lemma decoder_inner_math_off_lt_size
    expected_symbols buffer0 state0 encoded_size i off again x :
  actual_mode2_decoder_trace_input
    expected_symbols buffer0 state0 encoded_size =>
  decoder_inner_math expected_symbols i off again x =>
  W32.to_uint x < rans_initial_state =>
  off \ult BArray24.get64 state0 1.
proof.
move=> hinput hmath hxsmall.
have hmath_copy := hmath.
rewrite /decoder_inner_math /= in hmath_copy.
move: hmath_copy => [hj [hsegment [hk [hoff _]]]].
have hinput' := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput'.
move: hinput' =>
  [hstream [hencsize [hsizebound [hstate_uint _]]]].
pose syms := symbol_list_of_array expected_symbols.
pose j := W64.to_uint i.
have hguard := decoder_inner_math_guard_exact
  expected_symbols i off again x hstream hmath.
have hkstrict : decoder_word_index expected_symbols i off <
    size (decoder_word_segment expected_symbols i) by
  move: hguard hxsmall; smt().
have hregion := decoder_inner_math_read_region
  expected_symbols i off again x hmath hkstrict.
have hofftrace := decoder_cursor_segment_before_final
  syms j (W64.to_uint off) _ _.
+ rewrite /syms symbol_list_of_array_size; exact hj.
+ move: hregion.
  rewrite /decoder_word_cursor /decoder_word_segment /syms /j.
  trivial.
rewrite W64.ultE hstate_uint.
move: hofftrace hencsize; rewrite /syms; smt().
qed.

lemma decoder_inner_math_read_byte_when_small
    expected_symbols buffer0 state0 encoded_size i off again x :
  actual_mode2_decoder_trace_input
    expected_symbols buffer0 state0 encoded_size =>
  decoder_inner_math expected_symbols i off again x =>
  W32.to_uint x < rans_initial_state =>
  decoder_read_byte_eq expected_symbols buffer0 i off.
proof.
move=> hinput hmath hxsmall.
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy => [hstream _].
have hguard := decoder_inner_math_guard_exact
  expected_symbols i off again x hstream hmath.
have hkstrict : decoder_word_index expected_symbols i off <
    size (decoder_word_segment expected_symbols i) by
  move: hguard hxsmall; smt().
exact (decoder_inner_math_read_byte
  expected_symbols buffer0 state0 encoded_size i off again x
  hinput hmath hkstrict).
qed.

lemma decoder_inner_math_step_from_read
    expected_symbols buffer0 i off again x :
  mode2_hbz_symbol_stream expected_symbols =>
  decoder_inner_math expected_symbols i off again x =>
  again <> W64.zero =>
  W32.to_uint x < rans_initial_state =>
  W64.to_uint off < mode2_hbz_count =>
  decoder_read_byte_eq expected_symbols buffer0 i off =>
  decoder_inner_math expected_symbols i (off + W64.one) again
    (append_word_byte x
      (BArray2048.get8 buffer0 (W64.to_uint off))).
proof.
move=> hstream hmath hagain hxsmall hoffsmall hread.
have hmath_copy := hmath.
rewrite /decoder_inner_math /= in hmath_copy.
move: hmath_copy => [hj [hsegment [hk [hoff [hx _]]]]].
pose syms := symbol_list_of_array expected_symbols.
pose j := W64.to_uint i.
pose s := W8.to_uint (BArray2048.get8 expected_symbols j).
pose tail_state := decoder_state_at syms (j + 1).
pose segment := decoder_segment_at syms j.
pose k := W64.to_uint off - decoder_cursor syms j.
have hs : 0 <= s < mode2_hbz_alphabet by
  rewrite /s /j; exact (hstream (W64.to_uint i) hj).
have htb := decoder_state_at_mode2_bounds expected_symbols (j + 1)
  hstream _; first smt().
have [hlen_eq hlen_bound] :=
  mode2_normalization_bytes_size s tail_state hs htb.
have hguard := decoder_inner_math_guard_exact
  expected_symbols i off again x hstream hmath.
have hkseg : k < size segment.
+ move: hguard hxsmall.
  rewrite /decoder_word_index /decoder_word_cursor /decoder_word_segment
    /syms /j /segment /k.
  smt().
have hseg_exact : segment = mode2_normalization_bytes tail_state s by
  exact hsegment.
have hseglen : size segment = mode2_normalization_len tail_state s by
  rewrite hseg_exact; exact hlen_eq.
have hkstrict : 0 <= k < mode2_normalization_len tail_state s by
  smt().
have hoffinc : W64.to_uint (off + W64.one) = W64.to_uint off + 1 by
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
have hxuint : W32.to_uint x = decoder_replay_prefix tail_state s k.
+ rewrite hx W32.to_uint_small.
  - have hrb := decoder_replay_prefix_bounds s tail_state k hs htb _;
      first smt().
    have hm32 : W32.modulus = 4294967296 by trivial.
    smt().
  trivial.
have hbyte :
    W8.to_uint (BArray2048.get8 buffer0 (W64.to_uint off)) =
    nth 0 (mode2_normalization_bytes tail_state s) k.
+ move: hread hsegment.
  rewrite /decoder_read_byte_eq /decoder_word_segment /decoder_word_index
    /decoder_word_cursor /syms /j /s /tail_state /segment /k.
  smt().
have hxstep := decoder_replay_word_step x tail_state s k
  (BArray2048.get8 buffer0 (W64.to_uint off)) hs htb hkstrict hxuint hbyte.
apply decoder_inner_math_components.
+ exact hj.
+ exact hsegment.
+ smt().
+ rewrite hoffinc hoff; ring.
+ have hkinc :
      W64.to_uint (off + W64.one) - decoder_cursor syms j = k + 1 by
    rewrite hoffinc /k; ring.
  rewrite hkinc.
  exact hxstep.
move=> hagainzero.
have hcontra : again = W64.zero by exact hagainzero.
smt().
qed.

lemma decoder_inner_trace_step
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off again x :
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off again x =>
  again <> W64.zero =>
  W32.to_uint x < rans_initial_state =>
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i (off + W64.one) again
    (append_word_byte x (BArray2048.get8 bufp (W64.to_uint off))).
proof.
move=> hlive hagain hxsmall.
have hcopy := hlive.
rewrite /decoder_inner_trace_live in hcopy.
move: hcopy => [hbindings [hmath [hprefix htail]]].
have hbindings_copy := hbindings.
rewrite /decoder_trace_bindings in hbindings_copy.
move: hbindings_copy =>
  [hinput [_ [hbuf [_ [_ [_ [hsize _]]]]]]].
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy => [hstream [_ [hsizebound [hstate_uint _]]]].
have hnext0 := decoder_inner_math_off_lt_size
  expected_symbols buffer0 state0 encoded_size i off again x
  hinput hmath hxsmall.
have hnext : off \ult size_in by
  rewrite hsize; exact hnext0.
have hread0 := decoder_inner_math_read_byte_when_small
  expected_symbols buffer0 state0 encoded_size i off again x
  hinput hmath hxsmall.
have hread : decoder_read_byte_eq expected_symbols bufp i off by
  rewrite hbuf; exact hread0.
have hnext_uint : W64.to_uint off < W64.to_uint size_in by
  move: hnext; rewrite W64.ultE.
have hsize_uint : W64.to_uint size_in = encoded_size by
  rewrite hsize hstate_uint.
have hoffenc : W64.to_uint off < encoded_size by
  rewrite -hsize_uint; exact hnext_uint.
have hencle : encoded_size <= 1024 by
  move: hsizebound; rewrite /mode2_hbz_count; smt().
have hoffsmall : W64.to_uint off < 1024 by smt().
have hmath_step := decoder_inner_math_step_from_read
  expected_symbols bufp i off again x hstream hmath hagain hxsmall
  hoffsmall hread.
apply decoder_inner_trace_live_components.
+ exact hbindings.
+ exact hmath_step.
+ exact hprefix.
+ exact htail.
qed.

lemma decoder_inner_trace_off_lt_size
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off again x :
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off again x =>
  W32.to_uint x < rans_initial_state =>
  off \ult size_in.
proof.
move=> hlive hxsmall.
have hcopy := hlive.
rewrite /decoder_inner_trace_live in hcopy.
move: hcopy => [hbindings [hmath _]].
have hbindings_copy := hbindings.
rewrite /decoder_trace_bindings in hbindings_copy.
move: hbindings_copy => [hinput [_ [_ [_ [_ [_ [hsize _]]]]]]].
rewrite hsize.
exact (decoder_inner_math_off_lt_size
  expected_symbols buffer0 state0 encoded_size i off again x
  hinput hmath hxsmall).
qed.

lemma decoder_inner_trace_stop
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off again x :
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off again x =>
  !(W32.to_uint x < rans_initial_state) =>
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off W64.zero x.
proof.
move=> hlive hxlarge.
have hcopy := hlive.
rewrite /decoder_inner_trace_live in hcopy.
move: hcopy => [hbindings [hmath [hprefix htail]]].
have hbindings_copy := hbindings.
rewrite /decoder_trace_bindings in hbindings_copy.
move: hbindings_copy => [hinput _].
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy => [hstream _].
have hmath_copy := hmath.
rewrite /decoder_inner_math /= in hmath_copy.
move: hmath_copy => [hj [hsegment [hk [hoff [hx _]]]]].
have hguard := decoder_inner_math_guard_exact
  expected_symbols i off again x hstream hmath.
have hkdone :
    W64.to_uint off -
      decoder_cursor (symbol_list_of_array expected_symbols)
        (W64.to_uint i) =
    size (decoder_segment_at
      (symbol_list_of_array expected_symbols) (W64.to_uint i)).
+ move: hguard hxlarge hk.
  rewrite /decoder_word_index /decoder_word_cursor /decoder_word_segment.
  smt().
have hmath0 : decoder_inner_math expected_symbols i off W64.zero x.
+ apply decoder_inner_math_components.
  - exact hj.
  - exact hsegment.
  - exact hk.
  - exact hoff.
  - exact hx.
  move=> _; exact hkdone.
apply decoder_inner_trace_live_components.
+ exact hbindings.
+ exact hmath0.
+ exact hprefix.
+ exact htail.
qed.

lemma decoder_inner_math_exit
    expected_symbols i off again x :
  mode2_hbz_symbol_stream expected_symbols =>
  decoder_inner_math expected_symbols i off again x =>
  again = W64.zero =>
  x = W32.of_int
        (decoder_state_at (symbol_list_of_array expected_symbols)
          (W64.to_uint i + 1)) /\
  W64.to_uint off =
    decoder_cursor (symbol_list_of_array expected_symbols)
      (W64.to_uint i + 1).
proof.
move=> hstream hmath hagain.
have hcopy := hmath.
rewrite /decoder_inner_math /= in hcopy.
move: hcopy => [hj [hsegment [hk [hoff [hx hdone]]]]].
pose syms := symbol_list_of_array expected_symbols.
pose j := W64.to_uint i.
pose s := W8.to_uint (BArray2048.get8 expected_symbols j).
pose tail_state := decoder_state_at syms (j + 1).
pose segment := decoder_segment_at syms j.
pose k := W64.to_uint off - decoder_cursor syms j.
have hs : 0 <= s < mode2_hbz_alphabet by
  rewrite /s /j; exact (hstream (W64.to_uint i) hj).
have htb := decoder_state_at_mode2_bounds expected_symbols (j + 1)
  hstream _; first smt().
have [hlen_eq hlen_bound] :=
  mode2_normalization_bytes_size s tail_state hs htb.
have hkdone : k = size segment by
  exact (hdone hagain).
have hseg_exact : segment = mode2_normalization_bytes tail_state s by
  exact hsegment.
have hseglen : size segment = mode2_normalization_len tail_state s by
  rewrite hseg_exact; exact hlen_eq.
have hreplay := decoder_replay_complete s tail_state hs htb.
have hx_k : x = W32.of_int (decoder_replay_prefix tail_state s k) by
  exact hx.
have hx_done : x = W32.of_int tail_state.
+ rewrite hx_k hkdone hseglen hreplay.
split.
+ move: hx_done; rewrite /syms /j /tail_state; trivial.
+ rewrite (decoder_cursor_step syms j _); first
    by rewrite /syms symbol_list_of_array_size; exact hj.
  move: hoff hkdone.
  rewrite /syms /j /segment /k.
  smt().
qed.

lemma decoder_outer_trace_live_components
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x :
  actual_mode2_decoder_trace_input
    expected_symbols buffer0 state0 encoded_size =>
  statep = state0 =>
  bufp = buffer0 =>
  symbolwp = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words =>
  dsymswp = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words =>
  count = W64.of_int mode2_hbz_count =>
  size_in = BArray24.get64 state0 1 =>
  m = W64.of_int mode2_hbz_alphabet =>
  bad = W64.zero =>
  0 <= W64.to_uint i <= mode2_hbz_count =>
  x = W32.of_int
    (decoder_state_at (symbol_list_of_array expected_symbols)
      (W64.to_uint i)) =>
  W64.to_uint off =
    decoder_cursor (symbol_list_of_array expected_symbols)
      (W64.to_uint i) =>
  decoded_symbol_prefix symsp expected_symbols (W64.to_uint i) =>
  decoded_symbol_tail_frame decoded0 symsp (W64.to_uint i) =>
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp count size_in m bad i off x.
proof.
move=> hinput hstate hbuf hsymbol hdsyms hcount hsize hm hbad hi
  hx hoff hprefix htail.
rewrite /decoder_outer_trace_live /=.
split; first exact hinput.
split; first exact hstate.
split; first exact hbuf.
split; first exact hsymbol.
split; first exact hdsyms.
split; first exact hcount.
split; first exact hsize.
split; first exact hm.
split; first exact hbad.
split; first exact hi.
split; first exact hx.
split; first exact hoff.
split; first exact hprefix.
exact htail.
qed.

lemma decoder_inner_trace_exit_to_outer
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off again x :
  decoder_inner_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off again x =>
  again = W64.zero =>
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp count size_in m bad
    (i + W64.one) off x.
proof.
move=> hlive hagain.
have hcopy := hlive.
rewrite /decoder_inner_trace_live in hcopy.
move: hcopy => [hbindings [hmath [hprefix htail]]].
have hbindings_copy := hbindings.
rewrite /decoder_trace_bindings in hbindings_copy.
move: hbindings_copy =>
  [hinput [hstate [hbuf [hsymbol [hdsyms [hcount [hsize [hm hbad]]]]]]]].
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy => [hstream _].
have hmath_copy := hmath.
rewrite /decoder_inner_math /= in hmath_copy.
move: hmath_copy => [hj _].
have [hx_done hoff_done] := decoder_inner_math_exit
  expected_symbols i off again x hstream hmath hagain.
have hiinc : W64.to_uint (i + W64.one) = W64.to_uint i + 1 by
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
apply decoder_outer_trace_live_components.
+ exact hinput.
+ exact hstate.
+ exact hbuf.
+ exact hsymbol.
+ exact hdsyms.
+ exact hcount.
+ exact hsize.
+ exact hm.
+ exact hbad.
+ rewrite hiinc; smt().
+ rewrite hiinc; exact hx_done.
+ rewrite hiinc; exact hoff_done.
+ rewrite hiinc; exact hprefix.
+ rewrite hiinc; exact htail.
qed.

lemma decoder_outer_trace_initial
    decoded0 expected_symbols buffer0 state0 encoded_size :
  actual_mode2_decoder_trace_input
    expected_symbols buffer0 state0 encoded_size =>
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size decoded0 state0 buffer0
    SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words
    SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words
    (W64.of_int mode2_hbz_count) (BArray24.get64 state0 1)
    (W64.of_int mode2_hbz_alphabet) W64.zero W64.zero
    (W64.of_int 4) (generated_decoder_parse32 buffer0).
proof.
move=> hinput.
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy => [hstream [_ [_ [_ [hsegment _]]]]].
have hx := generated_decoder_parse32_from_trace
  buffer0 expected_symbols hstream hsegment.
rewrite /decoder_outer_trace_live /=.
split; first exact hinput.
split.
+ rewrite /mode2_hbz_count; smt().
split.
+ exact hx.
split.
+ rewrite decoder_cursor_start; trivial.
split.
+ exact (decoded_symbol_prefix_zero decoded0 expected_symbols).
exact (decoded_symbol_tail_frame_refl decoded0 0).
qed.

lemma decoder_outer_trace_exit_components
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp statep bufp symbolwp dsymswp count size_in m bad i off x cond :
  decoder_outer_trace_live decoded0 expected_symbols buffer0 state0
    encoded_size symsp statep bufp symbolwp dsymswp
    count size_in m bad i off x =>
  cond = (i \ult count) =>
  !cond =>
  bad = W64.zero /\
  x = W32.of_int rans_initial_state /\
  off = W64.of_int encoded_size /\
  size_in = W64.of_int encoded_size /\
  decoded_symbol_prefix symsp expected_symbols mode2_hbz_count /\
  decoded_symbol_tail_frame decoded0 symsp mode2_hbz_count.
proof.
move=> hlive hguard hnot.
have hcopy := hlive.
rewrite /decoder_outer_trace_live /= in hcopy.
move: hcopy =>
  [hinput [_ [_ [_ [_ [hcount [hsize [_ [hbad
    [hibound [hx [hoff [hprefix htail]]]]]]]]]]]]].
have hinput_copy := hinput.
rewrite /actual_mode2_decoder_trace_input in hinput_copy.
move: hinput_copy =>
  [_ [hencoded [hencoded_bound [_ [_ [_ [_ [hstate_size _]]]]]]]].
have hcount_uint : W64.to_uint count = mode2_hbz_count.
+ rewrite hcount W64.of_uintK.
  have hsmall : 0 <= mode2_hbz_count < W64.modulus.
  - rewrite /mode2_hbz_count.
    have hm64 : W64.modulus = 18446744073709551616 by trivial.
    smt().
  rewrite modz_small; exact hsmall.
have hnlt : !(W64.to_uint i < mode2_hbz_count).
+ move: hnot.
  rewrite hguard W64.ultE hcount_uint.
  trivial.
have hi : W64.to_uint i = mode2_hbz_count by smt().
have hsymbols_size := symbol_list_of_array_size expected_symbols.
have hx_final : x = W32.of_int rans_initial_state.
+ move: hx.
  rewrite hi -hsymbols_size decoder_state_final.
  trivial.
have hoff_uint : W64.to_uint off = encoded_size.
+ move: hoff.
  rewrite hi -hsymbols_size decoder_cursor_final -hencoded.
  trivial.
have hoff_word := mode2_w64_word_from_encoded_size
  off encoded_size hencoded_bound hoff_uint.
split; first exact hbad.
split; first exact hx_final.
split; first exact hoff_word.
split.
+ rewrite hsize hstate_size.
split.
+ move: hprefix; rewrite hi; trivial.
move: htail; rewrite hi; trivial.
qed.

op actual_mode2_decoder_trace_post
    (decoded0 expected_symbols : BArray2048.t)
    (result : BArray2048.t * BArray24.t)
    (encoded_size : int) : bool =
  BArray24.get64 result.`2 1 = W64.zero /\
  BArray24.get64 result.`2 0 = W64.of_int encoded_size /\
  decoded_symbol_prefix result.`1 expected_symbols mode2_hbz_count /\
  decoded_symbol_tail_frame decoded0 result.`1 mode2_hbz_count.

end Mode2RansDecoderActualTrace.
