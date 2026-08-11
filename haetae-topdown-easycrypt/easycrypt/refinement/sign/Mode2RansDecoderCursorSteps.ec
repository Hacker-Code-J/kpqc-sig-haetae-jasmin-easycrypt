require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  Mode2HbzCodecSpec Mode2RansByteStack
  Mode2RansArrayListBridge Mode2RansNormalization
  Mode2RansEncodeRefinement Mode2HbzTableCertificate
  Mode2RansDecoderCursor.

theory Mode2RansDecoderCursorSteps.

import Mode2HbzCodecSpec Mode2RansByteStack
       Mode2RansArrayListBridge Mode2RansNormalization
       Mode2RansEncodeRefinement Mode2HbzTableCertificate
       Mode2RansDecoderCursor.

lemma trace_segments_drop (symbols : int list) i :
  0 <= i <= size symbols =>
  drop i (trace_segments symbols) = trace_segments (drop i symbols).
proof.
elim: symbols i => [|s tl ih] i /=; first smt().
move=> hi.
have [-> | hpos] : i = 0 \/ 0 < i by smt().
+ trivial.
have hi1 : 0 <= i - 1 <= size tl by smt().
have hrec := ih (i - 1) hi1.
move: hrec; smt().
qed.

lemma trace_segments_nth_drop (symbols : int list) i :
  0 <= i < size symbols =>
  nth [] (trace_segments symbols) i =
    mode2_normalization_bytes (encode_trace (drop (i + 1) symbols)).`1
      (nth 0 symbols i).
proof.
move=> hi.
have hseg : 0 <= i < size (trace_segments symbols).
+ rewrite trace_segments_size.
   exact hi.
have hsym : 0 <= i <= size symbols by smt().
have hdropseg := trace_segments_drop symbols i hsym.
rewrite (drop_nth [] i (trace_segments symbols) hseg) in hdropseg.
rewrite (drop_nth 0 i symbols hi) /= in hdropseg.
move: hdropseg; smt().
qed.

lemma decoder_segment_at_drop (symbols : int list) i :
  0 <= i < size symbols =>
  decoder_segment_at symbols i =
    mode2_normalization_bytes (encode_trace (drop (i + 1) symbols)).`1
      (nth 0 symbols i).
proof.
move=> hi.
rewrite /decoder_segment_at.
exact (trace_segments_nth_drop symbols i hi).
qed.

lemma decoder_state_at_symbol_suffix expected i :
  0 <= i <= mode2_hbz_count =>
  decoder_state_at (symbol_list_of_array expected) i =
    (encode_trace (symbol_suffix expected i)).`1.
proof.
move=> hi.
case (i = mode2_hbz_count) => hlast.
+ rewrite hlast symbol_suffix_at_end /=.
  have hsize := symbol_list_of_array_size expected.
  rewrite -hsize decoder_state_final.
  trivial.
+ apply (trace_states_nth_drop
    (symbol_list_of_array expected) i).
  rewrite symbol_list_of_array_size.
  smt().
qed.

lemma cuts_from_nth_step cursor segments i :
  0 <= i < size segments =>
  nth 0 (cuts_from cursor segments) (i + 1) =
    nth 0 (cuts_from cursor segments) i + size (nth [] segments i).
proof.
by elim: segments cursor i => [|seg tl ih] cursor i /= /#.
qed.

lemma cuts_from_nth_prefix (cursor : int) (segments : (int list) list) i :
  0 <= i <= size segments =>
  nth 0 (cuts_from cursor segments) i =
    cursor + size (flatten (take i segments)).
proof.
elim: segments cursor i => [|seg tl ih] cursor i /=.
+ move=> hi.
  have -> : i = 0 by smt().
  trivial.
+ move=> hi.
  case (i = 0) => hi0.
  - subst i; trivial.
  - have hi1 : 0 <= i - 1 <= size tl by smt().
    have hrec := ih (cursor + size seg) (i - 1) hi1.
    rewrite ifF 1:/#.
    move: hrec.
    rewrite flatten_cons size_cat.
    smt().
qed.

lemma decoder_cursor_prefix_size symbols i :
  0 <= i <= size symbols =>
  decoder_cursor symbols i =
    4 + size (flatten (take i (trace_segments symbols))).
proof.
move=> hi.
rewrite /decoder_cursor /trace_cuts.
apply cuts_from_nth_prefix.
rewrite trace_segments_size.
exact hi.
qed.

lemma decoder_cursor_bounds symbols i :
  0 <= i <= size symbols =>
  4 <= decoder_cursor symbols i <= decoder_cursor symbols (size symbols).
proof.
move=> hi.
rewrite decoder_cursor_prefix_size 1:hi.
rewrite decoder_cursor_prefix_size 1:/#.
rewrite -(trace_segments_size symbols) take_size.
have -> :
    flatten (trace_segments symbols) =
    flatten (take i (trace_segments symbols)) ++
      flatten (drop i (trace_segments symbols)).
+ rewrite -flatten_cat.
  rewrite cat_take_drop.
  trivial.
rewrite size_cat.
have hs := size_ge0 (flatten (take i (trace_segments symbols))).
have hr := size_ge0 (flatten (drop i (trace_segments symbols))).
smt().
qed.

lemma decoder_cursor_step symbols i :
  0 <= i < size symbols =>
  decoder_cursor symbols (i + 1) =
    decoder_cursor symbols i + size (decoder_segment_at symbols i).
proof.
move=> hi.
rewrite /decoder_cursor /decoder_segment_at /trace_cuts.
apply cuts_from_nth_step.
rewrite trace_segments_size.
exact hi.
qed.

lemma cuts_from_last cursor segments :
  nth 0 (cuts_from cursor segments) (size segments) =
    cursor + size (flatten segments).
proof.
elim: segments cursor => [|seg tl ih] cursor /=.
+ trivial.
rewrite ifF 1:/#.
rewrite (ih (cursor + size seg)) /=.
smt(size_cat).
qed.

lemma decoder_cursor_final symbols :
  decoder_cursor symbols (size symbols) = size (trace_bytes symbols).
proof.
rewrite /decoder_cursor /trace_cuts.
rewrite -(trace_segments_size symbols).
rewrite cuts_from_last.
rewrite trace_bytes_size.
ring.
qed.

lemma decoder_cursor_segment_before_final symbols i off :
  0 <= i < size symbols =>
  decoder_cursor symbols i <= off <
    decoder_cursor symbols i + size (decoder_segment_at symbols i) =>
  off < size (trace_bytes symbols).
proof.
move=> hi hoff.
have hstep := decoder_cursor_step symbols i hi.
have hbound := decoder_cursor_bounds symbols (i + 1) _; first smt().
have hfinal := decoder_cursor_final symbols.
smt().
qed.

lemma decoder_segment_symbol_suffix expected i :
  mode2_hbz_symbol_stream expected =>
  0 <= i < mode2_hbz_count =>
  decoder_segment_at (symbol_list_of_array expected) i =
    mode2_normalization_bytes
      (encode_trace (symbol_suffix expected (i + 1))).`1
      (W8.to_uint (BArray2048.get8 expected i)).
proof.
move=> hstream hi.
rewrite decoder_segment_at_drop.
+ rewrite symbol_list_of_array_size.
  exact hi.
rewrite /symbol_suffix.
rewrite (symbol_list_of_array_nth expected i hi).
trivial.
qed.

end Mode2RansDecoderCursorSteps.
