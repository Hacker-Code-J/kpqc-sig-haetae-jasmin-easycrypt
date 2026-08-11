require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  Mode2HbzCodecSpec Mode2RansByteStack
  Mode2RansArrayListBridge Mode2RansNormalization
  Mode2RansEncodeRefinement Mode2HbzTableCertificate.

theory Mode2RansDecoderCursor.

import Mode2HbzCodecSpec Mode2RansByteStack
       Mode2RansArrayListBridge Mode2RansNormalization
       Mode2RansEncodeRefinement Mode2HbzTableCertificate.

op decoder_state_at (symbols : int list) (i : int) : int =
  nth rans_initial_state (trace_states symbols) i.

op decoder_segment_at (symbols : int list) (i : int) : int list =
  nth [] (trace_segments symbols) i.

op decoder_cursor (symbols : int list) (i : int) : int =
  nth 0 (trace_cuts symbols) i.

op decoded_symbol_prefix
    (decoded expected : BArray2048.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray2048.get8 decoded i = BArray2048.get8 expected i.

op decoded_symbol_tail_frame
    (before after : BArray2048.t) (start : int) : bool =
  forall i, start <= i < mode2_hbz_capacity =>
    BArray2048.get8 after i = BArray2048.get8 before i.

lemma trace_states_nth_drop (symbols : int list) i :
  0 <= i < size symbols =>
  nth rans_initial_state (trace_states symbols) i =
    (encode_trace (drop i symbols)).`1.
proof.
elim: symbols i => [|s tl ih] i /=; first smt().
case (i = 0) => hi0.
+ by subst i.
move=> hi.
have hi1 : 0 <= i - 1 < size tl by smt().
rewrite ifF 1:/#.
exact (ih (i - 1) hi1).
qed.

lemma decoded_symbol_prefix_zero decoded expected :
  decoded_symbol_prefix decoded expected 0.
proof. rewrite /decoded_symbol_prefix; smt(). qed.

lemma decoded_symbol_prefix_step decoded expected n :
  0 <= n < mode2_hbz_count =>
  decoded_symbol_prefix decoded expected n =>
  decoded_symbol_prefix
    (BArray2048.set8 decoded n (BArray2048.get8 expected n))
    expected (n + 1).
proof.
move=> hn hprefix.
rewrite /decoded_symbol_prefix => i hi.
rewrite BArray2048.get_setE 1:/# 1:/#.
qed.

lemma decoded_symbol_tail_frame_refl bytes start :
  decoded_symbol_tail_frame bytes bytes start.
proof. rewrite /decoded_symbol_tail_frame; trivial. qed.

lemma decoded_symbol_tail_frame_set_before before after start idx value :
  0 <= idx < start =>
  decoded_symbol_tail_frame before after start =>
  decoded_symbol_tail_frame before
    (BArray2048.set8 after idx value) start.
proof.
move=> hidx hframe.
rewrite /decoded_symbol_tail_frame => i hi.
rewrite BArray2048.get_setE 1:/# 1:/#.
qed.

lemma trace_bytes_size symbols :
  size (trace_bytes symbols) = 4 + size (flatten (trace_segments symbols)).
proof.
rewrite /trace_bytes size_cat /=.
trivial.
qed.

lemma decoder_cursor_start symbols :
  decoder_cursor symbols 0 = 4.
proof.
rewrite /decoder_cursor.
exact (trace_cuts_start symbols).
qed.

lemma decoder_state_start symbols :
  decoder_state_at symbols 0 = (encode_trace symbols).`1.
proof.
case: symbols => [|s tl] //=.
qed.

lemma decoder_state_final symbols :
  decoder_state_at symbols (size symbols) = rans_initial_state.
proof.
rewrite /decoder_state_at.
rewrite (nth_change_dfl 0 rans_initial_state).
+ rewrite trace_states_size.
  smt(size_ge0).
exact (trace_states_last symbols).
qed.

lemma decoder_segment_head s tl :
  decoder_segment_at (s :: tl) 0 =
    mode2_normalization_bytes (encode_trace tl).`1 s.
proof. trivial. qed.

lemma decoder_segment_head_size s tl :
  0 <= s < mode2_hbz_alphabet =>
  canonical_symbol_list tl =>
  0 <= size (decoder_segment_at (s :: tl) 0) <= 2.
proof.
move=> hs htl.
rewrite decoder_segment_head.
have hstate := encode_trace_state_bounds tl htl.
have [_ hsz] := mode2_normalization_bytes_size
  s (encode_trace tl).`1 hs hstate.
exact hsz.
qed.

lemma decoder_parse32_from_trace buffer symbols :
  canonical_symbol_list symbols =>
  segment_matches buffer 0 (trace_bytes symbols) =>
  parse32_le
    [W8.to_uint (BArray2048.get8 buffer 0);
     W8.to_uint (BArray2048.get8 buffer 1);
     W8.to_uint (BArray2048.get8 buffer 2);
     W8.to_uint (BArray2048.get8 buffer 3)] =
  (encode_trace symbols).`1.
proof.
move=> hcan hmatch.
have h0 := segment_matches_nth buffer 0 (trace_bytes symbols) 0 hmatch _.
+ rewrite /trace_bytes /serialize32_le /=; smt(size_ge0).
have h1 := segment_matches_nth buffer 0 (trace_bytes symbols) 1 hmatch _.
+ rewrite /trace_bytes /serialize32_le /=; smt(size_ge0).
have h2 := segment_matches_nth buffer 0 (trace_bytes symbols) 2 hmatch _.
+ rewrite /trace_bytes /serialize32_le /=; smt(size_ge0).
have h3 := segment_matches_nth buffer 0 (trace_bytes symbols) 3 hmatch _.
+ rewrite /trace_bytes /serialize32_le /=; smt(size_ge0).
rewrite /trace_bytes /serialize32_le /= in h0.
rewrite /trace_bytes /serialize32_le /= in h1.
rewrite /trace_bytes /serialize32_le /= in h2.
rewrite /trace_bytes /serialize32_le /= in h3.
rewrite /parse32_le /=.
have hbound := encode_trace_state_bounds symbols hcan.
have hw32 : 0 <= (encode_trace symbols).`1 < w32_modulus_i.
+ rewrite /w32_modulus_i /rans_initial_state in hbound.
   smt().
have hparse := serialize32_parse_inverse (encode_trace symbols).`1 hw32.
rewrite /parse32_le /serialize32_le /= in hparse.
by smt().
qed.

lemma decoder_cursor_witness_satisfiable :
  exists symbols,
    canonical_symbol_list symbols /\
    decoder_cursor symbols 0 = 4 /\
    decoder_state_at symbols (size symbols) = rans_initial_state.
proof.
exists [].
split; first trivial.
split; first exact (decoder_cursor_start []).
exact (decoder_state_final []).
qed.

end Mode2RansDecoderCursor.
