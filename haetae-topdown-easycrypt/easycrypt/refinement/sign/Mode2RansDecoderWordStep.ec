require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  SignatureUnpackMode2Target
  Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2HbzSymbolWordsGenerated
  Mode2RansCore Mode2RansByteStack Mode2RansArrayListBridge
  Mode2RansEncodeRefinement Mode2RansDecoderCursor.

theory Mode2RansDecoderWordStep.

import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2HbzSymbolWordsGenerated
       Mode2RansCore Mode2RansByteStack Mode2RansArrayListBridge
       Mode2RansEncodeRefinement Mode2RansDecoderCursor.

op actual_mode2_decoder_packed (s : int) : W32.t =
  BArray528.get32 SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words s.

op actual_mode2_decoder_start (s : int) : W32.t =
  actual_mode2_decoder_packed s `&` W32.of_int 65535.

op actual_mode2_decoder_freq (s : int) : W32.t =
  actual_mode2_decoder_packed s `>>` W8.of_int 16.

op actual_mode2_decoder_lookup (x : W32.t) : W32.t =
  let slot = W32.to_uint x %% rans_scale in
  let word =
    BArray2048.get32 SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words
      (slot %/ 2) in
  if slot %% 2 = 0 then word else word `>>` W8.of_int 16.

op actual_mode2_decoder_symbol (x : W32.t) : int =
  W32.to_uint (actual_mode2_decoder_lookup x `&` W32.of_int 65535).

op actual_mode2_decoder_step (x : W32.t) (s : int) : W32.t =
  W32.of_int (hbz_math_decode_step (W32.to_uint x) s).

lemma actual_mode2_decoder_start_uint s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint (actual_mode2_decoder_start s) = hbz_start s.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /actual_mode2_decoder_start /actual_mode2_decoder_packed
              decoder_low_halfword_semantics
              /SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words
              /hbz_start BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_decoder_freq_uint s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint (actual_mode2_decoder_freq s) = hbz_freq s.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /actual_mode2_decoder_freq /actual_mode2_decoder_packed
              /SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words
              /hbz_freq BArray528.get32_of_list32 1:// 1:// /=
              W32.shr_div W8.of_uintK /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_decoder_symbol_table x :
  actual_mode2_decoder_symbol x =
  table_symbol_at
    SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words
    (W32.to_uint x %% rans_scale).
proof.
rewrite /actual_mode2_decoder_symbol /actual_mode2_decoder_lookup
        /table_symbol_at /=.
case (W32.to_uint x %% rans_scale %% 2 = 0) => hp.
+ rewrite /= decoder_low_halfword_semantics; trivial.
+ rewrite /= decoder_high_halfword_semantics; trivial.
qed.

lemma actual_mode2_decoder_lookup_symbol
    (expected_symbols : BArray2048.t) i :
  mode2_hbz_symbol_stream expected_symbols =>
  0 <= i < mode2_hbz_count =>
  actual_mode2_decoder_symbol
    (W32.of_int
      (decoder_state_at (symbol_list_of_array expected_symbols) i)) =
  W8.to_uint (BArray2048.get8 expected_symbols i).
proof.
move=> hstream hi.
have hcan := mode2_stream_canonical_list expected_symbols hstream.
have hsuf :
    canonical_symbol_list (symbol_suffix expected_symbols (i + 1)).
+ apply (canonical_symbol_suffix expected_symbols (i + 1) hstream).
  smt().
have hs :
    0 <= W8.to_uint (BArray2048.get8 expected_symbols i) <
      mode2_hbz_alphabet by exact (hstream i hi).
have hcons := symbol_suffix_cons expected_symbols i hi.
have hstate :
    decoder_state_at (symbol_list_of_array expected_symbols) i =
    (encode_trace (symbol_suffix expected_symbols i)).`1.
+ apply (trace_states_nth_drop
     (symbol_list_of_array expected_symbols) i).
  rewrite symbol_list_of_array_size; smt().
have hfullcan :
    canonical_symbol_list (symbol_suffix expected_symbols i).
+ apply (canonical_symbol_suffix expected_symbols i hstream).
  smt().
have hfullbound := encode_trace_state_bounds
  (symbol_suffix expected_symbols i) hfullcan.
have hrange :
    0 <= decoder_state_at (symbol_list_of_array expected_symbols) i <
      w32_modulus_i by
  move: hfullbound; rewrite hstate /w32_modulus_i; smt().
have hword :
    W32.to_uint
      (W32.of_int
        (decoder_state_at (symbol_list_of_array expected_symbols) i)) =
    decoder_state_at (symbol_list_of_array expected_symbols) i by
  rewrite W32.of_uintK modz_small 1:hrange; trivial.
rewrite actual_mode2_decoder_symbol_table hword.
rewrite hstate.
rewrite hcons.
have hslot :
    0 <=
      (encode_trace
        (W8.to_uint (BArray2048.get8 expected_symbols i) ::
         symbol_suffix expected_symbols (i + 1))).`1 %% rans_scale <
      rans_scale.
+ apply modz_cmp.
  rewrite /rans_scale; smt().
rewrite actual_mode2_hbz_symbol_words 1:hslot.
exact (trace_head_symbol_selected
  (W8.to_uint (BArray2048.get8 expected_symbols i))
  (symbol_suffix expected_symbols (i + 1)) hs hsuf).
qed.

lemma actual_mode2_decoder_step_correct (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= W32.to_uint x < 2147483648 =>
  actual_mode2_decoder_step x s =
    W32.of_int (hbz_math_decode_step (W32.to_uint x) s).
proof.
move=> _ _.
trivial.
qed.

end Mode2RansDecoderWordStep.
