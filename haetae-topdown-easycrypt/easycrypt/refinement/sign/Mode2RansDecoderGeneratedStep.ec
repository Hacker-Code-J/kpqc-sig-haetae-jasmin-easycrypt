require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  SignatureUnpackMode2Target
  Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2HbzSymbolWordsGenerated
  Mode2RansCore Mode2RansByteStack Mode2RansArrayListBridge
  Mode2RansEncodeRefinement Mode2RansDecoderCursor Mode2RansDecoderWordStep
  Mode2RansDecoderActualWord.

theory Mode2RansDecoderGeneratedStep.

import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2HbzSymbolWordsGenerated
       Mode2RansCore Mode2RansByteStack Mode2RansArrayListBridge
       Mode2RansEncodeRefinement
       Mode2RansDecoderCursor Mode2RansDecoderWordStep
       Mode2RansDecoderActualWord.

op generated_decoder_slot (x : W32.t) : W64.t =
  (zeroextu64 x) `&` W64.of_int 1023.

op generated_decoder_word_index (x : W32.t) : W64.t =
  generated_decoder_slot x `>>` W8.of_int 1.

op generated_decoder_parity (x : W32.t) : W64.t =
  generated_decoder_slot x `&` W64.one.

op generated_decoder_lookup_word (x : W32.t) : W32.t =
  let word = BArray2048.get32
    SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words
    (W64.to_uint (generated_decoder_word_index x)) in
  if generated_decoder_parity x <> W64.zero then
    word `>>` W8.of_int 16
  else word.

op generated_decoder_lookup_word_from
    (symbol_words : BArray2048.t) (x : W32.t) : W32.t =
  let word = BArray2048.get32 symbol_words
    (W64.to_uint (generated_decoder_word_index x)) in
  if generated_decoder_parity x <> W64.zero then
    word `>>` W8.of_int 16
  else word.

lemma generated_decoder_lookup_word_from_mode2 symbol_words x :
  symbol_words = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words =>
  generated_decoder_lookup_word_from symbol_words x =
    generated_decoder_lookup_word x.
proof.
move=> ->.
rewrite /generated_decoder_lookup_word_from
        /generated_decoder_lookup_word.
trivial.
qed.

op generated_decoder_symbol (x : W32.t) : W8.t =
  truncateu8
    (zeroextu64 (generated_decoder_lookup_word x `&` W32.of_int 65535)).

op generated_decoder_symbol_from
    (symbol_words : BArray2048.t) (x : W32.t) : W8.t =
  truncateu8
    (zeroextu64
      (generated_decoder_lookup_word_from symbol_words x `&`
       W32.of_int 65535)).

op generated_decoder_word_update (x : W32.t) (s : W8.t) : W32.t =
  let packed = BArray528.get32
    SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words (W8.to_uint s) in
  let start = packed `&` W32.of_int 65535 in
  let freq = packed `>>` W8.of_int 16 in
  ((((x `>>` W8.of_int 10) * freq) +
      (x `&` W32.of_int 1023)) - start).

op generated_decoder_word_update_from
    (dsyms_words : BArray528.t) (x : W32.t) (s : W8.t) : W32.t =
  let packed = BArray528.get32 dsyms_words (W8.to_uint s) in
  let start = packed `&` W32.of_int 65535 in
  let freq = packed `>>` W8.of_int 16 in
  ((((x `>>` W8.of_int 10) * freq) +
      (x `&` W32.of_int 1023)) - start).

lemma generated_decoder_symbol_from_mode2 symbol_words x :
  symbol_words = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words =>
  generated_decoder_symbol_from symbol_words x = generated_decoder_symbol x.
proof.
move=> htable.
rewrite /generated_decoder_symbol_from /generated_decoder_symbol
        (generated_decoder_lookup_word_from_mode2 symbol_words x htable).
trivial.
qed.

lemma generated_decoder_word_update_from_mode2 dsyms_words x s :
  dsyms_words = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words =>
  generated_decoder_word_update_from dsyms_words x s =
    generated_decoder_word_update x s.
proof.
move=> ->.
rewrite /generated_decoder_word_update_from
        /generated_decoder_word_update.
trivial.
qed.

lemma generated_decoder_slot_uint x :
  W64.to_uint (generated_decoder_slot x) = W32.to_uint x %% rans_scale.
proof.
rewrite /generated_decoder_slot (W64.to_uint_and_mod 10) 1:/#.
rewrite W2u32.to_uint_zeroextu64 /rans_scale.
trivial.
qed.

lemma generated_decoder_word_index_uint x :
  W64.to_uint (generated_decoder_word_index x) =
    (W32.to_uint x %% rans_scale) %/ 2.
proof.
rewrite /generated_decoder_word_index W64.shr_div_le 1:/#
        generated_decoder_slot_uint.
trivial.
qed.

lemma generated_decoder_parity_uint x :
  W64.to_uint (generated_decoder_parity x) =
    (W32.to_uint x %% rans_scale) %% 2.
proof.
rewrite /generated_decoder_parity (W64.to_uint_and_mod 1) 1:/#
        generated_decoder_slot_uint.
trivial.
qed.

lemma generated_decoder_parity_nonzero x :
  (generated_decoder_parity x <> W64.zero) <=>
  (W32.to_uint x %% rans_scale) %% 2 = 1.
proof.
have heqzero :
    (generated_decoder_parity x = W64.zero) <=>
    (W64.to_uint (generated_decoder_parity x) = 0).
+ rewrite W64.to_uint_eq W64.to_uint0.
  trivial.
rewrite heqzero.
have hrem := modz_cmp (W32.to_uint x %% rans_scale) 2 _; first smt().
have huint := generated_decoder_parity_uint x.
smt().
qed.

lemma generated_decoder_lookup_matches x :
  generated_decoder_lookup_word x = actual_mode2_decoder_lookup x.
proof.
rewrite /generated_decoder_lookup_word /actual_mode2_decoder_lookup /=
        generated_decoder_word_index_uint.
case (generated_decoder_parity x <> W64.zero) => hp.
+ have heqzero :
      (generated_decoder_parity x = W64.zero) <=>
      (W64.to_uint (generated_decoder_parity x) = 0) by
    rewrite W64.to_uint_eq W64.to_uint0; trivial.
  have hpuint : W64.to_uint (generated_decoder_parity x) <> 0 by
    move: hp; rewrite heqzero.
  have huint := generated_decoder_parity_uint x.
  have hrem := modz_cmp (W32.to_uint x %% rans_scale) 2 _; first smt().
  have hp1 : (W32.to_uint x %% rans_scale) %% 2 = 1 by smt().
  rewrite ifF 1:/#; trivial.
+ have hp0 : (W32.to_uint x %% rans_scale) %% 2 = 0.
  - have heq : generated_decoder_parity x = W64.zero by smt().
    have huint := generated_decoder_parity_uint x.
    rewrite heq W64.to_uint0 in huint.
    smt().
  rewrite ifT 1:hp0; trivial.
qed.

lemma truncate_low8_uint (w : W32.t) :
  W32.to_uint w < W8.modulus =>
  W8.to_uint (truncateu8 (zeroextu64 w)) = W32.to_uint w.
proof.
move=> hw.
have [hw0 _] := W32.to_uint_cmp w.
rewrite W8u8.to_uint_truncateu8 W2u32.to_uint_zeroextu64.
rewrite modz_small.
+ rewrite /absz W8.ge0_modulus /=.
  split.
  - exact hw0.
  - move=> _.
    move: hw.
    simplify.
    trivial.
+ trivial.
qed.

lemma generated_decoder_symbol_uint x :
  W32.to_uint
    (actual_mode2_decoder_lookup x `&` W32.of_int 65535) < W8.modulus =>
  W8.to_uint (generated_decoder_symbol x) = actual_mode2_decoder_symbol x.
proof.
move=> hsymbol.
rewrite /generated_decoder_symbol generated_decoder_lookup_matches.
rewrite /actual_mode2_decoder_symbol.
exact (truncate_low8_uint
  (actual_mode2_decoder_lookup x `&` W32.of_int 65535) hsymbol).
qed.

lemma generated_decoder_symbol_expected
    (expected_symbols : BArray2048.t) i :
  mode2_hbz_symbol_stream expected_symbols =>
  0 <= i < mode2_hbz_count =>
  generated_decoder_symbol
    (W32.of_int
      (decoder_state_at (symbol_list_of_array expected_symbols) i)) =
  BArray2048.get8 expected_symbols i.
proof.
move=> hstream hi.
have hlookup :=
  actual_mode2_decoder_lookup_symbol expected_symbols i hstream hi.
have hbound :
  W32.to_uint
    (actual_mode2_decoder_lookup
      (W32.of_int
        (decoder_state_at (symbol_list_of_array expected_symbols) i))
       `&` W32.of_int 65535) < W8.modulus.
+ rewrite /actual_mode2_decoder_symbol in hlookup.
  rewrite hlookup.
  have := W8.to_uint_cmp (BArray2048.get8 expected_symbols i).
  smt().
apply W8.to_uint_eq.
rewrite generated_decoder_symbol_uint 1:hbound.
exact hlookup.
qed.

lemma generated_decoder_low_word_expected
    (expected_symbols : BArray2048.t) i :
  mode2_hbz_symbol_stream expected_symbols =>
  0 <= i < mode2_hbz_count =>
  W32.to_uint
    (generated_decoder_lookup_word
      (W32.of_int
        (decoder_state_at (symbol_list_of_array expected_symbols) i))
     `&` W32.of_int 65535) =
  W8.to_uint (BArray2048.get8 expected_symbols i).
proof.
move=> hstream hi.
rewrite generated_decoder_lookup_matches.
exact (actual_mode2_decoder_lookup_symbol
  expected_symbols i hstream hi).
qed.

lemma hbz_symbol_for_slot_interval_inverse s slot :
  0 <= s < mode2_hbz_alphabet =>
  0 <= slot < rans_scale =>
  hbz_symbol_for_slot slot = s =>
  hbz_start s <= slot < hbz_start s + hbz_freq s.
proof.
rewrite /mode2_hbz_alphabet /rans_scale /hbz_symbol_for_slot
        /hbz_start /hbz_freq.
smt().
qed.

lemma decoder_state_expected_slot_interval
    (expected_symbols : BArray2048.t) i :
  mode2_hbz_symbol_stream expected_symbols =>
  0 <= i < mode2_hbz_count =>
  hbz_start (W8.to_uint (BArray2048.get8 expected_symbols i)) <=
    decoder_state_at (symbol_list_of_array expected_symbols) i %% rans_scale <
  hbz_start (W8.to_uint (BArray2048.get8 expected_symbols i)) +
    hbz_freq (W8.to_uint (BArray2048.get8 expected_symbols i)).
proof.
move=> hstream hi.
have hs := hstream i hi.
have hcan := canonical_symbol_suffix expected_symbols i hstream _; first smt().
have hstate := trace_states_nth_drop
  (symbol_list_of_array expected_symbols) i _.
+ rewrite symbol_list_of_array_size; exact hi.
have hslot := modz_cmp
  (decoder_state_at (symbol_list_of_array expected_symbols) i)
  rans_scale _; first rewrite /rans_scale; smt().
apply (hbz_symbol_for_slot_interval_inverse
  (W8.to_uint (BArray2048.get8 expected_symbols i))
  (decoder_state_at (symbol_list_of_array expected_symbols) i %% rans_scale)
  hs hslot).
rewrite /decoder_state_at hstate.
have hcons := symbol_suffix_cons expected_symbols i hi.
rewrite /symbol_suffix in hcons.
rewrite hcons.
apply trace_head_symbol_selected.
+ exact hs.
+ apply (canonical_symbol_suffix expected_symbols (i + 1) hstream).
  smt().
qed.

lemma generated_decoder_word_update_matches x s :
  W8.to_uint s < mode2_hbz_alphabet =>
  rans_initial_state <= W32.to_uint x < 2147483648 =>
  hbz_start (W8.to_uint s) <= W32.to_uint x %% rans_scale <
    hbz_start (W8.to_uint s) + hbz_freq (W8.to_uint s) =>
  generated_decoder_word_update x s =
    W32.of_int
      (hbz_math_decode_step (W32.to_uint x) (W8.to_uint s)).
proof.
move=> hs hx hslot.
have hs0 : 0 <= W8.to_uint s < mode2_hbz_alphabet by
  have := W8.to_uint_cmp s; smt().
have heq :
    generated_decoder_word_update x s =
    actual_mode2_decoder_word_update x (W8.to_uint s) by
  rewrite /generated_decoder_word_update
          /actual_mode2_decoder_word_update
          /actual_mode2_decoder_freq
          /actual_mode2_decoder_start
          /actual_mode2_decoder_packed /=.
rewrite heq.
exact (actual_mode2_decoder_word_update_correct
  x (W8.to_uint s) hs0 hx hslot).
qed.

lemma generated_decoder_step_preconditions_satisfiable :
  exists x s,
    W8.to_uint s < mode2_hbz_alphabet /\
    rans_initial_state <= W32.to_uint x < 2147483648 /\
    hbz_start (W8.to_uint s) <= W32.to_uint x %% rans_scale <
      hbz_start (W8.to_uint s) + hbz_freq (W8.to_uint s).
proof.
pose n := mode2_normalized_state rans_initial_state 6.
pose y := hbz_fast_encode_step n 6.
exists (W32.of_int y) (W8.of_int 6).
have hs : 0 <= 6 < mode2_hbz_alphabet.
+ rewrite /mode2_hbz_alphabet; smt().
have hinit : rans_initial_state <= rans_initial_state < 2147483648.
+ rewrite /rans_initial_state; smt().
have hn : 1 <= n < hbz_xmax 6.
+ rewrite /n.
  exact (renorm_reduced_bounds 6 rans_initial_state hs hinit).
have hy : rans_initial_state <= y < 2147483648.
+ rewrite /y /n.
  exact (normalized_fast_step_state_bounds 6 rans_initial_state hs hinit).
have hy_eq : y = hbz_math_encode_step n 6.
+ rewrite /y.
  exact (hbz_fast_step_matches_math 6 n hs hn).
have hslot :
    hbz_start 6 <= y %% rans_scale < hbz_start 6 + hbz_freq 6.
+ have [hstart [hfreq hcover]] := hbz_interval_bounds 6 hs.
  rewrite hy_eq /hbz_math_encode_step.
  rewrite (pure_rans_step_slot n (hbz_start 6) (hbz_freq 6)).
  - have hmod := modz_cmp n (hbz_freq 6) hfreq.
    smt().
  - smt().
  - exact hstart.
  - exact hfreq.
  exact hcover.
rewrite W8.to_uint_small.
+ smt().
split; first by move: hs; smt().
split.
+ rewrite W32.to_uint_small.
  - exact hy.
  rewrite /y /n /W32.modulus.
  smt().
rewrite W32.to_uint_small.
+ exact hslot.
rewrite /y /n /W32.modulus.
smt().
qed.

end Mode2RansDecoderGeneratedStep.
