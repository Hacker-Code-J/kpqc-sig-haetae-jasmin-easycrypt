require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansCore.

theory Mode2RansByteStack.

import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansCore.

op byte_radix : int = 256.
op w32_modulus_i : int = 4294967296.

op append_byte (x b : int) : int = byte_radix * x + b.

op read_bytes (x : int) (bs : int list) : int =
  with bs = [] => x
  with bs = b :: tl => read_bytes (append_byte x b) tl.

op renorm_len (x xmax : int) : int =
  if x < xmax then 0
  else if x %/ byte_radix < xmax then 1
  else 2.

op renorm_reduced (x xmax : int) : int =
  if x < xmax then x
  else if x %/ byte_radix < xmax then x %/ byte_radix
  else x %/ (byte_radix * byte_radix).

op renorm_bytes (x xmax : int) : int list =
  if x < xmax then []
  else if x %/ byte_radix < xmax then [x %% byte_radix]
  else [(x %/ byte_radix) %% byte_radix; x %% byte_radix].

op serialize32_le (x : int) : int list =
  [x %% byte_radix;
   (x %/ byte_radix) %% byte_radix;
   (x %/ (byte_radix * byte_radix)) %% byte_radix;
   (x %/ (byte_radix * byte_radix * byte_radix)) %% byte_radix].

op parse32_le (bs : int list) : int =
  nth 0 bs 0 +
  byte_radix * nth 0 bs 1 +
  byte_radix * byte_radix * nth 0 bs 2 +
  byte_radix * byte_radix * byte_radix * nth 0 bs 3.

op mode2_normalization_bytes (x s : int) : int list =
  renorm_bytes x (hbz_xmax s).

op mode2_normalized_state (x s : int) : int =
  renorm_reduced x (hbz_xmax s).

op mode2_normalization_len (x s : int) : int =
  renorm_len x (hbz_xmax s).

op encode_trace (symbols : int list) : int * int list =
  with symbols = [] => (rans_initial_state, [])
  with symbols = s :: tl =>
    let tail = encode_trace tl in
    let reduced = mode2_normalized_state tail.`1 s in
    (hbz_fast_encode_step reduced s,
     mode2_normalization_bytes tail.`1 s ++ tail.`2).

op trace_states (symbols : int list) : int list =
  with symbols = [] => [rans_initial_state]
  with symbols = _ :: tl => (encode_trace symbols).`1 :: trace_states tl.

op trace_segments (symbols : int list) : int list list =
  with symbols = [] => []
  with symbols = s :: tl =>
    mode2_normalization_bytes (encode_trace tl).`1 s :: trace_segments tl.

op cuts_from (cursor : int) (segments : int list list) : int list =
  with segments = [] => [cursor]
  with segments = seg :: tl =>
    cursor :: cuts_from (cursor + size seg) tl.

op trace_cuts (symbols : int list) : int list =
  cuts_from 4 (trace_segments symbols).

op trace_bytes (symbols : int list) : int list =
  serialize32_le (encode_trace symbols).`1 ++ flatten (trace_segments symbols).

op valid_rans_trace
    (symbols xs cuts bytes : int list) : bool =
  xs = trace_states symbols /\
  cuts = trace_cuts symbols /\
  bytes = trace_bytes symbols.

op canonical_symbol_list (symbols : int list) : bool =
  with symbols = [] => true
  with symbols = s :: tl =>
    0 <= s < mode2_hbz_alphabet /\ canonical_symbol_list tl.

lemma renorm_len_range x xmax :
  0 <= renorm_len x xmax <= 2.
proof. rewrite /renorm_len; smt(). qed.

lemma mode2_xmax_lower s :
  0 <= s < mode2_hbz_alphabet =>
  2097152 <= hbz_xmax s.
proof.
move=> hs.
have hf := hbz_frequency_positive s hs.
rewrite /hbz_xmax.
smt().
qed.

lemma renorm_len_le2 s x :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  0 <= mode2_normalization_len x s <= 2.
proof. move=> _ _; exact (renorm_len_range x (hbz_xmax s)). qed.

lemma renorm_reduced_bounds s x :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  1 <= mode2_normalized_state x s < hbz_xmax s.
proof.
move=> hs hx.
have hxm := mode2_xmax_lower s hs.
rewrite /mode2_normalized_state /renorm_reduced /byte_radix.
case (x < hbz_xmax s) => h0; first smt().
case (x %/ 256 < hbz_xmax s) => h1.
+ have hdiv := divz_eq x 256.
  have hmod := modz_cmp x 256 _; first smt().
  smt().
+ have hdiv := divz_eq x 65536.
  have hmod := modz_cmp x 65536 _; first smt().
  smt().
qed.

lemma read_bytes_zero x :
  read_bytes x [] = x.
proof. trivial. qed.

lemma read_bytes_one x b :
  read_bytes x [b] = append_byte x b.
proof. trivial. qed.

lemma read_bytes_two x b0 b1 :
  read_bytes x [b0; b1] = append_byte (append_byte x b0) b1.
proof. trivial. qed.

lemma renorm_bytes_readback s x :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  read_bytes
    (mode2_normalized_state x s)
    (mode2_normalization_bytes x s) = x.
proof.
move=> hs hx.
rewrite /mode2_normalized_state /mode2_normalization_bytes
        /renorm_reduced /renorm_bytes /byte_radix.
case (x < hbz_xmax s) => h0; first trivial.
case (x %/ 256 < hbz_xmax s) => h1.
+ rewrite /read_bytes /append_byte.
  have hdiv := divz_eq x 256.
  smt().
+ rewrite /read_bytes /append_byte.
  have hdiv0 := divz_eq x 256.
  have hdiv1 := divz_eq (x %/ 256) 256.
  have hassoc : x %/ 65536 = x %/ 256 %/ 256.
  + rewrite -divzMr 1:/# 1:/#.
    trivial.
  smt().
qed.

lemma serialize32_parse_inverse x :
  0 <= x < w32_modulus_i =>
  parse32_le (serialize32_le x) = x.
proof.
move=> hx.
rewrite /parse32_le /serialize32_le /byte_radix /=.
have h0 := divz_eq x 256.
have h1 := divz_eq (x %/ 256) 256.
have h2 := divz_eq (x %/ 65536) 256.
have h3 := divz_eq (x %/ 16777216) 256.
have h65536 : x %/ 65536 = x %/ 256 %/ 256.
+ rewrite -divzMr 1:/# 1:/#; trivial.
have h16777216 : x %/ 16777216 = x %/ 65536 %/ 256.
+ by rewrite -divzMr 1:/# 1:/#.
have h4294967296 : x %/ 4294967296 = x %/ 16777216 %/ 256.
+ by rewrite -divzMr 1:/# 1:/#.
have htop : x %/ 4294967296 = 0.
+ apply divz_small.
  rewrite /w32_modulus_i in hx.
  smt().
smt().
qed.

lemma normalized_fast_step_state_bounds s x :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  rans_initial_state <=
    hbz_fast_encode_step (mode2_normalized_state x s) s <
  2147483648.
proof.
move=> hs hx.
have hr := renorm_reduced_bounds s x hs hx.
split.
+ rewrite hbz_fast_step_matches_math 1:hs 1:hr.
  have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
  move: hs_mem.
  do 13! (rewrite range_ltn //=; move=> [->>|];
    [rewrite /mode2_normalized_state /renorm_reduced
             /hbz_xmax /hbz_freq /rans_initial_state
             /byte_radix /= in hr;
     rewrite /mode2_normalized_state /renorm_reduced
             /hbz_xmax /hbz_freq /rans_initial_state
             /byte_radix /= in hx;
     rewrite /hbz_math_encode_step /hbz_start /hbz_freq
             /rans_scale /rans_initial_state /=;
     smt(@IntDiv)|]).
  by rewrite range_geq.
+ have := hbz_fast_step_w32_range
    s (mode2_normalized_state x s) hs hr.
  smt().
qed.

lemma encode_trace_bytes_segments symbols :
  (encode_trace symbols).`2 = flatten (trace_segments symbols).
proof.
elim: symbols => [|s tl ih] /=.
+ trivial.
+ rewrite ih.
  trivial.
qed.

lemma encode_trace_state_bounds symbols :
  canonical_symbol_list symbols =>
  rans_initial_state <= (encode_trace symbols).`1 < 2147483648.
proof.
elim: symbols => [|s tl ih] /=.
+ rewrite /rans_initial_state; smt().
+ move=> [hs htl].
  have htail := ih htl.
  exact (normalized_fast_step_state_bounds
    s (encode_trace tl).`1 hs htail).
qed.

lemma trace_head_symbol_selected s tl :
  0 <= s < mode2_hbz_alphabet =>
  canonical_symbol_list tl =>
  hbz_symbol_for_slot
    ((encode_trace (s :: tl)).`1 %% rans_scale) = s.
proof.
move=> hs htl.
have htail := encode_trace_state_bounds tl htl.
have hr := renorm_reduced_bounds s (encode_trace tl).`1 hs htail.
have hs_copy := hs.
have hnonnegative :
  0 <= mode2_normalized_state (encode_trace tl).`1 s by smt().
rewrite /encode_trace /=.
rewrite hbz_fast_step_matches_math 1:hs 1:hr.
exact (hbz_encoded_slot_selects_symbol s
  (mode2_normalized_state (encode_trace tl).`1 s)
  hs_copy hnonnegative).
qed.

lemma trace_head_decodes_to_reduced s tl :
  0 <= s < mode2_hbz_alphabet =>
  canonical_symbol_list tl =>
  hbz_math_decode_step (encode_trace (s :: tl)).`1 s =
    mode2_normalized_state (encode_trace tl).`1 s.
proof.
move=> hs htl.
have htail := encode_trace_state_bounds tl htl.
have hr := renorm_reduced_bounds s (encode_trace tl).`1 hs htail.
rewrite /encode_trace /=.
exact (hbz_fast_step_decode_inverse
  s (mode2_normalized_state (encode_trace tl).`1 s) hs hr).
qed.

lemma trace_head_normalization_readback s tl :
  0 <= s < mode2_hbz_alphabet =>
  canonical_symbol_list tl =>
  read_bytes
    (hbz_math_decode_step (encode_trace (s :: tl)).`1 s)
    (mode2_normalization_bytes (encode_trace tl).`1 s) =
  (encode_trace tl).`1.
proof.
move=> hs htl.
have htail := encode_trace_state_bounds tl htl.
rewrite trace_head_decodes_to_reduced 1:hs 1:htl.
exact (renorm_bytes_readback s (encode_trace tl).`1 hs htail).
qed.

lemma trace_states_size symbols :
  size (trace_states symbols) = size symbols + 1.
proof.
elim: symbols => [|s tl ih].
+ trivial.
+ rewrite /trace_states /= ih.
  ring.
qed.

lemma trace_states_last symbols :
  nth 0 (trace_states symbols) (size symbols) = rans_initial_state.
proof.
elim: symbols => [|s tl ih].
+ trivial.
+ rewrite /trace_states /=.
  rewrite ifF 1:/#.
  exact ih.
qed.

lemma cuts_from_size cursor segments :
  size (cuts_from cursor segments) = size segments + 1.
proof.
elim: segments cursor => [|seg tl ih] cursor.
+ trivial.
+ rewrite /cuts_from /= ih.
  ring.
qed.

lemma trace_segments_size symbols :
  size (trace_segments symbols) = size symbols.
proof.
elim: symbols => [|s tl ih].
+ trivial.
+ rewrite /trace_segments /= ih.
  trivial.
qed.

lemma trace_cuts_size symbols :
  size (trace_cuts symbols) = size symbols + 1.
proof.
rewrite /trace_cuts cuts_from_size trace_segments_size.
trivial.
qed.

lemma trace_cuts_start symbols :
  nth 0 (trace_cuts symbols) 0 = 4.
proof. by case: symbols => [|s tl] //=; rewrite /trace_cuts. qed.

lemma valid_rans_trace_canonical symbols :
  valid_rans_trace symbols
    (trace_states symbols) (trace_cuts symbols) (trace_bytes symbols).
proof. by rewrite /valid_rans_trace. qed.

lemma byte_stack_preconditions_satisfiable :
  0 <= 6 < mode2_hbz_alphabet /\
  rans_initial_state <= rans_initial_state < 2147483648.
proof.
rewrite /mode2_hbz_alphabet /rans_initial_state.
smt().
qed.

end Mode2RansByteStack.
