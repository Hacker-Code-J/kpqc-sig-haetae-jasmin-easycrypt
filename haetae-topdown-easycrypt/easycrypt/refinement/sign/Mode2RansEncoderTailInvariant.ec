require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  SignaturePackMode2Target
  Mode2HbzCodecSpec Mode2HbzTableCertificate
  Mode2RansByteStack Mode2RansNormalization
  Mode2RansEncodeRefinement Mode2RansArrayListBridge Mode2RansEncoderTrace
  Mode2RansEncoderInnerProgress Mode2RansEncoderWordStep.

theory Mode2RansEncoderTailInvariant.

import Mode2HbzCodecSpec Mode2HbzTableCertificate
       Mode2RansByteStack Mode2RansNormalization
       Mode2RansEncodeRefinement Mode2RansArrayListBridge Mode2RansEncoderTrace
       Mode2RansEncoderInnerProgress Mode2RansEncoderWordStep.

op encoder_outer_tail_inv
    (enc0 symbols0 encp : BArray2048.t)
    (i : int) (x : W32.t) (off : W64.t) : bool =
  0 <= i <= mode2_hbz_count /\
  W32.to_uint x = (encode_trace (symbol_suffix symbols0 i)).`1 /\
  W64.to_uint off + size (encode_trace (symbol_suffix symbols0 i)).`2 =
    mode2_hbz_count /\
  segment_matches encp (W64.to_uint off)
    (encode_trace (symbol_suffix symbols0 i)).`2 /\
  prefix_frame enc0 encp (W64.to_uint off) /\
  4 <= W64.to_uint off.

op encoder_inner_tail_inv
    (before : BArray2048.t) (symbol_tail : int list) (s : int)
    (x : W32.t) (off : W64.t) (encp : BArray2048.t) : bool =
  exists (x0 : W32.t) off0 k,
    (4 <= off0 <= mode2_hbz_count) /\
    W32.to_uint x0 = (encode_trace symbol_tail).`1 /\
    off0 + size (encode_trace symbol_tail).`2 = mode2_hbz_count /\
    (0 <= k <= mode2_normalization_len (W32.to_uint x0) s) /\
    (rans_initial_state <= W32.to_uint x0 < 2147483648) /\
    W64.to_uint off = off0 - k /\
    W32.to_uint x = inner_state_after (W32.to_uint x0) k /\
    segment_matches encp (off0 - k)
      (inner_written_suffix (W32.to_uint x0) s k ++
       (encode_trace symbol_tail).`2) /\
    prefix_frame before encp (off0 - k).

op encoder_inner_tail_live
    (before : BArray2048.t) (symbol_tail : int list) (s : int)
    (x : W32.t) (off : W64.t) (encp : BArray2048.t) : bool =
  0 <= s < mode2_hbz_alphabet /\
  encoder_inner_tail_inv before symbol_tail s x off encp.

lemma encoder_inner_tail_byte_word x x0 k :
  W32.to_uint x = inner_state_after x0 k =>
  truncateu8 x = W8.of_int (inner_state_after x0 k %% byte_radix).
proof.
move=> hx.
rewrite -(W8.to_uintK' (truncateu8 x)).
congr.
rewrite encoder_low_byte_uint hx /byte_radix.
trivial.
qed.

lemma encoder_inner_tail_prefix_step
    (before encp : BArray2048.t) off0 k (off : W64.t) (value : W8.t) :
  W64.to_uint off = off0 - k =>
  0 < off0 - k <= mode2_hbz_capacity =>
  prefix_frame before encp (off0 - k) =>
  prefix_frame before
    (BArray2048.set8 encp (W64.to_uint (off - W64.one)) value)
    (off0 - (k + 1)).
proof.
move=> hoff hfit hframe.
rewrite cursor_decrement_no_underflow 1:/# hoff.
have -> : off0 - (k + 1) = off0 - k - 1 by ring.
exact (prefix_frame_prepend_write before encp (off0 - k)
  value hfit hframe).
qed.

lemma encoder_inner_tail_segment_word_step
    (encp : BArray2048.t) off0 k (off : W64.t) (x x0 : W32.t)
    s (tail : int list) :
  W64.to_uint off = off0 - k =>
  W32.to_uint x = inner_state_after (W32.to_uint x0) k =>
  segment_matches
    (BArray2048.set8 encp (off0 - k - 1)
      (W8.of_int (inner_state_after (W32.to_uint x0) k %% byte_radix)))
    (off0 - (k + 1))
    (inner_written_suffix (W32.to_uint x0) s (k + 1) ++ tail) =>
  segment_matches
    (BArray2048.set8 encp (W64.to_uint (off - W64.one)) (truncateu8 x))
    (off0 - (k + 1))
    (inner_written_suffix (W32.to_uint x0) s (k + 1) ++ tail).
proof.
move=> hoff hx hsegment.
rewrite cursor_decrement_no_underflow 1:/# hoff.
rewrite (encoder_inner_tail_byte_word x (W32.to_uint x0) k hx).
exact hsegment.
qed.

lemma encoder_inner_tail_shift_word (x : W32.t) x0 k :
  W32.to_uint x = inner_state_after x0 k =>
  0 <= k < 2 =>
  W32.to_uint (x `>>` W8.of_int 8) = inner_state_after x0 (k + 1).
proof.
move=> hx hk.
rewrite encoder_shift8_uint hx.
rewrite -(inner_state_after_step x0 k hk).
trivial.
qed.

lemma encoder_inner_tail_exit_index s (x0 x : W32.t) k :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= W32.to_uint x0 < 2147483648 =>
  0 <= k =>
  k <= mode2_normalization_len (W32.to_uint x0) s =>
  W32.to_uint x = inner_state_after (W32.to_uint x0) k =>
  !(hbz_xmax_word s \ule x) =>
  k = mode2_normalization_len (W32.to_uint x0) s.
proof.
move=> hs hx0 hklo hkhi hxcur hstop.
case (k = mode2_normalization_len (W32.to_uint x0) s) => // hne.
have hkl : 0 <= k < mode2_normalization_len (W32.to_uint x0) s by
  smt().
have hbig := inner_guard_before_total s (W32.to_uint x0) k hkl.
rewrite W32.uleE hbz_xmax_word_uint 1:hs in hstop.
rewrite -hxcur in hbig.
smt().
qed.

lemma encoder_inner_tail_cursor_positive before symbol_tail s x off encp :
  0 <= s < mode2_hbz_alphabet =>
  encoder_inner_tail_inv before symbol_tail s x off encp =>
  hbz_xmax_word s \ule x =>
  0 < W64.to_uint off.
proof.
move=> hs hinv hguard.
rewrite /encoder_inner_tail_inv in hinv.
move: hinv => [x0 off0 k
  [[hofflo hoffhi] [hstate0 [hcursor0 [[hklo hkhi]
   [hx0 [hoffcur [hxcur [hbytes hframe]]]]]]]]].
have htotal : 0 <= mode2_normalization_len (W32.to_uint x0) s <= 2.
+ exact (renorm_len_le2 s (W32.to_uint x0) hs hx0).
have hklt : k < mode2_normalization_len (W32.to_uint x0) s.
+ have hsmall := inner_guard_after_total s (W32.to_uint x0) hs hx0.
  rewrite W32.uleE hbz_xmax_word_uint 1:hs in hguard.
  smt(inner_state_after_total).
rewrite hoffcur.
smt().
qed.

lemma encoder_outer_tail_init enc0 symbols0 :
  mode2_hbz_symbol_stream symbols0 =>
  encoder_outer_tail_inv
    enc0 symbols0 enc0 mode2_hbz_count
    (W32.of_int rans_initial_state) (W64.of_int mode2_hbz_count).
proof.
move=> hstream.
rewrite /encoder_outer_tail_inv.
split; first smt().
split.
+ rewrite symbol_suffix_at_end /=.
   rewrite W32.to_uint_small.
   - trivial.
   rewrite /rans_initial_state /w32_modulus_i.
   smt().
split.
+ rewrite symbol_suffix_at_end /=.
   rewrite W64.of_uintK /= /mode2_hbz_count.
   trivial.
split.
+ rewrite symbol_suffix_at_end /=.
   apply segment_matches_nil.
   rewrite /mode2_hbz_count /mode2_hbz_capacity.
   smt().
split.
+ exact (prefix_frame_refl enc0 mode2_hbz_count).
rewrite W64.of_uintK /= /mode2_hbz_count.
trivial.
qed.

lemma encoder_outer_tail_init_unconditional enc0 symbols0 :
  encoder_outer_tail_inv
    enc0 symbols0 enc0 mode2_hbz_count
    (W32.of_int rans_initial_state) (W64.of_int mode2_hbz_count).
proof.
rewrite /encoder_outer_tail_inv.
split; first smt().
split.
+ rewrite symbol_suffix_at_end /=.
  rewrite W32.to_uint_small.
  - trivial.
  rewrite /rans_initial_state /w32_modulus_i.
  smt().
split.
+ rewrite symbol_suffix_at_end /=.
  rewrite W64.of_uintK /= /mode2_hbz_count.
  trivial.
split.
+ rewrite symbol_suffix_at_end /=.
  apply segment_matches_nil.
  rewrite /mode2_hbz_count /mode2_hbz_capacity.
  smt().
split.
+ exact (prefix_frame_refl enc0 mode2_hbz_count).
rewrite W64.of_uintK /= /mode2_hbz_count.
trivial.
qed.

lemma encoder_inner_tail_init before symbol_tail s x off encp :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= W32.to_uint x < 2147483648 =>
  4 <= W64.to_uint off <= mode2_hbz_count =>
  W32.to_uint x = (encode_trace symbol_tail).`1 =>
  W64.to_uint off + size (encode_trace symbol_tail).`2 = mode2_hbz_count =>
  segment_matches encp (W64.to_uint off) (encode_trace symbol_tail).`2 =>
  prefix_frame before encp (W64.to_uint off) =>
  encoder_inner_tail_inv before symbol_tail s x off encp.
proof.
move=> hs hx hoff hstate hcursor htail hframe.
rewrite /encoder_inner_tail_inv.
exists x (W64.to_uint off) 0.
split; first exact hoff.
split.
+ exact hstate.
split.
+ exact hcursor.
split.
+ have hlen := renorm_len_le2 s (W32.to_uint x) hs hx.
   smt().
split; first exact hx.
split.
+ smt().
split.
+ rewrite inner_state_after_zero.
   trivial.
split.
+ have hzero := inner_written_suffix_zero s (W32.to_uint x) hs hx.
   rewrite hzero /=.
   exact htail.
exact hframe.
qed.

lemma encoder_inner_tail_progress before symbol_tail s x off encp :
  0 <= s < mode2_hbz_alphabet =>
  encoder_inner_tail_inv before symbol_tail s x off encp =>
  hbz_xmax_word s \ule x =>
  encoder_inner_tail_inv before symbol_tail s
    (x `>>` W8.of_int 8)
    (off - W64.one)
    (BArray2048.set8 encp (W64.to_uint (off - W64.one)) (truncateu8 x)).
proof.
move=> hs hinv hguard.
rewrite /encoder_inner_tail_inv in hinv.
move: hinv => [x0 off0 k
  [[hofflo hoffhi] [hstate0 [hcursor0 [[hklo hkhi]
   [hx0 [hoffcur [hxcur [hbytes hframe]]]]]]]]].
have htotal : 0 <= mode2_normalization_len (W32.to_uint x0) s <= 2.
+ exact (renorm_len_le2 s (W32.to_uint x0) hs hx0).
have hklt : k < mode2_normalization_len (W32.to_uint x0) s.
+ have hsmall := inner_guard_after_total s (W32.to_uint x0) hs hx0.
   rewrite W32.uleE hbz_xmax_word_uint 1:hs in hguard.
   smt(inner_state_after_total).
have hpos : 0 < off0 - k.
+ have hfit : mode2_normalization_len (W32.to_uint x0) s <= off0.
   - move: htotal => [_ hle2].
     smt().
   have hkoff := inner_progress_cursor off0 k
     (mode2_normalization_len (W32.to_uint x0) s) htotal _ hfit.
   * smt().
   smt().
have hkstep : 0 <= k < mode2_normalization_len (W32.to_uint x0) s by
  smt().
have hfitstep : mode2_normalization_len (W32.to_uint x0) s <= off0 by
  move: htotal => [_ hle2]; smt().
have hstepseg :=
  inner_progress_segment_step encp off0 (W32.to_uint x0) s k
    (encode_trace symbol_tail).`2
    hs hx0 hkstep hfitstep hbytes.
rewrite /encoder_inner_tail_inv.
exists x0 off0 (k + 1).
split; first smt().
split.
+ exact hstate0.
split.
+ exact hcursor0.
split.
+ smt().
split; first exact hx0.
split.
+ rewrite cursor_decrement_no_underflow.
   - rewrite hoffcur.
     exact hpos.
   rewrite hoffcur.
   ring.
have hk2 : 0 <= k < 2 by smt().
have hxnext := encoder_inner_tail_shift_word
  x (W32.to_uint x0) k hxcur hk2.
split; first exact hxnext.
split; first exact (encoder_inner_tail_segment_word_step
  encp off0 k off x x0 s (encode_trace symbol_tail).`2
  hoffcur hxcur hstepseg).
apply (encoder_inner_tail_prefix_step before encp off0 k off (truncateu8 x)).
+ exact hoffcur.
+ rewrite /mode2_hbz_capacity /mode2_hbz_count; smt().
exact hframe.
qed.

lemma encoder_inner_tail_live_progress before symbol_tail s x off encp :
  encoder_inner_tail_live before symbol_tail s x off encp =>
  hbz_xmax_word s \ule x =>
  encoder_inner_tail_live before symbol_tail s
    (x `>>` W8.of_int 8)
    (off - W64.one)
    (BArray2048.set8 encp (W64.to_uint (off - W64.one)) (truncateu8 x)).
proof.
move=> [hs hinv] hguard.
split; first exact hs.
exact (encoder_inner_tail_progress before symbol_tail s x off encp
  hs hinv hguard).
qed.

lemma encoder_inner_tail_exit_exact before symbol_tail s x off encp :
  0 <= s < mode2_hbz_alphabet =>
  encoder_inner_tail_inv before symbol_tail s x off encp =>
  !(hbz_xmax_word s \ule x) =>
  exists (x0 : W32.t) off0,
    (4 <= off0 <= mode2_hbz_count) /\
    W32.to_uint x0 = (encode_trace symbol_tail).`1 /\
    off0 + size (encode_trace symbol_tail).`2 = mode2_hbz_count /\
    (rans_initial_state <= W32.to_uint x0 < 2147483648) /\
    W64.to_uint off =
      off0 - mode2_normalization_len (W32.to_uint x0) s /\
    W32.to_uint x = mode2_normalized_state (W32.to_uint x0) s /\
    segment_matches encp (W64.to_uint off)
      (mode2_normalization_bytes (W32.to_uint x0) s ++
       (encode_trace symbol_tail).`2) /\
    prefix_frame before encp (W64.to_uint off).
proof.
move=> hs hinv hstop.
rewrite /encoder_inner_tail_inv in hinv.
move: hinv => [x0 off0 k
  [[hofflo hoffhi] [hstate0 [hcursor0 [[hklo hkhi]
   [hx0 [hoffcur [hxcur [hbytes hframe]]]]]]]]].
case (k = mode2_normalization_len (W32.to_uint x0) s) => [->>|hknot].
+ rewrite inner_written_suffix_total in hbytes.
  rewrite inner_state_after_total in hxcur.
  rewrite -hoffcur in hbytes.
  rewrite -hoffcur in hframe.
  exists x0 off0.
  split; first smt().
  split; first exact hstate0.
  split; first exact hcursor0.
  split; first exact hx0.
  split; first exact hoffcur.
  split; first exact hxcur.
  split; first exact hbytes.
  exact hframe.
+ have hkdone := encoder_inner_tail_exit_index s x0 x k
    hs hx0 hklo hkhi hxcur hstop.
  smt().
qed.

lemma encoder_outer_tail_to_inner enc0 symbols0 encp i x off :
  mode2_hbz_symbol_stream symbols0 =>
  0 <= i < mode2_hbz_count =>
  encoder_outer_tail_inv enc0 symbols0 encp (i + 1) x off =>
  encoder_inner_tail_inv enc0
    (symbol_suffix symbols0 (i + 1))
    (W8.to_uint (BArray2048.get8 symbols0 i))
    x off encp.
proof.
move=> hstream hi hout.
rewrite /encoder_outer_tail_inv in hout.
move: hout => [hiinv [hx [hoff [htail [hframe hofflo]]]]].
have hs : 0 <= W8.to_uint (BArray2048.get8 symbols0 i) < mode2_hbz_alphabet.
+ exact (hstream i hi).
have hxbound :
    rans_initial_state <= W32.to_uint x < 2147483648.
+ rewrite hx.
   apply encode_trace_suffix_state_bound.
   - exact hstream.
   smt().
have hoffbound : 4 <= W64.to_uint off <= mode2_hbz_count by
  smt(List.size_ge0).
exact (encoder_inner_tail_init enc0
  (symbol_suffix symbols0 (i + 1))
  (W8.to_uint (BArray2048.get8 symbols0 i))
  x off encp hs hxbound hoffbound hx hoff htail hframe).
qed.

lemma encoder_tail_state_extension symbols0 i s (x0 : W32.t) :
  mode2_hbz_symbol_stream symbols0 =>
  0 <= i < mode2_hbz_count =>
  s = W8.to_uint (BArray2048.get8 symbols0 i) =>
  W32.to_uint x0 = (encode_trace (symbol_suffix symbols0 (i + 1))).`1 =>
  (encode_trace (symbol_suffix symbols0 i)).`1 =
    hbz_fast_encode_step (mode2_normalized_state (W32.to_uint x0) s) s.
proof.
move=> hstream hi hs hx0.
have [hstate _] := encode_trace_suffix_extension symbols0 i hstream hi.
rewrite hs hx0.
exact hstate.
qed.

lemma encoder_tail_bytes_extension symbols0 i s (x0 : W32.t) :
  mode2_hbz_symbol_stream symbols0 =>
  0 <= i < mode2_hbz_count =>
  s = W8.to_uint (BArray2048.get8 symbols0 i) =>
  W32.to_uint x0 = (encode_trace (symbol_suffix symbols0 (i + 1))).`1 =>
  (encode_trace (symbol_suffix symbols0 i)).`2 =
    mode2_normalization_bytes (W32.to_uint x0) s ++
    (encode_trace (symbol_suffix symbols0 (i + 1))).`2.
proof.
move=> hstream hi hs hx0.
have [_ hbytes] := encode_trace_suffix_extension symbols0 i hstream hi.
rewrite hs hx0.
exact hbytes.
qed.

lemma encoder_outer_tail_advance_success
    enc0 symbols0 encp i s x off :
  mode2_hbz_symbol_stream symbols0 =>
  0 <= i < mode2_hbz_count =>
  s = W8.to_uint (BArray2048.get8 symbols0 i) =>
  0 <= s < mode2_hbz_alphabet =>
  4 <= W64.to_uint off =>
  (exists (x0 : W32.t) off0,
    (4 <= off0 <= mode2_hbz_count) /\
    W32.to_uint x0 = (encode_trace (symbol_suffix symbols0 (i + 1))).`1 /\
    off0 + size (encode_trace (symbol_suffix symbols0 (i + 1))).`2 =
      mode2_hbz_count /\
    (rans_initial_state <= W32.to_uint x0 < 2147483648) /\
    W64.to_uint off = off0 - mode2_normalization_len (W32.to_uint x0) s /\
    W32.to_uint x = mode2_normalized_state (W32.to_uint x0) s /\
    segment_matches encp (W64.to_uint off)
      (mode2_normalization_bytes (W32.to_uint x0) s ++
       (encode_trace (symbol_suffix symbols0 (i + 1))).`2) /\
    prefix_frame enc0 encp (W64.to_uint off)) =>
  encoder_outer_tail_inv enc0 symbols0 encp i
    (actual_mode2_encoder_word_step x s) off.
proof.
move=> hstream hi hsdef hs hofflive hexit.
move: hexit => [x0 off0 hexit].
move: hexit => [hoffbound hexit].
move: hoffbound => [hofflo hoffhi].
move: hexit => [hstate0 hexit].
move: hexit => [hcursor0 hexit].
move: hexit => [hx0 hexit].
move: hexit => [hoffcur hexit].
move: hexit => [hxcur hexit].
move: hexit => [hbytes hframe].
rewrite -(encoder_tail_bytes_extension
  symbols0 i s x0 hstream hi hsdef hstate0) in hbytes.
have hxstep : 1 <= W32.to_uint x < hbz_xmax s.
+ rewrite hxcur.
  exact (renorm_reduced_bounds s (W32.to_uint x0) hs hx0).
rewrite /encoder_outer_tail_inv.
split; first smt().
split.
+ rewrite actual_mode2_encoder_word_step_correct 1:hs 1:hxstep.
   have hfast := hbz_fast_step_w32_range s (W32.to_uint x) hs hxstep.
   have hsmall :
       0 <= hbz_fast_encode_step (W32.to_uint x) s < w32_modulus_i by
     rewrite /w32_modulus_i; smt().
   rewrite W32.to_uint_small 1:hsmall.
   rewrite hxcur.
   rewrite (encoder_tail_state_extension
     symbols0 i s x0 hstream hi hsdef hstate0).
   trivial.
split.
+ rewrite (encoder_tail_bytes_extension
     symbols0 i s x0 hstream hi hsdef hstate0) size_cat hoffcur.
   have hcase := mode2_normalization_bytes_size s (W32.to_uint x0) hs hx0.
   move: hcase => [hlen _].
   rewrite hlen.
   smt().
split.
+ exact hbytes.
split; first exact hframe.
exact hofflive.
qed.

end Mode2RansEncoderTailInvariant.
