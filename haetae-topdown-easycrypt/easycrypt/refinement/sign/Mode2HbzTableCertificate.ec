require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require SignaturePackMode2Target SignatureUnpackMode2Target.
require import Mode2HbzCodecSpec.

theory Mode2HbzTableCertificate.

import Mode2HbzCodecSpec.

op hbz_start (s : int) : int =
  if s = 0 then 0 else
  if s = 1 then 1 else
  if s = 2 then 2 else
  if s = 3 then 3 else
  if s = 4 then 8 else
  if s = 5 then 66 else
  if s = 6 then 312 else
  if s = 7 then 710 else
  if s = 8 then 957 else
  if s = 9 then 1016 else
  if s = 10 then 1021 else
  if s = 11 then 1022 else
  if s = 12 then 1023 else 0.

op hbz_freq (s : int) : int =
  if s = 0 then 1 else
  if s = 1 then 1 else
  if s = 2 then 1 else
  if s = 3 then 5 else
  if s = 4 then 58 else
  if s = 5 then 246 else
  if s = 6 then 398 else
  if s = 7 then 247 else
  if s = 8 then 59 else
  if s = 9 then 5 else
  if s = 10 then 1 else
  if s = 11 then 1 else
  if s = 12 then 1 else 0.

op hbz_rcp_word (s : int) : W32.t =
  if s = 0 then W32.of_int (-1) else
  if s = 1 then W32.of_int (-1) else
  if s = 2 then W32.of_int (-1) else
  if s = 3 then W32.of_int (-858993459) else
  if s = 4 then W32.of_int (-1925330167) else
  if s = 5 then W32.of_int (-2060187564) else
  if s = 6 then W32.of_int (-1532375266) else
  if s = 7 then W32.of_int (-2069235255) else
  if s = 8 then W32.of_int (-1965493508) else
  if s = 9 then W32.of_int (-858993459) else
  if s = 10 then W32.of_int (-1) else
  if s = 11 then W32.of_int (-1) else
  if s = 12 then W32.of_int (-1) else W32.zero.

op hbz_rcp_uint (s : int) : int =
  if hbz_freq s = 1 then 4294967295 else
  if hbz_freq s = 5 then 3435973837 else
  if hbz_freq s = 58 then 2369637129 else
  if hbz_freq s = 246 then 2234779732 else
  if hbz_freq s = 398 then 2762592030 else
  if hbz_freq s = 247 then 2225732041 else
  if hbz_freq s = 59 then 2329473788 else 0.

op hbz_rcp_shift (s : int) : int =
  if hbz_freq s = 1 then 0 else
  if hbz_freq s = 5 then 2 else
  if hbz_freq s = 58 then 5 else
  if hbz_freq s = 246 then 7 else
  if hbz_freq s = 398 then 8 else
  if hbz_freq s = 247 then 7 else
  if hbz_freq s = 59 then 5 else 0.

op hbz_bias (s : int) : int =
  if hbz_freq s = 1 then hbz_start s + rans_scale - 1
  else hbz_start s.

op hbz_xmax (s : int) : int = 2097152 * hbz_freq s.

op hbz_complement (s : int) : int = rans_scale - hbz_freq s.

op hbz_packed_encoder_word (s : int) : int =
  65536 * hbz_rcp_shift s + hbz_complement s.

op hbz_encoder_field (s k : int) : W32.t =
  if k = 0 then W32.of_int (hbz_xmax s) else
  if k = 1 then hbz_rcp_word s else
  if k = 2 then W32.of_int (hbz_bias s) else
  W32.of_int (hbz_packed_encoder_word s).

op hbz_decoder_word (s : int) : W32.t =
  W32.of_int (65536 * hbz_freq s + hbz_start s).

op hbz_symbol_for_slot (slot : int) : int =
  if slot < 1 then 0 else
  if slot < 2 then 1 else
  if slot < 3 then 2 else
  if slot < 8 then 3 else
  if slot < 66 then 4 else
  if slot < 312 then 5 else
  if slot < 710 then 6 else
  if slot < 957 then 7 else
  if slot < 1016 then 8 else
  if slot < 1021 then 9 else
  if slot < 1022 then 10 else
  if slot < 1023 then 11 else 12.

op table_symbol_at (table : BArray2048.t) (slot : int) : int =
  let word = BArray2048.get32 table (slot %/ 2) in
  if slot %% 2 = 0 then W32.to_uint word %% 65536
  else W32.to_uint word %/ 65536.

op hbz_packed_symbol_word (word_index : int) : int =
  hbz_symbol_for_slot (2 * word_index) +
  65536 * hbz_symbol_for_slot (2 * word_index + 1).

op hbz_required_quotient (x s : int) : int =
  if hbz_freq s = 1 then x - 1 else x %/ hbz_freq s.

op hbz_reciprocal_quotient (x s : int) : int =
  ((x * hbz_rcp_uint s) %/ 4294967296) %/ (2 ^ hbz_rcp_shift s).

op hbz_math_encode_step (x s : int) : int =
  (x %/ hbz_freq s) * rans_scale + hbz_start s + x %% hbz_freq s.

op hbz_fast_encode_step (x s : int) : int =
  x + hbz_bias s + hbz_required_quotient x s * hbz_complement s.

op mode2_hbz_table_certificate
    (esyms dsyms : BArray528.t) (symbol_words : BArray2048.t) : bool =
  (forall s k, 0 <= s < mode2_hbz_alphabet => 0 <= k < 4 =>
     BArray528.get32 esyms (4 * s + k) = hbz_encoder_field s k) /\
  (forall s, 0 <= s < mode2_hbz_alphabet =>
     BArray528.get32 dsyms s = hbz_decoder_word s) /\
  (forall slot, 0 <= slot < rans_scale =>
     table_symbol_at symbol_words slot = hbz_symbol_for_slot slot).

lemma hbz_frequency_positive s :
  0 <= s < mode2_hbz_alphabet => 0 < hbz_freq s.
proof.
rewrite /mode2_hbz_alphabet /hbz_freq.
smt().
qed.

lemma hbz_frequency_sum :
  hbz_freq 0 + hbz_freq 1 + hbz_freq 2 + hbz_freq 3 +
  hbz_freq 4 + hbz_freq 5 + hbz_freq 6 + hbz_freq 7 +
  hbz_freq 8 + hbz_freq 9 + hbz_freq 10 + hbz_freq 11 +
  hbz_freq 12 = rans_scale.
proof. by rewrite /hbz_freq /rans_scale. qed.

lemma hbz_intervals_adjacent s :
  0 <= s < mode2_hbz_alphabet - 1 =>
  hbz_start (s + 1) = hbz_start s + hbz_freq s.
proof.
rewrite /mode2_hbz_alphabet /hbz_start /hbz_freq.
smt().
qed.

lemma hbz_intervals_cover_scale :
  hbz_start 0 = 0 /\
  hbz_start 12 + hbz_freq 12 = rans_scale.
proof. by rewrite /hbz_start /hbz_freq /rans_scale. qed.

lemma hbz_slot_interval s slot :
  0 <= s < mode2_hbz_alphabet =>
  hbz_start s <= slot < hbz_start s + hbz_freq s =>
  hbz_symbol_for_slot slot = s.
proof.
rewrite /mode2_hbz_alphabet /hbz_start /hbz_freq
        /hbz_symbol_for_slot.
smt().
qed.

lemma hbz_rcp_word_uint s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint (hbz_rcp_word s) = hbz_rcp_uint s.
proof.
move=> hs.
case (s = 0) => hs0.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 1) => hs1.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 2) => hs2.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 3) => hs3.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 4) => hs4.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 5) => hs5.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 6) => hs6.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 7) => hs7.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 8) => hs8.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 9) => hs9.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 10) => hs10.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
case (s = 11) => hs11.
+ subst s; by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
have -> : s = 12 by rewrite /mode2_hbz_alphabet in hs; smt().
by rewrite /hbz_freq /hbz_rcp_word /hbz_rcp_uint.
qed.

lemma actual_mode2_hbz_esym_symbol_0 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms k =
  hbz_encoder_field 0 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_1 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (4 + k) =
  hbz_encoder_field 1 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_2 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (8 + k) =
  hbz_encoder_field 2 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_3 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (12 + k) =
  hbz_encoder_field 3 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_4 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (16 + k) =
  hbz_encoder_field 4 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_5 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (20 + k) =
  hbz_encoder_field 5 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_6 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (24 + k) =
  hbz_encoder_field 6 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_7 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (28 + k) =
  hbz_encoder_field 7 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_8 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (32 + k) =
  hbz_encoder_field 8 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_9 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (36 + k) =
  hbz_encoder_field 9 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_10 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (40 + k) =
  hbz_encoder_field 10 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_11 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (44 + k) =
  hbz_encoder_field 11 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_symbol_12 k :
  0 <= k < 4 =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (48 + k) =
  hbz_encoder_field 12 k.
proof.
move=> hk; have hm : k \in range 0 4 by rewrite mem_range.
move: hm.
do 4! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_encoder_field /hbz_xmax /hbz_freq
              /hbz_rcp_word /hbz_bias /hbz_start /rans_scale
              /hbz_packed_encoder_word /hbz_rcp_shift /hbz_complement
              /SignaturePackMode2Target.jmode2_hb_z1_esyms
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_hbz_esym_fields s k :
  0 <= s < mode2_hbz_alphabet =>
  0 <= k < 4 =>
  BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms (4 * s + k) =
  hbz_encoder_field s k.
proof.
move=> hs hk.
case (s = 0) => h0; first by subst s; apply actual_mode2_hbz_esym_symbol_0.
case (s = 1) => h1; first by subst s; apply actual_mode2_hbz_esym_symbol_1.
case (s = 2) => h2; first by subst s; apply actual_mode2_hbz_esym_symbol_2.
case (s = 3) => h3; first by subst s; apply actual_mode2_hbz_esym_symbol_3.
case (s = 4) => h4; first by subst s; apply actual_mode2_hbz_esym_symbol_4.
case (s = 5) => h5; first by subst s; apply actual_mode2_hbz_esym_symbol_5.
case (s = 6) => h6; first by subst s; apply actual_mode2_hbz_esym_symbol_6.
case (s = 7) => h7; first by subst s; apply actual_mode2_hbz_esym_symbol_7.
case (s = 8) => h8; first by subst s; apply actual_mode2_hbz_esym_symbol_8.
case (s = 9) => h9; first by subst s; apply actual_mode2_hbz_esym_symbol_9.
case (s = 10) => h10; first by subst s; apply actual_mode2_hbz_esym_symbol_10.
case (s = 11) => h11; first by subst s; apply actual_mode2_hbz_esym_symbol_11.
have -> : s = 12 by rewrite /mode2_hbz_alphabet in hs; smt().
by apply actual_mode2_hbz_esym_symbol_12.
qed.

lemma actual_mode2_hbz_dsym_words s :
  0 <= s < mode2_hbz_alphabet =>
  BArray528.get32
    SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words s =
  hbz_decoder_word s.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_decoder_word /hbz_freq /hbz_start
              /SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words
              BArray528.get32_of_list32 1:// 1:// /=|]).
by rewrite range_geq.
qed.

lemma hbz_symbol_for_slot_range slot :
  0 <= slot < rans_scale =>
  0 <= hbz_symbol_for_slot slot < mode2_hbz_alphabet.
proof.
rewrite /rans_scale /mode2_hbz_alphabet /hbz_symbol_for_slot.
smt().
qed.

lemma hbz_packed_symbol_word_uint word_index :
  0 <= word_index < 512 =>
  W32.to_uint (W32.of_int (hbz_packed_symbol_word word_index)) =
  hbz_packed_symbol_word word_index.
proof.
move=> hword.
have hlo := hbz_symbol_for_slot_range (2 * word_index) _.
+ rewrite /rans_scale; smt().
have hhi := hbz_symbol_for_slot_range (2 * word_index + 1) _.
+ rewrite /rans_scale; smt().
rewrite W32.of_uintK modz_small 1:/#.
trivial.
qed.

lemma hbz_packed_symbol_word_low word_index :
  0 <= word_index < 512 =>
  hbz_packed_symbol_word word_index %% 65536 =
  hbz_symbol_for_slot (2 * word_index).
proof.
move=> hword.
have hlo := hbz_symbol_for_slot_range (2 * word_index) _.
+ rewrite /rans_scale; smt().
have hhi := hbz_symbol_for_slot_range (2 * word_index + 1) _.
+ rewrite /rans_scale; smt().
rewrite /hbz_packed_symbol_word.
have -> :
    65536 * hbz_symbol_for_slot (2 * word_index + 1) =
    hbz_symbol_for_slot (2 * word_index + 1) * 65536 by ring.
rewrite modzMDr modz_small 1:/#.
trivial.
qed.

lemma hbz_packed_symbol_word_high word_index :
  0 <= word_index < 512 =>
  hbz_packed_symbol_word word_index %/ 65536 =
  hbz_symbol_for_slot (2 * word_index + 1).
proof.
move=> hword.
have hlo := hbz_symbol_for_slot_range (2 * word_index) _.
+ rewrite /rans_scale; smt().
have hhi := hbz_symbol_for_slot_range (2 * word_index + 1) _.
+ rewrite /rans_scale; smt().
rewrite /hbz_packed_symbol_word.
have -> :
    65536 * hbz_symbol_for_slot (2 * word_index + 1) =
    hbz_symbol_for_slot (2 * word_index + 1) * 65536 by ring.
rewrite divzMDr 1:/# divz_small 1:/#.
trivial.
qed.

lemma mode2_hbz_pack_unpack_tables_identical :
  SignaturePackMode2Target.jmode2_hb_z1_esyms =
    SignatureUnpackMode2Target.jmode2_hb_z1_esyms /\
  SignaturePackMode2Target.jmode2_hb_z1_symbol_words =
    SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words /\
  SignaturePackMode2Target.jmode2_hb_z1_dsyms_words =
    SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words.
proof.
rewrite /SignaturePackMode2Target.jmode2_hb_z1_esyms
        /SignatureUnpackMode2Target.jmode2_hb_z1_esyms
        /SignaturePackMode2Target.jmode2_hb_z1_symbol_words
        /SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words
        /SignaturePackMode2Target.jmode2_hb_z1_dsyms_words
        /SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words.
trivial.
qed.

lemma decoder_low_halfword_semantics (word : W32.t) :
  W32.to_uint (word `&` W32.of_int 65535) = W32.to_uint word %% 65536.
proof.
rewrite (W32.to_uint_and_mod 16) 1:/#.
trivial.
qed.

lemma decoder_high_halfword_semantics (word : W32.t) :
  W32.to_uint ((word `>>` W8.of_int 16) `&` W32.of_int 65535) =
  W32.to_uint word %/ 65536.
proof.
rewrite (W32.to_uint_and_mod 16) 1:/# W32.shr_div
        W8.of_uintK /=.
have hq : 0 <= W32.to_uint word %/ 65536 < 65536.
+ have hw := W32.to_uint_cmp word.
  smt(@IntDiv).
rewrite modz_small 1:/#.
trivial.
qed.

lemma hbz_reciprocal_exact s x :
  0 <= s < mode2_hbz_alphabet =>
  1 <= x < hbz_xmax s =>
  hbz_reciprocal_quotient x s = hbz_required_quotient x s.
proof.
move=> hs hx.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [rewrite /hbz_xmax /hbz_freq /= in hx;
   rewrite /hbz_reciprocal_quotient /hbz_required_quotient
           /hbz_rcp_uint /hbz_rcp_shift /hbz_freq /=;
   smt()|]).
by rewrite range_geq.
qed.

lemma hbz_fast_step_matches_math s x :
  0 <= s < mode2_hbz_alphabet =>
  1 <= x < hbz_xmax s =>
  hbz_fast_encode_step x s = hbz_math_encode_step x s.
proof.
move=> hs hx.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [rewrite /hbz_xmax /hbz_freq /= in hx;
   rewrite /hbz_fast_encode_step /hbz_math_encode_step
           /hbz_required_quotient /hbz_bias /hbz_complement
           /hbz_start /hbz_freq /rans_scale /=;
   smt(@IntDiv)|]).
by rewrite range_geq.
qed.

lemma hbz_fast_step_w32_range s x :
  0 <= s < mode2_hbz_alphabet =>
  1 <= x < hbz_xmax s =>
  0 <= hbz_fast_encode_step x s < 2147483648.
proof.
move=> hs hx.
rewrite hbz_fast_step_matches_math 1:hs 1:hx.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [rewrite /hbz_xmax /hbz_freq /= in hx;
   rewrite /hbz_math_encode_step /hbz_start /hbz_freq /rans_scale /=;
   smt(@IntDiv)|]).
by rewrite range_geq.
qed.

lemma hbz_rcp_product_w64_range s x :
  0 <= s < mode2_hbz_alphabet =>
  1 <= x < hbz_xmax s =>
  0 <= x * hbz_rcp_uint s < W64.modulus.
proof.
move=> hs hx.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [rewrite /hbz_xmax /hbz_freq /= in hx;
   rewrite /hbz_rcp_uint /hbz_freq /W64.modulus /=;
   smt()|]).
by rewrite range_geq.
qed.

end Mode2HbzTableCertificate.
