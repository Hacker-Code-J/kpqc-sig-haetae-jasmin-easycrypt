require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansCore
  Mode2RansByteStack Mode2RansDecoderWordStep.

theory Mode2RansDecoderActualWord.

import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansCore
       Mode2RansByteStack Mode2RansDecoderWordStep.

op actual_mode2_decoder_word_update (x : W32.t) s : W32.t =
  ((((x `>>` W8.of_int 10) * actual_mode2_decoder_freq s) +
      (x `&` W32.of_int 1023)) - actual_mode2_decoder_start s).

lemma hbz_start_w32_bounds s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_start s /\ hbz_start s < W32.modulus.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_start /W32.modulus /=|]).
by rewrite range_geq.
qed.

lemma hbz_freq_w32_bounds s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_freq s /\ hbz_freq s < W32.modulus.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_freq /W32.modulus /=|]).
by rewrite range_geq.
qed.

lemma actual_mode2_decoder_start_word s :
  0 <= s < mode2_hbz_alphabet =>
  actual_mode2_decoder_start s = W32.of_int (hbz_start s).
proof.
move=> hs.
apply W32.to_uint_eq.
rewrite actual_mode2_decoder_start_uint 1:hs W32.to_uint_small.
+ have [hlo hhi] := hbz_start_w32_bounds s hs.
   smt().
trivial.
qed.

lemma actual_mode2_decoder_freq_word s :
  0 <= s < mode2_hbz_alphabet =>
  actual_mode2_decoder_freq s = W32.of_int (hbz_freq s).
proof.
move=> hs.
apply W32.to_uint_eq.
rewrite actual_mode2_decoder_freq_uint 1:hs W32.to_uint_small.
+ have [hlo hhi] := hbz_freq_w32_bounds s hs.
   smt().
trivial.
qed.

lemma actual_mode2_decoder_shift_word x :
  x `>>` W8.of_int 10 = W32.of_int (W32.to_uint x %/ rans_scale).
proof.
apply W32.to_uint_eq.
rewrite W32.shr_div_le 1:/#.
rewrite W32.to_uint_small.
+ apply divz_cmp.
  - rewrite /rans_scale; trivial.
  - have [hx0 hxhi] := W32.to_uint_cmp x.
    rewrite /rans_scale.
    split.
    * exact hx0.
    * move=> _.
      have hm := W32.ge0_modulus.
      smt().
rewrite /rans_scale.
trivial.
qed.

lemma actual_mode2_decoder_slot_word x :
  x `&` W32.of_int 1023 = W32.of_int (W32.to_uint x %% rans_scale).
proof.
apply W32.to_uint_eq.
rewrite (W32.to_uint_and_mod 10) 1:/#.
rewrite W32.to_uint_small.
+ have [hmod0 hmodhi] := modz_cmp (W32.to_uint x) rans_scale _.
  - rewrite /rans_scale; trivial.
  - rewrite /rans_scale in hmodhi.
    have hm := W32.ge2_modulus.
    split.
    * exact hmod0.
    * move=> _.
      smt().
trivial.
qed.

lemma actual_mode2_decoder_word_update_range (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= W32.to_uint x < 2147483648 =>
  hbz_start s <= W32.to_uint x %% rans_scale < hbz_start s + hbz_freq s =>
  0 <=
    (W32.to_uint x %/ rans_scale) * hbz_freq s +
    (W32.to_uint x %% rans_scale) - hbz_start s <
    W32.modulus.
proof.
move=> hs hx hslot.
have [hstart [hfreq hcover]] := hbz_interval_bounds s hs.
have hq_nonneg : 0 <= W32.to_uint x %/ rans_scale.
+ apply divz_ge0.
  - rewrite /rans_scale; trivial.
  - have [hx0 _] := W32.to_uint_cmp x.
    exact hx0.
have hlo :
    0 <=
      (W32.to_uint x %/ rans_scale) * hbz_freq s +
      (W32.to_uint x %% rans_scale) - hbz_start s by smt().
have hmul_le :
    (W32.to_uint x %/ rans_scale) * hbz_freq s <=
    (W32.to_uint x %/ rans_scale) * rans_scale.
+ smt().
have hdiveq := divz_eq (W32.to_uint x) rans_scale.
have hupper :
    (W32.to_uint x %/ rans_scale) * hbz_freq s +
    (W32.to_uint x %% rans_scale) - hbz_start s <= W32.to_uint x by
  smt().
pose z :=
  (W32.to_uint x %/ rans_scale) * hbz_freq s +
  (W32.to_uint x %% rans_scale) - hbz_start s.
have hz0 : 0 <= z by rewrite /z; exact hlo.
have hzx : z <= W32.to_uint x by rewrite /z; exact hupper.
have [_ hxlt] := W32.to_uint_cmp x.
have hzlt : z < W32.modulus.
+ move/lez_eqVlt: hzx => [hzxeq|hzxlt].
  - rewrite hzxeq; exact hxlt.
  - exact (ltz_trans (W32.to_uint x) z W32.modulus hzxlt hxlt).
have hgoal : 0 <= z < W32.modulus.
+ rewrite hz0 hzlt; trivial.
rewrite /z in hgoal.
exact hgoal.
qed.

lemma actual_mode2_decoder_word_update_correct (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= W32.to_uint x < 2147483648 =>
  hbz_start s <= W32.to_uint x %% rans_scale < hbz_start s + hbz_freq s =>
  actual_mode2_decoder_word_update x s =
    W32.of_int (hbz_math_decode_step (W32.to_uint x) s).
proof.
move=> hs hx hslot.
have hstep :=
  actual_mode2_decoder_word_update_range x s hs hx hslot.
rewrite /actual_mode2_decoder_word_update.
rewrite actual_mode2_decoder_shift_word.
rewrite actual_mode2_decoder_freq_word 1:hs.
rewrite actual_mode2_decoder_slot_word.
rewrite actual_mode2_decoder_start_word 1:hs.
rewrite W32.of_intM.
rewrite -(W32.of_intD
  ((W32.to_uint x %/ rans_scale) * hbz_freq s)
  (W32.to_uint x %% rans_scale)).
rewrite -W32.of_intN.
rewrite -(W32.of_intD
  (((W32.to_uint x %/ rans_scale) * hbz_freq s) +
    (W32.to_uint x %% rans_scale))
  (- hbz_start s)).
rewrite /hbz_math_decode_step /pure_rans_decode_step.
trivial.
qed.

lemma actual_mode2_decoder_word_update_preconditions_satisfiable :
  exists x s,
    0 <= s < mode2_hbz_alphabet /\
    rans_initial_state <= W32.to_uint x < 2147483648 /\
    hbz_start s <= W32.to_uint x %% rans_scale <
      hbz_start s + hbz_freq s.
proof.
pose n := mode2_normalized_state rans_initial_state 6.
pose y := hbz_fast_encode_step n 6.
exists (W32.of_int y) 6.
have hs : 0 <= 6 < mode2_hbz_alphabet.
+ rewrite /mode2_hbz_alphabet; smt().
have hinit : rans_initial_state <= rans_initial_state < 2147483648.
+ rewrite /rans_initial_state; smt().
have hn : 1 <= n < hbz_xmax 6.
+ rewrite /n.
   exact (renorm_reduced_bounds 6 rans_initial_state hs hinit).
have hy :
    rans_initial_state <= y < 2147483648.
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
split; first exact hs.
split.
+ rewrite W32.to_uint_small.
   - exact hy.
  rewrite /y /n.
  have hy0 : 0 <= y by smt().
  rewrite /W32.modulus.
  smt().
rewrite W32.to_uint_small.
+ exact hslot.
rewrite /y /n /W32.modulus.
smt().
qed.

end Mode2RansDecoderActualWord.
