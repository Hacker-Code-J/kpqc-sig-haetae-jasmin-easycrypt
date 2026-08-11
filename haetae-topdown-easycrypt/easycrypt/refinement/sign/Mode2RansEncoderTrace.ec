require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansEncodeTarget SignaturePackMode2Target
  Mode2HbzCodecSpec Mode2HbzTableCertificate
  Mode2RansByteStack Mode2RansNormalization
  Mode2RansEncodeRefinement Mode2RansArrayListBridge
  Mode2RansEncoderWordStep.

theory Mode2RansEncoderTrace.

import Mode2HbzCodecSpec Mode2HbzTableCertificate
       Mode2RansByteStack Mode2RansNormalization
       Mode2RansEncodeRefinement Mode2RansArrayListBridge
       Mode2RansEncoderWordStep.

module Encode = RansEncodeTarget.M.

op hbz_xmax_word (s : int) : W32.t = W32.of_int (hbz_xmax s).

op hbz_low_byte (x : W32.t) : int =
  W8.to_uint (truncateu8 x).

op hbz_high_byte (x : W32.t) : int =
  W8.to_uint (truncateu8 (x `>>` W8.of_int 8)).

lemma hbz_xmax_w32_range s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_xmax s < W32.modulus.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_xmax /hbz_freq /W32.modulus /=|]).
by rewrite range_geq.
qed.

lemma hbz_xmax_word_uint s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint (hbz_xmax_word s) = hbz_xmax s.
proof.
move=> hs.
rewrite /hbz_xmax_word W32.to_uint_small 1:(hbz_xmax_w32_range s hs).
trivial.
qed.

lemma hbz_xmax_word_ule x s :
  0 <= s < mode2_hbz_alphabet =>
  (hbz_xmax s <= W32.to_uint x) =>
  hbz_xmax_word s \ule x.
proof.
move=> hs hx.
rewrite W32.uleE hbz_xmax_word_uint 1:hs.
exact hx.
qed.

lemma hbz_xmax_word_nule x s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint x < hbz_xmax s =>
  !(hbz_xmax_word s \ule x).
proof.
move=> hs hx.
rewrite W32.uleE hbz_xmax_word_uint 1:hs.
smt().
qed.

lemma shift8_below_2pow23 (x : W32.t) :
  W32.to_uint x < 2147483648 =>
  W32.to_uint (x `>>` W8.of_int 8) < 8388608.
proof.
move=> hx.
rewrite encoder_shift8_uint.
smt().
qed.

lemma shift16_below_mode2_xmax (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint x < 2147483648 =>
  W32.to_uint ((x `>>` W8.of_int 8) `>>` W8.of_int 8) < hbz_xmax s.
proof.
move=> hs hx.
rewrite !encoder_shift8_uint.
have hxm := mode2_xmax_lower s hs.
smt().
qed.

lemma shift16_below_mode2_xmax_all (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint ((x `>>` W8.of_int 8) `>>` W8.of_int 8) < hbz_xmax s.
proof.
move=> hs.
rewrite !encoder_shift8_uint.
have hx := W32.to_uint_cmp x.
have hxm := mode2_xmax_lower s hs.
rewrite ltz_divLR 1:/#.
smt().
qed.

lemma hbz_low_byte_range x :
  0 <= hbz_low_byte x < 256.
proof.
rewrite /hbz_low_byte encoder_low_byte_uint.
have hx := W32.to_uint_cmp x.
smt().
qed.

lemma hbz_high_byte_range x :
  0 <= hbz_high_byte x < 256.
proof.
rewrite /hbz_high_byte encoder_low_byte_uint.
have hx := W32.to_uint_cmp (x `>>` W8.of_int 8).
rewrite encoder_shift8_uint in hx.
smt().
qed.

op encoder_phase_state (x k : int) : int =
  if k = 0 then x
  else if k = 1 then x %/ 256
  else if k = 2 then x %/ 65536
  else if k = 3 then x %/ 16777216
  else 0.

(* Bytes already emitted by the generated backward normalization loop.
   The newest byte is at the lowest address and therefore heads the list. *)
op encoder_phase_written (x k : int) : int list =
  if k = 0 then []
  else if k = 1 then [x %% 256]
  else if k = 2 then [(x %/ 256) %% 256; x %% 256]
  else if k = 3 then
    [(x %/ 65536) %% 256; (x %/ 256) %% 256; x %% 256]
  else
    [(x %/ 16777216) %% 256; (x %/ 65536) %% 256;
     (x %/ 256) %% 256; x %% 256].

lemma encoder_phase_written_size x k :
  0 <= k <= 4 => size (encoder_phase_written x k) = k.
proof.
move=> hk.
rewrite /encoder_phase_written.
case (k = 0) => h0; first smt().
case (k = 1) => h1; first smt().
case (k = 2) => h2; first smt().
case (k = 3) => h3; first smt().
smt().
qed.

lemma encoder_phase_written_step x k :
  0 <= k < 4 =>
  encoder_phase_written x (k + 1) =
    (encoder_phase_state x k %% 256) :: encoder_phase_written x k.
proof.
move=> hk.
rewrite /encoder_phase_written /encoder_phase_state.
case (k = 0) => h0; first smt().
case (k = 1) => h1; first smt().
case (k = 2) => h2; first smt().
case (k = 3) => h3; smt().
qed.

lemma encoder_phase_byte_range x k :
  0 <= encoder_phase_state x k %% 256 < 256.
proof. exact (modz_cmp (encoder_phase_state x k) 256 _); smt(). qed.

lemma encoder_phase_state_zero x :
  encoder_phase_state x 0 = x.
proof. trivial. qed.

lemma encoder_phase_state_step x k :
  0 <= x < w32_modulus_i =>
  0 <= k < 4 =>
  encoder_phase_state x (k + 1) =
    encoder_phase_state x k %/ 256.
proof.
move=> hx hk.
have hkcases : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
elim hkcases => hk0.
+ subst k; trivial.
+ elim hk0 => hk1.
  - subst k.
    rewrite /encoder_phase_state /= -divzMr 1:/# 1:/#; trivial.
  - elim hk1 => hk2.
    * subst k.
      rewrite /encoder_phase_state /= -divzMr 1:/# 1:/#; trivial.
    * subst k.
      rewrite /encoder_phase_state /=.
      rewrite -divzMr 1:/# 1:/#.
      have htop : x %/ 4294967296 = 0.
      - apply divz_small.
        rewrite /w32_modulus_i in hx.
        smt().
      smt().
qed.

lemma encoder_phase_four_zero x :
  encoder_phase_state x 4 = 0.
proof. trivial. qed.

lemma encoder_phase_cursor_positive off0 k :
  4 <= off0 =>
  0 <= k < 4 =>
  0 < off0 - k.
proof. smt(). qed.

lemma encoder_phase_cursor_positive_lr off0 k :
  4 <= off0 =>
  0 <= k =>
  k < 4 =>
  0 < off0 - k.
proof. smt(). qed.

lemma encoder_phase_state_step_lr x k :
  0 <= x < w32_modulus_i =>
  0 <= k =>
  k < 4 =>
  encoder_phase_state x (k + 1) =
    encoder_phase_state x k %/ 256.
proof.
move=> hx hklo hklt.
apply (encoder_phase_state_step x k).
- exact hx.
smt().
qed.

lemma encoder_phase_guard_before_four
    (x x0 x_max : W32.t) k :
  0 <= k <= 4 =>
  1 <= W32.to_uint x_max =>
  W32.to_uint x = encoder_phase_state (W32.to_uint x0) k =>
  x_max \ule x =>
  k < 4.
proof.
move=> hk hxmax hxcur hguard.
have hk4 : k < 4 \/ k = 4 by smt().
elim hk4 => // hk4.
subst k.
rewrite W32.uleE in hguard.
rewrite encoder_phase_four_zero in hxcur.
smt().
qed.

lemma encoder_phase_index_split k :
  0 <= k <= 4 => k < 4 \/ k = 4.
proof. smt(). qed.

lemma encoder_phase_index_split_lr k :
  0 <= k => k <= 4 => k < 4 \/ k = 4.
proof. smt(). qed.

lemma encoder_phase_next_bounds k :
  0 <= k => k < 4 => 0 <= k + 1 <= 4.
proof. smt(). qed.

lemma encoder_offset_bounds off0 :
  4 <= off0 =>
  off0 <= mode2_hbz_count =>
  4 <= off0 <= mode2_hbz_count.
proof. smt(). qed.

lemma actual_mode2_esym_xmax_positive s :
  0 <= s < mode2_hbz_alphabet =>
  1 <= W32.to_uint
    (BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms (4 * s)).
proof.
move=> hs.
have [hxmax _] := actual_mode2_esym_word_fields s hs.
rewrite hxmax W32.to_uint_small 1:(hbz_xmax_w32_range s hs).
have hf := hbz_frequency_positive s hs.
rewrite /hbz_xmax.
smt().
qed.

op encoder_inner_phase_inv (x_max x : W32.t) (off : W64.t) : bool =
  exists (x0 : W32.t) off0 k,
    (4 <= off0 <= mode2_hbz_count) /\
    (0 <= k <= 4) /\
    1 <= W32.to_uint x_max /\
    W64.to_uint off = off0 - k /\
    W32.to_uint x = encoder_phase_state (W32.to_uint x0) k.

op encoder_inner_live_view (x_max x : W32.t) (off : W64.t) : bool =
  exists (x0 : W32.t) off0 k,
    (4 <= off0 <= mode2_hbz_count) /\
    (0 <= k < 4) /\
    1 <= W32.to_uint x_max /\
    W64.to_uint off = off0 - k /\
    W32.to_uint x = encoder_phase_state (W32.to_uint x0) k.

op encoder_inner_segment_inv
    (x_max x : W32.t) (off : W64.t) (encp : BArray2048.t) : bool =
  exists (x0 : W32.t) off0 k (before : BArray2048.t),
    (4 <= off0 <= mode2_hbz_count) /\
    (0 <= k <= 4) /\
    1 <= W32.to_uint x_max /\
    W64.to_uint off = off0 - k /\
    W32.to_uint x = encoder_phase_state (W32.to_uint x0) k /\
    segment_matches encp (off0 - k)
      (encoder_phase_written (W32.to_uint x0) k) /\
    prefix_frame before encp (off0 - k).

lemma encoder_inner_phase_live x_max x off :
  encoder_inner_phase_inv x_max x off =>
  x_max \ule x =>
  encoder_inner_live_view x_max x off.
proof.
move=> hphase hguard.
rewrite /encoder_inner_phase_inv in hphase.
move: hphase => /> x0 off0 k
  hofflo hoffhi hklo hkhi hxmax hoffcur hxcur.
have hk : 0 <= k <= 4 by smt().
have hklt := encoder_phase_guard_before_four x x0 x_max k
  hk hxmax hxcur hguard.
rewrite /encoder_inner_live_view.
exists x0 off0 k.
smt().
qed.

lemma encoder_inner_phase_step x_max x off :
  encoder_inner_phase_inv x_max x off =>
  x_max \ule x =>
  encoder_inner_phase_inv
    x_max (x `>>` W8.of_int 8) (off - W64.one).
proof.
move=> hphase hguard.
have hlive := encoder_inner_phase_live x_max x off hphase hguard.
rewrite /encoder_inner_live_view in hlive.
move: hlive => /> x0 off0 k
  hofflo hoffhi hklo hklt hxmax hoffcur hxcur.
have hdiff := encoder_phase_cursor_positive_lr off0 k hofflo hklo hklt.
rewrite /encoder_inner_phase_inv.
exists x0 off0 (k + 1).
split; first exact (encoder_offset_bounds off0 hofflo hoffhi).
split; first exact (encoder_phase_next_bounds k hklo hklt).
split; first exact hxmax.
split.
- rewrite cursor_decrement_no_underflow.
  + rewrite hoffcur.
    exact hdiff.
  smt().
- rewrite encoder_shift8_uint.
  rewrite hxcur.
  rewrite -(encoder_phase_state_step_lr (W32.to_uint x0) k
    (W32.to_uint_cmp x0) hklo hklt).
  trivial.
qed.

lemma encoder_inner_phase_init x_max x off :
  4 <= W64.to_uint off <= mode2_hbz_count =>
  1 <= W32.to_uint x_max =>
  encoder_inner_phase_inv x_max x off.
proof.
move=> hoff hxmax.
rewrite /encoder_inner_phase_inv.
exists x (W64.to_uint off) 0.
rewrite encoder_phase_state_zero.
smt().
qed.

lemma encoder_inner_phase_off_upper x_max x off :
  encoder_inner_phase_inv x_max x off =>
  W64.to_uint off <= mode2_hbz_count.
proof.
rewrite /encoder_inner_phase_inv.
move=> [x0 off0 k
  [[hofflo hoffhi] [[hklo hkle] [hxmax [hoff hx]]]]].
rewrite hoff.
smt().
qed.

lemma encoder_inner_segment_init x_max x off encp :
  4 <= W64.to_uint off <= mode2_hbz_count =>
  1 <= W32.to_uint x_max =>
  encoder_inner_segment_inv x_max x off encp.
proof.
move=> hoff hxmax.
rewrite /encoder_inner_segment_inv.
exists x (W64.to_uint off) 0 encp.
split; first exact hoff.
split; first smt().
split; first exact hxmax.
split; first smt().
split; first by rewrite encoder_phase_state_zero.
split.
- rewrite /encoder_phase_written.
  apply segment_matches_nil.
  rewrite /mode2_hbz_count in hoff.
  rewrite /mode2_hbz_capacity.
  smt().
- exact (prefix_frame_refl encp (W64.to_uint off)).
qed.

lemma encoder_inner_segment_step x_max x off encp :
  encoder_inner_segment_inv x_max x off encp =>
  x_max \ule x =>
  encoder_inner_segment_inv
    x_max (x `>>` W8.of_int 8) (off - W64.one)
    (BArray2048.set8 encp (W64.to_uint (off - W64.one))
      (truncateu8 x)).
proof.
move=> hseg hguard.
rewrite /encoder_inner_segment_inv in hseg.
elim hseg => x0 off0 k before hseg.
move: hseg => [hoff [hk0 [hxmax [hoffcur [hxcur [hbytes hframe]]]]]].
move: hoff => [hofflo hoffhi].
move: hk0 => [hklo hkhi].
have hk : 0 <= k <= 4 by smt().
have hklt := encoder_phase_guard_before_four x x0 x_max k
  hk hxmax hxcur hguard.
have hpos := encoder_phase_cursor_positive_lr off0 k hofflo hklo hklt.
have hoffnext :
    W64.to_uint (off - W64.one) = off0 - (k + 1).
- rewrite cursor_decrement_no_underflow 1:/#.
  smt().
have hb : 0 <= encoder_phase_state (W32.to_uint x0) k %% 256 < 256.
- exact (encoder_phase_byte_range (W32.to_uint x0) k).
have hbword :
    W8.of_int (encoder_phase_state (W32.to_uint x0) k %% 256) =
    truncateu8 x.
- rewrite -(W8.to_uintK' (truncateu8 x)).
  congr.
  rewrite encoder_low_byte_uint hxcur.
  trivial.
have hbytes' := segment_matches_prepend_set encp (off0 - k)
  (encoder_phase_written (W32.to_uint x0) k)
  (encoder_phase_state (W32.to_uint x0) k %% 256)
  hbytes hpos hb.
rewrite hbword in hbytes'.
have hstartcap : 0 < off0 - k <= mode2_hbz_capacity.
- rewrite /mode2_hbz_count in hoffhi.
  rewrite /mode2_hbz_capacity.
  smt().
have hframe' := prefix_frame_prepend_write before encp (off0 - k)
  (truncateu8 x) hstartcap hframe.
rewrite /encoder_inner_segment_inv.
exists x0 off0 (k + 1) before.
split; first exact (encoder_offset_bounds off0 hofflo hoffhi).
split; first exact (encoder_phase_next_bounds k hklo hklt).
split; first exact hxmax.
split; first exact hoffnext.
split.
- rewrite encoder_shift8_uint hxcur.
  rewrite -(encoder_phase_state_step_lr (W32.to_uint x0) k
    (W32.to_uint_cmp x0) hklo hklt).
  trivial.
split.
- rewrite encoder_phase_written_step 1:/#.
  rewrite hoffnext.
  have -> : off0 - (k + 1) = off0 - k - 1 by ring.
  exact hbytes'.
- rewrite hoffnext.
  have -> : off0 - (k + 1) = off0 - k - 1 by ring.
  exact hframe'.
qed.

end Mode2RansEncoderTrace.
