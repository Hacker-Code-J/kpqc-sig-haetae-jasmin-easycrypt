require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import SignaturePackMode2Target Mode2HbzCodecSpec
  Mode2HbzTableCertificate Mode2RansCore.

theory Mode2RansEncoderWordStep.

import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansCore.

op encoder_shift_ladder (q shift : W32.t) : W32.t =
  if shift = W32.of_int 1 then q `>>` W8.of_int 1 else
  if shift = W32.of_int 2 then q `>>` W8.of_int 2 else
  if shift = W32.of_int 3 then q `>>` W8.of_int 3 else
  if shift = W32.of_int 4 then q `>>` W8.of_int 4 else
  if shift = W32.of_int 5 then q `>>` W8.of_int 5 else
  if shift = W32.of_int 6 then q `>>` W8.of_int 6 else
  if shift = W32.of_int 7 then q `>>` W8.of_int 7 else
  if shift = W32.of_int 8 then q `>>` W8.of_int 8 else
  if shift = W32.of_int 9 then q `>>` W8.of_int 9 else
  if shift = W32.of_int 10 then q `>>` W8.of_int 10 else
  if shift = W32.of_int 11 then q `>>` W8.of_int 11 else
  if shift = W32.of_int 12 then q `>>` W8.of_int 12 else
  if shift = W32.of_int 13 then q `>>` W8.of_int 13 else
  if shift = W32.of_int 14 then q `>>` W8.of_int 14 else
  if shift = W32.of_int 15 then q `>>` W8.of_int 15 else q.

op actual_mode2_encoder_word_step (x : W32.t) (s : int) : W32.t =
  let rcp = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms (4 * s + 1) in
  let bias = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms (4 * s + 2) in
  let packed = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms (4 * s + 3) in
  let complement = packed `&` W32.of_int 65535 in
  let shift = packed `>>` W8.of_int 16 in
  let product = (zeroextu64 x) * (zeroextu64 rcp) in
  let high = product `>>` W8.of_int 32 in
  let q = encoder_shift_ladder (truncateu32 high) shift in
  (x + bias) + q * complement.

lemma actual_mode2_esym_lookup_bounds s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= 4 * s /\ 4 * s + 3 < 528.
proof. rewrite /mode2_hbz_alphabet; smt(). qed.

lemma actual_mode2_esym_word_fields s :
  0 <= s < mode2_hbz_alphabet =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
      (4 * s) = W32.of_int (hbz_xmax s) /\
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
      (4 * s + 1) = hbz_rcp_word s /\
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
      (4 * s + 2) = W32.of_int (hbz_bias s) /\
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
      (4 * s + 3) = W32.of_int (hbz_packed_encoder_word s).
proof.
move=> hs.
split.
+ rewrite (actual_mode2_hbz_esym_fields s 0 hs _); first smt().
  trivial.
split.
+ rewrite (actual_mode2_hbz_esym_fields s 1 hs _); first smt().
  trivial.
split.
+ rewrite (actual_mode2_hbz_esym_fields s 2 hs _); first smt().
  trivial.
rewrite (actual_mode2_hbz_esym_fields s 3 hs _); first smt().
trivial.
qed.

lemma hbz_packed_encoder_word_range s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_packed_encoder_word s < W32.modulus.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_packed_encoder_word /hbz_rcp_shift
              /hbz_complement /hbz_freq /rans_scale /W32.modulus /=|]).
by rewrite range_geq.
qed.

lemma hbz_complement_range s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_complement s < 65536.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_complement /hbz_freq /rans_scale /=|]).
by rewrite range_geq.
qed.

lemma hbz_bias_range s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_bias s < W32.modulus.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_bias /hbz_freq /hbz_start /rans_scale /W32.modulus /=|]).
by rewrite range_geq.
qed.

lemma actual_packed_complement_uint s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint
    (W32.of_int (hbz_packed_encoder_word s) `&` W32.of_int 65535) =
  hbz_complement s.
proof.
move=> hs.
rewrite (W32.to_uint_and_mod 16) 1:/#.
rewrite W32.to_uint_small 1:(hbz_packed_encoder_word_range s hs).
rewrite /hbz_packed_encoder_word.
have hc := hbz_complement_range s hs.
have -> : 65536 * hbz_rcp_shift s + hbz_complement s =
    hbz_complement s + hbz_rcp_shift s * 65536 by ring.
rewrite modzMDr modz_small 1:/#.
trivial.
qed.

lemma actual_packed_shift_uint s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint
    (W32.of_int (hbz_packed_encoder_word s) `>>` W8.of_int 16) =
  hbz_rcp_shift s.
proof.
move=> hs.
rewrite W32.shr_div W8.of_uintK /=.
rewrite W32.to_uint_small 1:(hbz_packed_encoder_word_range s hs).
rewrite /hbz_packed_encoder_word.
have hc := hbz_complement_range s hs.
have -> : 65536 * hbz_rcp_shift s + hbz_complement s =
    hbz_complement s + hbz_rcp_shift s * 65536 by ring.
rewrite divzMDr 1:/# divz_small 1:/#.
trivial.
qed.

lemma hbz_rcp_shift_cases s :
  0 <= s < mode2_hbz_alphabet =>
  hbz_rcp_shift s = 0 \/ hbz_rcp_shift s = 2 \/
  hbz_rcp_shift s = 5 \/ hbz_rcp_shift s = 7 \/
  hbz_rcp_shift s = 8.
proof.
rewrite /mode2_hbz_alphabet /hbz_rcp_shift /hbz_freq.
smt().
qed.

lemma encoder_shift_ladder_uint q s :
  0 <= s < mode2_hbz_alphabet =>
  W32.to_uint
    (encoder_shift_ladder q (W32.of_int (hbz_rcp_shift s))) =
  W32.to_uint q %/ (2 ^ hbz_rcp_shift s).
proof.
move=> hs.
have hcases0 := hbz_rcp_shift_cases s hs.
elim hcases0 => [->|hcases1]; first by
  rewrite /encoder_shift_ladder !W32.to_uint_eq !W32.of_uintK /=.
elim hcases1 => [->|hcases2]; first by
  rewrite /encoder_shift_ladder !W32.to_uint_eq !W32.of_uintK /=
          W32.shr_div W8.of_uintK /=.
elim hcases2 => [->|hcases3]; first by
  rewrite /encoder_shift_ladder !W32.to_uint_eq !W32.of_uintK /=
          W32.shr_div W8.of_uintK /=.
elim hcases3 => [->|->]; by
  rewrite /encoder_shift_ladder !W32.to_uint_eq !W32.of_uintK /=
          W32.shr_div W8.of_uintK /=.
qed.

lemma w32_w64_modulus_factor :
  W32.modulus * 4294967296 = ptr_modulus.
proof.
smt().
qed.

lemma rcp_high_quotient_w32_range (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  1 <= W32.to_uint x < hbz_xmax s =>
  0 <= W32.to_uint x * hbz_rcp_uint s %/ 4294967296 < W32.modulus.
proof.
move=> hs hx.
have hp := hbz_rcp_product_w64_range s (W32.to_uint x) hs hx.
split.
+ rewrite divz_ge0 1:/#.
  smt().
+ rewrite ltz_divLR 1:/#.
  smt(w32_w64_modulus_factor).
qed.

lemma actual_rcp_high_word_uint (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  1 <= W32.to_uint x < hbz_xmax s =>
  W32.to_uint
    (truncateu32
      (((zeroextu64 x) * (zeroextu64 (hbz_rcp_word s)))
        `>>` W8.of_int 32)) =
  (W32.to_uint x * hbz_rcp_uint s) %/ 4294967296.
proof.
move=> hs hx.
have hp := hbz_rcp_product_w64_range s (W32.to_uint x) hs hx.
have hprodlt :
    W64.to_uint (zeroextu64 x) *
      W64.to_uint (zeroextu64 (hbz_rcp_word s)) < W64.modulus.
+ rewrite !W2u32.to_uint_zeroextu64 hbz_rcp_word_uint 1:hs.
  move: hp; rewrite /ptr_modulus; smt().
have hprod :
    W64.to_uint ((zeroextu64 x) * (zeroextu64 (hbz_rcp_word s))) =
    W32.to_uint x * hbz_rcp_uint s.
+ rewrite W64.to_uintM_small 1:hprodlt
          !W2u32.to_uint_zeroextu64 hbz_rcp_word_uint 1:hs.
  trivial.
have hshift :
    W64.to_uint
      (((zeroextu64 x) * (zeroextu64 (hbz_rcp_word s)))
        `>>` W8.of_int 32) =
    (W32.to_uint x * hbz_rcp_uint s) %/ 4294967296.
+ rewrite W64.shr_div_le 1:/# hprod /=.
  trivial.
rewrite W2u32.to_uint_truncateu32 hshift
        modz_small 1:(rcp_high_quotient_w32_range x s hs hx).
trivial.
qed.

lemma actual_rcp_quotient_uint (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  1 <= W32.to_uint x < hbz_xmax s =>
  W32.to_uint
    (encoder_shift_ladder
      (truncateu32
        (((zeroextu64 x) * (zeroextu64 (hbz_rcp_word s)))
          `>>` W8.of_int 32))
      (W32.of_int (hbz_rcp_shift s))) =
  hbz_required_quotient (W32.to_uint x) s.
proof.
move=> hs hx.
rewrite encoder_shift_ladder_uint 1:hs.
rewrite actual_rcp_high_word_uint 1:hs 1:hx.
exact (hbz_reciprocal_exact s (W32.to_uint x) hs hx).
qed.

lemma hbz_quotient_complement_w32_range s x :
  0 <= s < mode2_hbz_alphabet =>
  1 <= x < hbz_xmax s =>
  0 <= hbz_required_quotient x s * hbz_complement s < W32.modulus.
proof.
move=> hs hx.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [rewrite /hbz_xmax /hbz_freq /= in hx;
   rewrite /hbz_required_quotient /hbz_complement
           /hbz_freq /rans_scale /W32.modulus /=;
   smt(@IntDiv)|]).
by rewrite range_geq.
qed.

lemma hbz_rcp_shift_w32_range s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_rcp_shift s < W32.modulus.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_rcp_shift /hbz_freq /W32.modulus /=|]).
by rewrite range_geq.
qed.

lemma hbz_required_quotient_w32_range s x :
  0 <= s < mode2_hbz_alphabet =>
  1 <= x < hbz_xmax s =>
  0 <= hbz_required_quotient x s < W32.modulus.
proof.
move=> hs hx.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [rewrite /hbz_xmax /hbz_freq /= in hx;
   rewrite /hbz_required_quotient /hbz_freq /W32.modulus /=;
   smt(@IntDiv)|]).
by rewrite range_geq.
qed.

lemma hbz_complement_w32_range s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_complement s < W32.modulus.
proof.
move=> hs.
have hs_mem : s \in range 0 13 by rewrite mem_range; smt().
move: hs_mem.
do 13! (rewrite range_ltn //=; move=> [->>|];
  [by rewrite /hbz_complement /hbz_freq /rans_scale /W32.modulus /=|]).
by rewrite range_geq.
qed.

lemma actual_packed_shift_word s :
  0 <= s < mode2_hbz_alphabet =>
  W32.of_int (hbz_packed_encoder_word s) `>>` W8.of_int 16 =
    W32.of_int (hbz_rcp_shift s).
proof.
move=> hs.
apply W32.to_uint_eq.
rewrite actual_packed_shift_uint 1:hs W32.to_uint_small.
exact (hbz_rcp_shift_w32_range s hs).
trivial.
qed.

lemma actual_packed_complement_word s :
  0 <= s < mode2_hbz_alphabet =>
  W32.of_int (hbz_packed_encoder_word s) `&` W32.of_int 65535 =
    W32.of_int (hbz_complement s).
proof.
move=> hs.
apply W32.to_uint_eq.
rewrite actual_packed_complement_uint 1:hs W32.to_uint_small.
exact (hbz_complement_w32_range s hs).
trivial.
qed.

lemma actual_rcp_quotient_word (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  1 <= W32.to_uint x < hbz_xmax s =>
  encoder_shift_ladder
      (truncateu32
        (((zeroextu64 x) * (zeroextu64 (hbz_rcp_word s)))
          `>>` W8.of_int 32))
      (W32.of_int (hbz_rcp_shift s)) =
    W32.of_int (hbz_required_quotient (W32.to_uint x) s).
proof.
move=> hs hx.
apply W32.to_uint_eq.
rewrite actual_rcp_quotient_uint 1:hs 1:hx W32.to_uint_small.
exact (hbz_required_quotient_w32_range s (W32.to_uint x) hs hx).
trivial.
qed.

lemma actual_mode2_encoder_word_step_correct (x : W32.t) s :
  0 <= s < mode2_hbz_alphabet =>
  1 <= W32.to_uint x < hbz_xmax s =>
  actual_mode2_encoder_word_step x s =
    W32.of_int (hbz_fast_encode_step (W32.to_uint x) s).
proof.
move=> hs hx.
have [hxmax [hrcp [hbias hpacked]]] := actual_mode2_esym_word_fields s hs.
rewrite /actual_mode2_encoder_word_step /= hrcp hbias hpacked.
have hshift := actual_packed_shift_uint s hs.
have hcomp := actual_packed_complement_uint s hs.
have hq := actual_rcp_quotient_uint x s hs hx.
have hfast := hbz_fast_step_w32_range s (W32.to_uint x) hs hx.
rewrite actual_packed_shift_word 1:hs.
rewrite actual_packed_complement_word 1:hs.
rewrite actual_rcp_quotient_word 1:hs 1:hx.
rewrite -W32.to_uintK'.
rewrite W32.of_intM.
rewrite -(W32.of_intD (W32.to_uint x) (hbz_bias s)).
rewrite -(W32.of_intD
  (W32.to_uint x + hbz_bias s)
  (hbz_required_quotient (W32.to_uint x) s * hbz_complement s)).
rewrite /hbz_fast_encode_step.
trivial.
qed.

lemma encoder_word_step_preconditions_satisfiable :
  0 <= 6 < mode2_hbz_alphabet /\
  1 <= W32.to_uint (W32.of_int rans_initial_state) < hbz_xmax 6.
proof.
rewrite W32.to_uint_small.
+ rewrite /rans_initial_state; smt().
rewrite /mode2_hbz_alphabet /rans_initial_state /hbz_xmax /hbz_freq.
smt().
qed.

end Mode2RansEncoderWordStep.
