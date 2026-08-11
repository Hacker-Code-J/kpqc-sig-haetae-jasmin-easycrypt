require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import SignaturePackMode2Target Mode2HbzCodecSpec
  Mode2HbzTableCertificate Mode2RansEncoderWordStep.

theory Mode2RansEncoderGeneratedWordStep.

import Mode2HbzCodecSpec Mode2HbzTableCertificate
       Mode2RansEncoderWordStep.

op generated_mode2_esym_base (s : W8.t) : W64.t =
  protect_64 ((zeroextu64 s) * W64.of_int 4) init_msf.

op generated_mode2_encoder_word_step (x : W32.t) (s : W8.t) : W32.t =
  let rcp = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 1) in
  let bias = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 2) in
  let packed = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 3) in
  let complement = packed `&` W32.of_int 65535 in
  let shift = protect_32 (packed `>>` W8.of_int 16) init_msf in
  let product = (zeroextu64 x) * (zeroextu64 rcp) in
  let high = product `>>` W8.of_int 32 in
  let q = encoder_shift_ladder (truncateu32 high) shift in
  (x + bias) + q * complement.

lemma generated_shift_ladder_fold (q shift : W32.t) :
  (if shift = W32.of_int 1 then q `>>` W8.of_int 1 else
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
   if shift = W32.of_int 15 then q `>>` W8.of_int 15 else q) =
  encoder_shift_ladder q shift.
proof. trivial. qed.

lemma generated_mode2_encoder_word_step_fold (x : W32.t) (s : W8.t) :
  let rcp = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 1) in
  let bias = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 2) in
  let packed = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 3) in
  let complement = packed `&` W32.of_int 65535 in
  let shift = protect_32 (packed `>>` W8.of_int 16) init_msf in
  let product = (zeroextu64 x) * (zeroextu64 rcp) in
  let high = product `>>` W8.of_int 32 in
  let q = encoder_shift_ladder (truncateu32 high) shift in
  (x + bias) + q * complement = generated_mode2_encoder_word_step x s.
proof. trivial. qed.

lemma generated_mode2_esym_base_uint s :
  W8.to_uint s < mode2_hbz_alphabet =>
  W64.to_uint (generated_mode2_esym_base s) = 4 * W8.to_uint s.
proof.
move=> hs.
rewrite /generated_mode2_esym_base /protect_64.
rewrite W64.to_uintM_small.
+ rewrite W8u8.to_uint_zeroextu64 W64.of_uintK /=.
  have hu := W8.to_uint_cmp s.
  rewrite /mode2_hbz_alphabet in hs.
  rewrite /ptr_modulus.
  smt().
rewrite W8u8.to_uint_zeroextu64 W64.of_uintK /=.
ring.
qed.

lemma generated_mode2_esym_index1_uint s :
  W8.to_uint s < mode2_hbz_alphabet =>
  W64.to_uint (generated_mode2_esym_base s + W64.one) =
    4 * W8.to_uint s + 1.
proof.
move=> hs.
rewrite W64.to_uintD_small 1:/# W64.to_uint1.
rewrite generated_mode2_esym_base_uint 1:hs.
ring.
qed.

lemma generated_mode2_esym_index2_uint s :
  W8.to_uint s < mode2_hbz_alphabet =>
  W64.to_uint ((generated_mode2_esym_base s + W64.one) + W64.one) =
    4 * W8.to_uint s + 2.
proof.
move=> hs.
rewrite W64.to_uintD_small 1:/# W64.to_uint1.
rewrite generated_mode2_esym_index1_uint 1:hs.
ring.
qed.

lemma generated_mode2_esym_index3_uint s :
  W8.to_uint s < mode2_hbz_alphabet =>
  W64.to_uint
    (((generated_mode2_esym_base s + W64.one) + W64.one) + W64.one) =
    4 * W8.to_uint s + 3.
proof.
move=> hs.
rewrite W64.to_uintD_small 1:/# W64.to_uint1.
rewrite generated_mode2_esym_index2_uint 1:hs.
ring.
qed.

lemma generated_mode2_xmax_loaded s :
  W8.to_uint s < mode2_hbz_alphabet =>
  protect_32
    (BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
      (W64.to_uint (generated_mode2_esym_base s))) init_msf =
    W32.of_int (hbz_xmax (W8.to_uint s)).
proof.
move=> hs.
rewrite /protect_32 generated_mode2_esym_base_uint 1:hs.
have hs0 : 0 <= W8.to_uint s < mode2_hbz_alphabet by
  have := W8.to_uint_cmp s; smt().
have [hxmax _] := actual_mode2_esym_word_fields (W8.to_uint s) hs0.
exact hxmax.
qed.

lemma generated_mode2_xmax_table s :
  0 <= s < mode2_hbz_alphabet =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * s) = W32.of_int (hbz_xmax s).
proof.
move=> hs.
have [hxmax _] := actual_mode2_esym_word_fields s hs.
exact hxmax.
qed.

lemma generated_mode2_rcp_loaded s :
  W8.to_uint s < mode2_hbz_alphabet =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
    (W64.to_uint (generated_mode2_esym_base s + W64.one)) =
  hbz_rcp_word (W8.to_uint s).
proof.
move=> hs.
rewrite generated_mode2_esym_index1_uint 1:hs.
have hs0 : 0 <= W8.to_uint s < mode2_hbz_alphabet by
  have := W8.to_uint_cmp s; smt().
have [_ [hrcp _]] := actual_mode2_esym_word_fields (W8.to_uint s) hs0.
exact hrcp.
qed.

lemma generated_mode2_bias_loaded s :
  W8.to_uint s < mode2_hbz_alphabet =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
    (W64.to_uint ((generated_mode2_esym_base s + W64.one) + W64.one)) =
  W32.of_int (hbz_bias (W8.to_uint s)).
proof.
move=> hs.
rewrite generated_mode2_esym_index2_uint 1:hs.
have hs0 : 0 <= W8.to_uint s < mode2_hbz_alphabet by
  have := W8.to_uint_cmp s; smt().
have [_ [_ [hbias _]]] := actual_mode2_esym_word_fields
  (W8.to_uint s) hs0.
exact hbias.
qed.

lemma generated_mode2_packed_loaded s :
  W8.to_uint s < mode2_hbz_alphabet =>
  BArray528.get32 SignaturePackMode2Target.jmode2_hb_z1_esyms
    (W64.to_uint
      (((generated_mode2_esym_base s + W64.one) + W64.one) + W64.one)) =
  W32.of_int (hbz_packed_encoder_word (W8.to_uint s)).
proof.
move=> hs.
rewrite generated_mode2_esym_index3_uint 1:hs.
have hs0 : 0 <= W8.to_uint s < mode2_hbz_alphabet by
  have := W8.to_uint_cmp s; smt().
have [_ [_ [_ hpacked]]] := actual_mode2_esym_word_fields
  (W8.to_uint s) hs0.
exact hpacked.
qed.

lemma generated_mode2_encoder_word_step_unfold x s :
  W8.to_uint s < mode2_hbz_alphabet =>
  generated_mode2_encoder_word_step x s =
    actual_mode2_encoder_word_step x (W8.to_uint s).
proof.
move=> hs.
rewrite /generated_mode2_encoder_word_step
        /actual_mode2_encoder_word_step /= /protect_32.
trivial.
qed.

lemma generated_loaded_word_update
    (x : W32.t) (s : W8.t)
    (rcp bias packed complement shift q : W32.t) :
  W8.to_uint s < mode2_hbz_alphabet =>
  rcp = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 1) =>
  bias = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 2) =>
  packed = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 3) =>
  complement = packed `&` W32.of_int 65535 =>
  shift = protect_32 (packed `>>` W8.of_int 16) init_msf =>
  q = encoder_shift_ladder
    (truncateu32
      (((zeroextu64 x) * (zeroextu64 rcp)) `>>` W8.of_int 32)) shift =>
  (x + bias) + q * complement =
    actual_mode2_encoder_word_step x (W8.to_uint s).
proof.
move=> hs -> -> -> -> -> ->.
exact (generated_mode2_encoder_word_step_unfold x s hs).
qed.

op generated_loaded_nested_update
    (x rcp bias complement shift : W32.t) : W32.t =
  let q = truncateu32
    (((zeroextu64 x) * (zeroextu64 rcp)) `>>` W8.of_int 32) in
  (x + bias) +
    (if shift = W32.of_int 1 then q `>>` W8.of_int 1 else
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
     if shift = W32.of_int 15 then q `>>` W8.of_int 15 else q) * complement.

lemma generated_loaded_nested_word_update
    (x : W32.t) (s : W8.t)
    (rcp bias packed complement shift : W32.t) :
  W8.to_uint s < mode2_hbz_alphabet =>
  rcp = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 1) =>
  bias = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 2) =>
  packed = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 3) =>
  complement = packed `&` W32.of_int 65535 =>
  shift = protect_32 (packed `>>` W8.of_int 16) init_msf =>
  generated_loaded_nested_update x rcp bias complement shift =
    actual_mode2_encoder_word_step x (W8.to_uint s).
proof.
move=> hs hrcp hbias hpacked hcomp hshift.
rewrite /generated_loaded_nested_update /=.
rewrite generated_shift_ladder_fold.
apply (generated_loaded_word_update x s rcp bias packed complement shift
  (encoder_shift_ladder
    (truncateu32
      (((zeroextu64 x) * (zeroextu64 rcp)) `>>` W8.of_int 32)) shift)).
+ exact hs.
+ exact hrcp.
+ exact hbias.
+ exact hpacked.
+ exact hcomp.
+ exact hshift.
+ trivial.
qed.

lemma generated_outer_word_update_matches x s :
  W8.to_uint s < mode2_hbz_alphabet =>
  1 <= W32.to_uint x < hbz_xmax (W8.to_uint s) =>
  generated_mode2_encoder_word_step x s =
    W32.of_int
      (hbz_fast_encode_step (W32.to_uint x) (W8.to_uint s)).
proof.
move=> hs hx.
rewrite generated_mode2_encoder_word_step_unfold 1:hs.
have hs0 : 0 <= W8.to_uint s < mode2_hbz_alphabet by
  have := W8.to_uint_cmp s; smt().
exact (actual_mode2_encoder_word_step_correct
  x (W8.to_uint s) hs0 hx).
qed.

lemma generated_word_step_preconditions_satisfiable :
  exists x s,
    W8.to_uint s < mode2_hbz_alphabet /\
    1 <= W32.to_uint x < hbz_xmax (W8.to_uint s).
proof.
exists (W32.of_int rans_initial_state) (W8.of_int 6).
rewrite W8.to_uint_small.
+ smt().
rewrite W32.to_uint_small.
+ rewrite /rans_initial_state; smt().
rewrite /mode2_hbz_alphabet /rans_initial_state /hbz_xmax /hbz_freq.
smt().
qed.

end Mode2RansEncoderGeneratedWordStep.
