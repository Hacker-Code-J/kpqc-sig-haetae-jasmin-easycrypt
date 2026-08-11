require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansCore
  Mode2RansByteStack Mode2RansNormalization Mode2RansArrayListBridge
  Mode2RansEncoderInnerProgress Mode2RansDecoderCursor.

theory Mode2RansDecoderNormalization.

import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansCore
       Mode2RansByteStack Mode2RansNormalization Mode2RansArrayListBridge
       Mode2RansEncoderInnerProgress Mode2RansDecoderCursor.

op decoder_replay_prefix (tail_state s k : int) : int =
  read_bytes
    (mode2_normalized_state tail_state s)
    (take k (mode2_normalization_bytes tail_state s)).

lemma read_bytes_cat x bs1 bs2 :
  read_bytes x (bs1 ++ bs2) = read_bytes (read_bytes x bs1) bs2.
proof.
elim: bs1 x => [|b bs1 ih] x /=.
+ trivial.
+ exact (ih (append_byte x b)).
qed.

lemma read_bytes_rcons x bytes b :
  read_bytes x (rcons bytes b) = append_byte (read_bytes x bytes) b.
proof.
elim: bytes x => [|a bytes ih] x /=.
+ trivial.
+ exact (ih (append_byte x a)).
qed.

lemma read_bytes_take_succ x bytes k :
  0 <= k < size bytes =>
  read_bytes x (take (k + 1) bytes) =
    append_byte (read_bytes x (take k bytes)) (nth 0 bytes k).
proof.
move=> hk.
rewrite (take_nth 0 k bytes hk) read_bytes_rcons.
trivial.
qed.

lemma normalization_byte_range tail_state s k :
  0 <= k < size (mode2_normalization_bytes tail_state s) =>
  0 <= nth 0 (mode2_normalization_bytes tail_state s) k < byte_radix.
proof.
move=> hk.
rewrite /mode2_normalization_bytes /renorm_bytes /byte_radix in hk.
rewrite /mode2_normalization_bytes /renorm_bytes /byte_radix.
case (tail_state < hbz_xmax s) => h0; first smt().
case (tail_state %/ 256 < hbz_xmax s) => h1.
+ have -> : k = 0 by smt().
  rewrite /=.
  apply modz_cmp; smt().
+ have hkcase : k = 0 \/ k = 1 by smt().
  elim hkcase => ->.
  - rewrite /=; apply modz_cmp; smt().
  - rewrite /=; apply modz_cmp; smt().
qed.

lemma decoder_replay_zero tail_state s :
  decoder_replay_prefix tail_state s 0 =
    mode2_normalized_state tail_state s.
proof.
rewrite /decoder_replay_prefix take0 /read_bytes.
trivial.
qed.

lemma decoder_replay_step tail_state s k :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= tail_state < 2147483648 =>
  0 <= k < mode2_normalization_len tail_state s =>
  decoder_replay_prefix tail_state s (k + 1) =
    append_byte (decoder_replay_prefix tail_state s k)
      (nth 0 (mode2_normalization_bytes tail_state s) k).
proof.
move=> hs hx hk.
rewrite /decoder_replay_prefix.
rewrite read_bytes_take_succ.
+ have [hlen _] := mode2_normalization_bytes_size s tail_state hs hx.
  rewrite hlen.
  exact hk.
trivial.
qed.

lemma decoder_replay_complete s tail_state :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= tail_state < 2147483648 =>
  decoder_replay_prefix tail_state s
    (mode2_normalization_len tail_state s) = tail_state.
proof.
move=> hs hx.
rewrite /decoder_replay_prefix.
have [hlen _] := mode2_normalization_bytes_size s tail_state hs hx.
rewrite -hlen take_size.
exact (renorm_bytes_readback s tail_state hs hx).
qed.

lemma decoder_replay_before_complete s tail_state k :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= tail_state < 2147483648 =>
  0 <= k < mode2_normalization_len tail_state s =>
  0 <= decoder_replay_prefix tail_state s k < rans_initial_state.
proof.
move=> hs hx hk.
rewrite /decoder_replay_prefix /mode2_normalization_len
        /mode2_normalization_bytes /mode2_normalized_state
        /renorm_len /renorm_bytes /renorm_reduced /byte_radix in hk.
rewrite /decoder_replay_prefix /mode2_normalization_len
        /mode2_normalization_bytes /mode2_normalized_state
        /renorm_len /renorm_bytes /renorm_reduced /byte_radix.
case (tail_state < hbz_xmax s) => h0; first smt().
case (tail_state %/ 256 < hbz_xmax s) => h1.
+ have -> : k = 0 by smt().
  rewrite /=.
  have hdiv := divz_eq tail_state 256.
  rewrite /rans_initial_state in hx.
  rewrite /rans_initial_state.
  smt(@IntDiv).
+ have hkcase : k = 0 \/ k = 1 by smt().
  elim hkcase => ->.
  - rewrite /=.
    have hdiv := divz_eq tail_state 65536.
    rewrite /rans_initial_state in hx.
    rewrite /rans_initial_state.
    smt(@IntDiv).
  - rewrite /= /read_bytes /append_byte.
    have hdiv0 := divz_eq tail_state 256.
    have hdiv1 := divz_eq (tail_state %/ 256) 256.
    have hassoc : tail_state %/ 65536 = tail_state %/ 256 %/ 256.
    * rewrite -divzMr 1:/# 1:/#.
      trivial.
    rewrite /rans_initial_state in hx.
    rewrite /rans_initial_state.
    smt(@IntDiv).
qed.

lemma decoder_replay_guard_exact s tail_state k :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= tail_state < 2147483648 =>
  0 <= k <= mode2_normalization_len tail_state s =>
  (decoder_replay_prefix tail_state s k < rans_initial_state <=>
   k < mode2_normalization_len tail_state s).
proof.
move=> hs hx hk.
split.
+ move=> hsmall.
  case (k = mode2_normalization_len tail_state s) => heq.
  - move: hsmall.
    rewrite heq (decoder_replay_complete s tail_state hs hx).
    smt().
  - smt().
+ move=> hbefore.
  have hrange : 0 <= k < mode2_normalization_len tail_state s by smt().
  have [_ hsmall] :=
    decoder_replay_before_complete s tail_state k hs hx hrange.
  exact hsmall.
qed.

lemma decoder_replay_prefix_bounds s tail_state k :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= tail_state < 2147483648 =>
  0 <= k <= mode2_normalization_len tail_state s =>
  0 <= decoder_replay_prefix tail_state s k < 2147483648.
proof.
move=> hs hx hk.
case (k = mode2_normalization_len tail_state s) => heq.
+ rewrite heq (decoder_replay_complete s tail_state hs hx).
  rewrite /rans_initial_state in hx.
  rewrite /rans_initial_state.
  smt().
+ have hbefore := decoder_replay_before_complete s tail_state k hs hx _;
    first smt().
  smt().
qed.

lemma decoder_replay_word_step (x : W32.t) tail_state s k byte :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= tail_state < 2147483648 =>
  0 <= k < mode2_normalization_len tail_state s =>
  W32.to_uint x = decoder_replay_prefix tail_state s k =>
  W8.to_uint byte = nth 0 (mode2_normalization_bytes tail_state s) k =>
  append_word_byte x byte =
    W32.of_int (decoder_replay_prefix tail_state s (k + 1)).
proof.
move=> hs hx hk hxword hbyte.
apply W32.to_uint_eq.
rewrite decoder_append_word_uint.
+ rewrite hxword.
  have hsmall := decoder_replay_before_complete s tail_state k hs hx hk.
  rewrite /rans_initial_state in hsmall.
  smt().
rewrite hxword hbyte (decoder_replay_step tail_state s k hs hx hk).
rewrite W32.to_uint_small.
+ have hnext :
      decoder_replay_prefix tail_state s (k + 1) <= tail_state.
  - rewrite /decoder_replay_prefix /mode2_normalization_len
            /mode2_normalization_bytes /mode2_normalized_state
            /renorm_len /renorm_bytes /renorm_reduced /byte_radix in hk.
    rewrite /decoder_replay_prefix /mode2_normalization_bytes
            /mode2_normalized_state /renorm_bytes /renorm_reduced
            /byte_radix.
    case (tail_state < hbz_xmax s) => h0; first smt().
    case (tail_state %/ 256 < hbz_xmax s) => h1.
    * have -> : k = 0 by smt().
      rewrite /= /read_bytes /append_byte.
      have hdiv := divz_eq tail_state 256.
      smt(@IntDiv).
    * have hkcase : k = 0 \/ k = 1 by smt().
      elim hkcase => ->.
      - rewrite /= /read_bytes /append_byte.
        have hdiv0 := divz_eq (tail_state %/ 256) 256.
        smt(@IntDiv).
      - rewrite /= /read_bytes /append_byte.
        have hdiv0 := divz_eq tail_state 256.
        have hdiv1 := divz_eq (tail_state %/ 256) 256.
        have hassoc : tail_state %/ 65536 = tail_state %/ 256 %/ 256.
        + rewrite -divzMr 1:/# 1:/#.
          trivial.
        smt(@IntDiv).
  rewrite /w32_modulus_i in hx.
  have hnonneg := decoder_replay_before_complete s tail_state k hs hx hk.
  have hb := normalization_byte_range tail_state s k _.
  - have [hlen _] := mode2_normalization_bytes_size s tail_state hs hx.
    smt().
  rewrite /append_byte /byte_radix in hnext.
  rewrite /byte_radix in hnonneg.
  rewrite /byte_radix in hb.
  rewrite /append_byte /byte_radix.
  smt().
trivial.
qed.

lemma decoder_normalization_preconditions_satisfiable :
  exists s tail_state,
    0 <= s < mode2_hbz_alphabet /\
    rans_initial_state <= tail_state < 2147483648 /\
    0 <= mode2_normalization_len tail_state s <= 2.
proof.
exists 6 rans_initial_state.
split; first rewrite /mode2_hbz_alphabet; smt().
split; first rewrite /rans_initial_state; smt().
exact (renorm_len_le2 6 rans_initial_state _ _); by
  rewrite /mode2_hbz_alphabet /rans_initial_state; smt().
qed.

end Mode2RansDecoderNormalization.
