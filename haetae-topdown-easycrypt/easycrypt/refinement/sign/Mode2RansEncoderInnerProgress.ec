require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansByteStack
  Mode2RansNormalization Mode2RansArrayListBridge.

theory Mode2RansEncoderInnerProgress.

import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansByteStack
       Mode2RansNormalization Mode2RansArrayListBridge.

op inner_state_after (x k : int) : int =
  if k = 0 then x
  else if k = 1 then x %/ byte_radix
  else x %/ (byte_radix * byte_radix).

op inner_written_suffix (x s k : int) : int list =
  drop (mode2_normalization_len x s - k)
    (mode2_normalization_bytes x s).

lemma normalization_len_cases s x :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  mode2_normalization_len x s = 0 \/
  mode2_normalization_len x s = 1 \/
  mode2_normalization_len x s = 2.
proof.
move=> hs hx.
have hlen := renorm_len_le2 s x hs hx.
smt().
qed.

lemma inner_written_suffix_zero s x :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  inner_written_suffix x s 0 = [].
proof.
move=> hs hx.
have [hlen _] := mode2_normalization_bytes_size s x hs hx.
rewrite /inner_written_suffix /= -hlen drop_oversize 1:/#.
trivial.
qed.

lemma inner_state_after_zero x :
  inner_state_after x 0 = x.
proof. trivial. qed.

lemma inner_state_after_step x k :
  0 <= k < 2 =>
  inner_state_after x (k + 1) = inner_state_after x k %/ byte_radix.
proof.
move=> hk.
have hcases : k = 0 \/ k = 1 by smt().
elim hcases => ->; first trivial.
rewrite /inner_state_after /byte_radix /=.
rewrite -divzMr 1:/# 1:/#.
trivial.
qed.

lemma inner_guard_before_total s x k :
  0 <= k < mode2_normalization_len x s =>
  hbz_xmax s <= inner_state_after x k.
proof.
move=> hk.
rewrite /mode2_normalization_len /renorm_len
        /inner_state_after /byte_radix in hk.
rewrite /mode2_normalization_len /renorm_len
        /inner_state_after /byte_radix.
case (x < hbz_xmax s) => h0; first smt().
case (x %/ 256 < hbz_xmax s) => h1.
+ smt().
+ have hkcases : k = 0 \/ k = 1.
  - move: hk; clear h0 h1; smt().
  elim hkcases => ->.
  - rewrite lezNgt; exact h0.
  - rewrite lezNgt; exact h1.
qed.

lemma inner_guard_after_total s x :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  inner_state_after x (mode2_normalization_len x s) < hbz_xmax s.
proof.
move=> hs hx.
rewrite /mode2_normalization_len /renorm_len
        /inner_state_after /byte_radix.
case (x < hbz_xmax s) => h0; first smt().
case (x %/ 256 < hbz_xmax s) => h1; first smt().
have [hrlo hrhi] := renorm_reduced_bounds s x hs hx.
rewrite /mode2_normalized_state /renorm_reduced /byte_radix in hrhi.
rewrite ifF 1:/# ifF 1:/# in hrhi.
exact hrhi.
qed.

lemma inner_state_after_total s x :
  inner_state_after x (mode2_normalization_len x s) =
    mode2_normalized_state x s.
proof.
rewrite /mode2_normalization_len /mode2_normalized_state
        /renorm_len /renorm_reduced /inner_state_after /byte_radix.
case (x < hbz_xmax s) => h0; first trivial.
case (x %/ 256 < hbz_xmax s) => h1; trivial.
qed.

lemma inner_written_suffix_total s x :
  inner_written_suffix x s (mode2_normalization_len x s) =
    mode2_normalization_bytes x s.
proof.
rewrite /inner_written_suffix.
have -> : mode2_normalization_len x s -
    mode2_normalization_len x s = 0 by ring.
exact (drop0 (mode2_normalization_bytes x s)).
qed.

lemma inner_written_suffix_step s x k :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  0 <= k < mode2_normalization_len x s =>
  inner_written_suffix x s (k + 1) =
    (inner_state_after x k %% byte_radix) ::
      inner_written_suffix x s k.
proof.
move=> hs hx hk.
rewrite /inner_written_suffix /mode2_normalization_len
        /mode2_normalization_bytes /renorm_len /renorm_bytes
        /inner_state_after /byte_radix in hk.
rewrite /inner_written_suffix /mode2_normalization_len
        /mode2_normalization_bytes /renorm_len /renorm_bytes
        /inner_state_after /byte_radix.
case (x < hbz_xmax s) => h0; first smt().
case (x %/ 256 < hbz_xmax s) => h1.
+ have hk0 : k = 0.
  - move: hk; smt().
  subst k.
  trivial.
+ have hkcases : k = 0 \/ k = 1.
  - move: hk; smt().
  elim hkcases => ->; trivial.
qed.

lemma inner_progress_cursor off0 k total :
  0 <= total <= 2 =>
  0 <= k <= total =>
  total <= off0 =>
  0 <= off0 - k /\ off0 - k <= off0.
proof. smt(). qed.

lemma inner_progress_segment_step a off0 x s k tail :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  0 <= k < mode2_normalization_len x s =>
  mode2_normalization_len x s <= off0 =>
  segment_matches a (off0 - k)
    (inner_written_suffix x s k ++ tail) =>
  segment_matches
    (BArray2048.set8 a (off0 - k - 1)
      (W8.of_int (inner_state_after x k %% byte_radix)))
    (off0 - (k + 1))
    (inner_written_suffix x s (k + 1) ++ tail).
proof.
move=> hs hx hk hfit hm.
rewrite inner_written_suffix_step 1:hs 1:hx 1:hk.
have hpos : 0 < off0 - k by smt().
have hb : 0 <= inner_state_after x k %% byte_radix < 256.
+ exact (modz_cmp (inner_state_after x k) 256 _); smt().
have hp := segment_matches_prepend_set a (off0 - k)
  (inner_written_suffix x s k ++ tail)
  (inner_state_after x k %% byte_radix) hm hpos hb.
have -> : off0 - (k + 1) = off0 - k - 1 by ring.
exact hp.
qed.

lemma inner_progress_preconditions_satisfiable :
  exists x s,
    0 <= s < mode2_hbz_alphabet /\
    rans_initial_state <= x < 2147483648 /\
    0 <= mode2_normalization_len x s <= 2.
proof.
exists rans_initial_state 0.
split; first rewrite /mode2_hbz_alphabet; smt().
split; first rewrite /rans_initial_state; smt().
exact (renorm_len_le2 0 rans_initial_state _ _); by
  rewrite /mode2_hbz_alphabet /rans_initial_state; smt().
qed.

end Mode2RansEncoderInnerProgress.
