require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2HbzCodecSpec Mode2RansByteStack
  Mode2RansNormalization Mode2RansArrayListBridge.

theory Mode2RansEncoderSerialization.

import Mode2HbzCodecSpec Mode2RansByteStack
       Mode2RansNormalization Mode2RansArrayListBridge.

op actual_w32_le_bytes (x : W32.t) : int list =
  [W8.to_uint (truncateu8 x);
   W8.to_uint (truncateu8 (x `>>` W8.of_int 8));
   W8.to_uint
     (truncateu8 ((x `>>` W8.of_int 8) `>>` W8.of_int 8));
   W8.to_uint
     (truncateu8
       (((x `>>` W8.of_int 8) `>>` W8.of_int 8) `>>` W8.of_int 8))].

op actual_store_w32_le
    (a : BArray2048.t) (start : int) (x : W32.t) : BArray2048.t =
  let a = BArray2048.set8 a start (truncateu8 x) in
  let x1 = x `>>` W8.of_int 8 in
  let a = BArray2048.set8 a (start + 1) (truncateu8 x1) in
  let x2 = x1 `>>` W8.of_int 8 in
  let a = BArray2048.set8 a (start + 2) (truncateu8 x2) in
  let x3 = x2 `>>` W8.of_int 8 in
  BArray2048.set8 a (start + 3) (truncateu8 x3).

lemma actual_w32_le_bytes_serialize (x : W32.t) :
  actual_w32_le_bytes x = serialize32_le (W32.to_uint x).
proof.
rewrite /actual_w32_le_bytes /serialize32_le /byte_radix.
rewrite !encoder_low_byte_uint !encoder_shift8_uint.
have h256 : W32.to_uint x %/ 256 %/ 256 =
    W32.to_uint x %/ 65536.
+ rewrite -divzMr 1:/# 1:/#; trivial.
have h65536 : W32.to_uint x %/ 65536 %/ 256 =
    W32.to_uint x %/ 16777216.
+ rewrite -divzMr 1:/# 1:/#; trivial.
rewrite h256 h65536.
trivial.
qed.

lemma actual_store_w32_le_get0 a start x :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  BArray2048.get8 (actual_store_w32_le a start x) start = truncateu8 x.
proof.
move=> hstart.
rewrite /actual_store_w32_le.
smt(BArray2048.get_setE).
qed.

lemma actual_store_w32_le_get1 a start x :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  BArray2048.get8 (actual_store_w32_le a start x) (start + 1) =
    truncateu8 (x `>>` W8.of_int 8).
proof.
move=> hstart.
rewrite /actual_store_w32_le.
smt(BArray2048.get_setE).
qed.

lemma actual_store_w32_le_get2 a start x :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  BArray2048.get8 (actual_store_w32_le a start x) (start + 2) =
    truncateu8 ((x `>>` W8.of_int 8) `>>` W8.of_int 8).
proof.
move=> hstart.
rewrite /actual_store_w32_le.
smt(BArray2048.get_setE).
qed.

lemma actual_store_w32_le_get3 a start x :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  BArray2048.get8 (actual_store_w32_le a start x) (start + 3) =
    truncateu8
      (((x `>>` W8.of_int 8) `>>` W8.of_int 8) `>>` W8.of_int 8).
proof.
move=> hstart.
rewrite /actual_store_w32_le.
smt(BArray2048.get_setE).
qed.

lemma actual_w32_le_bytes_nth0 x :
  nth 0 (actual_w32_le_bytes x) 0 = W8.to_uint (truncateu8 x).
proof. trivial. qed.

lemma actual_w32_le_bytes_nth1 x :
  nth 0 (actual_w32_le_bytes x) 1 =
    W8.to_uint (truncateu8 (x `>>` W8.of_int 8)).
proof. trivial. qed.

lemma actual_w32_le_bytes_nth2 x :
  nth 0 (actual_w32_le_bytes x) 2 =
    W8.to_uint
      (truncateu8 ((x `>>` W8.of_int 8) `>>` W8.of_int 8)).
proof. trivial. qed.

lemma actual_w32_le_bytes_nth3 x :
  nth 0 (actual_w32_le_bytes x) 3 =
    W8.to_uint
      (truncateu8
        (((x `>>` W8.of_int 8) `>>` W8.of_int 8) `>>` W8.of_int 8)).
proof. trivial. qed.

lemma actual_store_w32_le_get_inside a start x k :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  0 <= k < 4 =>
  W8.to_uint (BArray2048.get8 (actual_store_w32_le a start x) (start + k)) =
    nth 0 (serialize32_le (W32.to_uint x)) k.
proof.
move=> hstart hk.
rewrite -actual_w32_le_bytes_serialize.
have hcases : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
elim hcases => h0.
+ subst k.
  rewrite actual_store_w32_le_get0 1:hstart.
  rewrite actual_w32_le_bytes_nth0.
  trivial.
+ elim h0 => h1.
  - subst k.
    rewrite actual_store_w32_le_get1 1:hstart.
    rewrite actual_w32_le_bytes_nth1.
    trivial.
  - elim h1 => h2.
    * subst k.
      rewrite actual_store_w32_le_get2 1:hstart.
      rewrite actual_w32_le_bytes_nth2.
      trivial.
    * subst k.
      rewrite actual_store_w32_le_get3 1:hstart.
      rewrite actual_w32_le_bytes_nth3.
      trivial.
qed.

lemma actual_store_w32_le_get_outside a start x j :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  0 <= j < mode2_hbz_capacity =>
  (j < start \/ start + 4 <= j) =>
  BArray2048.get8 (actual_store_w32_le a start x) j =
    BArray2048.get8 a j.
proof.
move=> hstart hj hout.
rewrite /actual_store_w32_le.
smt(BArray2048.get_setE).
qed.

lemma actual_store_w32_le_prefix_frame before a start x :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  prefix_frame before a (start + 4) =>
  prefix_frame before (actual_store_w32_le a start x) start.
proof.
move=> hstart hframe.
rewrite /prefix_frame => k hk.
have hj : 0 <= k < mode2_hbz_capacity by smt().
have hout : k < start by smt().
have houtside : k < start \/ start + 4 <= k by left; exact hout.
rewrite (actual_store_w32_le_get_outside a start x k
           hstart hj houtside).
have hk4 : 0 <= k < start + 4 by smt().
exact (hframe k hk4).
qed.

lemma actual_encoder_final_state_serialization a start x :
  0 <= start /\ start + 4 <= mode2_hbz_capacity =>
  (forall k, 0 <= k < 4 =>
     W8.to_uint
       (BArray2048.get8 (actual_store_w32_le a start x) (start + k)) =
     nth 0 (serialize32_le (W32.to_uint x)) k) /\
  (forall j, 0 <= j < mode2_hbz_capacity =>
     (j < start \/ start + 4 <= j) =>
     BArray2048.get8 (actual_store_w32_le a start x) j =
     BArray2048.get8 a j).
proof.
move=> hstart.
split.
+ move=> k hk.
  exact (actual_store_w32_le_get_inside a start x k hstart hk).
+ move=> j hj hout.
  exact (actual_store_w32_le_get_outside a start x j hstart hj hout).
qed.

lemma actual_encoder_success_size_bounds off normalization_size :
  0 <= normalization_size =>
  4 <= off /\ off + normalization_size = mode2_hbz_count =>
  0 <= off - 4 <= 1020 /\
  4 <= 4 + normalization_size <= mode2_hbz_count /\
  off - 4 + (4 + normalization_size) = mode2_hbz_count.
proof.
move=> hsize [hoff hsum].
rewrite /mode2_hbz_count in hsum.
rewrite /mode2_hbz_count.
smt().
qed.

lemma encoder_serialization_preconditions_satisfiable :
  exists a bs,
    segment_matches a 4 bs /\
    prefix_frame a a 4 /\
    size bs = 0.
proof.
exists witness [].
have hstart : 0 <= 4 <= mode2_hbz_capacity by
  rewrite /mode2_hbz_capacity; smt().
split; first exact (segment_matches_nil witness 4 hstart).
split; first exact (prefix_frame_refl witness 4).
trivial.
qed.

end Mode2RansEncoderSerialization.
