require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray8192.

theory VerifyUnpackVkM23CoefficientsPostFreeze.

(* This theory isolates the exact 15-byte/8-word group transition used by the
   generated decoder.  Composing these group lemmas with the generated
   procedure's two nested loops remains a separate obligation. *)

op mode2_rows : int = 2.
op mode2_groups_per_poly : int = 32.
op mode2_coeffs_per_group : int = 8.
op mode2_coeffs_per_poly : int = 256.
op mode2_active_words : int = 512.
op mode2_input_prefix : int = 32.
op mode2_poly_stride : int = 480.
op mode2_group_stride : int = 15.
op coeff_tail_frame (before after : BArray8192.t) (start : int) : bool =
  forall i, start <= i < 2048 =>
    BArray8192.get32 after i = BArray8192.get32 before i.

op unpack_vk_group_byte_offset (poly group : int) : int =
  mode2_input_prefix + mode2_poly_stride * poly + mode2_group_stride * group.

op unpack_vk_group_byte (vkp : BArray2752.t) (poly group byte : int) : W8.t =
  BArray2752.get8 vkp (unpack_vk_group_byte_offset poly group + byte).

op unpack_vk_lane_word (vkp : BArray2752.t) (poly group lane : int) : W32.t =
  if lane = 0 then
    (zeroextu32 (unpack_vk_group_byte vkp poly group 0)) `|`
    (((zeroextu32 (unpack_vk_group_byte vkp poly group 1)) `&`
      W32.of_int 127) `<<` W8.of_int 8)
  else if lane = 1 then
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 1)) `>>`
      W8.of_int 7) `|`
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 2)) `<<`
      W8.of_int 1) `|`
    ((((zeroextu32 (unpack_vk_group_byte vkp poly group 3)) `&`
       W32.of_int 63)) `<<` W8.of_int 9)
  else if lane = 2 then
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 3)) `>>`
      W8.of_int 6) `|`
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 4)) `<<`
      W8.of_int 2) `|`
    ((((zeroextu32 (unpack_vk_group_byte vkp poly group 5)) `&`
       W32.of_int 31)) `<<` W8.of_int 10)
  else if lane = 3 then
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 5)) `>>`
      W8.of_int 5) `|`
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 6)) `<<`
      W8.of_int 3) `|`
    ((((zeroextu32 (unpack_vk_group_byte vkp poly group 7)) `&`
       W32.of_int 15)) `<<` W8.of_int 11)
  else if lane = 4 then
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 7)) `>>`
      W8.of_int 4) `|`
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 8)) `<<`
      W8.of_int 4) `|`
    ((((zeroextu32 (unpack_vk_group_byte vkp poly group 9)) `&`
       W32.of_int 7)) `<<` W8.of_int 12)
  else if lane = 5 then
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 9)) `>>`
      W8.of_int 3) `|`
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 10)) `<<`
      W8.of_int 5) `|`
    ((((zeroextu32 (unpack_vk_group_byte vkp poly group 11)) `&`
       W32.of_int 3)) `<<` W8.of_int 13)
  else if lane = 6 then
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 11)) `>>`
      W8.of_int 2) `|`
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 12)) `<<`
      W8.of_int 6) `|`
    ((((zeroextu32 (unpack_vk_group_byte vkp poly group 13)) `&`
       W32.of_int 1)) `<<` W8.of_int 14)
  else if lane = 7 then
    (((zeroextu32 (unpack_vk_group_byte vkp poly group 13)) `>>`
      W8.of_int 1) `&` W32.of_int 127) `|`
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 14)) `<<`
      W8.of_int 7)
  else W32.zero.

op unpack_vk_coeff_word (vkp : BArray2752.t) (idx : int) : W32.t =
  if 0 <= idx < mode2_active_words then
    let poly = idx %/ mode2_coeffs_per_poly in
    let row_idx = idx %% mode2_coeffs_per_poly in
    let group = row_idx %/ mode2_coeffs_per_group in
    let lane = row_idx %% mode2_coeffs_per_group in
    unpack_vk_lane_word vkp poly group lane
  else W32.zero.

op decoded_coeff_prefix (outp : BArray8192.t) (vkp : BArray2752.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 outp i = unpack_vk_coeff_word vkp i.

lemma coeff_tail_frame_refl before start :
  coeff_tail_frame before before start.
proof. rewrite /coeff_tail_frame; trivial. qed.

lemma coeff_tail_frame_step before after n value :
  0 <= n < 2048 =>
  coeff_tail_frame before after n =>
  coeff_tail_frame before (BArray8192.set32 after n value) (n + 1).
proof.
move=> hn hframe.
rewrite /coeff_tail_frame => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
rewrite ifF 1:/#.
apply hframe; smt().
qed.

lemma decoded_coeff_prefix_zero outp vkp :
  decoded_coeff_prefix outp vkp 0.
proof. rewrite /decoded_coeff_prefix; smt(). qed.

lemma decoded_coeff_prefix_step outp vkp n value :
  0 <= n < mode2_active_words =>
  value = unpack_vk_coeff_word vkp n =>
  decoded_coeff_prefix outp vkp n =>
  decoded_coeff_prefix (BArray8192.set32 outp n value) vkp (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /decoded_coeff_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
   apply hprefix; smt().
qed.

lemma unpack_vk_coeff_word_group vkp poly group lane :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  0 <= lane < mode2_coeffs_per_group =>
  unpack_vk_coeff_word vkp
    (mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * group + lane) =
  unpack_vk_lane_word vkp poly group lane.
proof.
move=> hpoly hgroup hlane.
rewrite /unpack_vk_coeff_word.
have hidx :
  0 <= mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * group + lane <
      mode2_active_words.
+ rewrite /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_active_words.
   smt().
rewrite hidx /=.
have hrow :
    (mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * group + lane) %%
      mode2_coeffs_per_poly =
    mode2_coeffs_per_group * group + lane.
+ rewrite /mode2_coeffs_per_poly /mode2_coeffs_per_group
           /mode2_active_words.
   smt(@IntDiv).
have hpolyq :
    (mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * group + lane) %/
      mode2_coeffs_per_poly = poly.
+ rewrite /mode2_coeffs_per_poly /mode2_coeffs_per_group
           /mode2_active_words.
   smt(@IntDiv).
rewrite hpolyq hrow.
have hgroupq :
    (mode2_coeffs_per_group * group + lane) %/ mode2_coeffs_per_group = group.
+ rewrite /mode2_coeffs_per_group.
   smt(@IntDiv).
have hlanem :
    (mode2_coeffs_per_group * group + lane) %% mode2_coeffs_per_group = lane.
+ rewrite /mode2_coeffs_per_group.
   smt(@IntDiv).
by rewrite hgroupq hlanem.
qed.

op unpack_vk_group_base (poly group : int) : int =
  mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * group.

op unpack_vk_group_stage1
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  BArray8192.set32 bp (unpack_vk_group_base poly group + 0)
    (unpack_vk_lane_word vkp poly group 0).

op unpack_vk_group_stage2
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  BArray8192.set32 (unpack_vk_group_stage1 bp vkp poly group)
    (unpack_vk_group_base poly group + 1)
    (unpack_vk_lane_word vkp poly group 1).

op unpack_vk_group_stage3
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  BArray8192.set32 (unpack_vk_group_stage2 bp vkp poly group)
    (unpack_vk_group_base poly group + 2)
    (unpack_vk_lane_word vkp poly group 2).

op unpack_vk_group_stage4
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  BArray8192.set32 (unpack_vk_group_stage3 bp vkp poly group)
    (unpack_vk_group_base poly group + 3)
    (unpack_vk_lane_word vkp poly group 3).

op unpack_vk_group_stage5
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  BArray8192.set32 (unpack_vk_group_stage4 bp vkp poly group)
    (unpack_vk_group_base poly group + 4)
    (unpack_vk_lane_word vkp poly group 4).

op unpack_vk_group_stage6
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  BArray8192.set32 (unpack_vk_group_stage5 bp vkp poly group)
    (unpack_vk_group_base poly group + 5)
    (unpack_vk_lane_word vkp poly group 5).

op unpack_vk_group_stage7
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  BArray8192.set32 (unpack_vk_group_stage6 bp vkp poly group)
    (unpack_vk_group_base poly group + 6)
    (unpack_vk_lane_word vkp poly group 6).

op unpack_vk_group_stage8
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  BArray8192.set32 (unpack_vk_group_stage7 bp vkp poly group)
    (unpack_vk_group_base poly group + 7)
    (unpack_vk_lane_word vkp poly group 7).

op unpack_vk_group_write
    (bp : BArray8192.t) (vkp : BArray2752.t) (poly group : int) : BArray8192.t =
  unpack_vk_group_stage8 bp vkp poly group.

lemma unpack_vk_group_base_range poly group lane :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  0 <= lane < mode2_coeffs_per_group =>
  0 <= unpack_vk_group_base poly group + lane < mode2_active_words.
proof.
rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
        /mode2_rows /mode2_groups_per_poly /mode2_active_words.
smt().
qed.

lemma decoded_coeff_prefix_stage1 bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  decoded_coeff_prefix bp vkp (unpack_vk_group_base poly group) =>
  decoded_coeff_prefix (unpack_vk_group_stage1 bp vkp poly group) vkp
    (unpack_vk_group_base poly group + 1).
proof.
move=> hpoly hgroup hprefix.
rewrite /unpack_vk_group_stage1.
apply (decoded_coeff_prefix_step _ _ (unpack_vk_group_base poly group)).
+ apply (unpack_vk_group_base_range poly group 0); smt().
+ have hlane0 : 0 <= 0 < mode2_coeffs_per_group by smt().
   rewrite (unpack_vk_coeff_word_group vkp poly group 0 hpoly hgroup hlane0).
   trivial.
+ exact hprefix.
qed.

lemma decoded_coeff_prefix_stage2 bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  decoded_coeff_prefix bp vkp (unpack_vk_group_base poly group) =>
  decoded_coeff_prefix (unpack_vk_group_stage2 bp vkp poly group) vkp
    (unpack_vk_group_base poly group + 2).
proof.
move=> hpoly hgroup hprefix.
rewrite /unpack_vk_group_stage2.
apply (decoded_coeff_prefix_step _ _ (unpack_vk_group_base poly group + 1)).
+ apply (unpack_vk_group_base_range poly group 1); smt().
+ have hlane1 : 0 <= 1 < mode2_coeffs_per_group by smt().
   rewrite (unpack_vk_coeff_word_group vkp poly group 1 hpoly hgroup hlane1).
   trivial.
+ exact (decoded_coeff_prefix_stage1 bp vkp poly group hpoly hgroup hprefix).
qed.

lemma decoded_coeff_prefix_stage3 bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  decoded_coeff_prefix bp vkp (unpack_vk_group_base poly group) =>
  decoded_coeff_prefix (unpack_vk_group_stage3 bp vkp poly group) vkp
    (unpack_vk_group_base poly group + 3).
proof.
move=> hpoly hgroup hprefix.
rewrite /unpack_vk_group_stage3.
apply (decoded_coeff_prefix_step _ _ (unpack_vk_group_base poly group + 2)).
+ apply (unpack_vk_group_base_range poly group 2); smt().
+ have hlane2 : 0 <= 2 < mode2_coeffs_per_group by smt().
   rewrite (unpack_vk_coeff_word_group vkp poly group 2 hpoly hgroup hlane2).
   trivial.
+ exact (decoded_coeff_prefix_stage2 bp vkp poly group hpoly hgroup hprefix).
qed.

lemma decoded_coeff_prefix_stage4 bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  decoded_coeff_prefix bp vkp (unpack_vk_group_base poly group) =>
  decoded_coeff_prefix (unpack_vk_group_stage4 bp vkp poly group) vkp
    (unpack_vk_group_base poly group + 4).
proof.
move=> hpoly hgroup hprefix.
rewrite /unpack_vk_group_stage4.
apply (decoded_coeff_prefix_step _ _ (unpack_vk_group_base poly group + 3)).
+ apply (unpack_vk_group_base_range poly group 3); smt().
+ have hlane3 : 0 <= 3 < mode2_coeffs_per_group by smt().
   rewrite (unpack_vk_coeff_word_group vkp poly group 3 hpoly hgroup hlane3).
   trivial.
+ exact (decoded_coeff_prefix_stage3 bp vkp poly group hpoly hgroup hprefix).
qed.

lemma decoded_coeff_prefix_stage5 bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  decoded_coeff_prefix bp vkp (unpack_vk_group_base poly group) =>
  decoded_coeff_prefix (unpack_vk_group_stage5 bp vkp poly group) vkp
    (unpack_vk_group_base poly group + 5).
proof.
move=> hpoly hgroup hprefix.
rewrite /unpack_vk_group_stage5.
apply (decoded_coeff_prefix_step _ _ (unpack_vk_group_base poly group + 4)).
+ apply (unpack_vk_group_base_range poly group 4); smt().
+ have hlane4 : 0 <= 4 < mode2_coeffs_per_group by smt().
   rewrite (unpack_vk_coeff_word_group vkp poly group 4 hpoly hgroup hlane4).
   trivial.
+ exact (decoded_coeff_prefix_stage4 bp vkp poly group hpoly hgroup hprefix).
qed.

lemma decoded_coeff_prefix_stage6 bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  decoded_coeff_prefix bp vkp (unpack_vk_group_base poly group) =>
  decoded_coeff_prefix (unpack_vk_group_stage6 bp vkp poly group) vkp
    (unpack_vk_group_base poly group + 6).
proof.
move=> hpoly hgroup hprefix.
rewrite /unpack_vk_group_stage6.
apply (decoded_coeff_prefix_step _ _ (unpack_vk_group_base poly group + 5)).
+ apply (unpack_vk_group_base_range poly group 5); smt().
+ have hlane5 : 0 <= 5 < mode2_coeffs_per_group by smt().
   rewrite (unpack_vk_coeff_word_group vkp poly group 5 hpoly hgroup hlane5).
   trivial.
+ exact (decoded_coeff_prefix_stage5 bp vkp poly group hpoly hgroup hprefix).
qed.

lemma decoded_coeff_prefix_stage7 bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  decoded_coeff_prefix bp vkp (unpack_vk_group_base poly group) =>
  decoded_coeff_prefix (unpack_vk_group_stage7 bp vkp poly group) vkp
    (unpack_vk_group_base poly group + 7).
proof.
move=> hpoly hgroup hprefix.
rewrite /unpack_vk_group_stage7.
apply (decoded_coeff_prefix_step _ _ (unpack_vk_group_base poly group + 6)).
+ apply (unpack_vk_group_base_range poly group 6); smt().
+ have hlane6 : 0 <= 6 < mode2_coeffs_per_group by smt().
   rewrite (unpack_vk_coeff_word_group vkp poly group 6 hpoly hgroup hlane6).
   trivial.
+ exact (decoded_coeff_prefix_stage6 bp vkp poly group hpoly hgroup hprefix).
qed.

lemma decoded_coeff_prefix_group_step bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  decoded_coeff_prefix bp vkp
    (mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * group) =>
  decoded_coeff_prefix (unpack_vk_group_write bp vkp poly group) vkp
    (mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * (group + 1)).
proof.
move=> hpoly hgroup hprefix.
rewrite /unpack_vk_group_write.
have hbase :
    mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * (group + 1) =
    unpack_vk_group_base poly group + 8.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_group; ring.
rewrite hbase.
rewrite /unpack_vk_group_stage8.
apply (decoded_coeff_prefix_step _ _ (unpack_vk_group_base poly group + 7)).
+ apply (unpack_vk_group_base_range poly group 7); smt().
+ have hlane7 : 0 <= 7 < mode2_coeffs_per_group by smt().
   rewrite (unpack_vk_coeff_word_group vkp poly group 7 hpoly hgroup hlane7).
   trivial.
+ exact (decoded_coeff_prefix_stage7 bp vkp poly group hpoly hgroup hprefix).
qed.

lemma coeff_tail_frame_stage1 before bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  coeff_tail_frame before bp (unpack_vk_group_base poly group) =>
  coeff_tail_frame before (unpack_vk_group_stage1 bp vkp poly group)
    (unpack_vk_group_base poly group + 1).
proof.
move=> hpoly hgroup hframe.
rewrite /unpack_vk_group_stage1.
apply coeff_tail_frame_step.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_rows /mode2_groups_per_poly.
   smt().
+ exact hframe.
qed.

lemma coeff_tail_frame_stage2 before bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  coeff_tail_frame before bp (unpack_vk_group_base poly group) =>
  coeff_tail_frame before (unpack_vk_group_stage2 bp vkp poly group)
    (unpack_vk_group_base poly group + 2).
proof.
move=> hpoly hgroup hframe.
rewrite /unpack_vk_group_stage2.
apply coeff_tail_frame_step.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_rows /mode2_groups_per_poly.
   smt().
+ exact (coeff_tail_frame_stage1 before bp vkp poly group hpoly hgroup hframe).
qed.

lemma coeff_tail_frame_stage3 before bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  coeff_tail_frame before bp (unpack_vk_group_base poly group) =>
  coeff_tail_frame before (unpack_vk_group_stage3 bp vkp poly group)
    (unpack_vk_group_base poly group + 3).
proof.
move=> hpoly hgroup hframe.
rewrite /unpack_vk_group_stage3.
apply coeff_tail_frame_step.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_rows /mode2_groups_per_poly.
   smt().
+ exact (coeff_tail_frame_stage2 before bp vkp poly group hpoly hgroup hframe).
qed.

lemma coeff_tail_frame_stage4 before bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  coeff_tail_frame before bp (unpack_vk_group_base poly group) =>
  coeff_tail_frame before (unpack_vk_group_stage4 bp vkp poly group)
    (unpack_vk_group_base poly group + 4).
proof.
move=> hpoly hgroup hframe.
rewrite /unpack_vk_group_stage4.
apply coeff_tail_frame_step.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_rows /mode2_groups_per_poly.
   smt().
+ exact (coeff_tail_frame_stage3 before bp vkp poly group hpoly hgroup hframe).
qed.

lemma coeff_tail_frame_stage5 before bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  coeff_tail_frame before bp (unpack_vk_group_base poly group) =>
  coeff_tail_frame before (unpack_vk_group_stage5 bp vkp poly group)
    (unpack_vk_group_base poly group + 5).
proof.
move=> hpoly hgroup hframe.
rewrite /unpack_vk_group_stage5.
apply coeff_tail_frame_step.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_rows /mode2_groups_per_poly.
   smt().
+ exact (coeff_tail_frame_stage4 before bp vkp poly group hpoly hgroup hframe).
qed.

lemma coeff_tail_frame_stage6 before bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  coeff_tail_frame before bp (unpack_vk_group_base poly group) =>
  coeff_tail_frame before (unpack_vk_group_stage6 bp vkp poly group)
    (unpack_vk_group_base poly group + 6).
proof.
move=> hpoly hgroup hframe.
rewrite /unpack_vk_group_stage6.
apply coeff_tail_frame_step.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_rows /mode2_groups_per_poly.
   smt().
+ exact (coeff_tail_frame_stage5 before bp vkp poly group hpoly hgroup hframe).
qed.

lemma coeff_tail_frame_stage7 before bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  coeff_tail_frame before bp (unpack_vk_group_base poly group) =>
  coeff_tail_frame before (unpack_vk_group_stage7 bp vkp poly group)
    (unpack_vk_group_base poly group + 7).
proof.
move=> hpoly hgroup hframe.
rewrite /unpack_vk_group_stage7.
apply coeff_tail_frame_step.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_rows /mode2_groups_per_poly.
   smt().
+ exact (coeff_tail_frame_stage6 before bp vkp poly group hpoly hgroup hframe).
qed.

lemma coeff_tail_frame_group_step before bp vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  coeff_tail_frame before bp
    (mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * group) =>
  coeff_tail_frame before (unpack_vk_group_write bp vkp poly group)
    (mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * (group + 1)).
proof.
move=> hpoly hgroup hframe.
rewrite /unpack_vk_group_write.
have hbase :
    mode2_coeffs_per_poly * poly + mode2_coeffs_per_group * (group + 1) =
    unpack_vk_group_base poly group + 8.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_group; ring.
rewrite hbase.
rewrite /unpack_vk_group_stage8.
apply coeff_tail_frame_step.
+ rewrite /unpack_vk_group_base /mode2_coeffs_per_poly /mode2_coeffs_per_group
          /mode2_rows /mode2_groups_per_poly.
   smt().
+ exact (coeff_tail_frame_stage7 before bp vkp poly group hpoly hgroup hframe).
qed.

end VerifyUnpackVkM23CoefficientsPostFreeze.
