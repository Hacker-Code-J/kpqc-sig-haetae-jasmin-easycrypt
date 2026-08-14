require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray8192 VerifyUnpackMode2Target
  VerifyUnpackVkM23CoefficientsPostFreeze.

theory VerifyUnpackVkM23BoundsPostFreeze.

import VerifyUnpackVkM23CoefficientsPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

op unpack_vk_coeff_prefix_bound (vkp : BArray2752.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    W32.to_uint (unpack_vk_coeff_word vkp i) < 32768.

lemma unpack_vk_lane_word_bound0 vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  W32.to_uint (unpack_vk_lane_word vkp poly group 0) < 32768.
proof.
move=> hpoly hgroup.
rewrite /unpack_vk_lane_word ifT 1:/#.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE /(`<<`) W32.shlwE W32.andwE.
   rewrite W8.of_uintK /= !W4u8.zeroextu32_bit.
   rewrite W32.get_to_uint W32.of_uintK /=.
   rewrite (modz_small 127 W32.modulus) 1:/#.
   smt().
rewrite W4u8.to_uint_zeroextu32.
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
rewrite (W32.to_uint_and_mod 7) 1:/# W4u8.to_uint_zeroextu32.
have hb0 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 0).
have hb1 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 1).
have hm1 := modz_cmp (W8.to_uint (unpack_vk_group_byte vkp poly group 1)) 128 _.
+ smt().
smt().
qed.

lemma unpack_vk_lane_word_bound1 vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  W32.to_uint (unpack_vk_lane_word vkp poly group 1) < 32768.
proof.
move=> hpoly hgroup.
rewrite /unpack_vk_lane_word ifF 1:/# ifT 1:/#.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE W32.orwE /(`>>`) W32.shrwE /(`<<`) !W32.shlwE W32.andwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   rewrite W32.get_to_uint W32.of_uintK /=.
   rewrite (modz_small 63 W32.modulus) 1:/#.
   smt().
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE /(`>>`) /(`<<`) W32.shlwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   smt().
rewrite W32.shr_div W8.of_uintK /=.
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
have hmask3u :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 3)) `&`
       W32.of_int 63) =
    W8.to_uint (unpack_vk_group_byte vkp poly group 3) %% 64.
+ rewrite (W32.to_uint_and_mod 6) 1:/# W4u8.to_uint_zeroextu32.
   trivial.
have hm3 := modz_cmp (W8.to_uint (unpack_vk_group_byte vkp poly group 3)) 64 _.
+ smt().
have hmask3lt :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 3)) `&`
       W32.of_int 63) < 2 ^ (32 - 9).
+ rewrite hmask3u.
   smt().
have hb1 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 1).
have hb2 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 2).
have hb3 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 3).
have hmask3b :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 3)) `&`
       W32.of_int 63) < 64.
+ rewrite hmask3u.
   smt().
rewrite W32.to_uint_shl 1:/# /=.
rewrite !W4u8.to_uint_zeroextu32.
rewrite (modz_small
  (W8.to_uint (unpack_vk_group_byte vkp poly group 2) * 2)
  W32.modulus).
+ smt().
rewrite (modz_small
  (W32.to_uint
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 3)) `&`
     W32.of_int 63) * 512)
  W32.modulus).
+ have hmask3cmp :=
    W32.to_uint_cmp
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 3)) `&`
       W32.of_int 63).
  smt().
smt().
qed.

lemma unpack_vk_lane_word_bound2 vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  W32.to_uint (unpack_vk_lane_word vkp poly group 2) < 32768.
proof.
move=> hpoly hgroup.
rewrite /unpack_vk_lane_word ifF 1:/# ifF 1:/# ifT 1:/#.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE W32.orwE /(`>>`) W32.shrwE /(`<<`) !W32.shlwE W32.andwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   rewrite W32.get_to_uint W32.of_uintK /=.
   rewrite (modz_small 31 W32.modulus) 1:/#.
   smt().
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE /(`>>`) /(`<<`) W32.shlwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   smt().
rewrite W32.shr_div W8.of_uintK /=.
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
have hmask5u :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 5)) `&`
       W32.of_int 31) =
    W8.to_uint (unpack_vk_group_byte vkp poly group 5) %% 32.
+ rewrite (W32.to_uint_and_mod 5) 1:/# W4u8.to_uint_zeroextu32.
   trivial.
have hm5 := modz_cmp (W8.to_uint (unpack_vk_group_byte vkp poly group 5)) 32 _.
+ smt().
have hmask5lt :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 5)) `&`
       W32.of_int 31) < 2 ^ (32 - 10).
+ rewrite hmask5u.
   smt().
rewrite W32.to_uint_shl 1:/# /=.
rewrite !W4u8.to_uint_zeroextu32.
have hb3 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 3).
have hb4 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 4).
have hb5 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 5).
rewrite (modz_small
  (W8.to_uint (unpack_vk_group_byte vkp poly group 4) * 4)
  W32.modulus).
+ smt().
rewrite (modz_small
  (W32.to_uint
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 5)) `&`
     W32.of_int 31) * 1024)
  W32.modulus).
+ have hmask5cmp :=
    W32.to_uint_cmp
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 5)) `&`
       W32.of_int 31).
  smt().
smt().
qed.

lemma unpack_vk_lane_word_bound3 vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  W32.to_uint (unpack_vk_lane_word vkp poly group 3) < 32768.
proof.
move=> hpoly hgroup.
rewrite /unpack_vk_lane_word ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/#.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE W32.orwE /(`>>`) W32.shrwE /(`<<`) !W32.shlwE W32.andwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   rewrite W32.get_to_uint W32.of_uintK /=.
   rewrite (modz_small 15 W32.modulus) 1:/#.
   smt().
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE /(`>>`) W32.shrwE /(`<<`) W32.shlwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   smt().
rewrite W32.shr_div W8.of_uintK /=.
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
have hmask7u :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 7)) `&`
       W32.of_int 15) =
    W8.to_uint (unpack_vk_group_byte vkp poly group 7) %% 16.
+ rewrite (W32.to_uint_and_mod 4) 1:/# W4u8.to_uint_zeroextu32.
   trivial.
have hm7 := modz_cmp (W8.to_uint (unpack_vk_group_byte vkp poly group 7)) 16 _.
+ smt().
have hmask7lt :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 7)) `&`
       W32.of_int 15) < 2 ^ (32 - 11).
+ rewrite hmask7u.
   smt().
rewrite W32.to_uint_shl 1:/# /=.
rewrite !W4u8.to_uint_zeroextu32.
have hb5 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 5).
have hb6 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 6).
have hb7 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 7).
rewrite (modz_small
  (W8.to_uint (unpack_vk_group_byte vkp poly group 6) * 8)
  W32.modulus).
+ smt().
rewrite (modz_small
  (W32.to_uint
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 7)) `&`
     W32.of_int 15) * 2048)
  W32.modulus).
+ have hmask7cmp :=
    W32.to_uint_cmp
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 7)) `&`
       W32.of_int 15).
  smt().
smt().
qed.

lemma unpack_vk_lane_word_bound4 vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  W32.to_uint (unpack_vk_lane_word vkp poly group 4) < 32768.
proof.
move=> hpoly hgroup.
rewrite /unpack_vk_lane_word ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/#.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE W32.orwE /(`>>`) W32.shrwE /(`<<`) !W32.shlwE W32.andwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   rewrite W32.get_to_uint W32.of_uintK /=.
   rewrite (modz_small 7 W32.modulus) 1:/#.
   smt().
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE /(`>>`) W32.shrwE /(`<<`) W32.shlwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   smt().
rewrite W32.shr_div W8.of_uintK /=.
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
have hmask9u :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 9)) `&`
       W32.of_int 7) =
    W8.to_uint (unpack_vk_group_byte vkp poly group 9) %% 8.
+ rewrite (W32.to_uint_and_mod 3) 1:/# W4u8.to_uint_zeroextu32.
   trivial.
have hm9 := modz_cmp (W8.to_uint (unpack_vk_group_byte vkp poly group 9)) 8 _.
+ smt().
have hmask9lt :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 9)) `&`
       W32.of_int 7) < 2 ^ (32 - 12).
+ rewrite hmask9u.
   smt().
rewrite W32.to_uint_shl 1:/# /=.
rewrite !W4u8.to_uint_zeroextu32.
have hb7 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 7).
have hb8 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 8).
have hb9 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 9).
rewrite (modz_small
  (W8.to_uint (unpack_vk_group_byte vkp poly group 8) * 16)
  W32.modulus).
+ smt().
rewrite (modz_small
  (W32.to_uint
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 9)) `&`
     W32.of_int 7) * 4096)
  W32.modulus).
+ have hmask9cmp :=
    W32.to_uint_cmp
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 9)) `&`
       W32.of_int 7).
  smt().
smt().
qed.

lemma unpack_vk_lane_word_bound5 vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  W32.to_uint (unpack_vk_lane_word vkp poly group 5) < 32768.
proof.
move=> hpoly hgroup.
rewrite /unpack_vk_lane_word ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/#.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE W32.orwE /(`>>`) W32.shrwE /(`<<`) !W32.shlwE W32.andwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   rewrite W32.get_to_uint W32.of_uintK /=.
   rewrite (modz_small 3 W32.modulus) 1:/#.
   smt().
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE /(`>>`) W32.shrwE /(`<<`) W32.shlwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   smt().
rewrite W32.shr_div W8.of_uintK /=.
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
have hmask11u :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 11)) `&`
       W32.of_int 3) =
    W8.to_uint (unpack_vk_group_byte vkp poly group 11) %% 4.
+ rewrite (W32.to_uint_and_mod 2) 1:/# W4u8.to_uint_zeroextu32.
   trivial.
have hm11 := modz_cmp (W8.to_uint (unpack_vk_group_byte vkp poly group 11)) 4 _.
+ smt().
have hmask11lt :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 11)) `&`
       W32.of_int 3) < 2 ^ (32 - 13).
+ rewrite hmask11u.
   smt().
rewrite W32.to_uint_shl 1:/# /=.
rewrite !W4u8.to_uint_zeroextu32.
have hb9 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 9).
have hb10 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 10).
have hb11 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 11).
rewrite (modz_small
  (W8.to_uint (unpack_vk_group_byte vkp poly group 10) * 32)
  W32.modulus).
+ smt().
rewrite (modz_small
  (W32.to_uint
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 11)) `&`
     W32.of_int 3) * 8192)
  W32.modulus).
+ have hmask11cmp :=
    W32.to_uint_cmp
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 11)) `&`
       W32.of_int 3).
  smt().
smt().
qed.

lemma unpack_vk_lane_word_bound6 vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  W32.to_uint (unpack_vk_lane_word vkp poly group 6) < 32768.
proof.
move=> hpoly hgroup.
rewrite /unpack_vk_lane_word ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/#.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE W32.orwE /(`>>`) W32.shrwE /(`<<`) !W32.shlwE W32.andwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   rewrite W32.get_to_uint W32.of_uintK /=.
   rewrite (modz_small 1 W32.modulus) 1:/#.
   smt().
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE /(`>>`) W32.shrwE /(`<<`) W32.shlwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   smt().
rewrite W32.shr_div W8.of_uintK /=.
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
have hmask13u :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 13)) `&`
       W32.of_int 1) =
    W8.to_uint (unpack_vk_group_byte vkp poly group 13) %% 2.
+ rewrite (W32.to_uint_and_mod 1) 1:/# W4u8.to_uint_zeroextu32.
   trivial.
have hm13 := modz_cmp (W8.to_uint (unpack_vk_group_byte vkp poly group 13)) 2 _.
+ smt().
have hmask13lt :
    W32.to_uint
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 13)) `&`
       W32.of_int 1) < 2 ^ (32 - 14).
+ rewrite hmask13u.
   smt().
rewrite W32.to_uint_shl 1:/# /=.
rewrite !W4u8.to_uint_zeroextu32.
have hb11 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 11).
have hb12 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 12).
have hb13 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 13).
rewrite (modz_small
  (W8.to_uint (unpack_vk_group_byte vkp poly group 12) * 64)
  W32.modulus).
+ smt().
rewrite (modz_small
  (W32.to_uint
    ((zeroextu32 (unpack_vk_group_byte vkp poly group 13)) `&`
     W32.of_int 1) * 16384)
  W32.modulus).
+ have hmask13cmp :=
    W32.to_uint_cmp
      ((zeroextu32 (unpack_vk_group_byte vkp poly group 13)) `&`
       W32.of_int 1).
  smt().
smt().
qed.

lemma unpack_vk_lane_word_bound7 vkp poly group :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  W32.to_uint (unpack_vk_lane_word vkp poly group 7) < 32768.
proof.
move=> hpoly hgroup.
rewrite /unpack_vk_lane_word ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/#.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
   rewrite W32.andwE /(`>>`) /(`<<`) W32.shlwE.
   rewrite !W8.of_uintK /= !W4u8.zeroextu32_bit.
   rewrite W32.get_to_uint W32.of_uintK /=.
   rewrite (modz_small 127 W32.modulus) 1:/#.
   smt().
rewrite (W32.to_uint_and_mod 7) 1:/#.
rewrite W32.shr_div W8.of_uintK /=.
rewrite /(`<<`) W32.to_uint_shl 1:/# W8.of_uintK /=.
rewrite W4u8.to_uint_zeroextu32.
have hb13 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 13).
have hb14 := W8.to_uint_cmp (unpack_vk_group_byte vkp poly group 14).
have hm13 := modz_cmp (W8.to_uint (unpack_vk_group_byte vkp poly group 13) %/ 2) 128 _.
+ smt().
rewrite (modz_small
  (W8.to_uint (unpack_vk_group_byte vkp poly group 13) %/ 2) 128).
+ smt().
smt().
qed.

lemma unpack_vk_lane_word_bound vkp poly group lane :
  0 <= poly < mode2_rows =>
  0 <= group < mode2_groups_per_poly =>
  0 <= lane < mode2_coeffs_per_group =>
  W32.to_uint (unpack_vk_lane_word vkp poly group lane) < 32768.
proof.
move=> hpoly hgroup hlane.
have hcases :
    lane = 0 \/ lane = 1 \/ lane = 2 \/ lane = 3 \/
    lane = 4 \/ lane = 5 \/ lane = 6 \/ lane = 7 by smt().
elim hcases => [->|hcases].
+ exact (unpack_vk_lane_word_bound0 vkp poly group hpoly hgroup).
elim hcases => [->|hcases].
+ exact (unpack_vk_lane_word_bound1 vkp poly group hpoly hgroup).
elim hcases => [->|hcases].
+ exact (unpack_vk_lane_word_bound2 vkp poly group hpoly hgroup).
elim hcases => [->|hcases].
+ exact (unpack_vk_lane_word_bound3 vkp poly group hpoly hgroup).
elim hcases => [->|hcases].
+ exact (unpack_vk_lane_word_bound4 vkp poly group hpoly hgroup).
elim hcases => [->|hcases].
+ exact (unpack_vk_lane_word_bound5 vkp poly group hpoly hgroup).
elim hcases => [->|hcases].
+ exact (unpack_vk_lane_word_bound6 vkp poly group hpoly hgroup).
move: hcases => ->.
exact (unpack_vk_lane_word_bound7 vkp poly group hpoly hgroup).
qed.

lemma unpack_vk_coeff_word_bound vkp i :
  0 <= i < mode2_active_words =>
  W32.to_uint (unpack_vk_coeff_word vkp i) < 32768.
proof.
move=> hi.
pose poly := i %/ mode2_coeffs_per_poly.
pose row_idx := i %% mode2_coeffs_per_poly.
pose group := row_idx %/ mode2_coeffs_per_group.
pose lane := row_idx %% mode2_coeffs_per_group.
have hpoly : 0 <= poly < mode2_rows.
+ rewrite /poly /mode2_coeffs_per_poly /mode2_rows /mode2_active_words in hi.
   smt(@IntDiv).
have hrow : 0 <= row_idx < mode2_coeffs_per_poly.
+ rewrite /row_idx /mode2_coeffs_per_poly.
   exact (modz_cmp i mode2_coeffs_per_poly _).
have hgroup : 0 <= group < mode2_groups_per_poly.
+ rewrite /group /row_idx /mode2_coeffs_per_group
           /mode2_groups_per_poly /mode2_coeffs_per_poly in hrow.
   smt(@IntDiv).
have hlane : 0 <= lane < mode2_coeffs_per_group.
+ rewrite /lane /group /row_idx /mode2_coeffs_per_group.
   exact (modz_cmp row_idx mode2_coeffs_per_group _).
have hdecomp :
    i = mode2_coeffs_per_poly * poly +
        mode2_coeffs_per_group * group + lane.
+ have hpolydiv := divz_eq i mode2_coeffs_per_poly.
  have hgroupdiv := divz_eq row_idx mode2_coeffs_per_group.
  rewrite /poly /row_idx /group /lane.
  rewrite /row_idx in hgroupdiv.
  smt().
rewrite hdecomp.
rewrite (unpack_vk_coeff_word_group vkp poly group lane hpoly hgroup hlane).
exact (unpack_vk_lane_word_bound vkp poly group lane hpoly hgroup hlane).
qed.

lemma unpack_vk_coeff_prefix_bound_all vkp :
  unpack_vk_coeff_prefix_bound vkp mode2_active_words.
proof.
rewrite /unpack_vk_coeff_prefix_bound => i hi.
exact (unpack_vk_coeff_word_bound vkp i hi).
qed.

lemma unpack_vk_m23_coeffs_mode2_actual_bound
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t) :
  hoare [Verify.__unpack_vk_m23_coeffs :
    bp = bp0 /\ vkp = vkp0 /\ count = W64.of_int mode2_rows
    ==>
    decoded_coeff_prefix res vkp0 mode2_active_words /\
    coeff_tail_frame bp0 res mode2_active_words /\
    forall i, 0 <= i < mode2_active_words =>
      W32.to_uint (BArray8192.get32 res i) < 32768].
proof.
conseq (unpack_vk_m23_coeffs_mode2_actual_exact bp0 vkp0).
+ auto.
move=> &m _ result [hprefix htail].
split; first exact hprefix.
split; first exact htail.
move=> i hi.
rewrite hprefix 1:hi.
exact (unpack_vk_coeff_word_bound vkp0 i hi).
qed.

end VerifyUnpackVkM23BoundsPostFreeze.
