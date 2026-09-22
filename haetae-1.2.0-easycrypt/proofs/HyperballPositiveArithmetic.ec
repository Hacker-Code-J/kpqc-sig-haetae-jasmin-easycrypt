require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec HyperballFixedPointCorrectness.
require import HyperballWordEvaluation HyperballSafeSpec.

(* These are unsigned integer interpretations of the existing word
   operations. In particular, subtraction requires a radix-sized margin;
   a merely nonnegative mathematical difference does not rule out a
   wrapped high word in the non-normalized result. *)

lemma hpa_value_nonnegative (x : hb_fp) : 0 <= hb_value x.
proof.
  have hlo := W64.to_uint_cmp x.`1.
  have hhi := W64.to_uint_cmp x.`2.
  rewrite /hb_value; smt().
qed.

lemma hpa_norm_int (a b : int) :
  0 <= a < hbs_radix =>
  hb_norm (W64.of_int a, W64.of_int b) = (W64.of_int a, W64.of_int b).
proof.
  rewrite /hbs_radix => ha.
  rewrite hwe_norm (modz_small a 18446744073709551616) 1:/#.
  by rewrite (modz_small a 281474976710656) 1:/#
    (divz_small a 281474976710656) 1:/# /=.
qed.

lemma hpa_norm_id (x : hb_fp) : hbs_canonical x => hb_norm x = x.
proof.
  case: x => a b; rewrite /hbs_canonical /= => ha.
  have ha0 := W64.to_uint_cmp a.
  have h := hpa_norm_int (W64.to_uint a) (W64.to_uint b) _; first smt().
  by move: h; rewrite !W64.to_uintK.
qed.

lemma hpa_norm_canonical (x : hb_fp) : hbs_canonical (hb_norm x).
proof.
  have [hlo hhi] := hb_norm_low_bound x.
  exact hhi.
qed.

lemma hpa_cneg_zero (x : hb_fp) : hbs_canonical x => hb_cneg x W64.zero = x.
proof.
  move=> hx; rewrite /hb_cneg /=; exact (hpa_norm_id x hx).
qed.

lemma hpa_cneg_canonical (x : hb_fp) :
  hbs_canonical x =>
  hb_cneg x W64.one =
    (W64.of_int (if W64.to_uint x.`1 = 0 then 0 else hbs_radix-W64.to_uint x.`1),
     W64.of_int (-W64.to_uint x.`2-(if W64.to_uint x.`1 = 0 then 0 else 1))).
proof.
  case: x => a b; rewrite /hbs_canonical /hbs_radix /= => ha.
  have ha0 := W64.to_uint_cmp a.
  have h := hwe_cneg1 (W64.to_uint a) (W64.to_uint b).
  rewrite !W64.to_uintK in h.
  rewrite (modz_small (W64.to_uint a) 18446744073709551616) 1:/#
    (modz_small (W64.to_uint a) 281474976710656) 1:/# in h.
  have he : W64.to_uint a+281474976710656-2*W64.to_uint a =
      281474976710656-W64.to_uint a by ring.
  move: h; rewrite he => h.
  case (W64.to_uint a = 0) => hz.
  + by move: h; rewrite hz hwe_norm /=.
  + have hn : 0 <= 281474976710656-W64.to_uint a < hbs_radix
      by rewrite /hbs_radix; smt().
    by move: h; rewrite (hpa_norm_int _ _ hn) /=.
qed.

lemma hpa_sub_words (x y : hb_fp) :
  hbs_canonical y =>
  hb_sub x y =
    (W64.of_int (W64.to_uint x.`1+
       (if W64.to_uint y.`1 = 0 then 0 else hbs_radix-W64.to_uint y.`1)),
     W64.of_int (W64.to_uint x.`2-W64.to_uint y.`2-
       (if W64.to_uint y.`1 = 0 then 0 else 1))).
proof.
  move=> hy; rewrite /hb_sub (hpa_cneg_canonical y hy) /=.
  rewrite -{1}(W64.to_uintK x.`1) -{1}(W64.to_uintK x.`2) !hwe_add.
  have -> : W64.to_uint x.`2+(-W64.to_uint y.`2-
      (if W64.to_uint y.`1=0 then 0 else 1)) =
    W64.to_uint x.`2-W64.to_uint y.`2-
      (if W64.to_uint y.`1=0 then 0 else 1) by ring.
  trivial.
qed.

lemma hpa_sub_exact (x y : hb_fp) :
  hbs_canonical x => hbs_canonical y =>
  hb_value x <= hbs_operand_cap => hb_value y <= hbs_operand_cap =>
  hbs_radix <= hb_value x-hb_value y =>
  W64.to_uint (hb_sub x y).`1 < 2*hbs_radix /\
  hb_value (hb_sub x y) = hb_value x-hb_value y.
proof.
  move=> hx hy hxcap hycap hdiff.
  have hw := hpa_sub_words x y hy.
  have /= hxl := W64.to_uint_cmp x.`1.
  have /= hxh := W64.to_uint_cmp x.`2.
  have /= hyl := W64.to_uint_cmp y.`1.
  have /= hyh := W64.to_uint_cmp y.`2.
  rewrite /hbs_canonical /hbs_radix in hx.
  rewrite /hbs_canonical /hbs_radix in hy.
  rewrite /hb_value /hbs_operand_cap in hxcap.
  rewrite /hb_value /hbs_operand_cap in hycap.
  rewrite /hb_value /hbs_radix in hdiff.
  case (W64.to_uint y.`1=0) => hz.
  + move: hw; rewrite hz /= => hw.
    have hh : 0 <= W64.to_uint x.`2-W64.to_uint y.`2 < 18446744073709551616
      by smt().
    rewrite hw /hb_value /hbs_radix /= !hwe_uint.
    rewrite (modz_small (W64.to_uint x.`2-W64.to_uint y.`2) 18446744073709551616) 1:hh.
    smt().
  + move: hw; rewrite hz /hbs_radix /= => hw.
    have hl : 0 <= W64.to_uint x.`1+(281474976710656-W64.to_uint y.`1) <
        18446744073709551616 by smt().
    have hh : 0 <= W64.to_uint x.`2-W64.to_uint y.`2-1 < 18446744073709551616
      by smt().
    rewrite hw /hb_value /hbs_radix /= !hwe_uint.
    rewrite (modz_small _ 18446744073709551616 hl)
      (modz_small (W64.to_uint x.`2-W64.to_uint y.`2-1) 18446744073709551616 hh).
    smt().
qed.

lemma hpa_threehalves_words (u : hb_fp) :
  hbs_canonical u =>
  hb_threehalves_minus u =
    (W64.of_int (if W64.to_uint u.`1=0 then 0 else hbs_radix-W64.to_uint u.`1),
     W64.of_int (402653184-W64.to_uint u.`2-
       (if W64.to_uint u.`1=0 then 0 else 1))).
proof.
  move=> hu.
  have /= hlo := W64.to_uint_cmp u.`1.
  have hul : W64.to_uint u.`1 < hbs_radix by exact hu.
  have hn : 0 <= (if W64.to_uint u.`1=0 then 0 else hbs_radix-W64.to_uint u.`1)
      < hbs_radix by move: hul; rewrite /hbs_radix; smt().
  rewrite /hb_threehalves_minus (hpa_cneg_canonical u hu) /=
    hwe_shl 1:// /= (hpa_norm_int _ _ hn).
  have -> : -W64.to_uint u.`2-(if W64.to_uint u.`1=0 then 0 else 1)+402653184 =
      402653184-W64.to_uint u.`2-(if W64.to_uint u.`1=0 then 0 else 1) by ring.
  trivial.
qed.

lemma hpa_threehalves_exact (u : hb_fp) :
  hbs_canonical u => hb_value u <= 3*hbs_q %/ 2 =>
  hbs_canonical (hb_threehalves_minus u) /\
  hb_value (hb_threehalves_minus u) = 3*hbs_q %/ 2-hb_value u.
proof.
  move=> hu hcap.
  have hw := hpa_threehalves_words u hu.
  have /= hlo := W64.to_uint_cmp u.`1.
  have /= hhi := W64.to_uint_cmp u.`2.
  rewrite /hbs_canonical /hbs_radix in hu.
  rewrite /hb_value /hbs_q /= in hcap.
  case (W64.to_uint u.`1=0) => hz.
  + move: hw; rewrite hz /= => hw.
    have hh : 0 <= 402653184-W64.to_uint u.`2 < 18446744073709551616 by smt().
    rewrite hw /hbs_canonical /hbs_radix /hb_value /hbs_q /= hwe_uint
      (modz_small _ 18446744073709551616 hh).
    smt().
  + move: hw; rewrite hz /hbs_radix /= => hw.
    have hl : 0 <= 281474976710656-W64.to_uint u.`1 < 18446744073709551616
      by smt().
    have hh : 0 <= 402653184-W64.to_uint u.`2-1 < 18446744073709551616 by smt().
    rewrite hw /hbs_canonical /hbs_radix /hb_value /hbs_q /= !hwe_uint
      (modz_small _ 18446744073709551616 hl)
      (modz_small _ 18446744073709551616 hh).
    smt().
qed.

lemma hpa_threehalves_positive (u : hb_fp) :
  hbs_canonical u => hb_value u <= 5*hbs_q %/ 4 =>
  hbs_canonical (hb_threehalves_minus u) /\
  hbs_q %/ 4 <= hb_value (hb_threehalves_minus u) <= 3*hbs_q %/ 2 /\
  0 < W64.to_uint (hb_threehalves_minus u).`2.
proof.
  move=> hu hcap.
  have hcap' : hb_value u <= 3*hbs_q %/ 2 by move: hcap; rewrite /hbs_q /=; smt().
  have [hc he] := hpa_threehalves_exact u hu hcap'.
  have hn := hpa_value_nonnegative u.
  have /= hh := W64.to_uint_cmp (hb_threehalves_minus u).`2.
  move: hc he; rewrite /hbs_canonical /hbs_radix /hb_value /hbs_q /= => hc he.
  rewrite /hbs_canonical /hbs_radix /hb_value /hbs_q /=.
  rewrite /hb_value /hbs_q /= in hcap.
  rewrite /hb_value in hn.
  smt().
qed.

lemma hpa_mul_canonical (x y : hb_fp) : hbs_canonical (hb_mul x y).
proof.
  rewrite /hb_mul /=; exact (hpa_norm_canonical _).
qed.

lemma hpa_positive_sign (t : hb_fp) :
  hb_value t <= 3*hbs_q %/ 2 =>
  (t.`2 `>>>` 63) `&` W64.one = W64.zero.
proof.
  move=> hcap.
  have /= hlo := W64.to_uint_cmp t.`1.
  have /= hhi := W64.to_uint_cmp t.`2.
  rewrite /hb_value /hbs_q /= in hcap.
  have hf : 0 <= W64.to_uint t.`2 < 9223372036854775808 by smt().
  by rewrite hwe_shr_word 1:// /=
    (divz_small (W64.to_uint t.`2) 9223372036854775808) 1:/# /=.
qed.

lemma hpa_signed_mul_positive (y t : hb_fp) :
  hbs_canonical t => hb_value t <= 3*hbs_q %/ 2 =>
  hb_signed_mul y t = hb_mul t y.
proof.
  move=> ht hcap.
  by rewrite /hb_signed_mul (hpa_positive_sign t hcap) /=
    (hpa_cneg_zero t ht) (hpa_cneg_zero _ (hpa_mul_canonical t y)).
qed.
