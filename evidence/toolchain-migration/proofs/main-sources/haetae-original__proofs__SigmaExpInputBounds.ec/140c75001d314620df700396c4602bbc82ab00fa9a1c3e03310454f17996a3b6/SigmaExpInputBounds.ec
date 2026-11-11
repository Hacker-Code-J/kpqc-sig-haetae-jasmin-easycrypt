require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import FixedPointSpec SigmaSpec SigmaCorrectness SigmaRoundingCorrectness SigmaSquareBounds
  HyperballGaussianBounds GaussianAccumulatorCorrectness CDTCorrectness.

op [opaque] sigma_square_exp_argument (square : W64.t * W64.t) (x : W64.t) : W64.t =
  ((((square.`2 - ((x * x) `<<<` 20)) `<<<` 20) `|`
     (square.`1 `>>>` 28)) + W64.one) `>>>` 1.

op [opaque] sigma_exp_from_cdt (p : BArray26.t) (x : W64.t) : W64.t =
  sigma_square_exp_argument
    (square_word (le6_word p 17) (le3_word p 23 `|` (x `<<<` 24))) x.

op [opaque] sigma_exp_argument (p : BArray26.t) : W64.t =
  sigma_exp_from_cdt p
    (W64.of_int (cdt_count (cdt_lo_input p) (cdt_hi_input p) 166)).

lemma sigma_exp_high_parts (cross product carry : W64.t) :
  W64.to_uint cross < 8589934592 =>
  W64.to_uint product < 9223372036854775808 =>
  W64.to_uint product %/ 268435456 <=
    W64.to_uint (((cross `>>>` 28) + (product `>>>` 28)) + (carry `>>>` 48)) <
    W64.to_uint product %/ 268435456 + 65568.
proof.
  move=> hc hp.
  have /= hc0 := W64.to_uint_cmp cross.
  have /= hp0 := W64.to_uint_cmp product.
  have hc28 : 0 <= W64.to_uint (cross `>>>` 28) < 32.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have hp28 : 0 <= W64.to_uint (product `>>>` 28) < 34359738368.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have hcarry := sigma_shr48_bound carry.
  have hadd : W64.to_uint ((cross `>>>` 28) + (product `>>>` 28)) =
    W64.to_uint (cross `>>>` 28) + W64.to_uint (product `>>>` 28).
  + rewrite W64.to_uintD_small; smt().
  rewrite W64.to_uintD_small 1:/# hadd.
  have hpval : W64.to_uint (product `>>>` 28) = W64.to_uint product %/ 268435456 by
    rewrite W64.to_uint_shr //=.
  smt().
qed.

lemma sigma_exp_square_interval a x :
  0 <= x <= 166 => x * 16777216 <= a < (x + 1) * 16777216 =>
  x * x * 281474976710656 <= a * a < (x + 1) * (x + 1) * 281474976710656.
proof. smt(). qed.

lemma sigma_exp_high_interval_join lower upper middle result :
  lower <= middle < upper => middle <= result < middle + 65568 =>
  lower <= result < upper + 65568.
proof. smt(). qed.

lemma sigma_exp_square_high_window (lo hi : W64.t) (x : int) :
  0 <= x <= 166 => W64.to_uint lo < 281474976710656 =>
  x * 16777216 <= W64.to_uint hi < (x + 1) * 16777216 =>
  x * x * 1048576 <= W64.to_uint (square_word lo hi).`2 <
    (x + 1) * (x + 1) * 1048576 + 65568.
proof.
  move=> hx hlo hhi.
  have /= h0 := W64.to_uint_cmp hi.
  have hp : W64.to_uint hi * W64.to_uint hi < 9223372036854775808 by smt().
  have hprod : W64.to_uint (hi * hi) = W64.to_uint hi * W64.to_uint hi by
    rewrite W64.to_uintM_small; smt().
  have htop : W64.mulhi hi hi = W64.zero by
    rewrite W64.to_uint_eq W64.to_uint0 W64.mulhi0; smt().
  have hcross := hb_mul48_high_bound lo hi hlo _; first smt().
  have hcross2 : W64.to_uint ((mul48_word lo hi).`2 `<<<` 1) < 8589934592 by
    rewrite W64.to_uint_shl //= modz_small; smt().
  have hsq := sigma_exp_square_interval (W64.to_uint hi) x hx hhi.
  have hquot : x * x * 1048576 <=
      W64.to_uint (hi * hi) %/ 268435456 < (x + 1) * (x + 1) * 1048576.
  + rewrite hprod lez_divRL 1:// ltz_divLR 1://.
    smt().
  have hparts : W64.to_uint (hi * hi) %/ 268435456 <=
      W64.to_uint (square_word lo hi).`2 < W64.to_uint (hi * hi) %/ 268435456 + 65568.
  + rewrite /square_word W64.muluE /= htop (W64.shlMP 0 36) //=.
    apply sigma_exp_high_parts; first exact hcross2.
    by rewrite hprod.
  exact (sigma_exp_high_interval_join _ _ _ _ hquot hparts).
qed.

lemma sigma_exp_shift_disjoint (low high : W64.t) :
  W64.to_uint low < 1048576 => low `&` (high `<<<` 20) = W64.zero.
proof.
  move=> hl.
  have hm : low `&` W64.masklsb 20 = low by apply (sigma_mask_id low 20); trivial.
  have hs : (high `<<<` 20) `&` W64.masklsb 20 = W64.zero.
  + rewrite W64.shlw_andmask 1:// /= W64.andw0.
    by rewrite W64.shlMP.
  by rewrite -{1}hm -W64.andwA (W64.andwC (W64.masklsb 20)) hs W64.andw0.
qed.

lemma sigma_exp_merge_bound (low difference : W64.t) :
  W64.to_uint low < 281474976710656 => W64.to_uint difference < 349241376 =>
  W64.to_uint ((((difference `<<<` 20) `|` (low `>>>` 28)) + W64.one) `>>>` 1)
    <= 183103063064576.
proof.
  move=> hl hd.
  have /= hl0 := W64.to_uint_cmp low.
  have /= hd0 := W64.to_uint_cmp difference.
  have hlow : 0 <= W64.to_uint (low `>>>` 28) < 1048576.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have hshift : W64.to_uint (difference `<<<` 20) = W64.to_uint difference * 1048576 by
    rewrite W64.to_uint_shl //= modz_small; smt().
  have hmerge : W64.to_uint ((difference `<<<` 20) `|` (low `>>>` 28)) =
    W64.to_uint difference * 1048576 + W64.to_uint (low `>>>` 28).
  + rewrite W64.to_uint_orw_disjoint.
    - rewrite W64.andwC; apply sigma_exp_shift_disjoint; smt().
    by rewrite hshift.
  have hinc : W64.to_uint (((difference `<<<` 20) `|` (low `>>>` 28)) + W64.one) =
      W64.to_uint difference * 1048576 + W64.to_uint (low `>>>` 28) + 1 by
    rewrite W64.to_uintD_small 1:/# hmerge W64.to_uint1.
  rewrite W64.to_uint_shr //= hinc.
  have he := divz_eq (W64.to_uint difference * 1048576 + W64.to_uint (low `>>>` 28) + 1) 2.
  have hm := modz_cmp (W64.to_uint difference * 1048576 + W64.to_uint (low `>>>` 28) + 1) 2.
  smt().
qed.

lemma sigma_exp_square_argument_bound (lo hi x : W64.t) :
  W64.to_uint x <= 166 => W64.to_uint lo < 281474976710656 =>
  W64.to_uint x * 16777216 <= W64.to_uint hi < (W64.to_uint x + 1) * 16777216 =>
  W64.to_uint (sigma_square_exp_argument (square_word lo hi) x) <= 183103063064576.
proof.
  move=> hx hlo hhi.
  have /= hx0 := W64.to_uint_cmp x.
  have hxx : 0 <= W64.to_uint x * W64.to_uint x <= 27556 by smt().
  have hbase : W64.to_uint ((x * x) `<<<` 20) =
      W64.to_uint x * W64.to_uint x * 1048576 by
    rewrite W64.to_uint_shl //= W64.to_uintM_small 1:/# modz_small; smt().
  have hsq := sigma_exp_square_high_window lo hi (W64.to_uint x) _ hlo hhi;
    first smt().
  have hsub : W64.to_uint ((square_word lo hi).`2 - ((x * x) `<<<` 20)) =
      W64.to_uint (square_word lo hi).`2 - W64.to_uint x * W64.to_uint x * 1048576.
  + rewrite W64.to_uintB; first by rewrite W64.uleE hbase; smt().
    by rewrite hbase.
  have hdelta : W64.to_uint ((square_word lo hi).`2 - ((x * x) `<<<` 20)) < 349241376.
  + rewrite hsub; smt().
  rewrite /sigma_square_exp_argument.
  apply sigma_exp_merge_bound; last exact hdelta.
  have := gauss_square_low_bound lo hi; smt().
qed.

lemma sigma_exp_from_cdt_bound (p : BArray26.t) (x : W64.t) :
  W64.to_uint x <= 166 => W64.to_uint (sigma_exp_from_cdt p x) <= 183103063064576.
proof.
  move=> hx.
  have hlo := sigma_le6_bound p 17.
  have hnoise := sigma_le3_bound p 23.
  have hy := sigma_high_uint (le3_word p 23) x _ hx; first smt().
  have hinterval : W64.to_uint x * 16777216 <=
      W64.to_uint (le3_word p 23 `|` (x `<<<` 24)) <
      (W64.to_uint x + 1) * 16777216 by rewrite hy; smt().
  rewrite /sigma_exp_from_cdt.
  apply sigma_exp_square_argument_bound; smt().
qed.

lemma sigma_exp_argument_bound (p : BArray26.t) :
  0 <= W64.to_uint (sigma_exp_argument p) <= 183103063064576.
proof.
  have hcount := cdt_count_range (cdt_lo_input p) (cdt_hi_input p) 166 _;
    first trivial.
  have hx : W64.to_uint (W64.of_int (cdt_count (cdt_lo_input p) (cdt_hi_input p) 166)) <= 166 by
    rewrite W64.of_uintK modz_small; smt().
  split.
  + have [hz _] := W64.to_uint_cmp (sigma_exp_argument p); exact hz.
  rewrite /sigma_exp_argument.
  move=> _.
  exact (sigma_exp_from_cdt_bound p _ hx).
qed.

lemma sigma_exp_argument_two_thirds (p : BArray26.t) :
  3 * W64.to_uint (sigma_exp_argument p) <= 2 * 281474976710656.
proof. have := sigma_exp_argument_bound p; smt(). qed.

lemma sigma_exp_argument_canonical (p : BArray26.t) :
  sigma_exp_argument p = sigma_exp_from_cdt p
    (W64.of_int (cdt_count (cdt_lo_input p) (cdt_hi_input p) 166)).
proof. by rewrite /sigma_exp_argument. qed.

(* Exposes the exact expression supplied to approx_exp, without changing the
   existing single-attempt specification or the production implementation. *)
lemma sigma_from_cdt_exp_argument (p : BArray26.t) (x : W64.t) :
  sigma_from_cdt p x =
    let rej = le6_word p 11 in
    let y0 = le6_word p 17 in
    let y1 = le3_word p 23 `|` (x `<<<` 24) in
    let r = (((y0 `>>>` 15) + W64.one) `>>>` 1) + (y1 `<<<` 32) in
    let sq = square_word y0 y1 in
    let e = approx_exp_word (sigma_exp_from_cdt p x) in
    (r, sq.`1, sq.`2,
      (((rej `^` (rej `&` W64.one)) - e) `|>>>` 63) `&`
        (((r `|` (W64.zero - r)) `>>>` 63) `|` rej) `&` W64.one).
proof. by rewrite /sigma_from_cdt /sigma_exp_from_cdt /sigma_square_exp_argument. qed.
