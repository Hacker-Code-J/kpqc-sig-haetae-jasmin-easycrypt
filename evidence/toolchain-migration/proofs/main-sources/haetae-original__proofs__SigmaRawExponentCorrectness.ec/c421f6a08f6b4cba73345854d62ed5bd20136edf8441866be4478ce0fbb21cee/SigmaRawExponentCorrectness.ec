require import AllCore IntDiv Real StdOrder StdRing.
from Jasmin require import JModel_x86.
require import SigmaSpec SigmaCorrectness SigmaRoundingCorrectness SigmaExpInputBounds
  GaussianAccumulatorCorrectness CDTCorrectness SigmaRawSpec.
import IntOrder RField RealOrder.

lemma sr_noise_bounds (p : BArray26.t) : 0 <= sr_noise p < sr_noise_modulus.
proof.
  have hlo := sigma_le6_bound p 17.
  have hhi := sigma_le3_bound p 23.
  rewrite /sr_noise /sr_scale /sr_noise_modulus; smt().
qed.

lemma sr_cdt_bounds (p : BArray26.t) : 0 <= sr_cdt p <= 166.
proof. rewrite /sr_cdt; apply cdt_count_range; trivial. qed.

lemma sr_cdt_word_uint (p : BArray26.t) :
  W64.to_uint (W64.of_int (sr_cdt p)) = sr_cdt p.
proof.
  have hc := sr_cdt_bounds p.
  rewrite W64.to_uint_small; smt().
qed.

lemma sr_numerator_nonnegative (p : BArray26.t) : 0 <= sr_numerator p.
proof.
  have hn := sr_noise_bounds p.
  have hc := sr_cdt_bounds p.
  rewrite /sr_numerator /sr_noise_modulus; smt().
qed.

lemma sr_exponent_nonnegative (p : BArray26.t) : 0%r <= sr_exponent p.
proof.
  have hn := sr_numerator_nonnegative p.
  rewrite /sr_exponent; smt().
qed.

lemma sr_merge_word_exact (low difference : W64.t) :
  W64.to_uint low < 281474976710656 => W64.to_uint difference < 349241376 =>
  W64.to_uint ((((difference `<<<` 20) `|` (low `>>>` 28)) + W64.one) `>>>` 1) =
    (W64.to_uint difference * 1048576 + W64.to_uint low %/ 268435456 + 1) %/ 2.
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
  by rewrite W64.to_uint_shr //= hinc W64.to_uint_shr //=.
qed.

lemma sr_merge_limb_div low high base :
  (high - base) * 1048576 + low %/ 268435456 =
    (low + 281474976710656 * high - base * 281474976710656) %/ 268435456.
proof.
  have -> : low + 281474976710656 * high - base * 281474976710656 =
    ((high - base) * 1048576) * 268435456 + low by ring.
  by rewrite divzMDl 1://.
qed.

lemma sr_square_argument_limb_exact (lo hi x : W64.t) :
  W64.to_uint x <= 166 => W64.to_uint lo < 281474976710656 =>
  W64.to_uint x * 16777216 <= W64.to_uint hi < (W64.to_uint x + 1) * 16777216 =>
  W64.to_uint (sigma_square_exp_argument (square_word lo hi) x) =
    (((gauss_limb_value (square_word lo hi).`1 (square_word lo hi).`2 -
       W64.to_uint x * W64.to_uint x * 295147905179352825856) %/ 268435456 + 1) %/ 2).
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
  have hdiff : W64.to_uint ((square_word lo hi).`2 - ((x * x) `<<<` 20)) < 349241376 by
    rewrite hsub; smt().
  have [hslo0 hslo] := gauss_square_low_bound lo hi.
  rewrite /sigma_square_exp_argument (sr_merge_word_exact _ _ hslo hdiff) hsub.
  rewrite sr_merge_limb_div /gauss_limb_value.
  have -> : W64.to_uint x * W64.to_uint x * 295147905179352825856 =
    (W64.to_uint x * W64.to_uint x * 1048576) * 281474976710656 by ring.
  trivial.
qed.

lemma sr_round_div_half n d : 0 < d =>
  (n %/ d + 1) %/ 2 = (n + d) %/ (2 * d).
proof.
  move=> hd.
  have hplus : (n + d) %/ d = n %/ d + 1.
  + have -> : n + d = 1 * d + n by ring.
    rewrite divzMDl 1:/#; ring.
  rewrite -hplus -(divz_mulp (n + d) d 2 hd _) 1://.
  have -> : d * 2 = 2 * d by ring.
  trivial.
qed.

lemma sr_exponent_division n :
  ((n %/ 75557863725914323419136) %/ 268435456 + 1) %/ 2 =
    (n + 20282409603651670423947251286016) %/ 40564819207303340847894502572032.
proof.
  rewrite -(divz_mulp n 75557863725914323419136 268435456 _ _) 1..2:// /=.
  by rewrite sr_round_div_half 1:// /=.
qed.

lemma sr_candidate_decoding (p : BArray26.t) :
  W64.to_uint (le6_word p 17) + 281474976710656 *
    W64.to_uint (le3_word p 23 `|` (W64.of_int (sr_cdt p) `<<<` 24)) = sr_candidate p.
proof.
  have hnoise := sigma_le3_bound p 23.
  have hcdt := sr_cdt_bounds p.
  have hx := sr_cdt_word_uint p.
  rewrite sigma_high_uint 1:/# 1:/# hx /sr_candidate /sr_noise /sr_scale /sr_noise_modulus.
  ring.
qed.

lemma sr_square_cancellation (p : BArray26.t) :
  (sr_candidate p * sr_candidate p) %/ 75557863725914323419136 -
      sr_cdt p * sr_cdt p * 295147905179352825856 =
    sr_numerator p %/ 75557863725914323419136.
proof.
  have he : sr_candidate p * sr_candidate p =
    (sr_cdt p * sr_cdt p * 295147905179352825856) * 75557863725914323419136 +
      sr_numerator p by
    rewrite /sr_candidate /sr_numerator /sr_noise_modulus; ring.
  by rewrite he divzMDl 1:// /=; ring.
qed.

lemma sr_rounded_exponent_error (n : int) :
  `|((n + 20282409603651670423947251286016) %/ 40564819207303340847894502572032)%r /
      sr_scale%r - n%r / 11417981541647679048466287755595961091061972992%r| <=
    1%r / (2%r * sr_scale%r).
proof.
  have he := divz_eq (n + 20282409603651670423947251286016) 40564819207303340847894502572032.
  have hr := modz_cmp (n + 20282409603651670423947251286016) 40564819207303340847894502572032.
  rewrite /sr_scale ler_norml; smt().
qed.

require import SigmaSquareExact.

lemma sr_high_word_bounds (p : BArray26.t) :
  sr_cdt p * 16777216 <=
    W64.to_uint (le3_word p 23 `|` (W64.of_int (sr_cdt p) `<<<` 24)) <
      (sr_cdt p + 1) * 16777216 /\
  W64.to_uint (le3_word p 23 `|` (W64.of_int (sr_cdt p) `<<<` 24)) < 2801795072.
proof.
  have hnoise := sigma_le3_bound p 23.
  have hcdt := sr_cdt_bounds p.
  have hx := sr_cdt_word_uint p.
  rewrite sigma_high_uint 1:/# 1:/# hx; smt().
qed.

lemma sigma_raw_exponent_exact (p : BArray26.t) :
  W64.to_uint (sigma_exp_argument p) = (sr_numerator p + 2^104) %/ 2^105.
proof.
  pose high := le3_word p 23 `|` (W64.of_int (sr_cdt p) `<<<` 24).
  have [hlow0 hlow] := sigma_le6_bound p 17.
  have hcount := sr_cdt_bounds p.
  have [hwindow hhigh] := sr_high_word_bounds p.
  have hxuint := sr_cdt_word_uint p.
  have hx : W64.to_uint (W64.of_int (sr_cdt p)) <= 166 by rewrite hxuint; smt().
  have hwindowword : W64.to_uint (W64.of_int (sr_cdt p)) * 16777216 <=
      W64.to_uint high < (W64.to_uint (W64.of_int (sr_cdt p)) + 1) * 16777216 by
    rewrite hxuint; exact hwindow.
  have hdecode : W64.to_uint (le6_word p 17) + 281474976710656 * W64.to_uint high =
      sr_candidate p by exact (sr_candidate_decoding p).
  have hsquare : gauss_limb_value (square_word (le6_word p 17) high).`1
      (square_word (le6_word p 17) high).`2 =
      (sr_candidate p * sr_candidate p) %/ 75557863725914323419136.
  + rewrite /gauss_limb_value -hdecode.
    exact (sigma_square_word_exact (le6_word p 17) high hlow hhigh).
  rewrite /sigma_exp_argument -/(sr_cdt p) /sigma_exp_from_cdt -/high.
  rewrite (sr_square_argument_limb_exact (le6_word p 17) high
    (W64.of_int (sr_cdt p)) hx hlow hwindowword) hxuint hsquare.
  by rewrite sr_square_cancellation sr_exponent_division /=.
qed.

lemma sigma_raw_exponent_error (p : BArray26.t) :
  `|(W64.to_uint (sigma_exp_argument p))%r / sr_scale%r - sr_exponent p| <=
    1%r / (2%r * sr_scale%r).
proof.
  rewrite sigma_raw_exponent_exact /sr_exponent.
  exact (sr_rounded_exponent_error (sr_numerator p)).
qed.
