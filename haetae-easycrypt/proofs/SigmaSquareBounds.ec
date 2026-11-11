require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SigmaSpec SigmaCorrectness SigmaRoundingCorrectness CDTCorrectness.

lemma sigma_shr28_bound (w : W64.t) :
  0 <= W64.to_uint (w `>>>` 28) < 68719476736.
proof.
  rewrite W64.to_uint_shr //=.
  apply divz_cmp; first trivial.
  exact: W64.to_uint_cmp.
qed.

lemma sigma_shr48_bound (w : W64.t) :
  0 <= W64.to_uint (w `>>>` 48) < 65536.
proof.
  rewrite W64.to_uint_shr //=.
  apply divz_cmp; first trivial.
  exact: W64.to_uint_cmp.
qed.

lemma sigma_square_coarse_high (a b c : W64.t) :
  0 <= W64.to_uint (((a `>>>` 28) + (b `>>>` 28)) + (c `>>>` 48))
    < 274877906944.
proof.
  have ha := sigma_shr28_bound a.
  have hb := sigma_shr28_bound b.
  have hc := sigma_shr48_bound c.
  have hab : W64.to_uint ((a `>>>` 28) + (b `>>>` 28)) =
      W64.to_uint (a `>>>` 28) + W64.to_uint (b `>>>` 28).
  + rewrite W64.to_uintD modz_small; smt().
  rewrite W64.to_uintD hab modz_small; smt().
qed.

(* Only a coarse bound on the actual truncated square is asserted here.
   No equality with an ideal real-valued square is assumed. *)
lemma sigma_square_high_bound (x0 x1 : W64.t) :
  W64.to_uint x1 < 4294967296 =>
  0 <= W64.to_uint (square_word x0 x1).`2 < 274877906944.
proof.
  move=> hx.
  have /= hr := W64.to_uint_cmp x1.
  have hprod : W64.to_uint x1 * W64.to_uint x1 < 18446744073709551616.
  + smt().
  have hhi : W64.mulhi x1 x1 = W64.zero.
  + rewrite W64.to_uint_eq W64.to_uint0 W64.mulhi0 //.
  rewrite /square_word W64.muluE /= hhi (W64.shlMP 0 36) //=.
  apply sigma_square_coarse_high.
qed.

lemma sigma76_square_high_bound (p : BArray26.t) :
  0 <= W64.to_uint (sigma76_spec p).`3 < 274877906944.
proof.
  have [h0 [h1 h2]] := sigma76_decoded_bounds p.
  pose count := cdt_count (cdt_lo_input p) (cdt_hi_input p) 166.
  have hx : W64.to_uint (W64.of_int count) = count.
  + rewrite W64.of_uintK modz_small; smt().
  have hy : W64.to_uint (le3_word p 23 `|` (W64.of_int count `<<<` 24)) < 4294967296.
  + rewrite sigma_high_uint 1:/# 1:/# hx; smt().
  rewrite /sigma76_spec /sigma_from_cdt /= -/count.
  exact (sigma_square_high_bound _ _ hy).
qed.

lemma sigma76_regs_square_high_bound (p : BArray26.t) :
  phoare [SamplerTarget.M.__sample_gauss_sigma76_regs : randp = p ==>
    0 <= W64.to_uint res.`3 < 274877906944] = 1%r.
proof.
  conseq sigma76_regs_lossless (sigma76_regs_correct p) => />.
  smt(sigma76_square_high_bound).
qed.
