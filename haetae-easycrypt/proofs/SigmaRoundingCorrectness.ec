require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SigmaSpec SigmaCorrectness CDTCorrectness.

lemma sigma_mask_id (w : W64.t) (k : int) :
  0 <= k => W64.to_uint w < 2^k =>
  w `&` W64.of_int (2^k - 1) = w.
proof.
  move=> hk hw.
  rewrite W64.and_mod // modz_small.
  + have := W64.to_uint_cmp w; smt(gt0_pow2).
  exact: W64.to_uintK.
qed.

lemma sigma_high_disjoint (hi x : W64.t) :
  W64.to_uint hi < 16777216 => hi `&` (x `<<<` 24) = W64.zero.
proof.
  move=> hhi.
  have hm : hi `&` W64.masklsb 24 = hi.
  + apply (sigma_mask_id hi 24); trivial.
  have hs : (x `<<<` 24) `&` W64.masklsb 24 = W64.zero.
  + rewrite W64.shlw_andmask 1:// /= W64.andw0.
    by rewrite W64.shlMP.
  by rewrite -{1}hm -W64.andwA (W64.andwC (W64.masklsb 24)) hs W64.andw0.
qed.

lemma sigma_high_uint (hi x : W64.t) :
  W64.to_uint hi < 16777216 => W64.to_uint x <= 166 =>
  W64.to_uint (hi `|` (x `<<<` 24)) =
    W64.to_uint hi + W64.to_uint x * 16777216.
proof.
  move=> hhi hx.
  rewrite W64.to_uint_orw_disjoint 1:sigma_high_disjoint //.
  rewrite W64.to_uint_shl //= modz_small //.
  have /= := W64.to_uint_cmp x; smt().
qed.

lemma sigma_round_word_uint (lo high : W64.t) :
  W64.to_uint lo < 281474976710656 =>
  W64.to_uint high < 2801795072 =>
  W64.to_uint ((((lo `>>>` 15) + W64.one) `>>>` 1) + (high `<<<` 32)) =
    ((W64.to_uint lo %/ 32768 + 1) %/ 2) + W64.to_uint high * 4294967296.
proof.
  move=> hlo hhigh.
  have /= hl := W64.to_uint_cmp lo.
  have /= hh := W64.to_uint_cmp high.
  have hd := divz_eq (W64.to_uint lo) 32768.
  have /= hm := modz_cmp (W64.to_uint lo) 32768.
  have hq : 0 <= W64.to_uint lo %/ 32768 < 8589934592 by smt().
  have hinc : W64.to_uint ((lo `>>>` 15) + W64.one) =
      W64.to_uint lo %/ 32768 + 1.
  + rewrite W64.to_uintD W64.to_uint1 W64.to_uint_shr //= modz_small; smt().
  have hround : W64.to_uint (((lo `>>>` 15) + W64.one) `>>>` 1) =
      (W64.to_uint lo %/ 32768 + 1) %/ 2.
  + by rewrite W64.to_uint_shr //= hinc.
  have hd2 := divz_eq (W64.to_uint lo %/ 32768 + 1) 2.
  have /= hm2 := modz_cmp (W64.to_uint lo %/ 32768 + 1) 2.
  have hround_bound : 0 <= (W64.to_uint lo %/ 32768 + 1) %/ 2 <= 4294967296
    by smt().
  have hshift : W64.to_uint (high `<<<` 32) = W64.to_uint high * 4294967296.
  + rewrite W64.to_uint_shl //= modz_small; smt().
  rewrite W64.to_uintD hround hshift modz_small; smt().
qed.

lemma sigma_or_bound (a b : W64.t) (k : int) :
  0 <= k => W64.to_uint a < 2^k => W64.to_uint b < 2^k =>
  W64.to_uint (a `|` b) < 2^k.
proof.
  move=> hk ha hb.
  have hm : (a `|` b) `&` W64.of_int (2^k - 1) = a `|` b.
  + by rewrite W64.andw_orwDl !sigma_mask_id.
  have he := W64.to_uint_and_mod k (a `|` b) hk.
  rewrite hm in he.
  have hr := modz_cmp (W64.to_uint (a `|` b)) (2^k).
  smt(gt0_pow2).
qed.

lemma sigma_byte_bound (p : BArray26.t) (i : int) :
  0 <= W64.to_uint (byte_word p i) < 256.
proof.
  rewrite /byte_word W8u8.to_uint_zeroextu64.
  exact: W8.to_uint_cmp.
qed.

lemma sigma_byte_shift_bound (p : BArray26.t) (i k : int) :
  0 <= k => W64.to_uint (byte_word p i `<<<` k) < 256 * 2^k.
proof.
  move=> hk.
  rewrite W64.to_uint_shl //.
  have hb := sigma_byte_bound p i.
  have hp := gt0_pow2 k.
  have hl := le_modz (W64.to_uint (byte_word p i) * 2^k) W64.modulus.
  smt().
qed.

lemma sigma_le3_bound (p : BArray26.t) (i : int) :
  0 <= W64.to_uint (le3_word p i) < 16777216.
proof.
  have h0 := sigma_byte_bound p i.
  have /= h1 := sigma_byte_shift_bound p (i + 1) 8 _; first trivial.
  have /= h2 := sigma_byte_shift_bound p (i + 2) 16 _; first trivial.
  have /= h01 := sigma_or_bound (byte_word p i) (byte_word p (i + 1) `<<<` 8) 24.
  have /= h012 := sigma_or_bound
    (byte_word p i `|` (byte_word p (i + 1) `<<<` 8))
    (byte_word p (i + 2) `<<<` 16) 24.
  have hr := W64.to_uint_cmp (le3_word p i).
  rewrite /le3_word in hr.
  rewrite /le3_word; smt().
qed.

lemma sigma_le6_bound (p : BArray26.t) (i : int) :
  0 <= W64.to_uint (le6_word p i) < 281474976710656.
proof.
  have h0 := sigma_le3_bound p i.
  have /= h3 := sigma_byte_shift_bound p (i + 3) 24 _; first trivial.
  have /= h4 := sigma_byte_shift_bound p (i + 4) 32 _; first trivial.
  have /= h5 := sigma_byte_shift_bound p (i + 5) 40 _; first trivial.
  have /= h03 := sigma_or_bound (le3_word p i) (byte_word p (i + 3) `<<<` 24) 48.
  have /= h04 := sigma_or_bound
    (le3_word p i `|` (byte_word p (i + 3) `<<<` 24))
    (byte_word p (i + 4) `<<<` 32) 48.
  have /= h05 := sigma_or_bound
    ((le3_word p i `|` (byte_word p (i + 3) `<<<` 24)) `|`
      (byte_word p (i + 4) `<<<` 32))
    (byte_word p (i + 5) `<<<` 40) 48.
  have hr := W64.to_uint_cmp (le6_word p i).
  rewrite /le6_word in hr.
  rewrite /le6_word; smt().
qed.

(* This definition decodes the exact low/high noise limbs and the proved CDT
   count from the 26-byte input. The inclusive count bound is 166. *)
op sigma76_rounding_int (p : BArray26.t) : int =
  sigma_round_int (W64.to_uint (le6_word p 17))
    (W64.to_uint (le3_word p 23))
    (cdt_count (cdt_lo_input p) (cdt_hi_input p) 166).

lemma sigma76_decoded_bounds (p : BArray26.t) :
  0 <= W64.to_uint (le6_word p 17) < 281474976710656 /\
  0 <= W64.to_uint (le3_word p 23) < 16777216 /\
  0 <= cdt_count (cdt_lo_input p) (cdt_hi_input p) 166 <= 166.
proof.
  have h0 := sigma_le6_bound p 17.
  have h1 := sigma_le3_bound p 23.
  have h2 := cdt_count_range (cdt_lo_input p) (cdt_hi_input p) 166 _;
    first trivial.
  smt().
qed.

lemma sigma76_rounding_int_bounds (p : BArray26.t) :
  0 <= sigma76_rounding_int p <= 12033618204333965312 /\
  sigma76_rounding_int p < 18446744073709551616.
proof.
  have [h0 [h1 h2]] := sigma76_decoded_bounds p.
  rewrite /sigma76_rounding_int.
  exact (sigma_round_int_bounds _ _ _ h0 h1 h2).
qed.

lemma sigma76_spec_rounding (p : BArray26.t) :
  W64.to_uint (sigma76_spec p).`1 = sigma76_rounding_int p.
proof.
  have [h0 [h1 h2]] := sigma76_decoded_bounds p.
  pose count := cdt_count (cdt_lo_input p) (cdt_hi_input p) 166.
  have hx : W64.to_uint (W64.of_int count) = count.
  + rewrite W64.of_uintK modz_small; smt().
  have hy : W64.to_uint (le3_word p 23 `|` (W64.of_int count `<<<` 24)) =
      W64.to_uint (le3_word p 23) + count * 16777216.
  + by rewrite sigma_high_uint 1:/# 1:/# hx.
  have hybound : W64.to_uint (le3_word p 23 `|` (W64.of_int count `<<<` 24))
      < 2801795072 by rewrite hy; smt().
  rewrite /sigma76_spec /sigma_from_cdt /= -/count.
  by rewrite sigma_round_word_uint 1:/# 1:hybound hy
    /sigma76_rounding_int /sigma_round_int /count /=.
qed.

lemma sigma76_spec_rounding_bounds (p : BArray26.t) :
  0 <= W64.to_uint (sigma76_spec p).`1 <= 12033618204333965312.
proof.
  rewrite !sigma76_spec_rounding /=.
  have := sigma76_rounding_int_bounds p; smt().
qed.

lemma sigma76_regs_rounding_correct (p : BArray26.t) :
  phoare [SamplerTarget.M.__sample_gauss_sigma76_regs : randp = p ==>
    W64.to_uint res.`1 = sigma76_rounding_int p /\
    0 <= W64.to_uint res.`1 <= 12033618204333965312] = 1%r.
proof.
  conseq sigma76_regs_lossless (sigma76_regs_correct p) => />.
  smt(sigma76_spec_rounding sigma76_rounding_int_bounds).
qed.

lemma sigma76_jazz_rounding_correct
    (r : BArray8.t) (s : BArray16.t) (a : BArray4.t) (p : BArray26.t) :
  phoare [SamplerTarget.M.sample_gauss_sigma76_jazz :
    rp = r /\ sqrp = s /\ acceptedp = a /\ randp = p ==>
    W64.to_uint (BArray8.get64 res.`1 0) = sigma76_rounding_int p /\
    0 <= W64.to_uint (BArray8.get64 res.`1 0) <= 12033618204333965312] = 1%r.
proof.
  conseq sigma76_jazz_lossless (sigma76_jazz_correct r s a p) => />.
  smt(sigma76_spec_rounding sigma76_rounding_int_bounds).
qed.
