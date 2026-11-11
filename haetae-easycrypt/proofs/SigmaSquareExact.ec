require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SigmaSpec SigmaSquareBounds HyperballGaussianBounds
  GaussianTraceSpec GaussianAccumulatorCorrectness.

(* Exact split of a product of two canonical 48-bit unsigned limbs. *)
lemma ss_mul48_exact (a b : W64.t) :
  W64.to_uint a < 281474976710656 => W64.to_uint b < 281474976710656 =>
  W64.to_uint (mul48_word a b).`1 = (W64.to_uint a * W64.to_uint b) %% 281474976710656 /\
  W64.to_uint (mul48_word a b).`2 = (W64.to_uint a * W64.to_uint b) %/ 281474976710656.
proof.
  move=> ha hb.
  have /= har := W64.to_uint_cmp a.
  have /= hbr := W64.to_uint_cmp b.
  have hp : 0 <= W64.to_uint a * W64.to_uint b < 79228162514264337593543950336 by smt().
  have /= hmul := W64.mulhiP a b.
  have /= hlr := W64.to_uint_cmp (a*b).
  have /= hhr := W64.to_uint_cmp (W64.mulhi a b).
  have hh : W64.to_uint (W64.mulhi a b) < 4294967296 by smt().
  have hshift : W64.to_uint (W64.mulhi a b `<<<` 16) =
      W64.to_uint (W64.mulhi a b)*65536.
  + rewrite W64.to_uint_shl //= modz_small; smt().
  have hdis : (W64.mulhi a b `<<<` 16) `&` ((a*b) `>>>` 48) = W64.zero.
  + rewrite W64.andwC; apply W64.shrw_shlw_disjoint; trivial.
  have hxor : (W64.mulhi a b `<<<` 16) `^` ((a*b) `>>>` 48) =
      (W64.mulhi a b `<<<` 16) `|` ((a*b) `>>>` 48).
  + by rewrite W64.orw_xorw hdis W64.xorw0_s.
  have hhi : W64.to_uint (mul48_word a b).`2 =
      W64.to_uint (W64.mulhi a b)*65536 + W64.to_uint (a*b) %/ 281474976710656.
  + by rewrite /mul48_word W64.muluE /= hxor W64.to_uint_orw_disjoint 1://
      hshift W64.to_uint_shr.
  have hlo : W64.to_uint (mul48_word a b).`1 = W64.to_uint (a*b) %% 281474976710656.
  + rewrite /mul48_word W64.muluE /=.
    have -> : 281474976710655 = 2^48-1 by trivial.
    by rewrite W64.to_uint_and_mod.
  have hlo_prod : W64.to_uint (mul48_word a b).`1 =
      (W64.to_uint a * W64.to_uint b) %% 281474976710656.
  + rewrite hlo W64.to_uintM /= modz_dvd; trivial.
  have hdlo := divz_eq (W64.to_uint (a*b)) 281474976710656.
  have hdprod := divz_eq (W64.to_uint a * W64.to_uint b) 281474976710656.
  have hjoin : W64.to_uint (mul48_word a b).`1 +
      281474976710656 * W64.to_uint (mul48_word a b).`2 = W64.to_uint a * W64.to_uint b.
  + rewrite hlo hhi; smt().
  smt().
qed.

lemma ss_mul48_bounds (a b : W64.t) :
  W64.to_uint a < 281474976710656 => W64.to_uint b < 281474976710656 =>
  0 <= W64.to_uint (mul48_word a b).`1 < 281474976710656 /\
  0 <= W64.to_uint (mul48_word a b).`2 < 281474976710656.
proof.
  move=> ha hb; have [hl hh] := ss_mul48_exact a b ha hb.
  have /= har := W64.to_uint_cmp a.
  have /= hbr := W64.to_uint_cmp b.
  have hp : 0 <= W64.to_uint a * W64.to_uint b < 79228162514264337593543950336 by smt().
  have hm := modz_cmp (W64.to_uint a * W64.to_uint b) 281474976710656 _; first trivial.
  have hd := divz_eq (W64.to_uint a * W64.to_uint b) 281474976710656.
  rewrite hl hh; smt().
qed.

lemma ss_shr48_zero (w : W64.t) : W64.to_uint w < 281474976710656 =>
  w `>>>` 48 = W64.zero.
proof.
  move=> hw; apply W64.to_uint_eq.
  rewrite W64.to_uint0 W64.to_uint_shr //= divz_small; have := W64.to_uint_cmp w; smt().
qed.

(* Masking after the 64-bit left shift recovers exactly the low48 slice,
   even when the left shift itself wraps in the machine word. *)
lemma ss_shift20_mask_exact (w : W64.t) :
  W64.to_uint ((w `<<<` 20) `&` W64.of_int 281474976710655) =
    (W64.to_uint w %% 268435456) * 1048576.
proof.
  have -> : 281474976710655 = 2^48-1 by trivial.
  rewrite W64.to_uint_and_mod // W64.to_uint_shl //= modz_dvd 1://.
  have hd := divz_eq (W64.to_uint w) 268435456.
  have hm := modz_cmp (W64.to_uint w) 268435456 _; first trivial.
  have he : W64.to_uint w*1048576 =
      (W64.to_uint w %/ 268435456)*281474976710656 +
      (W64.to_uint w %% 268435456)*1048576 by smt().
  rewrite he modzMDl modz_small; smt().
qed.

lemma ss_integer_square_identity (l h : int) :
  ((l*l %/ 281474976710656 + 2*((l*h) %% 281474976710656)) %/ 268435456) +
    1048576*(2*((l*h) %/ 281474976710656)) + 1048576*(h*h) =
    (l+281474976710656*h)*(l+281474976710656*h) %/ 75557863725914323419136.
proof.
  have hn : 75557863725914323419136 = 281474976710656*268435456 by trivial.
  rewrite hn divz_mulp 1,2://.
  have hz : (l+281474976710656*h)*(l+281474976710656*h) =
      (2*l*h+281474976710656*h*h)*281474976710656 + l*l by ring.
  rewrite hz divzMDl 1://.
  have he : 2*l*h+281474976710656*h*h+l*l %/ 281474976710656 =
      (1048576*(2*((l*h) %/ 281474976710656)+h*h))*268435456 +
      (l*l %/ 281474976710656+2*((l*h) %% 281474976710656)).
  + have hc := divz_eq (l*h) 281474976710656; smt().
  rewrite he divzMDl 1://; ring.
qed.

lemma ss_add3_uint (a b c : W64.t) :
  W64.to_uint a + W64.to_uint b + W64.to_uint c < 18446744073709551616 =>
  W64.to_uint (a+b+c) = W64.to_uint a + W64.to_uint b + W64.to_uint c.
proof.
  move=> hsum.
  have /= ha := W64.to_uint_cmp a.
  have /= hb := W64.to_uint_cmp b.
  have /= hc := W64.to_uint_cmp c.
  have hab : W64.to_uint (a+b) = W64.to_uint a + W64.to_uint b.
  + apply W64.to_uintD_small; smt().
  rewrite W64.to_uintD hab modz_small; smt().
qed.

(* All machine additions in square_word are exact on the sampler's input
   domain. The two deliberate masked shifts retain the appropriate radix
   slices; the final normalization transfers their carry into the high limb. *)
lemma sigma_square_word_exact (lo hi : W64.t) :
  W64.to_uint lo < 281474976710656 =>
  W64.to_uint hi < 2801795072 =>
  let z = W64.to_uint lo + 281474976710656 * W64.to_uint hi in
  W64.to_uint (square_word lo hi).`1 +
    281474976710656 * W64.to_uint (square_word lo hi).`2 =
    z*z %/ 75557863725914323419136.
proof.
  move=> hlo hhi /=.
  have /= hlr := W64.to_uint_cmp lo.
  have /= hhr := W64.to_uint_cmp hi.
  have hhi48 : W64.to_uint hi < 281474976710656 by smt().
  pose a := mul48_word lo lo.
  pose b := mul48_word lo hi.
  have [ha0 ha1] := ss_mul48_exact lo lo hlo hlo.
  have [hb0 hb1] := ss_mul48_exact lo hi hlo hhi48.
  have [ha0r ha1r] := ss_mul48_bounds lo lo hlo hlo.
  have [hb0r hb1r] := ss_mul48_bounds lo hi hlo hhi48.
  have hcross : 0 <= W64.to_uint b.`2 < 4294967296.
  + apply hb_mul48_high_bound; smt().
  have hzero : a.`1 `>>>` 48 = W64.zero.
  + apply ss_shr48_zero; smt().
  have hhighzero : W64.mulhi hi hi = W64.zero.
  + rewrite W64.to_uint_eq W64.to_uint0 W64.mulhi0; smt().
  have hprod : W64.to_uint (hi*hi) = W64.to_uint hi * W64.to_uint hi.
  + apply W64.to_uintM_small; smt().
  have hbshift : W64.to_uint (b.`1 `<<<` 1) = 2*W64.to_uint b.`1.
  + rewrite W64.to_uint_shl //= modz_small; smt().
  pose r0 := a.`2 + (b.`1 `<<<` 1).
  pose r1 := b.`2 `<<<` 1.
  have hr0 : W64.to_uint r0 = W64.to_uint a.`2 + 2*W64.to_uint b.`1.
  + rewrite /r0 W64.to_uintD hbshift modz_small; smt().
  have hr0b : 0 <= W64.to_uint r0 < 844424930131968 by smt().
  have hr1 : W64.to_uint r1 = 2*W64.to_uint b.`2.
  + rewrite /r1 W64.to_uint_shl //= modz_small; smt().
  have hr1b : 0 <= W64.to_uint r1 < 8589934592 by smt().
  pose s0 := (r0 `>>>` 28) +
    ((r1 `<<<` 20) `&` W64.of_int 281474976710655) +
    (((hi*hi) `<<<` 20) `&` W64.of_int 281474976710655).
  pose s1 := (r1 `>>>` 28) + ((hi*hi) `>>>` 28).
  have hr028 : 0 <= W64.to_uint (r0 `>>>` 28) < 3145728.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have hr1m := modz_cmp (W64.to_uint r1) 268435456 _; first trivial.
  have hpm := modz_cmp (W64.to_uint (hi*hi)) 268435456 _; first trivial.
  have hs0 : W64.to_uint s0 = W64.to_uint r0 %/ 268435456 +
      (W64.to_uint r1 %% 268435456)*1048576 +
      (W64.to_uint (hi*hi) %% 268435456)*1048576.
  + rewrite /s0 ss_add3_uint.
    - rewrite !ss_shift20_mask_exact; smt().
    by rewrite W64.to_uint_shr //= !ss_shift20_mask_exact.
  have hs0b : 0 <= W64.to_uint s0 < 562949956567040.
  + have h0 : W64.to_uint (r0 `>>>` 28) = W64.to_uint r0 %/ 268435456
      by rewrite W64.to_uint_shr.
    smt().
  have hr128 := sigma_shr28_bound r1.
  have hp28 := sigma_shr28_bound (hi*hi).
  have hs1 : W64.to_uint s1 = W64.to_uint r1 %/ 268435456 +
      W64.to_uint (hi*hi) %/ 268435456.
  + rewrite /s1 W64.to_uintD_small 1:/# !W64.to_uint_shr //=.
  have hs1b : 0 <= W64.to_uint s1 < 137438953472.
  + have h1 : W64.to_uint (r1 `>>>` 28) = W64.to_uint r1 %/ 268435456
      by rewrite W64.to_uint_shr.
    have h2 : W64.to_uint ((hi*hi) `>>>` 28) = W64.to_uint (hi*hi) %/ 268435456
      by rewrite W64.to_uint_shr.
    smt().
  have hform : square_word lo hi = gauss_normalize s0 s1.
  + by rewrite /square_word W64.muluE /= -/a -/b hzero hhighzero
      (W64.shlMP 0 36) //= /gauss_normalize /s0 /s1 /r0 /r1.
  have hs0q := divz_eq (W64.to_uint s0) 281474976710656.
  have hs0m := modz_cmp (W64.to_uint s0) 281474976710656 _; first trivial.
  have hnorm := gauss_normalize_value_exact s0 s1 _; first smt().
  rewrite /gauss_limb_value in hnorm.
  rewrite hform hnorm hs0 hs1.
  have hrd := divz_eq (W64.to_uint r1) 268435456.
  have hpd := divz_eq (W64.to_uint (hi*hi)) 268435456.
  have hmerge : W64.to_uint r0 %/ 268435456 +
      (W64.to_uint r1 %% 268435456)*1048576 +
      (W64.to_uint (hi*hi) %% 268435456)*1048576 +
      281474976710656*(W64.to_uint r1 %/ 268435456 +
        W64.to_uint (hi*hi) %/ 268435456) =
      W64.to_uint r0 %/ 268435456 + 1048576*W64.to_uint r1 +
        1048576*W64.to_uint (hi*hi) by smt().
  rewrite hmerge hr0 hr1 hprod /a /b ha1 hb0 hb1.
  exact (ss_integer_square_identity (W64.to_uint lo) (W64.to_uint hi)).
qed.
