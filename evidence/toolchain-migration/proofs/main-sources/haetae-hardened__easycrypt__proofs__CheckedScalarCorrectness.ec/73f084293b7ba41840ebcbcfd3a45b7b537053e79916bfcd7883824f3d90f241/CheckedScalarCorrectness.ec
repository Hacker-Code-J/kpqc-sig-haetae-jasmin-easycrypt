require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec HyperballFixedPointCorrectness CheckedScaleSpec
  Rejection48Correctness SigmaSpec HardenedHyperballTarget.

module HCS = HardenedHyperballTarget.M.

lemma hcs_round_integer n :
  n %/ 32768 + (n %/ 16384) %% 2 = (n+16384) %/ 32768.
proof.
  have hd := divz_eq n 32768.
  have hr := modz_cmp n 32768 _; first trivial.
  have hs := modz_pow2_div 15 14 n _; first trivial.
  rewrite /= in hs.
  have he : n+16384 = (n %/ 32768)*32768 + (n %% 32768+16384) by smt().
  rewrite he divzMDl 1:// -hs.
  case (n %% 32768 < 16384) => hc.
  + by rewrite (divz_small (n %% 32768) 16384 _) 1:/#
      (divz_small (n %% 32768+16384) 32768 _) 1:/#.
  have h1 : n %% 32768 %/ 16384 = 1 by apply divz_eqP; smt().
  have h2 : (n %% 32768+16384) %/ 32768 = 1 by apply divz_eqP; smt().
  by rewrite h1 h2.
qed.

lemma hcs_round_range (high : W64.t) :
  0 <= (W64.to_uint high+16384) %/ 32768 <= 562949953421312.
proof.
  have /= h := W64.to_uint_cmp high.
  have hd := divz_eq (W64.to_uint high+16384) 32768.
  have hr := modz_cmp (W64.to_uint high+16384) 32768 _; first trivial.
  smt().
qed.

lemma hcs_round_word_uint (high : W64.t) :
  W64.to_uint (hcs_round_word high) = (W64.to_uint high+16384) %/ 32768.
proof.
  have ha : W64.to_uint (high `>>>` 15) = W64.to_uint high %/ 32768 by
    rewrite W64.to_uint_shr.
  have hb : W64.to_uint ((high `>>>` 14) `&` W64.one) = (W64.to_uint high %/ 16384) %% 2.
  + rewrite (W64.to_uint_and_mod 1 (high `>>>` 14)) 1:// W64.to_uint_shr //=.
  have hr := hcs_round_range high.
  rewrite /hcs_round_word W64.to_uintD_small.
  + rewrite ha hb hcs_round_integer; smt().
  by rewrite ha hb hcs_round_integer.
qed.

lemma hcs_magnitude_uint sample scale :
  W64.to_uint (hcs_magnitude_word sample scale) = hcs_wide_magnitude sample scale.
proof. by rewrite /hcs_magnitude_word /hcs_wide_magnitude hcs_round_word_uint. qed.

lemma hcs_magnitude_range sample scale :
  0 <= hcs_wide_magnitude sample scale <= 562949953421312.
proof. rewrite /hcs_wide_magnitude; exact (hcs_round_range _). qed.

lemma hcs_truncate_add (a b : W64.t) :
  truncateu32 (a+b) = truncateu32 a + truncateu32 b.
proof.
  rewrite -{1}(W64.to_uintK a) -{1}(W64.to_uintK b) -W64.of_intD
    hb_truncate_of_int /W2u32.truncateu32 W32.of_intD.
  trivial.
qed.

lemma hcs_truncate_bits (a : W64.t) : truncateu32 a = a \bits32 0.
proof. by rewrite W2u32.bits32_div 1:// /W2u32.truncateu32 /=. qed.

lemma hcs_truncate_xor (a b : W64.t) :
  truncateu32 (a `^` b) = truncateu32 a `^` truncateu32 b.
proof.
  rewrite !hcs_truncate_bits.
  apply W32.wordP => i hi.
  by rewrite W32.xorwE !W2u32.bits32iE 1..3:hi /=.
qed.

lemma hcs_round_truncate (high : W64.t) :
  truncateu32 (hcs_round_word high) =
    truncateu32 ((high+W64.of_int 16384) `>>>` 15).
proof.
  apply W32.to_uint_eq.
  rewrite /W2u32.truncateu32 !W32.of_uintK hcs_round_word_uint
    W64.to_uint_shr //= W64.to_uintD W64.of_uintK /=.
  have he := modz_pow2_div 64 15 (W64.to_uint high+16384) _; first trivial.
  rewrite /= in he.
  rewrite he modz_dvd; trivial.
qed.

lemma hcs_coefficient_legacy sample scale sign :
  hcs_coefficient sample scale sign = hb_mul_rnd13 sample scale sign.
proof.
  rewrite /hcs_coefficient /hcs_magnitude_word /hb_mul_rnd13 /hcs_product /=
    !hcs_truncate_add !hcs_truncate_xor hcs_round_truncate.
  trivial.
qed.

lemma hcs_badmask_zero sample scale :
  hcs_badmask sample scale = W64.zero <=> hcs_wide_magnitude sample scale <= 2147483647.
proof.
  have hn : W64.onew <> W64.zero by rewrite W64.oneE W64.to_uint_eq W64.to_uint0 W64.of_uintK.
  rewrite /hcs_badmask; case (hcs_wide_magnitude sample scale <= 2147483647); smt().
qed.

lemma hcs_badmask_cases sample scale :
  hcs_badmask sample scale = W64.zero \/ hcs_badmask sample scale = W64.onew.
proof. rewrite /hcs_badmask; case (hcs_wide_magnitude sample scale <= 2147483647); smt(). qed.

lemma hcs_coefficient_signed sample scale sign :
  sign = W64.zero \/ sign = W64.one => hcs_badmask sample scale = W64.zero =>
  W32.to_sint (hcs_coefficient sample scale sign) =
    if sign = W64.zero then hcs_wide_magnitude sample scale else -hcs_wide_magnitude sample scale.
proof.
  move=> hs hb; have hf : hcs_wide_magnitude sample scale <= 2147483647 by
    rewrite -hcs_badmask_zero.
  rewrite /hcs_coefficient -hcs_magnitude_uint.
  apply hb_signed_truncate_fit; first exact hs.
  by rewrite hcs_magnitude_uint.
qed.

lemma hcs_badmask_word sample scale :
  (W64.of_int 2147483647 - hcs_magnitude_word sample scale) `|>>>` 63 =
    hcs_badmask sample scale.
proof.
  have hr := hcs_magnitude_range sample scale.
  rewrite -{1}(W64.to_uintK (hcs_magnitude_word sample scale)) hcs_magnitude_uint.
  rewrite (rejection48_compare_mask 2147483647 (hcs_wide_magnitude sample scale)) 1..2:/#.
  rewrite /hcs_badmask; case (hcs_wide_magnitude sample scale <= 2147483647); smt().
qed.

lemma hcs_mul48_correct a0 b0 :
  hoare [HCS.__mul48 : a=a0 /\ b=b0 ==> res=mul48_word a0 b0].
proof. proc; wp; skip; auto => />; rewrite /mul48_word /=. qed.

lemma hcs_mul_regs_correct a b c d :
  hoare [HCS.__fixpoint_mul_regs : x0=a /\ x1=b /\ y0=c /\ y1=d
    ==> res=hb_mul (a,b) (c,d)].
proof.
  proc; wp; ecall (hcs_mul48_correct x1 y0).
  wp; ecall (hcs_mul48_correct x0 y1).
  wp; ecall (hcs_mul48_correct x0 y0).
  wp; skip; auto => />; rewrite /hb_mul /hb_norm /=.
qed.

lemma hcs_regs_correct sample a b sign0 :
  hoare [HCS._hb_checked_mul_rnd13_regs :
    x=sample /\ y0=a /\ y1=b /\ sign=sign0 ==> res=hcs_scalar sample (a,b) sign0].
proof.
  proc; wp; ecall (hcs_mul_regs_correct x0 x1 y0 y1).
  wp; skip; auto => />.
  rewrite /W64.(`<<`) /W64.(`>>`) /W64.(`|>>`) !W8.of_uintK /=.
  rewrite /hcs_scalar /hcs_coefficient /hcs_magnitude_word /hcs_product /hcs_round_word /=.
  have h := hcs_badmask_word sample (a,b).
  by move: h; rewrite /hcs_magnitude_word /hcs_product /hcs_round_word /= => ->.
qed.

lemma hcs_pointer_correct sample scale sign0 :
  hoare [HCS._hb_checked_mul_rnd13 : x=sample /\ yp=scale /\ sign=sign0
    ==> res=hcs_scale_sample sample scale sign0].
proof.
  proc; ecall (hcs_regs_correct x y0 y1 s).
  wp; skip; auto => />; rewrite /hcs_scale_sample /hb_load.
qed.

lemma hcs_mul_regs_ll : islossless HCS.__fixpoint_mul_regs.
proof. proc; inline *; auto. qed.

lemma hcs_regs_ll : islossless HCS._hb_checked_mul_rnd13_regs.
proof. proc; wp; call hcs_mul_regs_ll; auto. qed.

lemma hcs_pointer_ll : islossless HCS._hb_checked_mul_rnd13.
proof. proc; call hcs_regs_ll; auto. qed.

lemma hcs_regs_total sample a b sign0 :
  phoare [HCS._hb_checked_mul_rnd13_regs :
    x=sample /\ y0=a /\ y1=b /\ sign=sign0 ==> res=hcs_scalar sample (a,b) sign0] = 1%r.
proof. by conseq hcs_regs_ll (hcs_regs_correct sample a b sign0). qed.

lemma hcs_pointer_total sample scale sign0 :
  phoare [HCS._hb_checked_mul_rnd13 : x=sample /\ yp=scale /\ sign=sign0
    ==> res=hcs_scale_sample sample scale sign0] = 1%r.
proof. by conseq hcs_pointer_ll (hcs_pointer_correct sample scale sign0). qed.
