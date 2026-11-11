require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.
require import Fq NTTCorrectness.

import Ring.IntID IntOrder.

theory NTTMontgomeryBounds.

lemma signed_low32_bound (a:int) :
  -2147483648 <= Fq.SignedReductions.smod (a * 940508161) 4294967296 < 2147483648.
proof.
have h := Fq.SignedReductions.smod_bnd (a * 940508161) 4294967296.
by smt().
qed.

lemma sredc_wide_formula (a:int) :
  -281474976710656 <= a <= 281474976710656 =>
  Fq.SignedReductions.SREDC a =
  (a - Fq.SignedReductions.smod (a * 940508161) 4294967296 * 64513) %/ 4294967296.
proof.
move=> ha.
have ht := signed_low32_bound a.
rewrite /Fq.SignedReductions.SREDC /=
  (Fq.SignedReductions.smod_div (a * 940508161)).
rewrite /Fq.SignedReductions.R /Fq.q /=.
rewrite (Fq.SignedReductions.smod_small
  (a - Fq.SignedReductions.smod (a * 940508161) 4294967296 * 64513)
  18446744073709551616); first 2 by smt().
have hs := Fq.SignedReductions.smod_sq
  (a - Fq.SignedReductions.smod (a * 940508161) 4294967296 * 64513).
rewrite /Fq.SignedReductions.R /= in hs.
rewrite hs.
apply Fq.SignedReductions.smod_small; first by smt().
by smt(IntDiv.lez_divRL IntDiv.ltz_divLR).
qed.

lemma sredc_wide_bound (a:int) :
  -281474976710656 <= a <= 281474976710656 =>
  -131072 <= Fq.SignedReductions.SREDC a < 131072.
proof.
move=> ha; rewrite (sredc_wide_formula a ha).
have ht := signed_low32_bound a.
by smt(IntDiv.lez_divRL IntDiv.ltz_divLR).
qed.

lemma sredc_canonical24_bound (a:int) :
  -1082331758592 <= a <= 1082331758592 =>
  -32768 <= Fq.SignedReductions.SREDC a < 32768.
proof.
move=> ha.
have haw : -281474976710656 <= a <= 281474976710656 by smt().
rewrite (sredc_wide_formula a haw).
have ht := signed_low32_bound a.
by smt(IntDiv.lez_divRL IntDiv.ltz_divLR).
qed.

lemma sredc_numerator_divisible (a:int) :
  (a - Fq.SignedReductions.smod (a * 940508161) 4294967296 * 64513) %% 4294967296 = 0.
proof.
rewrite -modzBm -modzMml Fq.SignedReductions.smod_congr modzMml.
rewrite -mulrA -modzMmr /=.
by done.
qed.

lemma sredc_wide_congr (a:int) :
  -281474976710656 <= a <= 281474976710656 =>
  Fq.SignedReductions.SREDC a %% 64513 = (a * 50386) %% 64513.
proof.
move=> ha; rewrite (sredc_wide_formula a ha).
pose t := Fq.SignedReductions.smod (a * 940508161) 4294967296.
pose v := (a - t * 64513) %/ 4294967296.
have hd : v * 4294967296 = a - t * 64513.
+ by rewrite /v divzE /t sredc_numerator_divisible /=.
have he : v = a * 50386 + (-t * 50386 - v * 3354459135) * 64513 by smt().
by rewrite {1}he modzMDr.
qed.

lemma fqmul_24_bounds_congr (a b:int) :
  -16777216 <= a < 16777216 =>
  -16777216 <= b < 16777216 =>
  -131072 <= Fq.SignedReductions.SREDC (a*b) < 131072 /\
  Fq.SignedReductions.SREDC (a*b) %% 64513 = (a*b*50386) %% 64513.
proof.
move=> ha hb.
have hp : -281474976710656 <= a*b <= 281474976710656 by smt().
split; first exact (sredc_wide_bound (a*b) hp).
exact (sredc_wide_congr (a*b) hp).
qed.

lemma fqmul_canonical24_bounds_congr (a b:int) :
  0 <= a < 64513 =>
  -16777216 <= b < 16777216 =>
  -32768 <= Fq.SignedReductions.SREDC (a*b) < 32768 /\
  Fq.SignedReductions.SREDC (a*b) %% 64513 = (a*b*50386) %% 64513.
proof.
move=> ha hb.
have hp : -1082331758592 <= a*b <= 1082331758592 by smt().
have hpw : -281474976710656 <= a*b <= 281474976710656 by smt().
split; first exact (sredc_canonical24_bound (a*b) hp).
exact (sredc_wide_congr (a*b) hpw).
qed.

lemma target_fqmul_24_total (aa bb:int) :
  -16777216 <= aa < 16777216 =>
  -16777216 <= bb < 16777216 =>
  phoare [HpolyTarget.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    -131072 <= W32.to_sint res < 131072 /\
    W32.to_sint res %% 64513 = (aa*bb*50386) %% 64513] = 1%r.
proof.
move=> ha hb.
have hf := fqmul_24_bounds_congr aa bb ha hb.
have hh : hoare [HpolyTarget.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    -131072 <= W32.to_sint res < 131072 /\
    W32.to_sint res %% 64513 = (aa*bb*50386) %% 64513].
+ by conseq (NTTCorrectness.target_fqmul_correct aa bb) => /#.
by conseq NTTCorrectness.target_fqmul_ll hh.
qed.

lemma target_fqmul_canonical24_total (aa bb:int) :
  0 <= aa < 64513 =>
  -16777216 <= bb < 16777216 =>
  phoare [HpolyTarget.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    -32768 <= W32.to_sint res < 32768 /\
    W32.to_sint res %% 64513 = (aa*bb*50386) %% 64513] = 1%r.
proof.
move=> ha hb.
have hf := fqmul_canonical24_bounds_congr aa bb ha hb.
have hh : hoare [HpolyTarget.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    -32768 <= W32.to_sint res < 32768 /\
    W32.to_sint res %% 64513 = (aa*bb*50386) %% 64513].
+ by conseq (NTTCorrectness.target_fqmul_correct aa bb) => /#.
by conseq NTTCorrectness.target_fqmul_ll hh.
qed.

end NTTMontgomeryBounds.
