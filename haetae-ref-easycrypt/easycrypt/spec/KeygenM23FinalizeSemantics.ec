require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenM23FinalizeSpec Fq.

theory KeygenM23FinalizeSemantics.

op q : int = 64513.
op qrec : int = 66575.
op radix : int = 4294967296.

op vk_low_int (x : int) : int =
  if x %% 2 = 0 then 0
  else if (x %/ 2) %% 2 = 0 then 1 else -1.

op vk_high_int (x : int) : int =
  (x - vk_low_int x) %/ 2.

lemma barrett_residue_range (z : int) :
  -262144 <= z < 262144 =>
  let t = (z * qrec) %/ radix in
  let x = z - t * q in
  0 <= x <= q /\ x %% q = z %% q.
proof.
rewrite /q /qrec /radix.
move=> hz /=.
pose k := z %/ 64513.
pose r := z %% 64513.
have hq : z = k * 64513 + r.
+ rewrite /k /r.
  exact (divz_eq z 64513).
have hr : 0 <= r < 64513.
+ rewrite /r.
  smt().
have hk : -5 <= k <= 4 by smt().
have hprod :
    z * 66575 =
      k * 4294967296 + (r * 66575 - k * 14321) by smt().
rewrite hprod divzMDl 1:/#.
case (k <= 0).
+ move=> hk0.
  have hsmall : 0 <= r * 66575 - k * 14321 < 4294967296
    by smt().
  rewrite divz_small 1:/#.
  split.
  + smt().
  have hx : z - k * 64513 = r by smt().
  rewrite hx modz_small 1:/#.
  by rewrite /r.
case (r = 0).
+ move=> hr0 hkpos.
  have hsmall :
      -4294967296 <= r * 66575 - k * 14321 < 0 by smt().
  have hdiv :
      (r * 66575 - k * 14321) %/ 4294967296 = -1.
  + have hshift :
        r * 66575 - k * 14321 =
          (-1) * 4294967296 +
          (4294967296 + r * 66575 - k * 14321) by ring.
    rewrite hshift divzMDl 1:/#.
    have hrem :
        0 <= 4294967296 + r * 66575 - k * 14321 <
          4294967296 by smt().
    by rewrite divz_small 1:/#.
  rewrite hdiv.
  split.
  + smt().
  have hzmod : z %% 64513 = r by rewrite /r.
  rewrite hzmod hr0.
  have hx : z - (k - 1) * 64513 = 64513 by smt().
  by rewrite hx modzz.
move=> hrnz hkpos.
have hsmall : 0 <= r * 66575 - k * 14321 < 4294967296
  by smt().
rewrite divz_small 1:/#.
split.
+ smt().
have hx : z - k * 64513 = r by smt().
rewrite hx modz_small 1:/#.
by rewrite /r.
qed.

lemma w32_sar_nonnegative (w : W32.t) (k : int) :
  0 <= k =>
  W32.to_uint w < 2147483648 =>
  W32.sar w k = w `>>>` k.
proof.
move=> hk hw.
apply W32.ext_eq => i hi.
rewrite /W32.sar /W32.(`|>>>`) W32.initiE 1:hi.
rewrite /W32.(`>>>`) W32.initiE 1:hi /=.
case (31 < i + k) => hik.
+ have hmin : min 31 (i + k) = 31 by smt().
  rewrite hmin W32.get_to_uint /=.
  have hdiv : W32.to_uint w %/ 2 ^ 31 = 0.
  + apply divz_small.
    apply bound_abs.
    have hpow : 2 ^ 31 = 2147483648 by trivial.
    rewrite hpow.
    smt(W32.to_uint_cmp).
  rewrite hdiv /=.
  by rewrite W32.get_out 1:/#.
+ have hmin : min 31 (i + k) = i + k by smt().
  rewrite hmin.
  case (0 <= i + k < 32) => hb.
  + done.
  have hout : !(0 <= i + k < 32) by smt().
  by rewrite W32.get_out 1:hout.
qed.

lemma w64_sar_nonnegative (w : W64.t) (k : int) :
  0 <= k =>
  W64.to_uint w < 9223372036854775808 =>
  W64.sar w k = w `>>>` k.
proof.
move=> hk hw.
apply W64.ext_eq => i hi.
rewrite /W64.sar /W64.(`|>>>`) W64.initiE 1:hi.
rewrite /W64.(`>>>`) W64.initiE 1:hi /=.
case (63 < i + k) => hik.
+ have hmin : min 63 (i + k) = 63 by smt().
  rewrite hmin W64.get_to_uint /=.
  have hdiv : W64.to_uint w %/ 2 ^ 63 = 0.
  + apply divz_small.
    apply bound_abs.
    have hpow : 2 ^ 63 = 9223372036854775808 by trivial.
    rewrite hpow.
    smt(W64.to_uint_cmp).
  rewrite hdiv /=.
  by rewrite W64.get_out 1:/#.
+ have hmin : min 63 (i + k) = i + k by smt().
  rewrite hmin.
  case (0 <= i + k < 64) => hb.
  + done.
  have hout : !(0 <= i + k < 64) by smt().
  by rewrite W64.get_out 1:hout.
qed.

lemma w32_sar_nonnegative_of_int (x k : int) :
  0 <= x < 2147483648 =>
  0 <= k =>
  W32.sar (W32.of_int x) k = W32.of_int (x %/ 2 ^ k).
proof.
move=> hx hk.
rewrite w32_sar_nonnegative 1:hk.
+ rewrite W32.to_uint_small 1:/#.
  smt().
rewrite W32.shrDP 1:hk.
rewrite (modz_small x W32.modulus).
+ apply bound_abs.
  smt().
by [].
qed.

lemma w64_sar_nonnegative_of_int (x k : int) :
  0 <= x < 9223372036854775808 =>
  0 <= k =>
  W64.sar (W64.of_int x) k = W64.of_int (x %/ 2 ^ k).
proof.
move=> hx hk.
rewrite w64_sar_nonnegative 1:hk.
+ rewrite W64.to_uint_small 1:/#.
  smt().
rewrite W64.shrDP 1:hk.
rewrite (modz_small x W64.modulus).
+ apply bound_abs.
  smt().
by [].
qed.

lemma bit62_eq_bit63_small (z : int) :
  -64513 <= z <= 64513 =>
  (W64.of_int z).[62] = (W64.of_int z).[63].
proof.
move=> hz.
rewrite !W64.of_intwE /W64.int_bit /=.
smt(@IntDiv).
qed.

lemma sar31_sar32_double_small (z : int) :
  -64513 <= z <= 64513 =>
  W64.sar (W64.of_int z) 31 =
    W64.sar (W64.of_int (2 * z)) 32.
proof.
move=> hz.
have hdouble :
    W64.of_int (2 * z) = W64.of_int z `<<<` 1.
+ rewrite W64.shlMP 1:/#.
  congr.
  ring.
rewrite hdouble.
apply W64.ext_eq => i hi.
rewrite /W64.sar /W64.(`|>>>`) !W64.initiE 1:hi 1:hi.
case (i < 32).
+ move=> hlo.
  have hmin31 : min 63 (i + 31) = i + 31 by smt().
  have hmin32 : min 63 (i + 32) = i + 32 by smt().
  rewrite hmin31 hmin32 /=.
  smt().
move=> hhi.
have hmin31 : min 63 (i + 31) = 63 by smt().
have hmin32 : min 63 (i + 32) = 63 by smt().
rewrite hmin31 hmin32 /=.
rewrite bit62_eq_bit63_small 1:hz.
done.
qed.

lemma sar31_nonnegative (z : int) :
  0 <= z <= 64513 =>
  W64.sar (W64.of_int z) 31 = W64.zero.
proof.
move=> hz.
rewrite sar31_sar32_double_small 1:/#.
have hsint : W64.to_sint (W64.of_int (2 * z)) = 2 * z.
+ apply W64.to_sintK_small.
  smt().
have hdiv : (2 * z) %/ 2 ^ 32 = 0.
+ smt(@IntDiv).
have hsem := Fq.SAR_sem32 (W64.of_int (2 * z)).
rewrite /(`|>>`) W8.of_uintK /= hsint hdiv in hsem.
exact hsem.
qed.

lemma sar31_negative (z : int) :
  -64513 <= z < 0 =>
  W64.sar (W64.of_int z) 31 = W64.of_int (-1).
proof.
move=> hz.
rewrite sar31_sar32_double_small 1:/#.
have hsint : W64.to_sint (W64.of_int (2 * z)) = 2 * z.
+ apply W64.to_sintK_small.
  smt().
have hdiv : (2 * z) %/ 2 ^ 32 = -1.
+ smt(@IntDiv).
have hsem := Fq.SAR_sem32 (W64.of_int (2 * z)).
rewrite /(`|>>`) W8.of_uintK /= hsint hdiv in hsem.
exact hsem.
qed.

lemma sigextu64_semantics (a : W32.t) :
  sigextu64 a = W64.of_int (W32.to_sint a).
proof. by rewrite /sigextu64. qed.

lemma barrett_shift_word (z : int) :
  -262144 <= z < 262144 =>
  W64.of_int (z * qrec) `|>>` W8.of_int 32 =
    W64.of_int ((z * qrec) %/ radix).
proof.
move=> hz.
rewrite Fq.SAR_sem32.
have hsmall :
    W64.min_sint <= z * qrec <= W64.max_sint.
+ rewrite /qrec.
  smt().
congr.
rewrite W64.to_sintK_small 1:hsmall.
by rewrite /radix.
qed.

lemma barrett_word_semantics (a : W32.t) :
  Fq.bw32 a 18 =>
  sigextu64 a -
    ((sigextu64 a * W64.of_int qrec `|>>` W8.of_int 32) *
      W64.of_int q) =
    W64.of_int
      (W32.to_sint a -
        ((W32.to_sint a * qrec) %/ radix) * q).
proof.
move=> ha.
have hz : -262144 <= W32.to_sint a < 262144.
+ rewrite /Fq.bw32 in ha.
  move: ha.
  by rewrite /=.
rewrite sigextu64_semantics
        W64.of_intM'
        barrett_shift_word 1:hz
        W64.of_intM'
        W64.of_intS'.
congr.
qed.

lemma w64_sar31_nonnegative_small (x : int) :
  0 <= x <= q =>
  W64.of_int x `|>>` W8.of_int 31 = W64.zero.
proof.
move=> hx.
rewrite /(`|>>`) W8.of_uintK /=.
rewrite w64_sar_nonnegative_of_int.
+ rewrite /q in hx.
  smt().
+ smt().
have hdiv : x %/ 2 ^ 31 = 0.
+ rewrite (_ : 2 ^ 31 = 2147483648) //.
  apply divz_small.
  apply bound_abs.
  rewrite /q in hx.
  smt().
by rewrite hdiv.
qed.

lemma freeze_word_semantics (a : W32.t) :
  Fq.bw32 a 18 =>
  KeygenM23FinalizeSpec.freeze_word a =
    W32.of_int (W32.to_sint a %% q).
proof.
move=> ha.
pose z := W32.to_sint a.
pose t := (z * qrec) %/ radix.
pose x := z - t * q.
have hz : -262144 <= z < 262144.
+ rewrite /z /Fq.bw32 in ha.
  move: ha.
  by rewrite /=.
have hx := barrett_residue_range z hz.
rewrite /t /x in hx.
have hxrange : 0 <= x <= q by smt().
have hxmod : x %% q = z %% q by smt().
rewrite /KeygenM23FinalizeSpec.freeze_word /=.
rewrite barrett_word_semantics 1:ha.
rewrite -/t -/x.
rewrite w64_sar31_nonnegative_small 1:hxrange.
rewrite W64.and0w W64.addr0_s W64.of_intS'.
case (x < q).
+ move=> hlt.
  rewrite /(`|>>`) W8.of_uintK /=.
  rewrite sar31_negative.
  + move: hxrange hlt.
    rewrite /q.
    smt().
  rewrite /truncateu32 /zeroextu64 /=.
  rewrite W64.to_uint_small.
  + rewrite /q in hxrange.
    smt().
  congr.
  rewrite -hxmod modz_small.
  + move: hxrange hlt.
    rewrite /q.
    smt().
  trivial.
+ move=> hnlt.
  have heq : x = q by smt().
  rewrite heq.
  rewrite /(`|>>`) W8.of_uintK /=.
  rewrite sar31_nonnegative.
  + rewrite /q.
    smt().
  rewrite /truncateu32 /zeroextu64 /=.
  rewrite -hxmod heq modzz.
  by rewrite /q /=.
qed.

lemma freeze_word_to_sint (a : W32.t) :
  Fq.bw32 a 18 =>
  W32.to_sint (KeygenM23FinalizeSpec.freeze_word a) =
    W32.to_sint a %% q.
proof.
move=> ha.
rewrite freeze_word_semantics 1:ha.
apply W32.to_sintK_small.
have hmod : 0 <= W32.to_sint a %% q < q.
+ apply modz_cmp.
  rewrite /q.
  smt().
rewrite /q in hmod.
smt().
qed.

lemma freeze_word_canonical (a : W32.t) :
  Fq.bw32 a 18 =>
  0 <= W32.to_sint (KeygenM23FinalizeSpec.freeze_word a) < q.
proof.
move=> ha.
rewrite freeze_word_to_sint 1:ha.
apply modz_cmp.
rewrite /q.
smt().
qed.

lemma w32_and_one (w : W32.t) :
  w `&` W32.one = W32.of_int (W32.to_uint w %% 2).
proof.
have h :
    w `&` W32.of_int (2 ^ 1 - 1) =
      W32.of_int (W32.to_uint w %% 2 ^ 1).
+ apply W32.and_mod.
  smt().
by move: h; rewrite /=.
qed.

lemma w32_shl_zero_one :
  W32.of_int 0 `<<` W8.of_int 1 = W32.of_int 0.
proof.
rewrite W32.shl_shlw 1:/# W32.shlMP 1:/#.
by [].
qed.

lemma w32_and_bit (w : W32.t) (r : int) :
  (r = 0 \/ r = 1) =>
  w `&` W32.of_int r =
    W32.of_int (r * (W32.to_uint w %% 2)).
proof.
move=> hr.
case hr.
+ move=> ->.
  by rewrite W32.andw0 /=.
move=> ->.
by rewrite w32_and_one.
qed.

lemma vk_low_int_formula (x : int) :
  vk_low_int x =
    x %% 2 - 2 * ((x %% 2) * ((x %/ 2) %% 2)).
proof.
have hr : 0 <= x %% 2 < 2 by smt(@IntDiv).
have hh : 0 <= (x %/ 2) %% 2 < 2 by smt(@IntDiv).
case (x %% 2 = 0) => hr0.
+ by rewrite /vk_low_int hr0.
have hrange : 0 <= x %% 2 < 2.
+ apply modz_cmp.
  smt().
have hr1 : x %% 2 = 1 by smt().
case ((x %/ 2) %% 2 = 0) => hh0.
+ by rewrite /vk_low_int hr1 hh0.
have hh1 : (x %/ 2) %% 2 = 1 by smt().
by rewrite /vk_low_int hr1 hh1.
qed.

lemma vk_low_int_range (x : int) :
  -1 <= vk_low_int x <= 1.
proof.
rewrite /vk_low_int.
by case (x %% 2 = 0); case ((x %/ 2) %% 2 = 0).
qed.

lemma vk_high_int_range (x : int) :
  0 <= x < q =>
  0 <= vk_high_int x < 32768.
proof.
move=> hx.
have hl := vk_low_int_range x.
rewrite /q in hx.
rewrite /vk_high_int.
have heven : (x - vk_low_int x) %% 2 = 0.
+ rewrite vk_low_int_formula.
  have hr : 0 <= x %% 2 < 2 by smt(@IntDiv).
  have hh : 0 <= (x %/ 2) %% 2 < 2 by smt(@IntDiv).
  have hxdiv := divz_eq x 2.
  smt(@IntDiv).
have hnonneg : 0 <= x - vk_low_int x.
+ case (x = 0).
  + move=> ->.
    by rewrite /vk_low_int.
  smt().
have hupper : x - vk_low_int x < 65536 by smt().
smt().
qed.

lemma egen_low_word_of_int (x : int) :
  0 <= x < q =>
  KeygenM23FinalizeSpec.egen_low_word (W32.of_int x) =
    W32.of_int (vk_low_int x).
proof.
move=> hx.
have hr : 0 <= x %% 2 < 2 by smt(@IntDiv).
have hh : 0 <= (x %/ 2) %% 2 < 2 by smt(@IntDiv).
have hand0 :
    W32.of_int x `&` W32.one = W32.of_int (x %% 2).
+ rewrite w32_and_one W32.to_uint_small.
  + rewrite /q in hx.
    smt().
  done.
have hsar :
    W32.of_int x `|>>` W8.of_int 1 =
      W32.of_int (x %/ 2).
+ rewrite /(`|>>`) W8.of_uintK /=.
  apply w32_sar_nonnegative_of_int.
  + rewrite /q in hx.
    smt().
  smt().
have hegen :
    KeygenM23FinalizeSpec.egen_low_word (W32.of_int x) =
      W32.of_int (x %% 2) -
        ((W32.of_int (x %/ 2) `&` W32.of_int (x %% 2))
          `<<` W8.of_int 1).
+ by rewrite /KeygenM23FinalizeSpec.egen_low_word hand0 hsar.
rewrite hegen.
have hrcases : x %% 2 = 0 \/ x %% 2 = 1.
+ have hrange' : 0 <= x %% 2 < 2.
  + apply modz_cmp.
    smt().
  smt().
rewrite w32_and_bit 1:hrcases W32.to_uint_small.
+ rewrite /q in hx.
  have hxdiv : 0 <= x %/ 2 <= x by smt(@IntDiv).
  smt().
rewrite W32.shl_shlw 1:/# W32.shlMP 1:/# /=.
rewrite vk_low_int_formula.
congr.
ring.
qed.

lemma egen_high_word_of_int (x : int) :
  0 <= x < q =>
  KeygenM23FinalizeSpec.egen_high_word (W32.of_int x) =
    W32.of_int (vk_high_int x).
proof.
move=> hx.
rewrite /KeygenM23FinalizeSpec.egen_high_word
        egen_low_word_of_int 1:hx
        W32.of_intS'.
have hl := vk_low_int_range x.
have harg : 0 <= x - vk_low_int x < 2147483648.
+ rewrite /q in hx.
  case (x = 0).
  + move=> ->.
    by rewrite /vk_low_int.
  smt().
rewrite /(`|>>`) W8.of_uintK /=.
rewrite w32_sar_nonnegative_of_int 1:harg 1:/#.
by rewrite /vk_high_int.
qed.

lemma egen_low_word_semantics (b : W32.t) :
  W32.to_uint b < q =>
  KeygenM23FinalizeSpec.egen_low_word b =
    W32.of_int (vk_low_int (W32.to_uint b)).
proof.
move=> hb.
rewrite -{1}(W32.to_uintK b).
apply egen_low_word_of_int.
rewrite /q in hb.
smt(W32.to_uint_cmp).
qed.

lemma egen_high_word_semantics (b : W32.t) :
  W32.to_uint b < q =>
  KeygenM23FinalizeSpec.egen_high_word b =
    W32.of_int (vk_high_int (W32.to_uint b)).
proof.
move=> hb.
rewrite -{1}(W32.to_uintK b).
apply egen_high_word_of_int.
rewrite /q in hb.
smt(W32.to_uint_cmp).
qed.

lemma egen_low_word_to_sint (b : W32.t) :
  W32.to_uint b < q =>
  W32.to_sint (KeygenM23FinalizeSpec.egen_low_word b) =
    vk_low_int (W32.to_uint b).
proof.
move=> hb.
rewrite egen_low_word_semantics 1:hb.
apply W32.to_sintK_small.
have hl := vk_low_int_range (W32.to_uint b).
smt().
qed.

lemma egen_high_word_to_sint (b : W32.t) :
  W32.to_uint b < q =>
  W32.to_sint (KeygenM23FinalizeSpec.egen_high_word b) =
    vk_high_int (W32.to_uint b).
proof.
move=> hb.
rewrite egen_high_word_semantics 1:hb.
apply W32.to_sintK_small.
have hh := vk_high_int_range (W32.to_uint b).
+ rewrite /q in hb.
  smt(W32.to_uint_cmp).
qed.

lemma frozen_sum_word_semantics (b s2 a : W32.t) :
  Fq.bw32 ((b + s2) + a) 18 =>
  KeygenM23FinalizeSpec.frozen_sum_word b s2 a =
    W32.of_int (W32.to_sint ((b + s2) + a) %% q).
proof.
move=> hsum.
rewrite /KeygenM23FinalizeSpec.frozen_sum_word.
exact (freeze_word_semantics ((b + s2) + a) hsum).
qed.

lemma finalize_words_semantics (b s2 a : W32.t) :
  Fq.bw32 ((b + s2) + a) 18 =>
  let x = W32.to_sint ((b + s2) + a) %% q in
  KeygenM23FinalizeSpec.finalize_b_word b s2 a =
    W32.of_int (vk_high_int x) /\
  KeygenM23FinalizeSpec.finalize_s2_word b s2 a =
    s2 - W32.of_int (vk_low_int x).
proof.
move=> hsum /=.
have hx :
    0 <= W32.to_sint ((b + s2) + a) %% q < q.
+ apply modz_cmp.
  rewrite /q.
  smt().
split.
+ rewrite /KeygenM23FinalizeSpec.finalize_b_word
          frozen_sum_word_semantics 1:hsum.
  apply egen_high_word_of_int.
  exact hx.
+ rewrite /KeygenM23FinalizeSpec.finalize_s2_word
          frozen_sum_word_semantics 1:hsum.
  rewrite egen_low_word_of_int 1:hx.
  trivial.
qed.

end KeygenM23FinalizeSemantics.
