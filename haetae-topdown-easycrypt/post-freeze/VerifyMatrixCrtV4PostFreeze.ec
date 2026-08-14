require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCrtFreezeMode2PostFreeze
               VerifyMatrixCrtCompositionPostFreeze.
require import Fq KeygenM23FinalizeSemantics.

import VerifyCrtFreezeMode2PostFreeze
       VerifyMatrixCrtCompositionPostFreeze.

theory VerifyMatrixCrtV4PostFreeze.

(* This theory gives the actual mode-2 CRT/freeze output its integer meaning.
   It does not identify the unpacked verification matrix with paper A1, and it
   does not establish the prepare-stage provenance of [wprime]. *)

op v4_q : int = 64513.
op v4_q2 : int = 2 * v4_q.
op v4_q2rec : int = 33287.
op v4_radix : int = 4294967296.
op v4_sar_bound : int = v4_q2 + 4.

lemma v4_q2E : v4_q2 = 129026.
proof. by rewrite /v4_q2 /v4_q. qed.

lemma v4_barrett_residue_range (z : int) :
  -262144 <= z < 262144 =>
  let t = (z * v4_q2rec) %/ v4_radix in
  let x = z - t * v4_q2 in
  -4 <= x <= v4_q2 + 4 /\ x %% v4_q2 = z %% v4_q2.
proof.
rewrite /v4_q2 /v4_q /v4_q2rec /v4_radix.
move=> hz /=.
pose k := z %/ 129026.
pose r := z %% 129026.
have hq : z = k * 129026 + r.
+ rewrite /k /r.
  exact (divz_eq z 129026).
have hr : 0 <= r < 129026.
+ rewrite /r.
  smt().
have hk : -3 <= k <= 2 by smt().
have hprod :
    z * 33287 =
      k * 4294967296 + (r * 33287 - k * 78834) by smt().
rewrite hprod divzMDl 1:/#.
case (r * 33287 - k * 78834 < 0).
+ move=> hneg.
  have hdelta :
      -4294967296 <= r * 33287 - k * 78834 < 0 by smt().
  have hdiv :
      (r * 33287 - k * 78834) %/ 4294967296 = -1.
  + have hshift :
        r * 33287 - k * 78834 =
          (-1) * 4294967296 +
          (4294967296 + r * 33287 - k * 78834) by ring.
    rewrite hshift divzMDl 1:/#.
    have hrem :
        0 <= 4294967296 + r * 33287 - k * 78834 <
          4294967296 by smt().
    by rewrite divz_small 1:/#.
  rewrite hdiv.
  have hx : z - (k - 1) * 129026 = r + 129026 by smt().
  rewrite hx.
  split; first smt().
  rewrite (_ : r + 129026 = 1 * 129026 + r) 1:/#.
  rewrite modzMDl.
  by rewrite /r modz_mod.
case (4294967296 <= r * 33287 - k * 78834).
+ move=> hlarge hnonneg.
  have hdelta :
      4294967296 <= r * 33287 - k * 78834 <
        2 * 4294967296 by smt().
  have hdiv :
      (r * 33287 - k * 78834) %/ 4294967296 = 1.
  + have hshift :
        r * 33287 - k * 78834 =
          1 * 4294967296 +
          (r * 33287 - k * 78834 - 4294967296) by ring.
    rewrite hshift divzMDl 1:/#.
    have hrem :
        0 <= r * 33287 - k * 78834 - 4294967296 <
          4294967296 by smt().
    by rewrite divz_small 1:/#.
  rewrite hdiv.
  have hx : z - (k + 1) * 129026 = r - 129026 by smt().
  rewrite hx.
  split; first smt().
  rewrite (_ : r - 129026 = (-1) * 129026 + r) 1:/#.
  rewrite modzMDl.
  by rewrite /r modz_mod.
move=> hsmall hnonneg.
have hdiv :
    (r * 33287 - k * 78834) %/ 4294967296 = 0.
+ rewrite divz_small.
  + apply bound_abs.
    smt().
  trivial.
rewrite hdiv.
have hx : z - k * 129026 = r by smt().
rewrite hx.
split; first smt().
by rewrite /r modz_mod.
qed.

lemma v4_bit62_eq_bit63_small (z : int) :
  -v4_sar_bound <= z <= v4_sar_bound =>
  (W64.of_int z).[62] = (W64.of_int z).[63].
proof.
move=> hz.
rewrite !W64.of_intwE /W64.int_bit /v4_sar_bound /v4_q2 /v4_q /=.
smt(@IntDiv).
qed.

lemma v4_sar31_sar32_double_small (z : int) :
  -v4_sar_bound <= z <= v4_sar_bound =>
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
rewrite v4_bit62_eq_bit63_small 1:hz.
done.
qed.

lemma v4_sar31_nonnegative (z : int) :
  0 <= z <= v4_sar_bound =>
  W64.sar (W64.of_int z) 31 = W64.zero.
proof.
move=> hz.
rewrite v4_sar31_sar32_double_small 1:/#.
have hsint : W64.to_sint (W64.of_int (2 * z)) = 2 * z.
+ apply W64.to_sintK_small.
  rewrite /v4_sar_bound /v4_q2 /v4_q in hz.
  smt().
have hdiv : (2 * z) %/ 2 ^ 32 = 0.
+ rewrite /v4_sar_bound /v4_q2 /v4_q in hz.
  smt(@IntDiv).
have hsem := Fq.SAR_sem32 (W64.of_int (2 * z)).
rewrite /(`|>>`) W8.of_uintK /= hsint hdiv in hsem.
exact hsem.
qed.

lemma v4_sar31_negative (z : int) :
  -v4_sar_bound <= z < 0 =>
  W64.sar (W64.of_int z) 31 = W64.of_int (-1).
proof.
move=> hz.
rewrite v4_sar31_sar32_double_small 1:/#.
have hsint : W64.to_sint (W64.of_int (2 * z)) = 2 * z.
+ apply W64.to_sintK_small.
  rewrite /v4_sar_bound /v4_q2 /v4_q in hz.
  smt().
have hdiv : (2 * z) %/ 2 ^ 32 = -1.
+ rewrite /v4_sar_bound /v4_q2 /v4_q in hz.
  smt(@IntDiv).
have hsem := Fq.SAR_sem32 (W64.of_int (2 * z)).
rewrite /(`|>>`) W8.of_uintK /= hsint hdiv in hsem.
exact hsem.
qed.

lemma v4_word_sar31_nonnegative (z : int) :
  0 <= z <= v4_sar_bound =>
  W64.of_int z `|>>` W8.of_int 31 = W64.zero.
proof.
move=> hz.
rewrite /(`|>>`) W8.of_uintK /=.
exact (v4_sar31_nonnegative z hz).
qed.

lemma v4_word_sar31_negative (z : int) :
  -v4_sar_bound <= z < 0 =>
  W64.of_int z `|>>` W8.of_int 31 = W64.of_int (-1).
proof.
move=> hz.
rewrite /(`|>>`) W8.of_uintK /=.
exact (v4_sar31_negative z hz).
qed.

lemma v4_barrett_shift_word (z : int) :
  -262144 <= z < 262144 =>
  W64.of_int (z * v4_q2rec) `|>>` W8.of_int 32 =
    W64.of_int ((z * v4_q2rec) %/ v4_radix).
proof.
move=> hz.
rewrite Fq.SAR_sem32.
have hsmall :
    W64.min_sint <= z * v4_q2rec <= W64.max_sint.
+ rewrite /v4_q2rec.
  smt().
congr.
rewrite W64.to_sintK_small 1:hsmall.
by rewrite /v4_radix.
qed.

lemma v4_barrett_word_semantics (a : W32.t) :
  Fq.bw32 a 18 =>
  sigextu64 a -
    ((sigextu64 a * W64.of_int v4_q2rec `|>>` W8.of_int 32) *
      W64.of_int v4_q2) =
    W64.of_int
      (W32.to_sint a -
        ((W32.to_sint a * v4_q2rec) %/ v4_radix) * v4_q2).
proof.
move=> ha.
have hz : -262144 <= W32.to_sint a < 262144.
+ rewrite /Fq.bw32 in ha.
  move: ha.
  by rewrite /=.
rewrite KeygenM23FinalizeSemantics.sigextu64_semantics
        W64.of_intM'
        v4_barrett_shift_word 1:hz
        W64.of_intM'
        W64.of_intS'.
congr.
qed.

lemma v4_w64_of_int_minus_one :
  W64.of_int (-1) = W64.onew.
proof. by rewrite /W64.onew. qed.

lemma freeze2q_word_semantics (a : W32.t) :
  Fq.bw32 a 18 =>
  freeze2q_word a = W32.of_int (W32.to_sint a %% v4_q2).
proof.
move=> ha.
pose z := W32.to_sint a.
pose t := (z * v4_q2rec) %/ v4_radix.
pose x := z - t * v4_q2.
have hz : -262144 <= z < 262144.
+ rewrite /z /Fq.bw32 in ha.
  move: ha.
  by rewrite /=.
have hx := v4_barrett_residue_range z hz.
rewrite /t /x in hx.
have hxrange : -4 <= x <= v4_q2 + 4 by smt().
have hxmod : x %% v4_q2 = z %% v4_q2 by smt().
rewrite /freeze2q_word /=.
rewrite v4_barrett_word_semantics 1:ha.
rewrite -/t -/x.
case (x < 0).
+ move=> hxneg.
  rewrite v4_word_sar31_negative 1:/#.
  rewrite v4_w64_of_int_minus_one W64.andwC W64.andw1.
  rewrite W64.of_intD'.
  pose y := x + 2 * v4_q2.
  have hyrange : v4_q2 <= y < 2 * v4_q2 by
    rewrite /y; smt().
  rewrite -/y.
  rewrite !W64.of_intS'.
  rewrite v4_word_sar31_nonnegative 1:/#.
  rewrite /truncateu32 /zeroextu64 /=.
  rewrite W64.to_uint_small.
  + rewrite /v4_q2 /v4_q in hyrange.
    smt().
  congr.
  rewrite -hxmod /y.
  have hcanon :
      (x + v4_q2) %% v4_q2 = x + v4_q2.
  + apply modz_small.
    rewrite /v4_q2 /v4_q in hxrange.
    smt().
  have hperiod :
      (x + v4_q2) %% v4_q2 = x %% v4_q2.
  + rewrite (_ : x + v4_q2 = 1 * v4_q2 + x) 1:/#.
    by rewrite modzMDl.
  smt().
move=> hxnonneg.
rewrite v4_word_sar31_nonnegative 1:/#.
rewrite W64.and0w W64.addr0_s !W64.of_intS'.
case (x < v4_q2).
+ move=> hxlt.
  rewrite v4_word_sar31_negative 1:/#.
  rewrite /truncateu32 /zeroextu64 /=.
  rewrite W64.to_uint_small.
  + rewrite /v4_q2 /v4_q in hxrange.
    smt().
  congr.
  rewrite -hxmod modz_small.
  + rewrite /v4_q2 /v4_q in hxrange.
    smt().
  trivial.
move=> hxnlt.
rewrite v4_word_sar31_nonnegative 1:/#.
rewrite /truncateu32 /zeroextu64 /=.
rewrite W64.to_uint_small.
+ rewrite /v4_q2 /v4_q in hxrange.
  smt().
congr.
rewrite -hxmod.
have hcanon :
    (x - v4_q2) %% v4_q2 = x - v4_q2.
+ apply modz_small.
  rewrite /v4_q2 /v4_q in hxrange.
  smt().
have hperiod :
    (x - v4_q2) %% v4_q2 = x %% v4_q2.
+ rewrite (_ : x - v4_q2 = (-1) * v4_q2 + x) 1:/#.
  by rewrite modzMDl.
smt().
qed.

lemma freeze2q_word_to_uint (a : W32.t) :
  Fq.bw32 a 18 =>
  W32.to_uint (freeze2q_word a) = W32.to_sint a %% v4_q2.
proof.
move=> ha.
rewrite freeze2q_word_semantics 1:ha.
apply W32.to_uint_small.
have hmod : 0 <= W32.to_sint a %% v4_q2 < v4_q2.
+ apply modz_cmp.
  rewrite /v4_q2 /v4_q.
  smt().
rewrite /v4_q2 /v4_q in hmod.
smt().
qed.

lemma freeze2q_word_canonical (a : W32.t) :
  Fq.bw32 a 18 =>
  0 <= W32.to_uint (freeze2q_word a) < v4_q2.
proof.
move=> ha.
rewrite freeze2q_word_to_uint 1:ha.
apply modz_cmp.
rewrite /v4_q2 /v4_q.
smt().
qed.

op v4_bitword (b : bool) : W32.t =
  if b then W32.one else W32.zero.

op v4_target_bit (wprimep : BArray1024.t) (idx : int) : bool =
  if 0 <= idx < mode2_row_words then
    (BArray1024.get32 wprimep idx).[0]
  else false.

op v4_selector_bit
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) : bool =
  (BArray8192.get32 highp idx).[0] <> v4_target_bit wprimep idx.

op v4_selector_int
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) : int =
  if v4_selector_bit highp wprimep idx then 1 else 0.

op v4_raw_lift_int
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) : int =
  W32.to_sint (BArray8192.get32 highp idx) +
  v4_q * v4_selector_int highp wprimep idx.

op v4_lift_int
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) : int =
  v4_raw_lift_int highp wprimep idx %% v4_q2.

lemma v4_q_dvd_q2 : v4_q %| v4_q2.
proof.
apply/dvdzP.
exists 2.
by rewrite /v4_q2.
qed.

lemma v4_two_dvd_q2 : 2 %| v4_q2.
proof.
apply/dvdzP.
exists v4_q.
rewrite /v4_q2.
ring.
qed.

lemma v4_lift_canonical
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  0 <= v4_lift_int highp wprimep idx < v4_q2.
proof.
rewrite /v4_lift_int.
apply modz_cmp.
rewrite /v4_q2 /v4_q.
smt().
qed.

lemma v4_lift_mod_q
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  v4_lift_int highp wprimep idx %% v4_q =
    W32.to_sint (BArray8192.get32 highp idx) %% v4_q.
proof.
rewrite /v4_lift_int modz_dvd 1:v4_q_dvd_q2.
rewrite /v4_raw_lift_int.
rewrite (_ :
  W32.to_sint (BArray8192.get32 highp idx) +
    v4_q * v4_selector_int highp wprimep idx =
  v4_selector_int highp wprimep idx * v4_q +
    W32.to_sint (BArray8192.get32 highp idx)) 1:/#.
by rewrite modzMDl.
qed.

lemma v4_w32_to_uint_mod2 (w : W32.t) :
  W32.to_uint w %% 2 = if w.[0] then 1 else 0.
proof.
rewrite -(W32.b2i_get w 0) 1:/# /= /b2i.
case w.[0]; trivial.
qed.

lemma v4_w32_to_sint_mod2 (w : W32.t) :
  W32.to_sint w %% 2 = if w.[0] then 1 else 0.
proof.
rewrite /W32.to_sint /W32.smod.
case (2 ^ (W32.size - 1) <= W32.to_uint w) => hsign.
+ rewrite (_ : W32.modulus = 4294967296) 1://.
  rewrite (_ :
    W32.to_uint w - 4294967296 =
      (-2147483648) * 2 + W32.to_uint w) 1:/#.
  rewrite modzMDl.
  exact (v4_w32_to_uint_mod2 w).
+ exact (v4_w32_to_uint_mod2 w).
qed.

lemma v4_xor_lift_mod2 (z : int) (high_bit target_bit : bool) :
  z %% 2 = (if high_bit then 1 else 0) =>
  (z + v4_q * (if high_bit <> target_bit then 1 else 0)) %% 2 =
    if target_bit then 1 else 0.
proof.
case high_bit => hhigh.
+ case target_bit => htarget.
  + move=> hparity.
    by rewrite /=.
  + move=> hparity.
    by rewrite /= /v4_q -modzDm hparity /=.
+ case target_bit => htarget.
  + move=> hparity.
    by rewrite /= /v4_q -modzDm hparity /=.
  + move=> hparity.
    by rewrite /=.
qed.

lemma v4_raw_lift_mod2
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  v4_raw_lift_int highp wprimep idx %% 2 =
    if v4_target_bit wprimep idx then 1 else 0.
proof.
rewrite /v4_raw_lift_int /v4_selector_int /v4_selector_bit.
apply
  (v4_xor_lift_mod2
    (W32.to_sint (BArray8192.get32 highp idx))
    (BArray8192.get32 highp idx).[0]
    (v4_target_bit wprimep idx)).
exact (v4_w32_to_sint_mod2 (BArray8192.get32 highp idx)).
qed.

lemma v4_lift_mod2
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  v4_lift_int highp wprimep idx %% 2 =
    if v4_target_bit wprimep idx then 1 else 0.
proof.
rewrite /v4_lift_int modz_dvd 1:v4_two_dvd_q2.
exact (v4_raw_lift_mod2 highp wprimep idx).
qed.

lemma v4_bitword_bit (b : bool) (bit : int) :
  0 <= bit < 32 => (v4_bitword b).[bit] = (bit = 0 /\ b).
proof.
move=> hbit.
case b => hb.
+ rewrite /v4_bitword /= W32.nth_one; trivial.
+ rewrite /v4_bitword /=; trivial.
qed.

lemma v4_and_one_is_bitword (w : W32.t) :
  w `&` W32.one = v4_bitword w.[0].
proof.
apply W32.ext_eq => k hk.
rewrite W32.andwE W32.nth_one (v4_bitword_bit w.[0] k hk).
smt().
qed.

lemma v4_xor_and_one_is_bitword (lft rgt : W32.t) :
  (lft `^` rgt) `&` W32.one =
    v4_bitword (lft.[0] <> rgt.[0]).
proof.
apply W32.ext_eq => k hk.
rewrite W32.andwE W32.xorwE W32.nth_one
        (v4_bitword_bit (lft.[0] <> rgt.[0]) k hk).
smt().
qed.

lemma v4_w32_of_int_minus_one :
  W32.of_int (-1) = W32.onew.
proof. by rewrite /W32.onew. qed.

lemma v4_w32_max_uint_onew :
  W32.of_int 4294967295 = W32.onew.
proof. by rewrite /W32.onew. qed.

lemma v4_w32_of_sintK (w : W32.t) :
  W32.of_int (W32.to_sint w) = w.
proof.
rewrite /W32.to_sint /W32.smod.
case (2 ^ (W32.size - 1) <= W32.to_uint w) => _.
+ by rewrite -W32.of_intS' W32.to_uintK'
             W32.of_int_modulus subr0.
+ by rewrite W32.to_uintK'.
qed.

lemma v4_select_q_word (b : bool) :
  (W32.zero - v4_bitword b) `&` W32.of_int 64513 =
    W32.of_int (v4_q * (if b then 1 else 0)).
proof.
case b => hb.
+ rewrite /v4_bitword /= v4_w32_max_uint_onew.
  rewrite W32.andwC W32.andw1.
  by rewrite /v4_q.
+ rewrite /v4_bitword /=.
  by rewrite /v4_q.
qed.

lemma mode2_fromcrt_add_xor_semantics (high wprime : W32.t) :
  mode2_fromcrt_add_xor high wprime =
    W32.of_int
      (v4_q * (if high.[0] <> wprime.[0] then 1 else 0)).
proof.
rewrite /mode2_fromcrt_add_xor v4_xor_and_one_is_bitword.
exact (v4_select_q_word (high.[0] <> wprime.[0])).
qed.

lemma mode2_fromcrt_add_high_semantics (high : W32.t) :
  mode2_fromcrt_add_high high =
    W32.of_int (v4_q * (if high.[0] then 1 else 0)).
proof.
rewrite /mode2_fromcrt_add_high v4_and_one_is_bitword.
exact (v4_select_q_word high.[0]).
qed.

lemma mode2_fromcrt_word_semantics
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  0 <= idx < mode2_active_words =>
  mode2_fromcrt_word highp wprimep idx =
    W32.of_int (v4_raw_lift_int highp wprimep idx).
proof.
move=> [hidx0 hidxmax].
rewrite /mode2_fromcrt_word /v4_raw_lift_int
        /v4_selector_int /v4_selector_bit /v4_target_bit.
case (idx < mode2_row_words) => hrow0.
+ rewrite hidx0 /=.
  rewrite mode2_fromcrt_add_xor_semantics.
  rewrite -(v4_w32_of_sintK (BArray8192.get32 highp idx)).
  rewrite W32.of_intD'.
  by rewrite !v4_w32_of_sintK.
have hsecond : mode2_row_words <= idx < mode2_active_words.
+ split.
  + by rewrite lezNgt hrow0.
  + move=> _.
    exact hidxmax.
rewrite hidx0 /= ifT 1:hsecond /=.
rewrite mode2_fromcrt_add_high_semantics.
rewrite -(v4_w32_of_sintK (BArray8192.get32 highp idx)).
rewrite W32.of_intD'.
rewrite !v4_w32_of_sintK.
case ((BArray8192.get32 highp idx).[0]); trivial.
qed.

lemma v4_raw_lift_bound18
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  Fq.bw32 (BArray8192.get32 highp idx) 16 =>
  -262144 <= v4_raw_lift_int highp wprimep idx < 262144.
proof.
rewrite /Fq.bw32 /v4_raw_lift_int /v4_selector_int /v4_q.
move=> hbound.
case (v4_selector_bit highp wprimep idx); smt().
qed.

lemma mode2_fromcrt_word_bound18
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  0 <= idx < mode2_active_words =>
  Fq.bw32 (BArray8192.get32 highp idx) 16 =>
  Fq.bw32 (mode2_fromcrt_word highp wprimep idx) 18.
proof.
move=> hidx hbound.
rewrite mode2_fromcrt_word_semantics 1:hidx /Fq.bw32.
have hraw := v4_raw_lift_bound18 highp wprimep idx hbound.
rewrite W32.to_sintK_small 1:/# /=.
rewrite -andaE.
exact hraw.
qed.

lemma mode2_fromcrt_word_to_sint
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  0 <= idx < mode2_active_words =>
  Fq.bw32 (BArray8192.get32 highp idx) 16 =>
  W32.to_sint (mode2_fromcrt_word highp wprimep idx) =
    v4_raw_lift_int highp wprimep idx.
proof.
move=> hidx hbound.
rewrite mode2_fromcrt_word_semantics 1:hidx.
apply W32.to_sintK_small.
have hraw := v4_raw_lift_bound18 highp wprimep idx hbound.
smt().
qed.

lemma freeze2q_fromcrt_v4_semantics
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) :
  0 <= idx < mode2_active_words =>
  Fq.bw32 (BArray8192.get32 highp idx) 16 =>
  W32.to_uint
    (freeze2q_word (mode2_fromcrt_word highp wprimep idx)) =
    v4_lift_int highp wprimep idx.
proof.
move=> hidx hbound.
rewrite freeze2q_word_to_uint.
+ exact (mode2_fromcrt_word_bound18 highp wprimep idx hidx hbound).
rewrite mode2_fromcrt_word_to_sint 1:hidx 1:hbound.
trivial.
qed.

op v4_crt_semantics
    (out high : BArray8192.t) (wprime : BArray1024.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    W32.to_uint (BArray8192.get32 out i) =
      v4_lift_int high wprime i /\
    0 <= W32.to_uint (BArray8192.get32 out i) < v4_q2 /\
    W32.to_uint (BArray8192.get32 out i) %% v4_q =
      W32.to_sint (BArray8192.get32 high i) %% v4_q /\
    W32.to_uint (BArray8192.get32 out i) %% 2 =
      (if v4_target_bit wprime i then 1 else 0).

lemma crt_freeze_prefix_v4_semantics
    (out high : BArray8192.t) (wprime : BArray1024.t) :
  (forall i, 0 <= i < mode2_active_words =>
    Fq.bw32 (BArray8192.get32 high i) 16) =>
  crt_freeze_prefix out high wprime mode2_active_words =>
  v4_crt_semantics out high wprime mode2_active_words.
proof.
move=> hbound hprefix.
rewrite /v4_crt_semantics => i hi.
have hword := hprefix i hi.
have hcoeff_bound := hbound i hi.
have hexact :=
  freeze2q_fromcrt_v4_semantics high wprime i hi hcoeff_bound.
rewrite hword.
split; first exact hexact.
split.
+ rewrite hexact.
  exact (v4_lift_canonical high wprime i).
split.
+ rewrite hexact.
  exact (v4_lift_mod_q high wprime i).
+ rewrite hexact.
  exact (v4_lift_mod2 high wprime i).
qed.

op verify_matrix_crt_mode2_v4_result
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (out high : BArray8192.t) : bool =
  verify_matrix_crt_mode2_result
    z10 high0 a10 wprime0 out high /\
  v4_crt_semantics out high wprime0 mode2_active_words.

lemma verify_matrix_crt_mode2_result_v4
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (out high : BArray8192.t) :
  verify_matrix_crt_mode2_result
    z10 high0 a10 wprime0 out high =>
  verify_matrix_crt_mode2_v4_result
    z10 high0 a10 wprime0 out high.
proof.
move=> hresult.
rewrite /verify_matrix_crt_mode2_v4_result.
split; first exact hresult.
have hbound :=
  verify_matrix_crt_mode2_result_active_bound16
    z10 high0 a10 wprime0 out high hresult.
move: hresult.
rewrite /verify_matrix_crt_mode2_result.
move=> [transformed [hforward [hrow0 [hrow1 [hprefix hrest]]]]].
exact (crt_freeze_prefix_v4_semantics out high wprime0 hbound hprefix).
qed.

lemma verify_matrix_crt_mode2_v4_crt_mixed_exact
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [ActualVerifyMatrixCrtMode2.run :
    z1p = z10 /\ highp = high0 /\
    a1p = a10 /\ wprimep = wprime0 /\
    VerifyMatrixCrtPostFreeze.VerifyMatrixCrtPostFreeze.verify_mode2_input_repr_bound16
      z10 p0 p1 p2 p3 /\
    VerifyMatrixCrtPostFreeze.VerifyMatrixCrtPostFreeze.verify_mode2_matrix_repr_bound20_17
      a10
    ==>
    verify_matrix_crt_mode2_v4_result
      z10 high0 a10 wprime0 res.`1 res.`2].
proof.
conseq
  (verify_matrix_crt_mode2_fromcrt_freeze_mixed_exact
    z10 high0 a10 wprime0 p0 p1 p2 p3).
move=> &hr _ result hresult.
exact
  (verify_matrix_crt_mode2_result_v4
    z10 high0 a10 wprime0 result.`1 result.`2 hresult).
qed.

lemma verify_matrix_crt_mode2_v4_crt_exact
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [ActualVerifyMatrixCrtMode2.run :
    z1p = z10 /\ highp = high0 /\
    a1p = a10 /\ wprimep = wprime0 /\
    VerifyMatrixCrtPostFreeze.VerifyMatrixCrtPostFreeze.verify_mode2_input_repr_bound16
      z10 p0 p1 p2 p3 /\
    VerifyMatrixCrtPostFreeze.VerifyMatrixCrtPostFreeze.verify_mode2_matrix_repr_bound16
      a10
    ==>
    verify_matrix_crt_mode2_v4_result
      z10 high0 a10 wprime0 res.`1 res.`2].
proof.
conseq
  (verify_matrix_crt_mode2_v4_crt_mixed_exact
    z10 high0 a10 wprime0 p0 p1 p2 p3) => //=.
move=> &m [hz1 [hhigh [hmat [hwprime [hinput hbound16]]]]].
split; first exact hz1.
split; first exact hhigh.
split; first exact hmat.
split; first exact hwprime.
split; first exact hinput.
exact
  (VerifyMatrixCrtPostFreeze.VerifyMatrixCrtPostFreeze.verify_mode2_matrix_repr_bound16_to_bound20_17
    a10 hbound16).
qed.

end VerifyMatrixCrtV4PostFreeze.
