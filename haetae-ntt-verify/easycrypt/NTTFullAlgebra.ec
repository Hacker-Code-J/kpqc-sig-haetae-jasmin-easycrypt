require import AllCore IntDiv List Ring StdOrder BitEncoding.

require import Array256.
require import GFq Rq.
require import NTT_Fq NTTFullSpec.

import Zq IntOrder BitReverse.

theory NTTFullAlgebra.

type poly = coeff Array256.t.

lemma exp_zroot_512 :
  Zq.exp zroot 512 = Zq.one.
proof.
have -> : 512 = 256 + 256 by ring.
rewrite (ZqField.exprD_nneg zroot 256 256) 1,2://.
rewrite NTT_Fq.exp_zroot_256.
by rewrite -incoeffM_mod /q /=.
qed.

lemma incoeff_m1 :
  incoeff (-1) = -Zq.one.
proof.
by rewrite incoeffN /Zq.one.
qed.

lemma exp_zroot_512_mul n :
  Zq.exp zroot (512 * n) = Zq.one.
proof.
by rewrite ZqField.exprM exp_zroot_512 ZqRing.expr1z.
qed.

lemma exp_zroot_dvd512 e :
  512 %| e =>
  Zq.exp zroot e = Zq.one.
proof.
move=> /dvdzP [n ->].
have -> : n * 512 = 512 * n by ring.
by rewrite exp_zroot_512_mul.
qed.

lemma exp_zroot_mod512 e n :
  Zq.exp zroot (e + 512 * n) = Zq.exp zroot e.
proof.
rewrite ZqRing.exprD 1:NTT_Fq.unit_zroot.
by rewrite exp_zroot_512_mul ZqRing.mulr1.
qed.

lemma exp_zroot_m256 :
  Zq.exp zroot (-256) = incoeff (-1).
proof.
have -> : -256 = 256 + 512 * (-1) by ring.
by rewrite exp_zroot_mod512 NTT_Fq.exp_zroot_256.
qed.

lemma pow2_div k :
  k \in range 0 8 =>
  2 ^ 7 %/ 2 ^ k = 2 ^ (7 - k).
proof.
move=> hk.
rewrite expz_div.
+ by rewrite mem_range in hk; smt().
+ by [].
by [].
qed.

lemma div256_pow2 k :
  k \in range 0 8 =>
  256 %/ 2 ^ k = 2 ^ (8 - k).
proof.
move=> hk.
have h256 : 256 = (2 ^ 8) by smt().
rewrite h256.
rewrite expz_div.
+ by rewrite mem_range in hk; smt().
+ by [].
by [].
qed.

lemma pow2S k :
  0 <= k =>
  2 ^ (k + 1) = 2 * 2 ^ k.
proof. by move=> hk; rewrite exprS. qed.

lemma div256_pair_range k bsj :
  k \in range 0 8 =>
  bsj \in range 0 (2 ^ (7 - k)) =>
  bsj * 2 \in range 0 (256 %/ 2 ^ k) /\
  bsj * 2 + 1 \in range 0 (256 %/ 2 ^ k).
proof.
move=> hk hbsj.
rewrite (div256_pow2 k hk).
have hpow : 2 ^ (8 - k) = 2 * 2 ^ (7 - k).
+ have h7k : 0 <= 7 - k by rewrite mem_range in hk; smt().
  have -> : 8 - k = 7 - k + 1 by ring.
  by rewrite pow2S.
rewrite hpow.
rewrite mem_range in hbsj.
rewrite !mem_range.
smt().
qed.

lemma bsrev_add_pow2 k i :
  k \in range 0 8 =>
  i \in range 0 (2 ^ k) =>
  bsrev 8 (2 ^ k + i) = 2 ^ (7 - k) + bsrev 8 i.
proof.
move=> hk hi.
rewrite addrC (bsrev_add k 8 i 1).
+ by rewrite mem_range in hk; smt().
+ by exact hi.
rewrite bsrev1 1:/#.
by rewrite pow2_div // addrC.
qed.

lemma bsrev_stage_index k ks :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  bsrev 8 (2 ^ k + ks) = (2 * bsrev k ks + 1) * 2 ^ (7 - k).
proof.
move=> hk hks.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hk8 : k <= 8 by rewrite mem_range in hk; smt().
have hk7 : k <= 7 by rewrite mem_range in hk; smt().
rewrite (bsrev_cat k 8 (2 ^ k + ks)).
+ by split.
have hdiv : (2 ^ k + ks) %/ 2 ^ k = 1.
+ rewrite -{1}(mul1r (2 ^ k)) divzMDl.
  + by rewrite gtr_eqF // expr_gt0.
  by rewrite divz_small; rewrite mem_range in hks; smt().
have hmod : (2 ^ k + ks) %% 2 ^ k = ks.
+ rewrite -{1}(mul1r (2 ^ k)) modzMDl.
  by rewrite modz_small; rewrite mem_range in hks; smt().
have hbsmod : bsrev k (2 ^ k + ks) = bsrev k ks.
+ have h := bsrev_mod k (2 ^ k + ks).
  rewrite hmod in h.
  by rewrite -h.
rewrite hdiv hbsmod bsrev1.
+ by smt().
have hpow : 2 ^ (8 - k) = 2 * 2 ^ (7 - k).
+ have h7k : 0 <= 7 - k by smt().
  have -> : 8 - k = 7 - k + 1 by ring.
  by rewrite pow2S.
rewrite hpow.
ring.
qed.

lemma zetas_stage k ks :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  NTT_Fq.zetas.[2 ^ k + ks] =
  Zq.exp zroot ((2 * bsrev k ks + 1) * 2 ^ (7 - k)).
proof.
move=> hk hks.
rewrite /NTT_Fq.zetas initiE /=.
+ rewrite mem_range in hk.
  rewrite mem_range in hks.
  have hp : 2 ^ k <= 2 ^ 7.
  + by apply StdOrder.IntOrder.ler_weexpn2l; smt().
  smt(expr_ge0).
by rewrite bsrev_stage_index.
qed.

lemma bsrev_extend_zero m x :
  0 <= m =>
  x \in range 0 (2 ^ m) =>
  bsrev (m + 1) x = 2 * bsrev m x.
proof.
move=> hm hx.
rewrite (bsrev_cat m (m + 1) x).
+ by split; smt().
have hdiv : x %/ 2 ^ m = 0 by rewrite divz_small; rewrite mem_range in hx; smt().
rewrite hdiv bsrev0.
have -> : m + 1 - m = 1 by ring.
by rewrite /=.
qed.

lemma bsrev_extend_one m x :
  0 <= m =>
  x \in range 0 (2 ^ m) =>
  bsrev (m + 1) (2 ^ m + x) = 1 + 2 * bsrev m x.
proof.
move=> hm hx.
rewrite (bsrev_cat m (m + 1) (2 ^ m + x)).
+ by split; smt().
have hdiv : (2 ^ m + x) %/ 2 ^ m = 1.
+ rewrite -{1}(mul1r (2 ^ m)) divzMDl.
  + by rewrite gtr_eqF // expr_gt0.
  by rewrite divz_small; rewrite mem_range in hx; smt().
have hmod : (2 ^ m + x) %% 2 ^ m = x.
+ rewrite -{1}(mul1r (2 ^ m)) modzMDl.
  by rewrite modz_small; rewrite mem_range in hx; smt().
have hbsmod : bsrev m (2 ^ m + x) = bsrev m x.
+ have h := bsrev_mod m (2 ^ m + x).
  rewrite hmod in h.
  by rewrite -h.
rewrite hdiv hbsmod bsrev1.
+ by smt().
have -> : m + 1 - m = 1 by ring.
by rewrite /=.
qed.

lemma bsrev_double m x :
  0 <= m =>
  x \in range 0 (2 ^ m) =>
  bsrev (m + 1) (2 * x) = bsrev m x.
proof.
move=> hm hx.
rewrite (bsrev_cat 1 (m + 1) (2 * x)).
+ by split; smt().
have hdiv : (2 * x) %/ 2 = x by smt().
have hmod : (2 * x) %% 2 = 0 by smt().
rewrite hdiv.
have hbsmod : bsrev 1 (2 * x) = bsrev 1 0.
+ have h := bsrev_mod 1 (2 * x).
  rewrite hmod in h.
  by rewrite -h.
rewrite hbsmod bsrev0 /=.
by [].
qed.

lemma bsrev_double_plus1 m x :
  0 <= m =>
  x \in range 0 (2 ^ m) =>
  bsrev (m + 1) (2 * x + 1) = 2 ^ m + bsrev m x.
proof.
move=> hm hx.
rewrite (bsrev_cat 1 (m + 1) (2 * x + 1)).
+ by split; smt().
have hdiv : (2 * x + 1) %/ 2 = x by smt().
have hmod : (2 * x + 1) %% 2 = 1 by smt().
rewrite hdiv.
have hbsmod : bsrev 1 (2 * x + 1) = bsrev 1 1.
+ have h := bsrev_mod 1 (2 * x + 1).
  rewrite hmod in h.
  by rewrite -h.
rewrite hbsmod bsrev1 1:/# /=.
by ring.
qed.

lemma bsrev_ones n :
  0 <= n =>
  bsrev n (2 ^ n - 1) = 2 ^ n - 1.
proof.
elim: n => [|n hn ih].
+ by rewrite expr0 bsrev0.
have hn0 : 0 <= n by smt().
have hrng : 2 ^ n - 1 \in range 0 (2 ^ n).
+ rewrite mem_range.
  by smt(expr_gt0).
have -> : 2 ^ (n + 1) - 1 = 2 ^ n + (2 ^ n - 1).
+ rewrite (pow2S n hn0).
  by ring.
rewrite bsrev_extend_one 1:hn0 1:hrng.
rewrite ih.
by ring.
qed.

lemma bsrev_zbase_index k ks :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  bsrev 8 (256 - 2 ^ (8 - k) + ks) =
    (2 * bsrev (7 - k) ks + 1) * 2 ^ k - 1.
proof.
move=> hk hks.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hk7 : k <= 7 by rewrite mem_range in hk; smt().
have h8k0 : 0 <= 8 - k by smt().
have h7k0 : 0 <= 7 - k by smt().
have hpow : 2 ^ k * 2 ^ (8 - k) = 256.
+ rewrite -exprD_nneg 1:hk0 1:h8k0.
  have -> : k + (8 - k) = 8 by ring.
  by [].
have hbase : 256 - 2 ^ (8 - k) = (2 ^ k - 1) * 2 ^ (8 - k).
+ rewrite -hpow.
  by ring.
rewrite hbase.
rewrite (bsrev_cat (8 - k) 8 ((2 ^ k - 1) * 2 ^ (8 - k) + ks)).
+ by split; smt().
have hks8 : ks \in range 0 (2 ^ (8 - k)).
+ rewrite mem_range in hks.
  rewrite mem_range.
  have hp : 2 ^ (7 - k) <= 2 ^ (8 - k).
  + by apply StdOrder.IntOrder.ler_weexpn2l; smt().
  smt().
have hdiv :
  ((2 ^ k - 1) * 2 ^ (8 - k) + ks) %/ 2 ^ (8 - k) =
  2 ^ k - 1.
+ rewrite divzMDl.
  + by rewrite gtr_eqF // expr_gt0.
  by rewrite divz_small; rewrite mem_range in hks8; smt().
have hmod :
  ((2 ^ k - 1) * 2 ^ (8 - k) + ks) %% 2 ^ (8 - k) = ks.
+ rewrite modzMDl.
  by rewrite modz_small; rewrite mem_range in hks8; smt().
have hbsmod :
  bsrev (8 - k) ((2 ^ k - 1) * 2 ^ (8 - k) + ks) =
  bsrev (8 - k) ks.
+ have h := bsrev_mod (8 - k) ((2 ^ k - 1) * 2 ^ (8 - k) + ks).
  rewrite hmod in h.
  by rewrite -h.
rewrite hdiv hbsmod.
have hbs : bsrev (8 - k) ks = 2 * bsrev (7 - k) ks.
+ have -> : 8 - k = 7 - k + 1 by ring.
  by rewrite bsrev_extend_zero 1:h7k0 1:hks.
rewrite hbs.
have -> : 8 - (8 - k) = k by ring.
rewrite bsrev_ones 1:hk0.
by ring.
qed.

lemma bsrev_stage_pair_low k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  bsrev 8 (bsrev (7 - k) off * 2 ^ (k + 1) + bsrev k ks) =
  ks * 2 ^ (8 - k) + off.
proof.
move=> hk hks hoff.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hk7 : k <= 7 by rewrite mem_range in hk; smt().
pose x := bsrev (7 - k) off * 2 ^ (k + 1) + bsrev k ks.
pose y := ks * 2 ^ (8 - k) + off.
have hy_rng : y \in range 0 256.
+ rewrite /y.
  rewrite mem_range in hks.
  rewrite mem_range in hoff.
  rewrite mem_range.
  have hpow : 2 ^ k * 2 ^ (8 - k) = 256.
  + rewrite -exprD_nneg.
    + by [].
    + by smt().
    have -> : k + (8 - k) = 8 by ring.
    by [].
  smt(expr_ge0 expr_gt0).
have hyy : bsrev 8 (bsrev 8 y) = y.
+ by apply bsrev_involutive.
have hrev_y : bsrev 8 y = x.
+ rewrite /x /y.
  rewrite (bsrev_cat (8 - k) 8 (ks * 2 ^ (8 - k) + off)).
  + by split; smt().
  have hoff8 : off \in range 0 (2 ^ (8 - k)).
  + rewrite mem_range in hoff.
    rewrite mem_range.
    have hp : 2 ^ (7 - k) <= 2 ^ (8 - k).
    + by apply StdOrder.IntOrder.ler_weexpn2l; smt().
    smt().
  have hdiv : (ks * 2 ^ (8 - k) + off) %/ 2 ^ (8 - k) = ks.
  + rewrite divzMDl.
    + by rewrite gtr_eqF // expr_gt0.
    by rewrite divz_small; rewrite mem_range in hoff8; smt().
  have hmod : (ks * 2 ^ (8 - k) + off) %% 2 ^ (8 - k) = off.
  + rewrite modzMDl.
    by rewrite modz_small; rewrite mem_range in hoff8; smt().
  have hbsmod :
    bsrev (8 - k) (ks * 2 ^ (8 - k) + off) = bsrev (8 - k) off.
  + have h := bsrev_mod (8 - k) (ks * 2 ^ (8 - k) + off).
    rewrite hmod in h.
    by rewrite -h.
  rewrite hdiv hbsmod.
  rewrite (bsrev_extend_zero (7 - k) off).
  + by smt().
  + exact hoff.
  have -> : 8 - (8 - k) = k by ring.
  rewrite pow2S //.
  ring.
by rewrite -hyy hrev_y.
qed.

lemma bsrev_stage_pair_high k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  bsrev 8 (bsrev (7 - k) off * 2 ^ (k + 1) + (2 ^ k + bsrev k ks)) =
  ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off).
proof.
move=> hk hks hoff.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hk7 : k <= 7 by rewrite mem_range in hk; smt().
pose x := bsrev (7 - k) off * 2 ^ (k + 1) + (2 ^ k + bsrev k ks).
pose y := ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off).
have hy_rng : y \in range 0 256.
+ rewrite /y.
  rewrite mem_range in hks.
  rewrite mem_range in hoff.
  rewrite mem_range.
  have hpow : 2 ^ k * 2 ^ (8 - k) = 256.
  + rewrite -exprD_nneg.
    + by [].
    + by smt().
    have -> : k + (8 - k) = 8 by ring.
    by [].
  have hpowS : 2 ^ (8 - k) = 2 * 2 ^ (7 - k).
  + have h7k : 0 <= 7 - k by smt().
    have -> : 8 - k = 7 - k + 1 by ring.
    by rewrite pow2S.
  smt(expr_ge0 expr_gt0).
have hyy : bsrev 8 (bsrev 8 y) = y.
+ by apply bsrev_involutive.
have hrev_y : bsrev 8 y = x.
+ rewrite /x /y.
  rewrite (bsrev_cat (8 - k) 8 (ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off))).
  + by split; smt().
  have hoff8 : 2 ^ (7 - k) + off \in range 0 (2 ^ (8 - k)).
  + rewrite mem_range in hoff.
    rewrite mem_range.
    have hpow : 2 ^ (8 - k) = 2 * 2 ^ (7 - k).
    + have h7k : 0 <= 7 - k by smt().
      have -> : 8 - k = 7 - k + 1 by ring.
      by rewrite pow2S.
    smt(expr_ge0 expr_gt0).
  have hdiv :
    (ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off)) %/ 2 ^ (8 - k) = ks.
  + rewrite divzMDl.
    + by rewrite gtr_eqF // expr_gt0.
    by rewrite divz_small; rewrite mem_range in hoff8; smt().
  have hmod :
    (ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off)) %% 2 ^ (8 - k) =
    2 ^ (7 - k) + off.
  + rewrite modzMDl.
    by rewrite modz_small; rewrite mem_range in hoff8; smt().
  have hbsmod :
    bsrev (8 - k) (ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off)) =
    bsrev (8 - k) (2 ^ (7 - k) + off).
  + have h := bsrev_mod (8 - k) (ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off)).
    rewrite hmod in h.
    by rewrite -h.
  rewrite hdiv hbsmod.
  rewrite (bsrev_extend_one (7 - k) off).
  + by smt().
  + exact hoff.
  have -> : 8 - (8 - k) = k by ring.
  rewrite pow2S //.
  ring.
by rewrite -hyy hrev_y.
qed.

lemma bsrev8_low_dvd k i :
  k \in range 0 8 =>
  i \in range 0 (2 ^ k) =>
  2 ^ (8 - k) %| bsrev 8 i.
proof.
move=> hk hi.
have h := bsrev_range_dvdz (8 - k) 8 i _ _.
+ by rewrite mem_range in hk; smt().
+ have -> : 8 - (8 - k) = k by ring.
  exact hi.
exact h.
qed.

lemma exp_zroot_stage_extra k i :
  k \in range 0 8 =>
  i \in range 0 (2 ^ k) =>
  Zq.exp zroot (2 ^ (k + 1) * bsrev 8 i) = Zq.one.
proof.
move=> hk hi.
have hdvd := bsrev8_low_dvd k i hk hi.
move: hdvd => /dvdzP [q hq].
have hq' : bsrev 8 i = 2 ^ (8 - k) * q by rewrite hq mulrC.
rewrite hq'.
have hpow : 2 ^ (k + 1) * 2 ^ (8 - k) = 512.
+ rewrite -exprD_nneg.
  + by rewrite mem_range in hk; smt().
  + by rewrite mem_range in hk; smt().
  have -> : k + 1 + (8 - k) = 9 by ring.
  by [].
have -> : 2 ^ (k + 1) * (2 ^ (8 - k) * q) = 512 * q by smt().
by rewrite exp_zroot_512_mul.
qed.

lemma exp_zroot_low_shift k start i :
  k \in range 0 8 =>
  start \in range 0 (2 ^ k) =>
  i \in range 0 (2 ^ k) =>
  Zq.exp zroot ((2 * (2 ^ k + start) + 1) * bsrev 8 i) =
  Zq.exp zroot ((2 * start + 1) * bsrev 8 i).
proof.
move=> hk hstart hi.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hbase :
  (2 * (2 ^ k + start) + 1) * bsrev 8 i =
  (2 * start + 1) * bsrev 8 i + 2 ^ (k + 1) * bsrev 8 i.
+ rewrite pow2S //; ring.
rewrite hbase ZqRing.exprD 1:NTT_Fq.unit_zroot.
rewrite (exp_zroot_stage_extra k i hk hi).
by rewrite ZqRing.mulr1.
qed.

lemma exp_zroot_high_shift k start i :
  k \in range 0 8 =>
  start \in range 0 (2 ^ k) =>
  i \in range 0 (2 ^ k) =>
  Zq.exp zroot
    ((2 * (2 ^ k + start) + 1) * (2 ^ (7 - k) + bsrev 8 i)) =
  - (Zq.exp zroot ((2 * start + 1) * 2 ^ (7 - k)) *
     Zq.exp zroot ((2 * start + 1) * bsrev 8 i)).
proof.
move=> hk hstart hi.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hpow256 : 2 ^ (k + 1) * 2 ^ (7 - k) = 256.
+ rewrite -exprD_nneg.
  + by smt().
  + by rewrite mem_range in hk; smt().
  have -> : k + 1 + (7 - k) = 8 by ring.
  by [].
have hbase :
  (2 * (2 ^ k + start) + 1) * (2 ^ (7 - k) + bsrev 8 i) =
  ((2 * start + 1) * 2 ^ (7 - k) +
   (2 * start + 1) * bsrev 8 i) +
  (256 + 2 ^ (k + 1) * bsrev 8 i).
+ have hpow256' : (2 * 2 ^ k) * 2 ^ (7 - k) = 256.
  + by rewrite -pow2S.
  rewrite pow2S //.
  smt().
rewrite hbase.
rewrite ZqRing.exprD 1:NTT_Fq.unit_zroot.
rewrite ZqRing.exprD 1:NTT_Fq.unit_zroot.
rewrite ZqRing.exprD 1:NTT_Fq.unit_zroot.
rewrite NTT_Fq.exp_zroot_256 incoeff_m1 (exp_zroot_stage_extra k i hk hi).
by ring.
qed.

lemma partial_ntt_split_low p k start bsj :
  k \in range 0 8 =>
  start \in range 0 (2 ^ k) =>
  bsj \in range 0 (2 ^ (7 - k)) =>
  NTTFullSpec.partial_ntt p (2 ^ (k + 1)) start bsj =
    NTTFullSpec.partial_ntt p (2 ^ k) start (bsj * 2) +
    Zq.exp zroot ((2 * start + 1) * 2 ^ (7 - k)) *
    NTTFullSpec.partial_ntt p (2 ^ k) start (bsj * 2 + 1).
proof.
move=> hk hstart hbsj.
rewrite /NTTFullSpec.partial_ntt.
rewrite (Rq.BigDom.BAdd.big_cat_int (2 ^ k) 0 (2 ^ (k + 1))).
+ by rewrite expr_ge0.
+ have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  by rewrite pow2S //; smt(expr_ge0).
rewrite Rq.BigDom.BAdd.mulr_sumr.
congr.
+ apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
  have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  have -> : bsj * 2 ^ (k + 1) + i = (bsj * 2) * 2 ^ k + i.
  + rewrite pow2S //; ring.
  by [].
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
rewrite (Rq.BigDom.BAdd.big_addn 0 (2 ^ (k + 1)) (2 ^ k)) /=.
have -> : 2 ^ (k + 1) - 2 ^ k = 2 ^ k.
+ by rewrite pow2S //; ring.
apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
have hki : i \in range 0 (2 ^ k) by rewrite mem_range.
have -> : i + 2 ^ k = 2 ^ k + i by ring.
rewrite bsrev_add_pow2 //.
rewrite ZqRing.mulrA -ZqRing.exprD.
+ exact NTT_Fq.unit_zroot.
rewrite -mulrDr.
have -> :
  (2 * start + 1) * (2 ^ (7 - k) + bsrev 8 i) =
  (2 * start + 1) * 2 ^ (7 - k) +
  (2 * start + 1) * bsrev 8 i by ring.
have -> :
  bsj * 2 ^ (k + 1) + (2 ^ k + i) =
  (bsj * 2 + 1) * 2 ^ k + i.
+ rewrite pow2S //; ring.
by [].
qed.

lemma partial_ntt_split_high p k start bsj :
  k \in range 0 8 =>
  start \in range 0 (2 ^ k) =>
  bsj \in range 0 (2 ^ (7 - k)) =>
  NTTFullSpec.partial_ntt p (2 ^ (k + 1)) (2 ^ k + start) bsj =
    NTTFullSpec.partial_ntt p (2 ^ k) start (bsj * 2) +
    (-(Zq.exp zroot ((2 * start + 1) * 2 ^ (7 - k)) *
       NTTFullSpec.partial_ntt p (2 ^ k) start (bsj * 2 + 1))).
proof.
move=> hk hstart hbsj.
rewrite /NTTFullSpec.partial_ntt.
rewrite (Rq.BigDom.BAdd.big_cat_int (2 ^ k) 0 (2 ^ (k + 1))).
+ by rewrite expr_ge0.
+ have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  by rewrite pow2S //; smt(expr_ge0).
rewrite Rq.BigDom.BAdd.mulr_sumr.
congr.
+ apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
  have hki : i \in range 0 (2 ^ k) by rewrite mem_range.
  rewrite (exp_zroot_low_shift k start i hk hstart hki).
  have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  have -> : bsj * 2 ^ (k + 1) + i = (bsj * 2) * 2 ^ k + i.
  + rewrite pow2S //; ring.
  by [].
rewrite Rq.BigDom.BAdd.sumrN.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
rewrite (Rq.BigDom.BAdd.big_addn 0 (2 ^ (k + 1)) (2 ^ k)) /=.
have -> : 2 ^ (k + 1) - 2 ^ k = 2 ^ k.
+ by rewrite pow2S //; ring.
apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
have hki : i \in range 0 (2 ^ k) by rewrite mem_range.
have -> : i + 2 ^ k = 2 ^ k + i by ring.
rewrite bsrev_add_pow2 //.
rewrite (exp_zroot_high_shift k start i hk hstart hki).
have -> :
  bsj * 2 ^ (k + 1) + (2 ^ k + i) =
  (bsj * 2 + 1) * 2 ^ k + i.
+ rewrite pow2S //; ring.
by ring.
qed.

op partial_ntt_spec (r p : poly, len start bsj : int) =
  r.[bsrev 8 (bsj * len + start)] =
  NTTFullSpec.partial_ntt p len start bsj.

op full_stage_spec (r p : poly, len : int) =
  forall start bsj,
    start \in range 0 len =>
    bsj \in range 0 (256 %/ len) =>
    partial_ntt_spec r p len start bsj.

op fwd_old_pair_spec (r p : poly, k ks off : int) =
  partial_ntt_spec r p (2 ^ k) (bsrev k ks) (2 * bsrev (7 - k) off) /\
  partial_ntt_spec r p (2 ^ k) (bsrev k ks) (2 * bsrev (7 - k) off + 1).

op fwd_new_pair_spec (r p : poly, k ks off : int) =
  partial_ntt_spec r p (2 ^ (k + 1)) (bsrev k ks) (bsrev (7 - k) off) /\
  partial_ntt_spec r p (2 ^ (k + 1)) (2 ^ k + bsrev k ks) (bsrev (7 - k) off).

op fwd_pair_done (ks off ks' off' : int) =
  ks' < ks \/ (ks' = ks /\ off' < off).

op fwd_stage_progress (r p : poly, k ks off : int) =
  forall ks' off',
    ks' \in range 0 (2 ^ k) =>
    off' \in range 0 (2 ^ (7 - k)) =>
    if fwd_pair_done ks off ks' off' then
      fwd_new_pair_spec r p k ks' off'
    else
      fwd_old_pair_spec r p k ks' off'.

op fwd_low_addr (k ks off : int) =
  ks * 2 ^ (8 - k) + off.

op fwd_high_addr (k ks off : int) =
  fwd_low_addr k ks off + 2 ^ (7 - k).

op set2_add_mulr (p : poly, z : coeff, a b : int) =
  p.[b <- p.[a] + (-(z * p.[b]))].[a <- p.[a] + z * p.[b]].

lemma fwd_high_addrE k ks off :
  fwd_high_addr k ks off =
  ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off).
proof. by rewrite /fwd_high_addr /fwd_low_addr; ring. qed.

lemma fwd_old_low_addr k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  bsrev 8 ((2 * bsrev (7 - k) off) * 2 ^ k + bsrev k ks) =
  fwd_low_addr k ks off.
proof.
move=> hk hks hoff.
rewrite /fwd_low_addr.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have -> :
  (2 * bsrev (7 - k) off) * 2 ^ k + bsrev k ks =
  bsrev (7 - k) off * 2 ^ (k + 1) + bsrev k ks.
+ rewrite pow2S //; ring.
by rewrite bsrev_stage_pair_low.
qed.

lemma fwd_old_high_addr k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  bsrev 8 ((2 * bsrev (7 - k) off + 1) * 2 ^ k + bsrev k ks) =
  fwd_high_addr k ks off.
proof.
move=> hk hks hoff.
rewrite fwd_high_addrE.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have -> :
  (2 * bsrev (7 - k) off + 1) * 2 ^ k + bsrev k ks =
  bsrev (7 - k) off * 2 ^ (k + 1) + (2 ^ k + bsrev k ks).
+ rewrite pow2S //; ring.
by rewrite bsrev_stage_pair_high.
qed.

lemma fwd_new_low_addr k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  bsrev 8 (bsrev (7 - k) off * 2 ^ (k + 1) + bsrev k ks) =
  fwd_low_addr k ks off.
proof.
move=> hk hks hoff.
by rewrite /fwd_low_addr bsrev_stage_pair_low.
qed.

lemma fwd_new_high_addr k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  bsrev 8 (bsrev (7 - k) off * 2 ^ (k + 1) + (2 ^ k + bsrev k ks)) =
  fwd_high_addr k ks off.
proof.
move=> hk hks hoff.
by rewrite fwd_high_addrE bsrev_stage_pair_high.
qed.

lemma block_low_div l x y :
  0 < l =>
  y \in range 0 l =>
  (x * (2 * l) + y) %/ (2 * l) = x.
proof.
move=> hl hy.
rewrite divzMDl.
+ by smt().
by rewrite divz_small; rewrite mem_range in hy; smt().
qed.

lemma block_low_mod l x y :
  0 < l =>
  y \in range 0 l =>
  (x * (2 * l) + y) %% (2 * l) = y.
proof.
move=> hl hy.
rewrite modzMDl.
by rewrite modz_small; rewrite mem_range in hy; smt().
qed.

lemma block_high_div l x y :
  0 < l =>
  y \in range 0 l =>
  (x * (2 * l) + (l + y)) %/ (2 * l) = x.
proof.
move=> hl hy.
rewrite divzMDl.
+ by smt().
by rewrite divz_small; rewrite mem_range in hy; smt().
qed.

lemma block_high_mod l x y :
  0 < l =>
  y \in range 0 l =>
  (x * (2 * l) + (l + y)) %% (2 * l) = l + y.
proof.
move=> hl hy.
rewrite modzMDl.
by rewrite modz_small; rewrite mem_range in hy; smt().
qed.

lemma fwd_pair_addr_disjoint k ks off ks' off' :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  ks' \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  off' \in range 0 (2 ^ (7 - k)) =>
  (ks' <> ks \/ off' <> off) =>
  fwd_low_addr k ks' off' <> fwd_low_addr k ks off /\
  fwd_low_addr k ks' off' <> fwd_high_addr k ks off /\
  fwd_high_addr k ks' off' <> fwd_low_addr k ks off /\
  fwd_high_addr k ks' off' <> fwd_high_addr k ks off.
proof.
move=> hk hks hks' hoff hoff' hneq.
pose l := 2 ^ (7 - k).
have hl : 0 < l by rewrite /l expr_gt0.
have hpow : 2 ^ (8 - k) = 2 * l.
+ rewrite /l.
  have h7k : 0 <= 7 - k by rewrite mem_range in hk; smt().
  have -> : 8 - k = 7 - k + 1 by ring.
  by rewrite pow2S.
have hoff_l : off \in range 0 l by rewrite /l.
have hoff'_l : off' \in range 0 l by rewrite /l.
rewrite /fwd_low_addr /fwd_high_addr hpow.
split.
+ apply/negP => heq.
  have hmod :
    (ks' * (2 * l) + off') %% (2 * l) =
    (ks * (2 * l) + off) %% (2 * l) by rewrite heq.
  have hoffeq : off' = off.
  + move: hmod.
    rewrite (block_low_mod l ks' off' hl hoff'_l).
    by rewrite (block_low_mod l ks off hl hoff_l).
  have hdiv :
    (ks' * (2 * l) + off') %/ (2 * l) =
    (ks * (2 * l) + off) %/ (2 * l) by rewrite heq.
  have hkseq : ks' = ks.
  + move: hdiv.
    rewrite (block_low_div l ks' off' hl hoff'_l).
    by rewrite (block_low_div l ks off hl hoff_l).
  by smt().
split.
+ apply/negP => heq.
  have hmod :
    (ks' * (2 * l) + off') %% (2 * l) =
    (ks * (2 * l) + (l + off)) %% (2 * l).
  + have heq' : ks' * (2 * l) + off' = ks * (2 * l) + (l + off) by smt().
    by rewrite heq'.
  move: hmod.
  rewrite (block_low_mod l ks' off' hl hoff'_l).
  rewrite (block_high_mod l ks off hl hoff_l).
  move=> hmodeq.
  rewrite mem_range in hoff_l.
  rewrite mem_range in hoff'_l.
  by smt().
split.
+ apply/negP => heq.
  have hmod :
    (ks' * (2 * l) + (l + off')) %% (2 * l) =
    (ks * (2 * l) + off) %% (2 * l).
  + have heq' : ks' * (2 * l) + (l + off') = ks * (2 * l) + off by smt().
    by rewrite heq'.
  move: hmod.
  rewrite (block_high_mod l ks' off' hl hoff'_l).
  rewrite (block_low_mod l ks off hl hoff_l).
  move=> hmodeq.
  rewrite mem_range in hoff_l.
  rewrite mem_range in hoff'_l.
  by smt().
apply/negP => heq.
have hmod :
  (ks' * (2 * l) + (l + off')) %% (2 * l) =
  (ks * (2 * l) + (l + off)) %% (2 * l).
+ have heq' : ks' * (2 * l) + (l + off') = ks * (2 * l) + (l + off) by smt().
  by rewrite heq'.
have hoffeq : off' = off.
+ move: hmod.
  rewrite (block_high_mod l ks' off' hl hoff'_l).
  rewrite (block_high_mod l ks off hl hoff_l).
  by smt().
have hdiv :
  (ks' * (2 * l) + (l + off')) %/ (2 * l) =
  (ks * (2 * l) + (l + off)) %/ (2 * l).
+ have heq' : ks' * (2 * l) + (l + off') = ks * (2 * l) + (l + off) by smt().
  by rewrite heq'.
have hkseq : ks' = ks.
+ move: hdiv.
  rewrite (block_high_div l ks' off' hl hoff'_l).
  by rewrite (block_high_div l ks off hl hoff_l).
by smt().
qed.

lemma forward_pair_inputs k start bsj :
  k \in range 0 8 =>
  start \in range 0 (2 ^ k) =>
  bsj \in range 0 (2 ^ (7 - k)) =>
  bsj * 2 ^ (k + 1) + start \in range 0 256 /\
  bsj * 2 ^ (k + 1) + (2 ^ k + start) \in range 0 256 /\
  bsj * 2 ^ (k + 1) + start <>
  bsj * 2 ^ (k + 1) + (2 ^ k + start).
proof.
move=> hk hstart hbsj.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hpow : 2 ^ (7 - k) * 2 ^ (k + 1) = 256.
+ rewrite -exprD_nneg.
  + by rewrite mem_range in hk; smt().
  + by rewrite mem_range in hk; smt().
  have -> : 7 - k + (k + 1) = 8 by ring.
  by [].
have hpowS : 2 ^ (k + 1) = 2 * 2 ^ k by rewrite pow2S.
rewrite mem_range in hstart.
rewrite mem_range in hbsj.
rewrite !mem_range.
smt(expr_ge0 expr_gt0).
qed.

lemma set2_add_mulr_eq1 p z a b :
  a <> b =>
  a \in range 0 256 =>
  (set2_add_mulr p z a b).[a] = p.[a] + z * p.[b].
proof.
move=> hab /mem_range ha.
by rewrite /set2_add_mulr Array256.get_set_if /= ha.
qed.

lemma set2_add_mulr_eq2 p z a b :
  a <> b =>
  b \in range 0 256 =>
  (set2_add_mulr p z a b).[b] = p.[a] + (-(z * p.[b])).
proof.
move=> hab /mem_range hb.
rewrite /set2_add_mulr Array256.get_set_if /=.
have -> : (b = a) = false by smt().
by rewrite Array256.get_set_if /= hb.
qed.

lemma set2_add_mulr_neq p z a b x :
  x <> a =>
  x <> b =>
  (set2_add_mulr p z a b).[x] = p.[x].
proof.
move=> hxa hxb.
by rewrite /set2_add_mulr !Array256.get_set_if /= hxa hxb.
qed.

lemma set2_add_mulr_assign (p : poly) (z : coeff) (a b : int) :
  a <> b =>
  a \in range 0 256 =>
  (p.[b <- p.[a] + (-(z * p.[b]))]
    .[a <- p.[b <- p.[a] + (-(z * p.[b]))].[a] + z * p.[b]]) =
  set2_add_mulr p z a b.
proof.
move=> hab ha.
rewrite /set2_add_mulr.
rewrite Array256.get_set_if /=.
have -> : (a = b) = false by smt().
by [].
qed.

lemma fwd_addr_ranges k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  fwd_low_addr k ks off \in range 0 256 /\
  fwd_high_addr k ks off \in range 0 256 /\
  fwd_low_addr k ks off <> fwd_high_addr k ks off.
proof.
move=> hk hks hoff.
rewrite /fwd_low_addr /fwd_high_addr.
rewrite mem_range in hks.
rewrite mem_range in hoff.
rewrite !mem_range.
have hblock : 2 ^ (8 - k) = 2 * 2 ^ (7 - k).
+ have h7k : 0 <= 7 - k by rewrite mem_range in hk; smt().
  have -> : 8 - k = 7 - k + 1 by ring.
  by rewrite pow2S.
have hprod : 2 ^ k * 2 ^ (8 - k) = 256.
+ rewrite -exprD_nneg.
  + by rewrite mem_range in hk; smt().
  + by rewrite mem_range in hk; smt().
  have -> : k + (8 - k) = 8 by ring.
  by [].
smt(expr_ge0 expr_gt0).
qed.

lemma partial_ntt_spec_neq_update p r z len start bsj a b :
  bsrev 8 (bsj * len + start) <> a =>
  bsrev 8 (bsj * len + start) <> b =>
  partial_ntt_spec r p len start bsj =>
  partial_ntt_spec (set2_add_mulr r z a b) p len start bsj.
proof.
move=> hxa hxb.
rewrite /partial_ntt_spec.
by rewrite set2_add_mulr_neq.
qed.

lemma fwd_old_pair_spec_neq_update p r z k ks off ks' off' :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  ks' \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  off' \in range 0 (2 ^ (7 - k)) =>
  (ks' <> ks \/ off' <> off) =>
  fwd_old_pair_spec r p k ks' off' =>
  fwd_old_pair_spec
    (set2_add_mulr r z (fwd_low_addr k ks off) (fwd_high_addr k ks off))
    p k ks' off'.
proof.
move=> hk hks hks' hoff hoff' hneq hold.
have [dLL [dLH [dHL dHH]]] :=
  fwd_pair_addr_disjoint k ks off ks' off' hk hks hks' hoff hoff' hneq.
rewrite /fwd_old_pair_spec.
rewrite /fwd_old_pair_spec in hold.
move: hold => [hlo hhi].
split.
+ apply
    (partial_ntt_spec_neq_update p r z (2 ^ k) (bsrev k ks')
       (2 * bsrev (7 - k) off') (fwd_low_addr k ks off)
       (fwd_high_addr k ks off)).
  + rewrite (fwd_old_low_addr k ks' off' hk hks' hoff').
    exact dLL.
  + rewrite (fwd_old_low_addr k ks' off' hk hks' hoff').
    exact dLH.
  + exact hlo.
+ apply
    (partial_ntt_spec_neq_update p r z (2 ^ k) (bsrev k ks')
       (2 * bsrev (7 - k) off' + 1) (fwd_low_addr k ks off)
       (fwd_high_addr k ks off)).
  + rewrite (fwd_old_high_addr k ks' off' hk hks' hoff').
    exact dHL.
  + rewrite (fwd_old_high_addr k ks' off' hk hks' hoff').
    exact dHH.
  + exact hhi.
qed.

lemma fwd_new_pair_spec_neq_update p r z k ks off ks' off' :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  ks' \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  off' \in range 0 (2 ^ (7 - k)) =>
  (ks' <> ks \/ off' <> off) =>
  fwd_new_pair_spec r p k ks' off' =>
  fwd_new_pair_spec
    (set2_add_mulr r z (fwd_low_addr k ks off) (fwd_high_addr k ks off))
    p k ks' off'.
proof.
move=> hk hks hks' hoff hoff' hneq hnew.
have [dLL [dLH [dHL dHH]]] :=
  fwd_pair_addr_disjoint k ks off ks' off' hk hks hks' hoff hoff' hneq.
rewrite /fwd_new_pair_spec.
rewrite /fwd_new_pair_spec in hnew.
move: hnew => [hlo hhi].
split.
+ apply
    (partial_ntt_spec_neq_update p r z (2 ^ (k + 1)) (bsrev k ks')
       (bsrev (7 - k) off') (fwd_low_addr k ks off)
       (fwd_high_addr k ks off)).
  + rewrite (fwd_new_low_addr k ks' off' hk hks' hoff').
    exact dLL.
  + rewrite (fwd_new_low_addr k ks' off' hk hks' hoff').
    exact dLH.
  + exact hlo.
+ apply
    (partial_ntt_spec_neq_update p r z (2 ^ (k + 1))
       (2 ^ k + bsrev k ks') (bsrev (7 - k) off')
       (fwd_low_addr k ks off) (fwd_high_addr k ks off)).
  + rewrite (fwd_new_high_addr k ks' off' hk hks' hoff').
    exact dHL.
  + rewrite (fwd_new_high_addr k ks' off' hk hks' hoff').
    exact dHH.
  + exact hhi.
qed.

lemma fwd_stage_progress_init p r k :
  k \in range 0 8 =>
  full_stage_spec r p (2 ^ k) =>
  fwd_stage_progress r p k 0 0.
proof.
move=> hk hstage.
rewrite /fwd_stage_progress => ks' off' hks' hoff'.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hk7 : k <= 7 by rewrite mem_range in hk; smt().
case: (fwd_pair_done 0 0 ks' off') => hdone.
+ rewrite /fwd_pair_done in hdone.
  rewrite mem_range in hks'.
  rewrite mem_range in hoff'.
  by smt().
rewrite /fwd_old_pair_spec.
have hstart : bsrev k ks' \in range 0 (2 ^ k).
+ by apply bsrev_range.
have hbsj : bsrev (7 - k) off' \in range 0 (2 ^ (7 - k)).
+ by apply bsrev_range.
have [hbsj0 hbsj1] := div256_pair_range k (bsrev (7 - k) off') hk hbsj.
have hbsj0' : 2 * bsrev (7 - k) off' \in range 0 (256 %/ 2 ^ k).
+ have -> : 2 * bsrev (7 - k) off' = bsrev (7 - k) off' * 2 by ring.
  exact hbsj0.
have hbsj1' : 2 * bsrev (7 - k) off' + 1 \in range 0 (256 %/ 2 ^ k).
+ have -> : 2 * bsrev (7 - k) off' + 1 = bsrev (7 - k) off' * 2 + 1 by ring.
  exact hbsj1.
split.
+ apply (hstage (bsrev k ks') (2 * bsrev (7 - k) off')).
  + exact hstart.
  + exact hbsj0'.
+ apply (hstage (bsrev k ks') (2 * bsrev (7 - k) off' + 1)).
  + exact hstart.
  + exact hbsj1'.
qed.

lemma fwd_stage_progress_old p r k ks off ks' off' :
  fwd_pair_done ks off ks' off' = false =>
  fwd_stage_progress r p k ks off =>
  ks' \in range 0 (2 ^ k) =>
  off' \in range 0 (2 ^ (7 - k)) =>
  fwd_old_pair_spec r p k ks' off'.
proof.
move=> hdone hprog hks' hoff'.
move: (hprog ks' off' hks' hoff').
by rewrite hdone.
qed.

lemma fwd_stage_progress_new p r k ks off ks' off' :
  fwd_pair_done ks off ks' off' = true =>
  fwd_stage_progress r p k ks off =>
  ks' \in range 0 (2 ^ k) =>
  off' \in range 0 (2 ^ (7 - k)) =>
  fwd_new_pair_spec r p k ks' off'.
proof.
move=> hdone hprog hks' hoff'.
move: (hprog ks' off' hks' hoff').
by rewrite hdone.
qed.

lemma forward_pair_refines_values p r k start bsj :
  k \in range 0 8 =>
  start \in range 0 (2 ^ k) =>
  bsj \in range 0 (2 ^ (7 - k)) =>
  partial_ntt_spec r p (2 ^ k) start (bsj * 2) =>
  partial_ntt_spec r p (2 ^ k) start (bsj * 2 + 1) =>
  let z = Zq.exp zroot ((2 * start + 1) * 2 ^ (7 - k)) in
  let a = bsrev 8 (bsj * 2 ^ (k + 1) + start) in
  let b = bsrev 8 (bsj * 2 ^ (k + 1) + (2 ^ k + start)) in
  partial_ntt_spec (set2_add_mulr r z a b) p (2 ^ (k + 1)) start bsj /\
  partial_ntt_spec (set2_add_mulr r z a b) p (2 ^ (k + 1)) (2 ^ k + start) bsj.
proof.
move=> hk hstart hbsj hpa hpb /=.
pose z := Zq.exp zroot ((2 * start + 1) * 2 ^ (7 - k)).
pose a := bsrev 8 (bsj * 2 ^ (k + 1) + start).
pose b := bsrev 8 (bsj * 2 ^ (k + 1) + (2 ^ k + start)).
have hin := forward_pair_inputs k start bsj hk hstart hbsj.
move: hin => [hin_a [hin_b hin_neq]].
have ha_rng : a \in range 0 256 by rewrite /a; apply NTTFullSpec.bsrev8_range_256.
have hb_rng : b \in range 0 256 by rewrite /b; apply NTTFullSpec.bsrev8_range_256.
have hab : a <> b.
+ rewrite /a /b.
  apply/negP => eq_br.
  have heq_in :=
    bsrev_injective 8
      (bsj * 2 ^ (k + 1) + start)
      (bsj * 2 ^ (k + 1) + (2 ^ k + start))
      _ _ _ eq_br.
  + by [].
  + exact hin_a.
  + exact hin_b.
  by smt().
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have ha_eq :
  a = bsrev 8 ((bsj * 2) * 2 ^ k + start).
+ rewrite /a.
  have -> : bsj * 2 ^ (k + 1) + start = (bsj * 2) * 2 ^ k + start.
  + rewrite pow2S //; ring.
  by [].
have hb_eq :
  b = bsrev 8 ((bsj * 2 + 1) * 2 ^ k + start).
+ rewrite /b.
  have -> :
    bsj * 2 ^ (k + 1) + (2 ^ k + start) =
    (bsj * 2 + 1) * 2 ^ k + start.
  + rewrite pow2S //; ring.
  by [].
split.
+ rewrite /partial_ntt_spec.
  rewrite set2_add_mulr_eq1.
  + exact hab.
  + exact ha_rng.
  rewrite /z ha_eq hb_eq hpa hpb.
  by rewrite -partial_ntt_split_low.
+ rewrite /partial_ntt_spec.
  rewrite set2_add_mulr_eq2.
  + exact hab.
  + exact hb_rng.
  rewrite /z ha_eq hb_eq hpa hpb.
  by rewrite -partial_ntt_split_high.
qed.

lemma forward_pair_refines p r k start bsj :
  k \in range 0 8 =>
  start \in range 0 (2 ^ k) =>
  bsj \in range 0 (2 ^ (7 - k)) =>
  full_stage_spec r p (2 ^ k) =>
  let z = Zq.exp zroot ((2 * start + 1) * 2 ^ (7 - k)) in
  let a = bsrev 8 (bsj * 2 ^ (k + 1) + start) in
  let b = bsrev 8 (bsj * 2 ^ (k + 1) + (2 ^ k + start)) in
  partial_ntt_spec (set2_add_mulr r z a b) p (2 ^ (k + 1)) start bsj /\
  partial_ntt_spec (set2_add_mulr r z a b) p (2 ^ (k + 1)) (2 ^ k + start) bsj.
proof.
move=> hk hstart hbsj hstage /=.
have [hbsj2 hbsj2p1] := div256_pair_range k bsj hk hbsj.
have hpa := hstage start (bsj * 2) hstart hbsj2.
have hpb := hstage start (bsj * 2 + 1) hstart hbsj2p1.
exact (forward_pair_refines_values p r k start bsj hk hstart hbsj hpa hpb).
qed.

lemma forward_nat_pair_refines p r k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  partial_ntt_spec r p (2 ^ k) (bsrev k ks) (2 * bsrev (7 - k) off) =>
  partial_ntt_spec r p (2 ^ k) (bsrev k ks) (2 * bsrev (7 - k) off + 1) =>
  let z = NTT_Fq.zetas.[2 ^ k + ks] in
  let j = ks * 2 ^ (8 - k) + off in
  partial_ntt_spec (set2_add_mulr r z j (j + 2 ^ (7 - k)))
    p (2 ^ (k + 1)) (bsrev k ks) (bsrev (7 - k) off) /\
  partial_ntt_spec (set2_add_mulr r z j (j + 2 ^ (7 - k)))
    p (2 ^ (k + 1)) (2 ^ k + bsrev k ks) (bsrev (7 - k) off).
proof.
move=> hk hks hoff hpa hpb /=.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hk7 : k <= 7 by rewrite mem_range in hk; smt().
have hstart : bsrev k ks \in range 0 (2 ^ k).
+ by apply bsrev_range.
have hbsj : bsrev (7 - k) off \in range 0 (2 ^ (7 - k)).
+ by apply bsrev_range.
have hpa' :
  partial_ntt_spec r p (2 ^ k) (bsrev k ks) (bsrev (7 - k) off * 2).
+ have -> : bsrev (7 - k) off * 2 = 2 * bsrev (7 - k) off by ring.
  exact hpa.
have hpb' :
  partial_ntt_spec r p (2 ^ k) (bsrev k ks) (bsrev (7 - k) off * 2 + 1).
+ have -> : bsrev (7 - k) off * 2 + 1 = 2 * bsrev (7 - k) off + 1 by ring.
  exact hpb.
have H :=
  forward_pair_refines_values p r k (bsrev k ks) (bsrev (7 - k) off)
    hk hstart hbsj hpa' hpb'.
rewrite (zetas_stage k ks hk hks).
have -> :
  ks * 2 ^ (8 - k) + off + 2 ^ (7 - k) =
  ks * 2 ^ (8 - k) + (2 ^ (7 - k) + off) by ring.
rewrite -(bsrev_stage_pair_low k ks off hk hks hoff).
rewrite -(bsrev_stage_pair_high k ks off hk hks hoff).
exact H.
qed.

lemma fwd_stage_progress_step p r k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  off \in range 0 (2 ^ (7 - k)) =>
  fwd_stage_progress r p k ks off =>
  fwd_stage_progress
    (set2_add_mulr r NTT_Fq.zetas.[2 ^ k + ks]
       (fwd_low_addr k ks off) (fwd_high_addr k ks off))
    p k ks (off + 1).
proof.
move=> hk hks hoff hprog.
rewrite /fwd_stage_progress => ks' off' hks' hoff'.
case: (ks' = ks /\ off' = off) => hcur.
+ move: hcur => [hks_eq hoff_eq].
  have hprev_false : fwd_pair_done ks off ks' off' = false.
  + rewrite /fwd_pair_done.
    by smt().
  have hold :=
    fwd_stage_progress_old p r k ks off ks' off'
      hprev_false hprog hks' hoff'.
  rewrite hks_eq hoff_eq in hold.
  rewrite /fwd_old_pair_spec in hold.
  move: hold => [hold0 hold1].
  have hpair :=
    forward_nat_pair_refines p r k ks off hk hks hoff hold0 hold1.
  have hnext_true : fwd_pair_done ks (off + 1) ks' off' = true.
  + rewrite /fwd_pair_done.
    by smt().
  rewrite hnext_true /fwd_new_pair_spec.
  rewrite hks_eq hoff_eq.
  rewrite /fwd_low_addr /fwd_high_addr.
  exact hpair.
have hneq : ks' <> ks \/ off' <> off by smt().
case: (fwd_pair_done ks (off + 1) ks' off') => hnext.
+ have hprev_true : fwd_pair_done ks off ks' off' = true.
  + rewrite /fwd_pair_done.
    rewrite /fwd_pair_done in hnext.
    by smt().
  have hnew :=
    fwd_stage_progress_new p r k ks off ks' off'
      hprev_true hprog hks' hoff'.
  exact
    (fwd_new_pair_spec_neq_update p r NTT_Fq.zetas.[2 ^ k + ks]
       k ks off ks' off' hk hks hks' hoff hoff' hneq hnew).
have hprev_false : fwd_pair_done ks off ks' off' = false.
+ rewrite /fwd_pair_done.
  rewrite /fwd_pair_done in hnext.
  by smt().
have hold :=
  fwd_stage_progress_old p r k ks off ks' off'
    hprev_false hprog hks' hoff'.
exact
  (fwd_old_pair_spec_neq_update p r NTT_Fq.zetas.[2 ^ k + ks]
     k ks off ks' off' hk hks hks' hoff hoff' hneq hold).
qed.

lemma fwd_stage_progress_next_block p r k ks :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ k) =>
  fwd_stage_progress r p k ks (2 ^ (7 - k)) =>
  fwd_stage_progress r p k (ks + 1) 0.
proof.
move=> hk hks hprog.
rewrite /fwd_stage_progress => ks' off' hks' hoff'.
have hdone :
  fwd_pair_done (ks + 1) 0 ks' off' =
  fwd_pair_done ks (2 ^ (7 - k)) ks' off'.
+ rewrite /fwd_pair_done.
  rewrite mem_range in hoff'.
  by smt().
rewrite hdone.
exact (hprog ks' off' hks' hoff').
qed.

lemma div256_pow2_next k :
  k \in range 0 8 =>
  256 %/ 2 ^ (k + 1) = 2 ^ (7 - k).
proof.
move=> hk.
have h256 : 256 = (2 ^ 8) by smt().
rewrite h256.
rewrite expz_div.
+ by rewrite mem_range in hk; smt().
+ by [].
have -> : 8 - (k + 1) = 7 - k by ring.
by [].
qed.

lemma fwd_stage_progress_finish p r k :
  k \in range 0 8 =>
  fwd_stage_progress r p k (2 ^ k) 0 =>
  full_stage_spec r p (2 ^ (k + 1)).
proof.
move=> hk hprog.
rewrite /full_stage_spec => start bsj hstart hbsj.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hk7 : k <= 7 by rewrite mem_range in hk; smt().
have hbsj' : bsj \in range 0 (2 ^ (7 - k)).
+ move: hbsj.
  by rewrite (div256_pow2_next k hk).
case: (start < 2 ^ k) => hlow.
+ have hstart_low : start \in range 0 (2 ^ k).
  + rewrite mem_range in hstart.
    rewrite mem_range.
    smt(expr_ge0).
  pose ks := bsrev k start.
  pose off := bsrev (7 - k) bsj.
  have hks : ks \in range 0 (2 ^ k).
  + rewrite /ks.
    by apply bsrev_range.
  have hoff : off \in range 0 (2 ^ (7 - k)).
  + rewrite /off.
    by apply bsrev_range.
  have hdone : fwd_pair_done (2 ^ k) 0 ks off = true.
  + rewrite /fwd_pair_done.
    rewrite mem_range in hks.
    by smt().
  have hnew :=
    fwd_stage_progress_new p r k (2 ^ k) 0 ks off
      hdone hprog hks hoff.
  rewrite /fwd_new_pair_spec in hnew.
  move: hnew => [hnew_low _].
  have hksK : bsrev k ks = start.
  + rewrite /ks bsrev_involutive.
    + by smt().
    + exact hstart_low.
    by [].
  have hoffK : bsrev (7 - k) off = bsj.
  + rewrite /off bsrev_involutive.
    + by smt().
    + exact hbsj'.
    by [].
  move: hnew_low.
  by rewrite hksK hoffK.
have hstart_hi : start - 2 ^ k \in range 0 (2 ^ k).
+ rewrite mem_range in hstart.
  rewrite mem_range.
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k by rewrite pow2S.
  smt(expr_ge0).
pose start0 := start - 2 ^ k.
pose ks := bsrev k start0.
pose off := bsrev (7 - k) bsj.
have hks : ks \in range 0 (2 ^ k).
+ rewrite /ks.
  by apply bsrev_range.
have hoff : off \in range 0 (2 ^ (7 - k)).
+ rewrite /off.
  by apply bsrev_range.
have hdone : fwd_pair_done (2 ^ k) 0 ks off = true.
+ rewrite /fwd_pair_done.
  rewrite mem_range in hks.
  by smt().
have hnew :=
  fwd_stage_progress_new p r k (2 ^ k) 0 ks off
    hdone hprog hks hoff.
rewrite /fwd_new_pair_spec in hnew.
move: hnew => [_ hnew_high].
have hksK : bsrev k ks = start0.
+ rewrite /ks bsrev_involutive.
  + by smt().
  + exact hstart_hi.
  by [].
have hoffK : bsrev (7 - k) off = bsj.
+ rewrite /off bsrev_involutive.
  + by smt().
  + exact hbsj'.
  by [].
have hstartK : 2 ^ k + bsrev k ks = start.
+ by rewrite hksK /start0; ring.
move: hnew_high.
by rewrite hstartK hoffK.
qed.

lemma pow2_stage_product k :
  k \in range 0 8 =>
  2 ^ k * 2 ^ (8 - k) = 256.
proof.
move=> hk.
rewrite -exprD_nneg.
+ by rewrite mem_range in hk; smt().
+ by rewrite mem_range in hk; smt().
have -> : k + (8 - k) = 8 by ring.
by [].
qed.

lemma pow2_stage_block k :
  k \in range 0 8 =>
  2 * 2 ^ (7 - k) = 2 ^ (8 - k).
proof.
move=> hk.
have h7k : 0 <= 7 - k by rewrite mem_range in hk; smt().
have -> : 8 - k = 7 - k + 1 by ring.
by rewrite pow2S.
qed.

lemma fwd_len_div2_next k :
  k \in range 0 7 =>
  2 ^ (7 - k) %/ 2 = 2 ^ (7 - (k + 1)).
proof.
move=> hk.
have hpow :
  2 ^ (7 - k) = 2 ^ (7 - (k + 1)) * 2.
+ have -> : 7 - k = 7 - (k + 1) + 1 by ring.
  rewrite pow2S.
  + by rewrite mem_range in hk; smt().
  by ring.
by rewrite hpow; smt().
qed.

op fwd_outer_inv (p r zetas : poly, len zetasctr : int) =
  zetas = NTT_Fq.zetas /\
  ((exists k,
      k \in range 0 8 /\
      len = 2 ^ (7 - k) /\
      zetasctr = 2 ^ k - 1 /\
      full_stage_spec r p (2 ^ k)) \/
   (len = 0 /\
    zetasctr = 255 /\
    full_stage_spec r p 256)).

op fwd_middle_inv (p r zetas : poly, len start zetasctr : int) =
  zetas = NTT_Fq.zetas /\
  exists k ks,
    k \in range 0 8 /\
    len = 2 ^ (7 - k) /\
    0 <= ks <= 2 ^ k /\
    start = ks * 2 ^ (8 - k) /\
    zetasctr = 2 ^ k - 1 + ks /\
    fwd_stage_progress r p k ks 0.

op fwd_inner_inv
   (p r zetas : poly, len start j zetasctr : int, zeta_ : coeff) =
  zetas = NTT_Fq.zetas /\
  exists k ks off,
    k \in range 0 8 /\
    ks \in range 0 (2 ^ k) /\
    0 <= off <= 2 ^ (7 - k) /\
    len = 2 ^ (7 - k) /\
    start = ks * 2 ^ (8 - k) /\
    j = start + off /\
    zetasctr = 2 ^ k + ks /\
    zeta_ = zetas.[zetasctr] /\
    fwd_stage_progress r p k ks off.

lemma fwd_outer_inv_init p :
  fwd_outer_inv p p NTT_Fq.zetas 128 0.
proof.
rewrite /fwd_outer_inv.
split; first by [].
left; exists 0.
split; first by rewrite range_ltn.
split; first by [].
split; first by [].
rewrite /full_stage_spec => start bsj hstart hbsj.
have hstart0 : start = 0.
+ rewrite mem_range in hstart.
  by smt().
rewrite hstart0.
rewrite /partial_ntt_spec /NTTFullSpec.partial_ntt.
by rewrite Rq.BigDom.BAdd.big_int1 /= ?mulr1 ?addr0 bsrev0
           ZqRing.expr0 ZqRing.mul1r.
qed.

lemma fwd_outer_exit_stage p r zetas len zetasctr :
  fwd_outer_inv p r zetas len zetasctr =>
  ! 1 <= len =>
  full_stage_spec r p 256.
proof.
rewrite /fwd_outer_inv.
move=> [_ [hstage | hdone]] hstop.
+ move: hstage => [k [hk [hlen [_ hspec]]]].
  have hpos : 1 <= len.
  + rewrite hlen.
    have h7k : 0 <= 7 - k by rewrite mem_range in hk; smt().
    by smt(expr_gt0).
  by smt().
by move: hdone => [_ [_ hspec]].
qed.

lemma fwd_outer_enter_middle p r zetas len zetasctr :
  fwd_outer_inv p r zetas len zetasctr =>
  1 <= len =>
  fwd_middle_inv p r zetas len 0 zetasctr.
proof.
rewrite /fwd_outer_inv /fwd_middle_inv.
move=> [hzetas [hstage | hdone]] hguard.
+ move: hstage => [k [hk [hlen [hzc hspec]]]].
  split; first exact hzetas.
  exists k 0.
  split; first exact hk.
  split; first exact hlen.
  split; first by smt(expr_ge0).
  split.
  + by ring.
  split; first by rewrite hzc; ring.
  by apply fwd_stage_progress_init.
move: hdone => [hlen [_ _]].
by smt().
qed.

lemma fwd_middle_enter_inner p r zetas len start zetasctr :
  fwd_middle_inv p r zetas len start zetasctr =>
  start < 256 =>
  fwd_inner_inv p r zetas len start start (zetasctr + 1)
    zetas.[zetasctr + 1].
proof.
rewrite /fwd_middle_inv /fwd_inner_inv.
move=> [hzetas hex] hguard.
move: hex => [k ks [hk [hlen [hksb [hstart [hzc hprog]]]]]].
split; first exact hzetas.
have hblock := pow2_stage_product k hk.
have hks : ks \in range 0 (2 ^ k).
+ rewrite mem_range.
  by smt(expr_gt0).
exists k ks 0.
split; first exact hk.
split; first exact hks.
split; first by smt(expr_ge0).
split; first exact hlen.
split; first exact hstart.
split; first by ring.
split; first by rewrite hzc; ring.
split; first by rewrite hzc.
exact hprog.
qed.

lemma fwd_inner_step_set2 p r zetas len start j zetasctr zeta_ :
  fwd_inner_inv p r zetas len start j zetasctr zeta_ =>
  j < start + len =>
  fwd_inner_inv p
    (set2_add_mulr r zeta_ j (j + len))
    zetas len start (j + 1) zetasctr zeta_.
proof.
rewrite /fwd_inner_inv.
move=> [hzetas hex] hguard.
move: hex => [k ks off [hk [hks [hoffb [hlen [hstart [hj [hzc [hzeta hprog]]]]]]]]].
split; first exact hzetas.
have hoff : off \in range 0 (2 ^ (7 - k)).
+ rewrite mem_range.
  move: hoffb => [hoff0 hoffle].
  split; first exact hoff0.
  move: hguard.
  rewrite hj hlen.
  by smt().
exists k ks (off + 1).
split; first exact hk.
split; first exact hks.
split; first by rewrite mem_range in hoff; smt().
split; first exact hlen.
split; first exact hstart.
split; first by rewrite hj; ring.
split; first exact hzc.
split; first exact hzeta.
have hstep :=
  fwd_stage_progress_step p r k ks off hk hks hoff hprog.
have -> :
  zeta_ = NTT_Fq.zetas.[2 ^ k + ks].
+ by rewrite hzeta hzetas hzc.
have -> :
  j = fwd_low_addr k ks off.
+ by rewrite /fwd_low_addr hj hstart; ring.
have -> :
  fwd_low_addr k ks off + len = fwd_high_addr k ks off.
+ by rewrite /fwd_high_addr hlen.
exact hstep.
qed.

lemma fwd_inner_step_array p r zetas len start j zetasctr zeta_ :
  fwd_inner_inv p r zetas len start j zetasctr zeta_ =>
  j < start + len =>
  fwd_inner_inv p
    (r.[j + len <- r.[j] + (-(zeta_ * r.[j + len]))]
       .[j <-
          r.[j + len <- r.[j] + (-(zeta_ * r.[j + len]))].[j] +
          zeta_ * r.[j + len]])
    zetas len start (j + 1) zetasctr zeta_.
proof.
move=> hin hguard.
rewrite /fwd_inner_inv in hin.
move: hin => [hzetas hex].
move: hex => [k ks off [hk [hks [hoffb [hlen [hstart [hj [hzc [hzeta hprog]]]]]]]]].
have hoff : off \in range 0 (2 ^ (7 - k)).
+ rewrite mem_range.
  move: hoffb => [hoff0 hoffle].
  split; first exact hoff0.
  move: hguard.
  rewrite hj hlen.
  by smt().
have [hj_rng [_ hj_neq]] := fwd_addr_ranges k ks off hk hks hoff.
have hj_low : j = fwd_low_addr k ks off.
+ by rewrite /fwd_low_addr hj hstart; ring.
have hj_high : j + len = fwd_high_addr k ks off.
+ by rewrite hj_low /fwd_high_addr hlen.
have hj_neqlen : j <> j + len by smt().
have hassign :
  r.[j + len <- r.[j] + (-(zeta_ * r.[j + len]))]
   .[j <-
      r.[j + len <- r.[j] + (-(zeta_ * r.[j + len]))].[j] +
      zeta_ * r.[j + len]] =
  set2_add_mulr r zeta_ j (j + len).
+ apply set2_add_mulr_assign.
  + exact hj_neqlen.
  rewrite hj_low.
  exact hj_rng.
rewrite hassign.
apply fwd_inner_step_set2.
+ rewrite /fwd_inner_inv.
  split; first exact hzetas.
  exists k ks off.
  split; first exact hk.
  split; first exact hks.
  split; first exact hoffb.
  split; first exact hlen.
  split; first exact hstart.
  split; first exact hj.
  split; first exact hzc.
  split; first exact hzeta.
  exact hprog.
exact hguard.
qed.

lemma fwd_inner_exit_middle p r zetas len start j zetasctr zeta_ :
  fwd_inner_inv p r zetas len start j zetasctr zeta_ =>
  ! j < start + len =>
  fwd_middle_inv p r zetas len (j + len) zetasctr.
proof.
rewrite /fwd_inner_inv /fwd_middle_inv.
move=> [hzetas hex] hstop.
move: hex => [k ks off [hk [hks [hoffb [hlen [hstart [hj [hzc [_ hprog]]]]]]]]].
split; first exact hzetas.
have hoff_end : off = 2 ^ (7 - k).
+ move: hoffb => [hoff0 hoffle].
  move: hstop.
  rewrite hj hlen.
  by smt().
exists k (ks + 1).
split; first exact hk.
split; first exact hlen.
split.
+ rewrite mem_range in hks.
  by smt().
split.
+ rewrite hj hstart hlen hoff_end.
  have hblock := pow2_stage_block k hk.
  by rewrite -hblock; ring.
split.
+ rewrite hzc.
  by ring.
have hprog_end : fwd_stage_progress r p k ks (2 ^ (7 - k)).
+ by rewrite -hoff_end.
exact (fwd_stage_progress_next_block p r k ks hk hks hprog_end).
qed.

lemma fwd_middle_exit_outer p r zetas len start zetasctr :
  fwd_middle_inv p r zetas len start zetasctr =>
  ! start < 256 =>
  fwd_outer_inv p r zetas (len %/ 2) zetasctr.
proof.
rewrite /fwd_middle_inv /fwd_outer_inv.
move=> [hzetas hex] hstop.
move: hex => [k ks [hk [hlen [hksb [hstart [hzc hprog]]]]]].
split; first exact hzetas.
have hblock := pow2_stage_product k hk.
have hks_end : ks = 2 ^ k.
+ move: hksb => [hks0 hksle].
  have hstart_le : start <= 256.
  + rewrite hstart.
    by smt(expr_ge0).
  have hstart_ge : 256 <= start by rewrite -lezNgt in hstop.
  have hstart_eq : start = 256 by smt().
  by smt(expr_gt0).
have hprog_end : fwd_stage_progress r p k (2 ^ k) 0.
+ by rewrite -hks_end.
have hfinish : full_stage_spec r p (2 ^ (k + 1)).
+ exact (fwd_stage_progress_finish p r k hk hprog_end).
case: (k < 7) => hklt7.
+ left; exists (k + 1).
  have hk_next : k + 1 \in range 0 8.
  + rewrite mem_range in hk.
    by rewrite mem_range; smt().
  split; first exact hk_next.
  split.
  + rewrite hlen.
    have hk_rng7 : k \in range 0 7 by rewrite mem_range; rewrite mem_range in hk; smt().
    by rewrite fwd_len_div2_next.
  split.
  + rewrite hzc hks_end.
    have hk0 : 0 <= k by rewrite mem_range in hk; smt().
    rewrite (pow2S k hk0).
    by ring.
  exact hfinish.
right.
have hk_eq7 : k = 7 by rewrite mem_range in hk; smt().
rewrite hlen hzc hks_end hk_eq7 /=.
move: hfinish; rewrite hk_eq7 /=.
by [].
qed.

lemma full_stage1_init (p : poly) :
  full_stage_spec p p 1.
proof.
rewrite /full_stage_spec => start bsj hstart hbsj.
have hstart0 : start = 0.
+ rewrite mem_range in hstart.
  by smt().
rewrite hstart0.
rewrite /partial_ntt_spec /NTTFullSpec.partial_ntt.
by rewrite Rq.BigDom.BAdd.big_int1 /= ?mulr1 ?addr0 bsrev0
           ZqRing.expr0 ZqRing.mul1r.
qed.

lemma full_stage256_imp p r :
  full_stage_spec r p 256 =>
  r = NTTFullSpec.full_ntt p.
proof.
move=> h.
apply NTTFullSpec.full_ntt_spec_imp.
rewrite /NTTFullSpec.full_ntt_spec => start hstart.
move: (h start 0 hstart _).
+ by rewrite range_ltn.
by rewrite /partial_ntt_spec mul0r add0r.
qed.

lemma fwd_outer_exit_full p r zetas len zetasctr :
  fwd_outer_inv p r zetas len zetasctr =>
  ! 1 <= len =>
  r = NTTFullSpec.full_ntt p.
proof.
move=> hin hstop.
by apply full_stage256_imp; apply (fwd_outer_exit_stage p r zetas len zetasctr).
qed.

lemma ntt_full_ntt (p : poly) :
  hoare [NTT_Fq.NTT.ntt :
    arg = (p, NTT_Fq.zetas) ==> res = NTTFullSpec.full_ntt p].
proof.
proc.
wp.
while (fwd_outer_inv p r zetas len zetasctr).
+ wp.
  while (fwd_middle_inv p r zetas len start zetasctr).
  + wp.
    while (fwd_inner_inv p r zetas len start j zetasctr zeta_).
    + wp.
      skip => &hr /=.
      smt(fwd_inner_step_array).
    wp.
    skip => &hr /=.
    smt(fwd_middle_enter_inner fwd_inner_exit_middle).
  wp.
  skip => &hr /=.
  smt(fwd_outer_enter_middle fwd_middle_exit_outer).
wp.
skip => &hr /=.
smt(fwd_outer_inv_init fwd_outer_exit_full).
qed.

op inv_low_addr (k ks off : int) =
  ks * 2 ^ (k + 1) + off.

op inv_high_addr (k ks off : int) =
  inv_low_addr k ks off + 2 ^ k.

lemma inv_high_addrE k ks off :
  inv_high_addr k ks off =
  ks * 2 ^ (k + 1) + (2 ^ k + off).
proof. by rewrite /inv_high_addr /inv_low_addr; ring. qed.

lemma inv_stage_blocks_product k :
  k \in range 0 8 =>
  2 ^ (7 - k) * 2 ^ (k + 1) = 256.
proof.
move=> hk.
rewrite -exprD_nneg.
+ by rewrite mem_range in hk; smt().
+ by rewrite mem_range in hk; smt().
have -> : 7 - k + (k + 1) = 8 by ring.
by [].
qed.

lemma inv_pair_inputs k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  inv_low_addr k ks off \in range 0 256 /\
  inv_high_addr k ks off \in range 0 256 /\
  inv_low_addr k ks off <> inv_high_addr k ks off.
proof.
move=> hk hks hoff.
rewrite /inv_low_addr /inv_high_addr.
rewrite mem_range in hks.
rewrite mem_range in hoff.
rewrite !mem_range.
have hprod := inv_stage_blocks_product k hk.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hpowS : 2 ^ (k + 1) = 2 * 2 ^ k by rewrite pow2S.
smt(expr_ge0 expr_gt0).
qed.

lemma bsrev_inv_pair_low k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  bsrev 8 (inv_low_addr k ks off) =
  bsrev k off * 2 ^ (8 - k) + bsrev (7 - k) ks.
proof.
move=> hk hks hoff.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have h7k0 : 0 <= 7 - k by rewrite mem_range in hk; smt().
rewrite /inv_low_addr.
have -> : ks * 2 ^ (k + 1) + off = (2 * ks) * 2 ^ k + off.
+ rewrite pow2S //; ring.
rewrite (bsrev_cat k 8 ((2 * ks) * 2 ^ k + off)).
+ by split; smt().
have hdiv : ((2 * ks) * 2 ^ k + off) %/ 2 ^ k = 2 * ks.
+ rewrite divzMDl.
  + by rewrite gtr_eqF // expr_gt0.
  by rewrite divz_small; rewrite mem_range in hoff; smt().
have hmod : ((2 * ks) * 2 ^ k + off) %% 2 ^ k = off.
+ rewrite modzMDl.
  by rewrite modz_small; rewrite mem_range in hoff; smt().
have hbsmod :
  bsrev k ((2 * ks) * 2 ^ k + off) = bsrev k off.
+ have h := bsrev_mod k ((2 * ks) * 2 ^ k + off).
  rewrite hmod in h.
  by rewrite -h.
rewrite hdiv hbsmod.
have hbsdiv : bsrev (8 - k) (2 * ks) = bsrev (7 - k) ks.
+ have -> : 8 - k = 7 - k + 1 by ring.
  by rewrite bsrev_double 1:h7k0 1:hks.
rewrite hbsdiv.
by ring.
qed.

lemma bsrev_inv_pair_high k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  bsrev 8 (inv_high_addr k ks off) =
  bsrev k off * 2 ^ (8 - k) + (2 ^ (7 - k) + bsrev (7 - k) ks).
proof.
move=> hk hks hoff.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have h7k0 : 0 <= 7 - k by rewrite mem_range in hk; smt().
rewrite inv_high_addrE.
have -> :
  ks * 2 ^ (k + 1) + (2 ^ k + off) =
  (2 * ks + 1) * 2 ^ k + off.
+ rewrite pow2S //; ring.
rewrite (bsrev_cat k 8 ((2 * ks + 1) * 2 ^ k + off)).
+ by split; smt().
have hdiv : ((2 * ks + 1) * 2 ^ k + off) %/ 2 ^ k = 2 * ks + 1.
+ rewrite divzMDl.
  + by rewrite gtr_eqF // expr_gt0.
  by rewrite divz_small; rewrite mem_range in hoff; smt().
have hmod : ((2 * ks + 1) * 2 ^ k + off) %% 2 ^ k = off.
+ rewrite modzMDl.
  by rewrite modz_small; rewrite mem_range in hoff; smt().
have hbsmod :
  bsrev k ((2 * ks + 1) * 2 ^ k + off) = bsrev k off.
+ have h := bsrev_mod k ((2 * ks + 1) * 2 ^ k + off).
  rewrite hmod in h.
  by rewrite -h.
rewrite hdiv hbsmod.
have hbsdiv :
  bsrev (8 - k) (2 * ks + 1) =
  2 ^ (7 - k) + bsrev (7 - k) ks.
+ have -> : 8 - k = 7 - k + 1 by ring.
  by rewrite bsrev_double_plus1 1:h7k0 1:hks.
rewrite hbsdiv.
by ring.
qed.

lemma zetas_inv_stage k ks :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] =
  Zq.exp zroot (- ((2 * bsrev (7 - k) ks + 1) * 2 ^ k)).
proof.
move=> hk hks.
rewrite /NTT_Fq.zetas_inv /= Array256.get_set_if /=.
pose l := 2 ^ (7 - k).
have hl_pos : 0 < l by rewrite /l expr_gt0.
have hks_l : 0 <= ks < l.
+ rewrite /l.
  by rewrite mem_range in hks.
have hl_le : l <= 128.
+ rewrite /l.
  have h128 : 128 = (2 ^ 7) by smt().
  rewrite h128.
  by apply StdOrder.IntOrder.ler_weexpn2l; rewrite mem_range in hk; smt().
have hpow : 2 ^ (8 - k) = 2 * l.
+ rewrite /l.
  have h7k : 0 <= 7 - k by rewrite mem_range in hk; smt().
  have -> : 8 - k = 7 - k + 1 by ring.
  by rewrite pow2S.
have hidx_rng : 256 - 2 ^ (8 - k) + ks \in range 0 256.
+ rewrite hpow mem_range.
  by smt().
have hidx_ne : (256 - 2 ^ (8 - k) + ks = 255) = false.
+ have hidx_lt : 256 - 2 ^ (8 - k) + ks < 255.
  + rewrite hpow.
    by smt().
  by smt().
rewrite hidx_ne.
rewrite initiE /=.
+ by smt().
rewrite bsrev_zbase_index 1:hk 1:hks.
have -> :
  - (((2 * bsrev (7 - k) ks + 1) * 2 ^ k - 1) + 1) =
  - ((2 * bsrev (7 - k) ks + 1) * 2 ^ k) by ring.
by [].
qed.

lemma inv_low_twiddle_factor k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  Zq.exp zroot (- ((2 * bsrev 8 (inv_low_addr k ks off) + 1) * 2 ^ k)) =
  NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks].
proof.
move=> hk hks hoff.
rewrite zetas_inv_stage 1:hk 1:hks.
rewrite bsrev_inv_pair_low 1:hk 1:hks 1:hoff.
have hbr : 0 <= bsrev k off by smt(bsrev_ge0).
have -> :
  - ((2 * (bsrev k off * 2 ^ (8 - k) + bsrev (7 - k) ks) + 1) * 2 ^ k) =
  - ((2 * bsrev (7 - k) ks + 1) * 2 ^ k) + 512 * (-(bsrev k off)).
+ have hpow : 2 * 2 ^ (8 - k) * 2 ^ k = 512.
  + have h8k : 0 <= 8 - k by rewrite mem_range in hk; smt().
    have hk0 : 0 <= k by rewrite mem_range in hk; smt().
    have hpowS : 2 ^ (8 - k + 1) = 2 * 2 ^ (8 - k) by rewrite pow2S.
    have -> : 2 * 2 ^ (8 - k) * 2 ^ k = 2 ^ (8 - k + 1) * 2 ^ k.
    + by rewrite hpowS.
    rewrite -exprD_nneg 1:/# 1://.
    have -> : 8 - k + 1 + k = 9 by ring.
    by [].
  smt().
rewrite exp_zroot_mod512.
by [].
qed.

lemma inv_high_twiddle_factor k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  Zq.exp zroot (- ((2 * bsrev 8 (inv_high_addr k ks off) + 1) * 2 ^ k)) =
  - NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks].
proof.
move=> hk hks hoff.
rewrite zetas_inv_stage 1:hk 1:hks.
rewrite bsrev_inv_pair_high 1:hk 1:hks 1:hoff.
have -> :
  - ((2 *
       (bsrev k off * 2 ^ (8 - k) +
        (2 ^ (7 - k) + bsrev (7 - k) ks)) + 1) * 2 ^ k) =
  (- ((2 * bsrev (7 - k) ks + 1) * 2 ^ k) + (-256)) +
  512 * (-(bsrev k off)).
+ have hpow512 : 2 * 2 ^ (8 - k) * 2 ^ k = 512.
  + have h8k : 0 <= 8 - k by rewrite mem_range in hk; smt().
    have hk0 : 0 <= k by rewrite mem_range in hk; smt().
    have hpowS : 2 ^ (8 - k + 1) = 2 * 2 ^ (8 - k) by rewrite pow2S.
    have -> : 2 * 2 ^ (8 - k) * 2 ^ k = 2 ^ (8 - k + 1) * 2 ^ k.
    + by rewrite hpowS.
    rewrite -exprD_nneg 1:/# 1://.
    have -> : 8 - k + 1 + k = 9 by ring.
    by [].
  have hpow256 : 2 * 2 ^ (7 - k) * 2 ^ k = 256.
  + have h7k : 0 <= 7 - k by rewrite mem_range in hk; smt().
    have hk0 : 0 <= k by rewrite mem_range in hk; smt().
    have hpowS : 2 ^ (7 - k + 1) = 2 * 2 ^ (7 - k) by rewrite pow2S.
    have -> : 2 * 2 ^ (7 - k) * 2 ^ k = 2 ^ (7 - k + 1) * 2 ^ k.
    + by rewrite hpowS.
    rewrite -exprD_nneg 1:/# 1://.
    have -> : 7 - k + 1 + k = 8 by ring.
    by [].
  smt().
rewrite exp_zroot_mod512.
rewrite ZqRing.exprD 1:NTT_Fq.unit_zroot exp_zroot_m256.
rewrite incoeff_m1.
by ring.
qed.

op partial_invntt (p : poly, len start bsj : int) =
  Rq.BigDom.BAdd.bigi predT
    (fun s =>
      p.[bsj * len + s] *
      Zq.exp zroot (- ((2 * bsrev 8 (bsj * len + s) + 1) * start)))
    0 len.

op partial_invntt_spec (r p : poly, len start bsj : int) =
  r.[bsj * len + start] = partial_invntt p len start bsj.

op inv_stage_spec (r p : poly, len : int) =
  forall start bsj,
    start \in range 0 len =>
    bsj \in range 0 (256 %/ len) =>
    partial_invntt_spec r p len start bsj.

lemma partial_invntt_split_low p k off ks :
  k \in range 0 8 =>
  off \in range 0 (2 ^ k) =>
  ks \in range 0 (2 ^ (7 - k)) =>
  partial_invntt p (2 ^ (k + 1)) off ks =
    partial_invntt p (2 ^ k) off (2 * ks) +
    partial_invntt p (2 ^ k) off (2 * ks + 1).
proof.
move=> hk hoff hks.
rewrite /partial_invntt.
rewrite (Rq.BigDom.BAdd.big_cat_int (2 ^ k) 0 (2 ^ (k + 1))).
+ by rewrite expr_ge0.
+ have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  by rewrite pow2S //; smt(expr_ge0).
congr.
+ apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
  have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  have -> : ks * 2 ^ (k + 1) + i = (2 * ks) * 2 ^ k + i.
  + rewrite pow2S //; ring.
  by [].
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
rewrite (Rq.BigDom.BAdd.big_addn 0 (2 ^ (k + 1)) (2 ^ k)) /=.
have -> : 2 ^ (k + 1) - 2 ^ k = 2 ^ k.
+ by rewrite pow2S //; ring.
apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
have -> :
  ks * 2 ^ (k + 1) + (i + 2 ^ k) =
  (2 * ks + 1) * 2 ^ k + i.
+ rewrite pow2S //; ring.
by [].
qed.

lemma partial_invntt_split_high p k off ks :
  k \in range 0 8 =>
  off \in range 0 (2 ^ k) =>
  ks \in range 0 (2 ^ (7 - k)) =>
  partial_invntt p (2 ^ (k + 1)) (2 ^ k + off) ks =
    NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] *
    (partial_invntt p (2 ^ k) off (2 * ks) +
     (-(partial_invntt p (2 ^ k) off (2 * ks + 1)))).
proof.
move=> hk hoff hks.
have -> :
  NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] *
  (partial_invntt p (2 ^ k) off (2 * ks) +
   (-(partial_invntt p (2 ^ k) off (2 * ks + 1)))) =
  NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] *
  partial_invntt p (2 ^ k) off (2 * ks) +
  (-(NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] *
     partial_invntt p (2 ^ k) off (2 * ks + 1))) by ring.
rewrite /partial_invntt.
rewrite (Rq.BigDom.BAdd.big_cat_int (2 ^ k) 0 (2 ^ (k + 1))).
+ by rewrite expr_ge0.
+ have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  by rewrite pow2S //; smt(expr_ge0).
rewrite Rq.BigDom.BAdd.mulr_sumr.
congr.
+ apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
  have hi_rng : i \in range 0 (2 ^ k) by rewrite mem_range.
  have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  have haddr : ks * 2 ^ (k + 1) + i = inv_low_addr k ks i.
  + rewrite /inv_low_addr pow2S //; ring.
  have hidx : (2 * ks) * 2 ^ k + i = ks * 2 ^ (k + 1) + i.
  + rewrite pow2S //; ring.
  rewrite hidx.
  have hzaddr :
    Zq.exp zroot (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + i) + 1) * 2 ^ k)) =
    NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks].
  + rewrite haddr.
    by rewrite inv_low_twiddle_factor 1:hk 1:hks 1:hi_rng.
  have -> :
    NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] *
    (p.[ks * 2 ^ (k + 1) + i] *
     Zq.exp zroot (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + i) + 1) * off))) =
    p.[ks * 2 ^ (k + 1) + i] *
    (Zq.exp zroot (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + i) + 1) * 2 ^ k)) *
     Zq.exp zroot (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + i) + 1) * off))).
  + rewrite -hzaddr; ring.
  rewrite -ZqRing.exprD.
  + exact NTT_Fq.unit_zroot.
  have -> :
    - ((2 * bsrev 8 (ks * 2 ^ (k + 1) + i) + 1) * 2 ^ k) +
    - ((2 * bsrev 8 (ks * 2 ^ (k + 1) + i) + 1) * off) =
    - ((2 * bsrev 8 (ks * 2 ^ (k + 1) + i) + 1) *
       (2 ^ k + off)) by ring.
  by [].
rewrite Rq.BigDom.BAdd.mulr_sumr.
rewrite Rq.BigDom.BAdd.sumrN.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
rewrite (Rq.BigDom.BAdd.big_addn 0 (2 ^ (k + 1)) (2 ^ k)) /=.
have -> : 2 ^ (k + 1) - 2 ^ k = 2 ^ k.
+ by rewrite pow2S //; ring.
apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
have hi_rng : i \in range 0 (2 ^ k) by rewrite mem_range.
have haddr : ks * 2 ^ (k + 1) + (i + 2 ^ k) = inv_high_addr k ks i.
+ rewrite inv_high_addrE pow2S //; ring.
have hidx :
  (2 * ks + 1) * 2 ^ k + i =
  ks * 2 ^ (k + 1) + (i + 2 ^ k).
+ rewrite pow2S //; ring.
rewrite hidx.
have hzaddr :
  Zq.exp zroot
    (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + (i + 2 ^ k)) + 1) * 2 ^ k)) =
  - NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks].
+ rewrite haddr.
  by rewrite inv_high_twiddle_factor 1:hk 1:hks 1:hi_rng.
have hzeta :
  NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] =
  - Zq.exp zroot
      (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + (i + 2 ^ k)) + 1) * 2 ^ k)).
+ rewrite hzaddr; ring.
have -> :
  - (NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] *
     (p.[ks * 2 ^ (k + 1) + (i + 2 ^ k)] *
      Zq.exp zroot
        (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + (i + 2 ^ k)) + 1) * off)))) =
  p.[ks * 2 ^ (k + 1) + (i + 2 ^ k)] *
  (Zq.exp zroot
     (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + (i + 2 ^ k)) + 1) * 2 ^ k)) *
   Zq.exp zroot
     (- ((2 * bsrev 8 (ks * 2 ^ (k + 1) + (i + 2 ^ k)) + 1) * off))).
+ rewrite hzeta; ring.
rewrite -ZqRing.exprD.
+ exact NTT_Fq.unit_zroot.
have -> :
  - ((2 * bsrev 8 (ks * 2 ^ (k + 1) + (i + 2 ^ k)) + 1) * 2 ^ k) +
  - ((2 * bsrev 8 (ks * 2 ^ (k + 1) + (i + 2 ^ k)) + 1) * off) =
  - ((2 * bsrev 8 (ks * 2 ^ (k + 1) + (i + 2 ^ k)) + 1) *
     (2 ^ k + off)) by ring.
by [].
qed.

op inv_old_pair_spec (r p : poly, k ks off : int) =
  partial_invntt_spec r p (2 ^ k) off (2 * ks) /\
  partial_invntt_spec r p (2 ^ k) off (2 * ks + 1).

op inv_new_pair_spec (r p : poly, k ks off : int) =
  partial_invntt_spec r p (2 ^ (k + 1)) off ks /\
  partial_invntt_spec r p (2 ^ (k + 1)) (2 ^ k + off) ks.

op inv_pair_done (ks off ks' off' : int) =
  ks' < ks \/ (ks' = ks /\ off' < off).

op inv_stage_progress (r p : poly, k ks off : int) =
  forall ks' off',
    ks' \in range 0 (2 ^ (7 - k)) =>
    off' \in range 0 (2 ^ k) =>
    if inv_pair_done ks off ks' off' then
      inv_new_pair_spec r p k ks' off'
    else
      inv_old_pair_spec r p k ks' off'.

op set2_inv_mulr (p : poly, z : coeff, a b : int) =
  p.[a <- p.[a] + p.[b]].[b <- z * (p.[a] + (-p.[b]))].

lemma inv_pair_addr_disjoint k ks off ks' off' :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  ks' \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  off' \in range 0 (2 ^ k) =>
  (ks' <> ks \/ off' <> off) =>
  inv_low_addr k ks' off' <> inv_low_addr k ks off /\
  inv_low_addr k ks' off' <> inv_high_addr k ks off /\
  inv_high_addr k ks' off' <> inv_low_addr k ks off /\
  inv_high_addr k ks' off' <> inv_high_addr k ks off.
proof.
move=> hk hks hks' hoff hoff' hneq.
pose l := 2 ^ k.
have hl : 0 < l by rewrite /l expr_gt0.
have hpow : 2 ^ (k + 1) = 2 * l.
+ by rewrite /l pow2S; rewrite mem_range in hk; smt().
have hoff_l : off \in range 0 l by rewrite /l.
have hoff'_l : off' \in range 0 l by rewrite /l.
rewrite /inv_low_addr /inv_high_addr hpow.
split.
+ apply/negP => heq.
  have hmod :
    (ks' * (2 * l) + off') %% (2 * l) =
    (ks * (2 * l) + off) %% (2 * l) by rewrite heq.
  have hoffeq : off' = off.
  + move: hmod.
    rewrite (block_low_mod l ks' off' hl hoff'_l).
    by rewrite (block_low_mod l ks off hl hoff_l).
  have hdiv :
    (ks' * (2 * l) + off') %/ (2 * l) =
    (ks * (2 * l) + off) %/ (2 * l) by rewrite heq.
  have hkseq : ks' = ks.
  + move: hdiv.
    rewrite (block_low_div l ks' off' hl hoff'_l).
    by rewrite (block_low_div l ks off hl hoff_l).
  by smt().
split.
+ apply/negP => heq.
  have hmod :
    (ks' * (2 * l) + off') %% (2 * l) =
    (ks * (2 * l) + (l + off)) %% (2 * l).
  + have heq' : ks' * (2 * l) + off' = ks * (2 * l) + (l + off) by smt().
    by rewrite heq'.
  move: hmod.
  rewrite (block_low_mod l ks' off' hl hoff'_l).
  rewrite (block_high_mod l ks off hl hoff_l).
  rewrite mem_range in hoff_l.
  rewrite mem_range in hoff'_l.
  by smt().
split.
+ apply/negP => heq.
  have hmod :
    (ks' * (2 * l) + (l + off')) %% (2 * l) =
    (ks * (2 * l) + off) %% (2 * l).
  + have heq' : ks' * (2 * l) + (l + off') = ks * (2 * l) + off by smt().
    by rewrite heq'.
  move: hmod.
  rewrite (block_high_mod l ks' off' hl hoff'_l).
  rewrite (block_low_mod l ks off hl hoff_l).
  rewrite mem_range in hoff_l.
  rewrite mem_range in hoff'_l.
  by smt().
apply/negP => heq.
have hmod :
  (ks' * (2 * l) + (l + off')) %% (2 * l) =
  (ks * (2 * l) + (l + off)) %% (2 * l).
+ have heq' : ks' * (2 * l) + (l + off') = ks * (2 * l) + (l + off) by smt().
  by rewrite heq'.
have hoffeq : off' = off.
+ move: hmod.
  rewrite (block_high_mod l ks' off' hl hoff'_l).
  rewrite (block_high_mod l ks off hl hoff_l).
  by smt().
have hdiv :
  (ks' * (2 * l) + (l + off')) %/ (2 * l) =
  (ks * (2 * l) + (l + off)) %/ (2 * l).
+ have heq' : ks' * (2 * l) + (l + off') = ks * (2 * l) + (l + off) by smt().
  by rewrite heq'.
have hkseq : ks' = ks.
+ move: hdiv.
  rewrite (block_high_div l ks' off' hl hoff'_l).
  by rewrite (block_high_div l ks off hl hoff_l).
by smt().
qed.

lemma set2_inv_mulr_eq1 p z a b :
  a <> b =>
  a \in range 0 256 =>
  (set2_inv_mulr p z a b).[a] = p.[a] + p.[b].
proof.
move=> hab /mem_range ha.
rewrite /set2_inv_mulr Array256.get_set_if /=.
have -> : (a = b) = false by smt().
by rewrite Array256.get_set_if /= ha.
qed.

lemma set2_inv_mulr_eq2 p z a b :
  b \in range 0 256 =>
  (set2_inv_mulr p z a b).[b] = z * (p.[a] + (-p.[b])).
proof.
move=> /mem_range hb.
by rewrite /set2_inv_mulr Array256.get_set_if /= hb.
qed.

lemma set2_inv_mulr_neq p z a b x :
  x <> a =>
  x <> b =>
  (set2_inv_mulr p z a b).[x] = p.[x].
proof.
move=> hxa hxb.
by rewrite /set2_inv_mulr !Array256.get_set_if /= hxa hxb.
qed.

lemma set2_inv_mulr_assign (p : poly) (z : coeff) (a b : int) :
  (p.[a <- p.[a] + p.[b]]
    .[b <- z * (p.[a] + (-p.[b]))]) =
  set2_inv_mulr p z a b.
proof. by rewrite /set2_inv_mulr. qed.

lemma partial_invntt_spec_neq_update p r z len start bsj a b :
  bsj * len + start <> a =>
  bsj * len + start <> b =>
  partial_invntt_spec r p len start bsj =>
  partial_invntt_spec (set2_inv_mulr r z a b) p len start bsj.
proof.
move=> hxa hxb.
rewrite /partial_invntt_spec.
by rewrite set2_inv_mulr_neq.
qed.

lemma inv_old_pair_spec_neq_update p r z k ks off ks' off' :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  ks' \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  off' \in range 0 (2 ^ k) =>
  (ks' <> ks \/ off' <> off) =>
  inv_old_pair_spec r p k ks' off' =>
  inv_old_pair_spec
    (set2_inv_mulr r z (inv_low_addr k ks off) (inv_high_addr k ks off))
    p k ks' off'.
proof.
move=> hk hks hks' hoff hoff' hneq hold.
have [dLL [dLH [dHL dHH]]] :=
  inv_pair_addr_disjoint k ks off ks' off' hk hks hks' hoff hoff' hneq.
rewrite /inv_old_pair_spec in hold.
move: hold => [hlo hhi].
rewrite /inv_old_pair_spec.
split.
+ apply
    (partial_invntt_spec_neq_update p r z (2 ^ k) off' (2 * ks')
       (inv_low_addr k ks off) (inv_high_addr k ks off)).
  + have -> : (2 * ks') * 2 ^ k + off' = inv_low_addr k ks' off'.
    + rewrite /inv_low_addr pow2S; first by rewrite mem_range in hk; smt().
      by ring.
    exact dLL.
  + have -> : (2 * ks') * 2 ^ k + off' = inv_low_addr k ks' off'.
    + rewrite /inv_low_addr pow2S; first by rewrite mem_range in hk; smt().
      by ring.
    exact dLH.
  + exact hlo.
+ apply
    (partial_invntt_spec_neq_update p r z (2 ^ k) off' (2 * ks' + 1)
       (inv_low_addr k ks off) (inv_high_addr k ks off)).
  + have -> : (2 * ks' + 1) * 2 ^ k + off' = inv_high_addr k ks' off'.
    + rewrite inv_high_addrE pow2S; first by rewrite mem_range in hk; smt().
      by ring.
    exact dHL.
  + have -> : (2 * ks' + 1) * 2 ^ k + off' = inv_high_addr k ks' off'.
    + rewrite inv_high_addrE pow2S; first by rewrite mem_range in hk; smt().
      by ring.
    exact dHH.
  + exact hhi.
qed.

lemma inv_new_pair_spec_neq_update p r z k ks off ks' off' :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  ks' \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  off' \in range 0 (2 ^ k) =>
  (ks' <> ks \/ off' <> off) =>
  inv_new_pair_spec r p k ks' off' =>
  inv_new_pair_spec
    (set2_inv_mulr r z (inv_low_addr k ks off) (inv_high_addr k ks off))
    p k ks' off'.
proof.
move=> hk hks hks' hoff hoff' hneq hnew.
have [dLL [dLH [dHL dHH]]] :=
  inv_pair_addr_disjoint k ks off ks' off' hk hks hks' hoff hoff' hneq.
rewrite /inv_new_pair_spec in hnew.
move: hnew => [hlo hhi].
rewrite /inv_new_pair_spec.
split.
  + apply
      (partial_invntt_spec_neq_update p r z (2 ^ (k + 1)) off' ks'
         (inv_low_addr k ks off) (inv_high_addr k ks off)).
    + have -> : ks' * 2 ^ (k + 1) + off' = inv_low_addr k ks' off'
      by rewrite /inv_low_addr.
      exact dLL.
    + have -> : ks' * 2 ^ (k + 1) + off' = inv_low_addr k ks' off'
      by rewrite /inv_low_addr.
      exact dLH.
    + exact hlo.
  + apply
      (partial_invntt_spec_neq_update p r z (2 ^ (k + 1)) (2 ^ k + off') ks'
         (inv_low_addr k ks off) (inv_high_addr k ks off)).
    + have -> :
        ks' * 2 ^ (k + 1) + (2 ^ k + off') =
        inv_high_addr k ks' off'
      by rewrite inv_high_addrE.
      exact dHL.
    + have -> :
        ks' * 2 ^ (k + 1) + (2 ^ k + off') =
        inv_high_addr k ks' off'
      by rewrite inv_high_addrE.
      exact dHH.
    + exact hhi.
qed.

lemma inv_stage_progress_init p r k :
  k \in range 0 8 =>
  inv_stage_spec r p (2 ^ k) =>
  inv_stage_progress r p k 0 0.
proof.
move=> hk hstage.
rewrite /inv_stage_progress => ks' off' hks' hoff'.
case: (inv_pair_done 0 0 ks' off') => hdone.
+ rewrite /inv_pair_done in hdone.
  rewrite mem_range in hks'.
  rewrite mem_range in hoff'.
  by smt().
rewrite /inv_old_pair_spec.
have [hks0 hks1] := div256_pair_range k ks' hk hks'.
split.
+ apply (hstage off' (2 * ks')).
  + exact hoff'.
  + have -> : 2 * ks' = ks' * 2 by ring.
    exact hks0.
+ apply (hstage off' (2 * ks' + 1)).
  + exact hoff'.
  + have -> : 2 * ks' + 1 = ks' * 2 + 1 by ring.
    exact hks1.
qed.

lemma inv_stage_progress_old p r k ks off ks' off' :
  inv_pair_done ks off ks' off' = false =>
  inv_stage_progress r p k ks off =>
  ks' \in range 0 (2 ^ (7 - k)) =>
  off' \in range 0 (2 ^ k) =>
  inv_old_pair_spec r p k ks' off'.
proof.
move=> hdone hprog hks' hoff'.
move: (hprog ks' off' hks' hoff').
by rewrite hdone.
qed.

lemma inv_stage_progress_new p r k ks off ks' off' :
  inv_pair_done ks off ks' off' = true =>
  inv_stage_progress r p k ks off =>
  ks' \in range 0 (2 ^ (7 - k)) =>
  off' \in range 0 (2 ^ k) =>
  inv_new_pair_spec r p k ks' off'.
proof.
move=> hdone hprog hks' hoff'.
move: (hprog ks' off' hks' hoff').
by rewrite hdone.
qed.

lemma inverse_pair_refines_values p r k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  partial_invntt_spec r p (2 ^ k) off (2 * ks) =>
  partial_invntt_spec r p (2 ^ k) off (2 * ks + 1) =>
  let z = NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks] in
  partial_invntt_spec
    (set2_inv_mulr r z (inv_low_addr k ks off) (inv_high_addr k ks off))
    p (2 ^ (k + 1)) off ks /\
  partial_invntt_spec
    (set2_inv_mulr r z (inv_low_addr k ks off) (inv_high_addr k ks off))
    p (2 ^ (k + 1)) (2 ^ k + off) ks.
proof.
move=> hk hks hoff hpa hpb /=.
have [ha_rng [hb_rng hab]] := inv_pair_inputs k ks off hk hks hoff.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have ha_eq : inv_low_addr k ks off = (2 * ks) * 2 ^ k + off.
+ rewrite /inv_low_addr pow2S //; ring.
have hb_eq : inv_high_addr k ks off = (2 * ks + 1) * 2 ^ k + off.
+ rewrite inv_high_addrE pow2S //; ring.
  split.
  + rewrite /partial_invntt_spec.
    have haddr_low :
      ks * 2 ^ (k + 1) + off = inv_low_addr k ks off
      by rewrite /inv_low_addr.
    rewrite haddr_low.
    rewrite
      (set2_inv_mulr_eq1 r NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks]
         (inv_low_addr k ks off) (inv_high_addr k ks off) hab ha_rng).
    rewrite ha_eq hb_eq hpa hpb.
    by rewrite -partial_invntt_split_low.
  + rewrite /partial_invntt_spec.
    have haddr_high :
      ks * 2 ^ (k + 1) + (2 ^ k + off) = inv_high_addr k ks off
      by rewrite inv_high_addrE.
    rewrite haddr_high.
    rewrite
      (set2_inv_mulr_eq2 r NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks]
         (inv_low_addr k ks off) (inv_high_addr k ks off) hb_rng).
    rewrite ha_eq hb_eq hpa hpb.
    by rewrite -partial_invntt_split_high.
qed.

lemma inv_stage_progress_step p r k ks off :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  off \in range 0 (2 ^ k) =>
  inv_stage_progress r p k ks off =>
  inv_stage_progress
    (set2_inv_mulr r NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks]
       (inv_low_addr k ks off) (inv_high_addr k ks off))
    p k ks (off + 1).
proof.
move=> hk hks hoff hprog.
rewrite /inv_stage_progress => ks' off' hks' hoff'.
case: (ks' = ks /\ off' = off) => hcur.
+ move: hcur => [hks_eq hoff_eq].
  have hprev_false : inv_pair_done ks off ks' off' = false.
  + rewrite /inv_pair_done.
    by smt().
  have hold :=
    inv_stage_progress_old p r k ks off ks' off'
      hprev_false hprog hks' hoff'.
  rewrite hks_eq hoff_eq in hold.
  rewrite /inv_old_pair_spec in hold.
  move: hold => [hold0 hold1].
  have hpair :=
    inverse_pair_refines_values p r k ks off hk hks hoff hold0 hold1.
  have hnext_true : inv_pair_done ks (off + 1) ks' off' = true.
  + rewrite /inv_pair_done.
    by smt().
  rewrite hnext_true /inv_new_pair_spec.
  by rewrite hks_eq hoff_eq.
have hneq : ks' <> ks \/ off' <> off by smt().
case: (inv_pair_done ks (off + 1) ks' off') => hnext.
+ have hprev_true : inv_pair_done ks off ks' off' = true.
  + rewrite /inv_pair_done.
    rewrite /inv_pair_done in hnext.
    by smt().
  have hnew :=
    inv_stage_progress_new p r k ks off ks' off'
      hprev_true hprog hks' hoff'.
  exact
    (inv_new_pair_spec_neq_update p r
       NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks]
       k ks off ks' off' hk hks hks' hoff hoff' hneq hnew).
have hprev_false : inv_pair_done ks off ks' off' = false.
+ rewrite /inv_pair_done.
  rewrite /inv_pair_done in hnext.
  by smt().
have hold :=
  inv_stage_progress_old p r k ks off ks' off'
    hprev_false hprog hks' hoff'.
exact
  (inv_old_pair_spec_neq_update p r
     NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks]
     k ks off ks' off' hk hks hks' hoff hoff' hneq hold).
qed.

lemma inv_stage_progress_next_block p r k ks :
  k \in range 0 8 =>
  ks \in range 0 (2 ^ (7 - k)) =>
  inv_stage_progress r p k ks (2 ^ k) =>
  inv_stage_progress r p k (ks + 1) 0.
proof.
move=> hk hks hprog.
rewrite /inv_stage_progress => ks' off' hks' hoff'.
have hdone :
  inv_pair_done (ks + 1) 0 ks' off' =
  inv_pair_done ks (2 ^ k) ks' off'.
+ rewrite /inv_pair_done.
  rewrite mem_range in hoff'.
  by smt().
rewrite hdone.
exact (hprog ks' off' hks' hoff').
qed.

lemma inv_stage_progress_finish p r k :
  k \in range 0 8 =>
  inv_stage_progress r p k (2 ^ (7 - k)) 0 =>
  inv_stage_spec r p (2 ^ (k + 1)).
proof.
move=> hk hprog.
rewrite /inv_stage_spec => start bsj hstart hbsj.
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have hbsj' : bsj \in range 0 (2 ^ (7 - k)).
+ move: hbsj.
  by rewrite (div256_pow2_next k hk).
case: (start < 2 ^ k) => hlow.
+ have hoff : start \in range 0 (2 ^ k).
  + rewrite mem_range in hstart.
    rewrite mem_range.
    smt(expr_ge0).
  have hdone : inv_pair_done (2 ^ (7 - k)) 0 bsj start = true.
  + rewrite /inv_pair_done.
    rewrite mem_range in hbsj'.
    by smt().
  have hnew :=
    inv_stage_progress_new p r k (2 ^ (7 - k)) 0 bsj start
      hdone hprog hbsj' hoff.
  by rewrite /inv_new_pair_spec in hnew; move: hnew => [hlo _].
have hoff : start - 2 ^ k \in range 0 (2 ^ k).
+ rewrite mem_range in hstart.
  rewrite mem_range.
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k by rewrite pow2S.
  smt(expr_ge0).
have hdone : inv_pair_done (2 ^ (7 - k)) 0 bsj (start - 2 ^ k) = true.
+ rewrite /inv_pair_done.
  rewrite mem_range in hbsj'.
  by smt().
have hnew :=
  inv_stage_progress_new p r k (2 ^ (7 - k)) 0 bsj (start - 2 ^ k)
    hdone hprog hbsj' hoff.
rewrite /inv_new_pair_spec in hnew.
move: hnew => [_ hhi].
have hstart_eq : 2 ^ k + (start - 2 ^ k) = start by ring.
rewrite -hstart_eq.
exact hhi.
qed.

op inv_outer_inv (p r zetas_inv : poly, len zetasctr : int) =
  zetas_inv = NTT_Fq.zetas_inv /\
  ((exists k,
      k \in range 0 8 /\
      len = 2 ^ k /\
      zetasctr = 256 - 2 ^ (8 - k) /\
      inv_stage_spec r p (2 ^ k)) \/
   (len = 256 /\
    zetasctr = 255 /\
    inv_stage_spec r p 256)).

op inv_middle_inv (p r zetas_inv : poly, len start zetasctr : int) =
  zetas_inv = NTT_Fq.zetas_inv /\
  exists k ks,
    k \in range 0 8 /\
    len = 2 ^ k /\
    0 <= ks <= 2 ^ (7 - k) /\
    start = ks * 2 ^ (k + 1) /\
    zetasctr = 256 - 2 ^ (8 - k) + ks /\
    inv_stage_progress r p k ks 0.

op inv_inner_inv
   (p r zetas_inv : poly, len start j zetasctr : int, zeta_ : coeff) =
  zetas_inv = NTT_Fq.zetas_inv /\
  exists k ks off,
    k \in range 0 8 /\
    ks \in range 0 (2 ^ (7 - k)) /\
    0 <= off <= 2 ^ k /\
    len = 2 ^ k /\
    start = ks * 2 ^ (k + 1) /\
    j = start + off /\
    zetasctr = 256 - 2 ^ (8 - k) + ks + 1 /\
    zeta_ = zetas_inv.[zetasctr - 1] /\
    inv_stage_progress r p k ks off.

op inv_post_inv (p r zetas_inv : poly, j : int) =
  zetas_inv = NTT_Fq.zetas_inv /\
  exists base,
    inv_stage_spec base p 256 /\
    0 <= j <= 256 /\
    forall i,
      i \in range 0 256 =>
      r.[i] = if i < j then base.[i] * zetas_inv.[255] else base.[i].

lemma inv_stage1_init (p : poly) :
  inv_stage_spec p p 1.
proof.
rewrite /inv_stage_spec => start bsj hstart hbsj.
have hstart0 : start = 0.
+ rewrite mem_range in hstart.
  by smt().
rewrite /partial_invntt_spec /partial_invntt hstart0.
rewrite Rq.BigDom.BAdd.big_int1 /=.
by rewrite ZqRing.expr0 ZqRing.mulr1.
qed.

lemma inv_outer_inv_init p :
  inv_outer_inv p p NTT_Fq.zetas_inv 1 0.
proof.
rewrite /inv_outer_inv.
split; first by [].
left; exists 0.
split; first by rewrite range_ltn.
split; first by [].
split; first by [].
exact (inv_stage1_init p).
qed.

lemma inv_outer_enter_middle p r zetas_inv len zetasctr :
  inv_outer_inv p r zetas_inv len zetasctr =>
  len < 256 =>
  inv_middle_inv p r zetas_inv len 0 zetasctr.
proof.
rewrite /inv_outer_inv /inv_middle_inv.
move=> [hzetas [hstage | hdone]] hguard.
+ move: hstage => [k [hk [hlen [hzc hspec]]]].
  split; first exact hzetas.
  exists k 0.
  split; first exact hk.
  split; first exact hlen.
  split; first by smt(expr_ge0).
  split.
  + by ring.
  split; first by rewrite hzc; ring.
  by apply inv_stage_progress_init.
move: hdone => [hlen [_ _]].
by smt().
qed.

lemma inv_middle_enter_inner p r zetas_inv len start zetasctr :
  inv_middle_inv p r zetas_inv len start zetasctr =>
  start < 256 =>
  inv_inner_inv p r zetas_inv len start start (zetasctr + 1)
    zetas_inv.[zetasctr].
proof.
rewrite /inv_middle_inv /inv_inner_inv.
move=> [hzetas hex] hguard.
move: hex => [k ks [hk [hlen [hksb [hstart [hzc hprog]]]]]].
split; first exact hzetas.
have hblock := inv_stage_blocks_product k hk.
have hks : ks \in range 0 (2 ^ (7 - k)).
+ rewrite mem_range.
  rewrite mem_range in hk.
  by smt(expr_gt0).
exists k ks 0.
split; first exact hk.
split; first exact hks.
split; first by smt(expr_ge0).
split; first exact hlen.
split; first exact hstart.
split; first by ring.
split; first by rewrite hzc; ring.
split.
+ have -> : zetasctr + 1 - 1 = zetasctr by ring.
  by [].
exact hprog.
qed.

lemma inv_inner_step_set2 p r zetas_inv len start j zetasctr zeta_ :
  inv_inner_inv p r zetas_inv len start j zetasctr zeta_ =>
  j < start + len =>
  inv_inner_inv p
    (set2_inv_mulr r zeta_ j (j + len))
    zetas_inv len start (j + 1) zetasctr zeta_.
proof.
rewrite /inv_inner_inv.
move=> [hzetas hex] hguard.
move: hex => [k ks off [hk [hks [hoffb [hlen [hstart [hj [hzc [hzeta hprog]]]]]]]]].
split; first exact hzetas.
have hoff : off \in range 0 (2 ^ k).
+ rewrite mem_range.
  move: hoffb => [hoff0 hoffle].
  split; first exact hoff0.
  move: hguard.
  rewrite hj hlen.
  by smt().
exists k ks (off + 1).
split; first exact hk.
split; first exact hks.
split; first by rewrite mem_range in hoff; smt().
split; first exact hlen.
split; first exact hstart.
split; first by rewrite hj; ring.
split; first exact hzc.
split; first exact hzeta.
have hstep :=
  inv_stage_progress_step p r k ks off hk hks hoff hprog.
have -> :
  zeta_ = NTT_Fq.zetas_inv.[256 - 2 ^ (8 - k) + ks].
+ by rewrite hzeta hzetas hzc; congr; ring.
have -> :
  j = inv_low_addr k ks off.
+ by rewrite /inv_low_addr hj hstart.
have -> :
  inv_low_addr k ks off + len = inv_high_addr k ks off.
+ by rewrite /inv_high_addr hlen.
exact hstep.
qed.

lemma inv_inner_step_array p r zetas_inv len start j zetasctr zeta_ :
  inv_inner_inv p r zetas_inv len start j zetasctr zeta_ =>
  j < start + len =>
  inv_inner_inv p
    ((r.[j <- r.[j] + r.[j + len]])
       .[j + len <-
          r.[j] +
          (-(r.[j <- r.[j] + r.[j + len]].[j + len]))]
       .[j + len <-
          zeta_ *
          ((r.[j <- r.[j] + r.[j + len]])
             .[j + len <-
                r.[j] +
                (-(r.[j <- r.[j] + r.[j + len]].[j + len]))])
             .[j + len]])
    zetas_inv len start (j + 1) zetasctr zeta_.
proof.
move=> hin hguard.
rewrite /inv_inner_inv in hin.
move: hin => [hzetas hex].
move: hex => [k ks off [hk [hks [hoffb [hlen [hstart [hj [hzc [hzeta hprog]]]]]]]]].
have hoff : off \in range 0 (2 ^ k).
+ rewrite mem_range.
  move: hoffb => [hoff0 hoffle].
  split; first exact hoff0.
  move: hguard.
  rewrite hj hlen.
  by smt().
	have [hj_rng [hjlen_rng0 hj_neq]] := inv_pair_inputs k ks off hk hks hoff.
have hj_low : j = inv_low_addr k ks off.
+ by rewrite /inv_low_addr hj hstart.
	have hj_high : j + len = inv_high_addr k ks off.
	+ by rewrite hj_low /inv_high_addr hlen.
	have hjlen_rng : j + len \in range 0 256.
	+ by rewrite hj_high.
	have hj_neqlen : j <> j + len by smt().
have hassign :
  ((r.[j <- r.[j] + r.[j + len]])
     .[j + len <-
        r.[j] +
        (-(r.[j <- r.[j] + r.[j + len]].[j + len]))]
     .[j + len <-
        zeta_ *
        ((r.[j <- r.[j] + r.[j + len]])
           .[j + len <-
              r.[j] +
              (-(r.[j <- r.[j] + r.[j + len]].[j + len]))])
           .[j + len]]) =
	  set2_inv_mulr r zeta_ j (j + len).
	+ have hget1 :
	    (r.[j <- r.[j] + r.[j + len]]).[j + len] = r.[j + len].
	  + rewrite Array256.get_set_if /=.
	    by smt().
	  rewrite hget1.
	  have hget2 :
	    (r.[j <- r.[j] + r.[j + len]]
	       .[j + len <- r.[j] + (-r.[j + len])]).[j + len] =
	    r.[j] + (-r.[j + len]).
	  + have hbound : 0 <= j + len < 256.
	    + rewrite mem_range in hjlen_rng.
	      exact hjlen_rng.
	    by rewrite Array256.get_set_if /= hbound.
	  rewrite hget2.
	  rewrite Array256.set_set_eq.
	  by rewrite set2_inv_mulr_assign.
rewrite hassign.
apply inv_inner_step_set2.
+ rewrite /inv_inner_inv.
  split; first exact hzetas.
  exists k ks off.
  split; first exact hk.
  split; first exact hks.
  split; first exact hoffb.
  split; first exact hlen.
  split; first exact hstart.
  split; first exact hj.
  split; first exact hzc.
  split; first exact hzeta.
  exact hprog.
exact hguard.
qed.

lemma inv_inner_step_array_wp p r zetas_inv len start j zetasctr zeta_ :
  inv_inner_inv p r zetas_inv len start j zetasctr zeta_ =>
  j < start + len =>
  inv_inner_inv p
    ((r.[j <- r.[j] + r.[j + len]])
       .[j + len <-
          zeta_ *
          ((r.[j <- r.[j] + r.[j + len]])
             .[j + len <-
                r.[j] -
                (r.[j <- r.[j] + r.[j + len]]).[j + len]])
             .[j + len]])
    zetas_inv len start (j + 1) zetasctr zeta_.
proof.
move=> hin hguard.
have hstep :=
  inv_inner_step_array p r zetas_inv len start j zetasctr zeta_ hin hguard.
move: hstep.
rewrite Array256.set_set_eq.
by [].
qed.

lemma inv_inner_exit_middle p r zetas_inv len start j zetasctr zeta_ :
  inv_inner_inv p r zetas_inv len start j zetasctr zeta_ =>
  ! j < start + len =>
  inv_middle_inv p r zetas_inv len (j + len) zetasctr.
proof.
rewrite /inv_inner_inv /inv_middle_inv.
move=> [hzetas hex] hstop.
move: hex => [k ks off [hk [hks [hoffb [hlen [hstart [hj [hzc [_ hprog]]]]]]]]].
split; first exact hzetas.
have hoff_end : off = 2 ^ k.
+ move: hoffb => [hoff0 hoffle].
  move: hstop.
  rewrite hj hlen.
  by smt().
exists k (ks + 1).
split; first exact hk.
split; first exact hlen.
split.
+ rewrite mem_range in hks.
  by smt().
split.
+ have hk0 : 0 <= k by rewrite mem_range in hk; smt().
  have hpowS : 2 ^ (k + 1) = 2 * 2 ^ k by rewrite (pow2S k hk0).
  rewrite hj hstart hlen hoff_end hpowS.
  by ring.
split.
+ rewrite hzc.
  by ring.
have hprog_end : inv_stage_progress r p k ks (2 ^ k).
+ by rewrite -hoff_end.
exact (inv_stage_progress_next_block p r k ks hk hks hprog_end).
qed.

lemma inv_middle_exit_outer p r zetas_inv len start zetasctr :
  inv_middle_inv p r zetas_inv len start zetasctr =>
  ! start < 256 =>
  inv_outer_inv p r zetas_inv (len * 2) zetasctr.
proof.
rewrite /inv_middle_inv /inv_outer_inv.
move=> [hzetas hex] hstop.
move: hex => [k ks [hk [hlen [hksb [hstart [hzc hprog]]]]]].
split; first exact hzetas.
have hblock := inv_stage_blocks_product k hk.
have hks_end : ks = 2 ^ (7 - k).
+ move: hksb => [hks0 hksle].
  have hstart_le : start <= 256.
  + rewrite hstart.
    by smt(expr_ge0).
  have hstart_ge : 256 <= start by rewrite -lezNgt in hstop.
  have hstart_eq : start = 256 by smt().
  by smt(expr_gt0).
have hprog_end : inv_stage_progress r p k (2 ^ (7 - k)) 0.
+ by rewrite -hks_end.
have hfinish : inv_stage_spec r p (2 ^ (k + 1)).
+ exact (inv_stage_progress_finish p r k hk hprog_end).
case: (k < 7) => hklt7.
+ left; exists (k + 1).
  have hk_next : k + 1 \in range 0 8.
  + rewrite mem_range in hk.
    by rewrite mem_range; smt().
  split; first exact hk_next.
  split.
  + rewrite hlen.
    have hk0 : 0 <= k by rewrite mem_range in hk; smt().
    rewrite (pow2S k hk0).
    by ring.
  split.
  + rewrite hzc hks_end.
    have h7k : 0 <= 7 - k by rewrite mem_range in hk; smt().
    have hpow : 2 ^ (8 - k) = 2 * 2 ^ (7 - k).
    + have -> : 8 - k = 7 - k + 1 by ring.
      by rewrite pow2S.
    have -> : 8 - (k + 1) = 7 - k by ring.
    by rewrite hpow; ring.
  exact hfinish.
right.
have hk_eq7 : k = 7 by rewrite mem_range in hk; smt().
rewrite hlen hzc hks_end hk_eq7 /=.
move: hfinish; rewrite hk_eq7 /=.
by [].
qed.

lemma inv_outer_exit_stage p r zetas_inv len zetasctr :
  inv_outer_inv p r zetas_inv len zetasctr =>
  ! len < 256 =>
  inv_stage_spec r p 256.
proof.
rewrite /inv_outer_inv.
move=> [_ [hstage | hdone]] hstop.
  + move: hstage => [k [hk [hlen [_ hspec]]]].
    have hlt : len < 256.
    + rewrite hlen.
      have hk0 : 0 <= k by rewrite mem_range in hk; smt().
      have hk7 : k <= 7 by rewrite mem_range in hk; smt().
      have hle : 2 ^ k <= 2 ^ 7.
      + apply StdOrder.IntOrder.ler_weexpn2l.
        + by smt().
        by split.
      by smt().
    by smt().
by move: hdone => [_ [_ hspec]].
qed.

lemma inv_outer_exit_post p r zetas_inv len zetasctr :
  inv_outer_inv p r zetas_inv len zetasctr =>
  ! len < 256 =>
  inv_post_inv p r zetas_inv 0.
proof.
move=> hin hstop.
have hstage := inv_outer_exit_stage p r zetas_inv len zetasctr hin hstop.
rewrite /inv_post_inv.
rewrite /inv_outer_inv in hin.
move: hin => [hzetas _].
split; first exact hzetas.
exists r.
split.
+ exact hstage.
split; first by smt().
move=> i hi.
have -> : (i < 0) = false.
+ rewrite mem_range in hi.
  by smt().
by [].
qed.

lemma inv_post_step p r zetas_inv j :
  inv_post_inv p r zetas_inv j =>
  j < 256 =>
  inv_post_inv p (r.[j <- r.[j] * zetas_inv.[255]]) zetas_inv (j + 1).
proof.
rewrite /inv_post_inv.
move=> [hzetas [base [hbase [hj hvals]]]] hguard.
split; first exact hzetas.
exists base.
split; first exact hbase.
split; first by smt().
move=> i hi.
rewrite Array256.get_set_if /=.
case: (i = j) => hij.
+ rewrite hij.
  have hjrng : j \in range 0 256 by rewrite mem_range; smt().
  have hjb : 0 <= j < 256 by rewrite mem_range in hjrng.
  rewrite hjb /=.
  rewrite hvals 1:hjrng.
  have -> : (j < j) = false by smt().
  have -> : (j < j + 1) = true by smt().
  by [].
case: (i < j) => hlt.
+ have -> : (i < j + 1) = true by smt().
  have hvali := hvals i hi.
  by rewrite hvali hlt.
have -> : (i < j + 1) = false by smt().
have hvali := hvals i hi.
by rewrite hvali hlt.
qed.

lemma zetas_inv_255 :
  NTT_Fq.zetas_inv.[255] = inv (incoeff 256).
proof.
by rewrite /NTT_Fq.zetas_inv /= NTT_Fq.scale255E.
qed.

lemma inv_post_exit_full p r zetas_inv j :
  inv_post_inv p r zetas_inv j =>
  ! j < 256 =>
  r = NTTFullSpec.full_invntt p.
proof.
rewrite /inv_post_inv.
move=> [hzetas [base [hbase [hj hvals]]]] hstop.
apply NTTFullSpec.full_invntt_spec_imp.
rewrite /NTTFullSpec.full_invntt_spec => i hi.
have hbr : bsrev 8 i \in range 0 256 by apply NTTFullSpec.bsrev8_range_256.
have hj256 : j = 256 by smt().
rewrite hvals 1:hbr.
have -> : (bsrev 8 i < j) = true.
+ rewrite hj256.
  rewrite mem_range in hbr.
  by smt().
rewrite hzetas zetas_inv_255.
have hbasei := hbase (bsrev 8 i) 0 hbr _.
+ by rewrite range_ltn.
move: hbasei.
rewrite /partial_invntt_spec.
have -> : 0 * 256 + bsrev 8 i = bsrev 8 i by ring.
move=> hbasei.
rewrite hbasei /partial_invntt.
have -> :
  Rq.BigDom.BAdd.bigi predT
    (fun s =>
       inv (incoeff 256) * p.[s] *
       ZqRing.exp zroot (- ((2 * br s + 1) * bsrev 8 i)))
    0 256 =
  Rq.BigDom.BAdd.bigi predT
    (fun s =>
       (p.[0 * 256 + s] *
        Zq.exp zroot (- ((2 * bsrev 8 (0 * 256 + s) + 1) * bsrev 8 i))) *
       inv (incoeff 256))
    0 256.
+ apply Rq.BigDom.BAdd.eq_big_int => s hs.
  by rewrite /br /=; ring.
by rewrite -Rq.BigDom.BAdd.mulr_suml.
qed.

lemma invntt_full_invntt (p : poly) :
  hoare [NTT_Fq.NTT.invntt :
    arg = (p, NTT_Fq.zetas_inv) ==> res = NTTFullSpec.full_invntt p].
proof.
proc.
wp.
while (inv_post_inv p r zetas_inv j).
+ wp.
  skip => &hr /=.
  smt(inv_post_step).
wp.
while (inv_outer_inv p r zetas_inv len zetasctr).
+ wp.
  while (inv_middle_inv p r zetas_inv len start zetasctr).
  + wp.
    while (inv_inner_inv p r zetas_inv len start j zetasctr zeta_).
    + wp.
      skip => &hr /=.
      smt(inv_inner_step_array_wp).
    wp.
    skip => &hr /=.
    smt(inv_middle_enter_inner inv_inner_exit_middle).
  wp.
  skip => &hr /=.
  smt(inv_outer_enter_middle inv_middle_exit_outer).
wp.
skip => &hr /=.
smt(inv_outer_inv_init inv_outer_exit_post inv_post_exit_full).
qed.

end NTTFullAlgebra.
