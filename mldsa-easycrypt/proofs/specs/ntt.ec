(* -------------------------------------------------------------------- *)
require import AllCore Array List Ring Number StdOrder IntDiv IntMin.
require import Poly ZModP PolyReduce.
require import BitEncoding.

import BS2Int.

(* -------------------------------------------------------------------- *)
type coeff.

clone import IDomain as QRing with type t <= coeff.

(* -------------------------------------------------------------------- *)
clone import PolyComRing as QPoly with
  type coeff <= coeff,
  theory Coeff <= QRing.

import QPoly.BigPoly.
import QPoly.PolyComRing.

clone PolyReduce as QPolyReduce with
  type coeff      <= coeff,
  theory Coeff    <- QPoly.Coeff,
  theory BasePoly <- QPoly.

import QPolyReduce.PIdeal.

(* -------------------------------------------------------------------- *)
op zeta_ : coeff.

(* -------------------------------------------------------------------- *)
type apoly = coeff array.

(* -------------------------------------------------------------------- *)
op bitrev (n : int) (i : int) = bs2int (rev (int2bs n i)).

(* -------------------------------------------------------------------- *)
module NTT = {
  proc ntt(p : apoly) : apoly = {
    var m, len, start, j : int;
    var t0, t1, z : coeff;

    m <- 0;
    len <- 128;

    while (1 <= len) {
      start <- 0;
      while (start < 256) {
        m <- m + 1;
        z <- exp zeta_ (bitrev 8 m);
        j <- start;
        while (j < start + len) {
          t0 <- p.[j];
          t1 <- p.[j + len];

          p.[j    ] <- t0 + z * t1;
          p.[j+len] <- t0 - z * t1;

          j <- j + 1;
        }
        start <- start + 2 * len;
      }
      len <- len %/ 2;
    }

    return p;
  }
}.

(* -------------------------------------------------------------------- *)
op topoly (p : apoly) (offset len : int) : QPoly.poly =
  PCA.bigi predT (fun i => p.[i + offset] ** exp X i) 0 len.

(* -------------------------------------------------------------------- *)
hint exact : ideal_idgen.

(* -------------------------------------------------------------------- *)
lemma ideal0 (I : poly -> bool): ideal I => I poly0.
proof. by case. qed.

(* -------------------------------------------------------------------- *)
lemma idealN (I : poly -> bool) (p : poly) : ideal I => I p => I (-p).
proof.
move=> ^h @/ideal [# _ + _] - /(_ poly0 p (ideal0 I h)).
by rewrite sub0r; apply.
qed.

(* -------------------------------------------------------------------- *)
lemma idealD (I : poly -> bool) (p q : poly) : ideal I => I p => I q => I (p + q).
proof.
move=> ^? @/ideal [# _ + _] Ip Iq - /(_ p (-q)); rewrite opprK.
by apply=> //; apply/idealN.
qed.

(* -------------------------------------------------------------------- *)
lemma idealMl (I : poly -> bool) (p r : poly) : ideal I => I p => I (r * p).
proof. by move=> @/ideal [# _ _]; apply. qed.

(* -------------------------------------------------------------------- *)
lemma idealMr (I : poly -> bool) (p r : poly) : ideal I => I p => I (p * r).
proof. by move=> *; rewrite mulrC &(idealMl). qed.

(* -------------------------------------------------------------------- *)
lemma idealZ (I : poly -> bool) (c : coeff) (p : poly) : ideal I => I p => I (c ** p).
proof. by move=> ?; rewrite scalepE &(idealMl). qed.

(* -------------------------------------------------------------------- *)
op eqm (c i : int) (p1 p2 : poly) =
  idgen [exp X c - polyC (exp zeta_ i)] (p2 - p1).

(* -------------------------------------------------------------------- *)
lemma eqm_refl (c i : int) (p : poly): eqm c i p p.
proof.
rewrite /eqm subrr /= &(ideal0 (idgen _)) (* FIXME *) &(ideal_idgen).
qed.

hint exact : eqm_refl.

(* -------------------------------------------------------------------- *)
lemma eqm_sym (c i : int) (p q : poly): eqm c i p q => eqm c i q p.
proof.
by move=> ?; rewrite /eqm -(opprB q p) &(idealN (idgen _)) //; solve.
qed.

(* -------------------------------------------------------------------- *)
lemma eqm_trans (c i : int) (r p q : poly): eqm c i p r => eqm c i r q => eqm c i p q.
proof.
move=> @/eqm ??; have ->: q - p = (q - r) + (r - p).
- by rewrite addrACA -addrA [_ + (-r - p)]addrA /= subrr sub0r.
by apply: (idealD (idgen _)); first solve.
qed.

(* -------------------------------------------------------------------- *)
axiom zeta_X256 : exp zeta_ 256 = -QRing.oner.

(* -------------------------------------------------------------------- *)
hint simplify IntID.expr0, IntID.expr_pred.

(* -------------------------------------------------------------------- *)
op log2 (x : int) =
  if x <= 1 then
    0 
  else argmax (fun i => exp 2 i) (fun i => i <= x).

(* -------------------------------------------------------------------- *)
lemma log2_0 : log2 0 = 0.
proof. by done. qed.

hint simplify log2_0.

(* -------------------------------------------------------------------- *)
lemma ltz_weexpn2l (x : int) :
  1 < x => forall (m n : int), 0 <= m < n => x ^ m < x ^ n.
proof.
move=> gt1_x m n [ge0_m lt_mn]; have ->: n = (n - m) + m by ring.
rewrite exprD_nneg ~-1://# IntOrder.ltr_pmull.
- by rewrite IntOrder.expr_gt0 /#.
- by apply/IntOrder.exprn_egt1 => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma ltz_weexpn2r (x : int) :
  1 < x => forall (m n : int), 0 <= m => 0 <= n => x ^ m < x ^ n => m < n.
proof.
move=> gt1_x m n ge0_m ge0_n; rewrite &(contraLR) !ltzNge /=.
by move=> ?; apply: IntOrder.ler_weexpn2l => //#.
qed.

(* -------------------------------------------------------------------- *)
lemma log2_pow2 (k : int) : 0 <= k => log2 (exp 2 k) = k.
proof.
rewrite lez_eqVlt => -[<<-//=|gt0_k] @/log2; rewrite ifF.
- by apply/ltzNge; rewrite -[1](IntID.expr0 2) &(ltz_weexpn2l).
apply: argmax_eq => /=; ~-1: smt().
by move=> j lt_kj; apply/ltzNge/ltz_weexpn2l => //#.
qed.

(* -------------------------------------------------------------------- *)
lemma topolyz0 (p : apoly) (i : int) : topoly p i 0 = poly0.
proof. by rewrite /topoly PCA.big_geq. qed.

(* -------------------------------------------------------------------- *)
lemma topoly_cat (p : apoly) (i j k : int) : 0 <= i => 0 <= j => 0 <= k =>
  (topoly p (i+j) k) * exp X j + topoly p i j = topoly p i (j + k).
proof.
move=> * @/topoly; apply/eq_sym.
rewrite (PCA.big_cat_int j) ~-1://# addrC; congr.
rewrite PCA.mulr_suml (PCA.big_addn 0 _ j) /=.
rewrite addrAC /= &(PCA.eq_big_int) => /= l ?.
rewrite addrAC addrA exprD_nneg ~-1:/#.
by rewrite !scalepE mulrA.
qed.

(* -------------------------------------------------------------------- *)
lemma topoly_eq (p q : apoly) (i j : int) :
  (forall k, k \in range i (i + j) => p.[k] = q.[k])
  => topoly p i j = topoly q i j.
proof.
move=> eq; apply: PCA.eq_big_int => /= l *; congr.
by apply: eq; smt(mem_range).
qed.

(* -------------------------------------------------------------------- *)
lemma eqm_eqR (c i : int) (p q1 q2 : poly) :
  q1 = q2 => eqm c i p q1 => eqm c i p q2.
proof. by move=> ->. qed.

(* -------------------------------------------------------------------- *)
lemma eqm_base (c i : int) : eqm c i (exp X c) (polyC (exp zeta_ i)).
proof.
rewrite /eqm -[_ - exp X _]opprB &(idealN (idgen _)); 1: by solve.
by apply: mem_idgen1_gen.
qed.

(* -------------------------------------------------------------------- *)
lemma eqm_eqpow (c i1 i2 : int) (p q : poly) :
  i1 = i2 => eqm c i1 p q => eqm c i2 p q.
proof. by move=> ->. qed.

(* -------------------------------------------------------------------- *)
lemma topolyS (p : apoly) (i : int) (l : int) :
  0 <= l => topoly p i (l + 1) = topoly p i l + p.[i + l] ** exp X l.
proof.
by move=> *; rewrite /topoly PCA.big_int_recr //= [l+i]addrC.
qed.

(* -------------------------------------------------------------------- *)
lemma topolySl (p : apoly) (i : int) (l : int) :
  0 <= l => topoly p i (l + 1) = polyC p.[i] + topoly p (i + 1) l * X.
proof.
move=> *; rewrite /topoly PCA.big_int_recl //= expr0 scalep1; congr.
rewrite PCA.mulr_suml &(PCA.eq_big_int) => /= k ?.
by rewrite exprS 1:/# !scalepE mulrA mulrAC; do 4! congr; ring.
qed.

(* -------------------------------------------------------------------- *)
lemma eqmD2l (c i : int) (p q1 q2 : poly) :
  eqm c i q1 q2 => eqm c i (p + q1) (p + q2).
proof. by move=> @/eqm ?; rewrite opprD addrACA subrr add0r. qed.

(* -------------------------------------------------------------------- *)
lemma eqmD2r (c i : int) (p q1 q2 : poly) :
  eqm c i q1 q2 => eqm c i (q1 + p) (q2 + p).
proof. by rewrite ![_+p]addrC &(eqmD2l). qed.

(* -------------------------------------------------------------------- *)
lemma eqmMr (c i : int) (p q r : poly) :
  eqm c i p q => eqm c i (p * r) (q * r).
proof. by move=> @/eqm ?; rewrite -mulrBl &(idealMr (idgen _)) //; solve. qed.

(* -------------------------------------------------------------------- *)
lemma eqmZ (c i : int) z (p q : poly) :
  eqm c i p q => eqm c i (z ** p) (z ** q).
proof. by move=> @/eqm ?; rewrite -scalepBr &(idealZ (idgen _)) //; solve. qed.

(* -------------------------------------------------------------------- *)
lemma eqm_subl_addr (c i : int) (p q r : poly) :
  eqm c i p (q + r) => eqm c i (p - r) q.
proof. by move=> @/eqm; rewrite opprB addrA. qed.

(* -------------------------------------------------------------------- *)
lemma mul2p (p : poly) : exp p 2 = p * p.
proof. by rewrite (exprS p 1) // expr1. qed.

(* -------------------------------------------------------------------- *)
lemma sub_sqr (a b : poly) : exp a 2 - exp b 2 = (a - b) * (a + b).
proof.
rewrite mulrBl !mulrDr [b*a]mulrC.
by rewrite [a*a + _]addrC subrACA subrr add0r !mul2p.
qed.

(* -------------------------------------------------------------------- *)
lemma eqm_fL (c i : int) (p q : poly) : 0 <= c => 0 <= i =>
  eqm (2^(c+1)) (2*i) p q => eqm (2^c) i p q.
proof.
move=> @/eqm ge0_c ge0_i /mem_idgen1_dvd.
rewrite exprSr // [2*i]mulrC 2!exprM -polyCX // sub_sqr.
pose r1 := (_ - _)%QPoly; pose r2 := (_ + _)%QPoly.
case/dvdrP=> s ->; rewrite mulrA mulrAC.
by apply/mem_idgen1_dvd; exists (s * r2).
qed.

(* -------------------------------------------------------------------- *)
lemma eqm_fR (c i : int) (p q : poly) : 0 <= c => 0 <= i =>
  eqm (2^(c+1)) (2*i) p q => eqm (2^c) (i+256) p q.
proof.
move=> @/eqm ge0_c ge0_i /mem_idgen1_dvd.
rewrite exprSr // [2*i]mulrC 2!exprM -polyCX // sub_sqr.
pose r1 := (_ - _)%QPoly; pose r2 := (_ + _)%QPoly.
case/dvdrP=> s ->; rewrite mulrA.
apply/mem_idgen1_dvd; exists (s * r1); congr.
rewrite -polyCX 1:/# exprD_nneg // !polyCX ~-1://.
by rewrite zeta_X256 polyCN mulrN opprK mulr1.
qed.

(* -------------------------------------------------------------------- *)
lemma foo (n q r : int) :
  0 < n => 0 <= q => 0 <= r => n %| q => n %| r => q < r => q + n <= r.
proof.
move=> 3? /dvdzP[kq ->>] /dvdzP[kr ->>] ?.
have ?: kq < kr by apply: (IntOrder.ltr_pmul2r n).
by rewrite -mulrSl &(IntOrder.ler_pmul2r) //#.
qed.

(* -------------------------------------------------------------------- *)
lemma bitrevS (k x : int) : 0 <= k => 0 <= x =>
  bitrev (k + 1) x = bitrev k (x %/ 2) + 2^k * b2i (odd x).
proof.
move=> * @/bitrev; rewrite int2bs_cons ~-1:/# rev_cons.
rewrite bs2int_rcons /= size_rev; congr.
by rewrite size_int2bs lez_maxr // dvdzE oddP.
qed.

(* -------------------------------------------------------------------- *)
lemma bitrevS_oddN (s : int) : !odd s => 0 <= s =>
  bitrev 8 (s + 1) = bitrev 8 s + 128.
proof.
move=> *; rewrite ![bitrev 8 _](bitrevS 7) ~-1://#.
rewrite oddS (_ : odd s = false) ~-1://# /= !(b2i0, b2i1) /=.
by rewrite divzDl //= dvdzE &(oddPn).
qed.

(* -------------------------------------------------------------------- *)
lemma bitrev_extend (k s : int) : 0 <= k => 0 <= s < 2^k =>
  2 * bitrev k s = bitrev (k + 1) s.
proof.
move=> *; rewrite {2}/bitrev int2bsS // rev_rcons /=.
by rewrite bs2int_cons (_ : (_ %/ _) = 0) //#.
qed.

(* -------------------------------------------------------------------- *)
lemma bitrev_extendX (k h s : int) : 0 <= h <= k => 0 <= s < 2^(k-h) =>
  2^(h+1) * bitrev (k-h) s = bitrev (k + 1) s.
proof.
case=> ge0_h; elim: h ge0_h k => [|h ge0_h ih] k * /=.
- by apply: bitrev_extend.
rewrite (IntID.exprS _ (h + 1)) 1:/#.
rewrite (_ : k - (h + 1) = (k - 1) - h) 1:#ring.
rewrite -mulrA ih ~-1:/# /= &(bitrev_extend) ~-1:/#.
suff: 2^(k - (h+1)) <= 2^k by smt().
by apply: IntOrder.ler_weexpn2l => //#.
qed.

(* -------------------------------------------------------------------- *)
lemma bitrev_div2 (s : int) : 0 <= s < 256 => !odd s =>
  bitrev 8 (s %/ 2) = 2 * bitrev 8 s.
proof.
move=> *; apply/eq_sym; rewrite (bitrevS 7) ~-1:/#.
rewrite (_ : odd s = false) 1:/# b2i0 /=.
by rewrite bitrev_extend //#.
qed.

(* -------------------------------------------------------------------- *)
lemma bitrev_hibit (k h : int) (s : int) : 0 <= h <= k => 0 <= s < 2^(k-h) =>
  bitrev (k+1) (2^(k - h) + s) = 2^h + bitrev (k+1) s.
proof.
move=> *; rewrite {1}/bitrev (int2bs_cat (k-h)) 1:/# rev_cat.
rewrite (_ : k + 1 - (k - h) = h + 1) 1:#ring.
rewrite divzDl 1:dvdzz divzz expf_eq0 b2i1 pdiv_small //=.
rewrite int2bs_cons 1:/# /= int2bs0 dvdzE /= rev_cons rev_nseq.
rewrite bs2int_cat size_rcons size_nseq lez_maxr 1:/#.
rewrite bs2int_rcons size_nseq lez_maxr 1:/#.
rewrite bs2int_nseq_false b2i1 /=; congr.
rewrite -int2bs_mod modzDl pmod_small 1:/#.
by rewrite -/(bitrev _ _) bitrev_extendX //#.
qed.

(* FIXME
(* -------------------------------------------------------------------- *)
hint simplify expr0, expr1, addr0, add0r, mulr0, mul0r, mulr1, mul1r, subrr.

(* -------------------------------------------------------------------- *)
hint simplify topolyz0.
*)

(* -------------------------------------------------------------------- *)
lemma mul2z (x : int) : 2 * x = x + x.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma ntt_correct (p_ : apoly) : hoare[
      NTT.ntt : p = p_ /\ size p = 256
  ==>
      forall i, 0 <= i < 256 =>
        eqm 1 ((2 * bitrev 8 i) + 1) (topoly p_ 0 256) (topoly res i 1)
].
proof.
proc; sp; pose P := topoly p_ 0 256.

while (
  let k = (if len = 0 then 0 else 1 + log2 len) in
      size p = 256
  /\  0 <= len <= 128
  /\ (1 <= len => exists k, 0 <= k /\ len = 2^k)
  /\ m = 2^(8-k) - 1
  /\ (forall i, 0 <= i < 256 %/ 2^k =>
        eqm (2^k) (2 * bitrev 8 i + 2^k) P (topoly p (i * 2^k) (2^k)))
); last first.
- skip=> |> ?; do! split.
  - by exists 7.
  - by rewrite (log2_pow2 7).
  - move=> i ?; rewrite (log2_pow2 7) ~-1:// /= => ?.
    by have ->> /=: i = 0 by smt().
  - move=> len_ a 3? _ + i 2?; have ->> /=: len_ = 0 by smt().
    by move/(_ i _); ~-1:smt().
sp; wp; while (
  let k = log2 len in
     size p = 256
  /\ 1 <= len <= 128
  /\ (1 <= len => exists k, 0 <= k /\ len = 2^k)
  /\ 0 <= start <= 256
  /\ 2 * len %| start
  /\ m = 2^(7 - k) - 1 + start %/ 2^(k+1)
  /\ (forall i, 0 <= i < start %/ 2^k =>
        eqm (2^k) (2 * bitrev 8 i + 2^k) P (topoly p (i * 2^k) (2^k)))
  /\ (forall i, start %/ 2^(k+1) <= i < 256 %/ 2^(k+1) =>
        eqm (2^(k+1)) (2 * bitrev 8 i + 2^(k+1)) P (topoly p (i * 2^(k+1)) (2^(k+1))))
); last first.
- skip=> |> &hr ? _ 2? h *; do! split.
  - by rewrite ifF 1:/#; do 2! congr; ring.
  - by move=> i 2?; have: false by smt().
  - move=> i ??; have := h i _; ~-1: smt().
    by rewrite ifF 1:/# [1+_]addzC.
  move=> a st ? _ 3? h1 h2; have ->> /=: st = 256 by smt().
  have [k [? ->>]]: exists k, 0 <= k /\ len{hr} = 2^k by smt().
  do! split.
  - apply: divz_ge0 => //; smt().
  - move=> _; have /lez_eqVlt [<<-//|lt0_k]: 0 <= k by assumption.
    by rewrite lez_divLR // -1:/# expr_pred // dvdz_mulr.
  - have /lez_eqVlt [<<-//|? _]: 0 <= k by assumption.
    exists (k-1); split; first smt().
    by rewrite expr_pred // mulKz.
  - have /lez_eqVlt [<<-//|?]: 0 <= k by assumption.
    have ->/=: log2 (2^k %/ 2) = k - 1.
    - by rewrite expr_pred // mulKz // log2_pow2 ~-1:/#.
    have ?: k <= 7.
    - have: 2^k <= 128 by assumption.
      by rewrite (_ : 128 = 2^7) 1:// &(IntOrder.ler_weexpn2r).
    rewrite log2_pow2 // (_ : 256 = 2^8) 1:// expz_div ~-1://#.
    rewrite [2^k]expr_pred ~-1:// mulKz ~-1:// expf_eq0 /=.
    rewrite opprD addrA [(8 - _) - _]addrAC /= addrAC; congr.
    have ->: forall x, x + x = 2 * x by smt().
    by rewrite -exprS -1:addrAC //#.
  - pose k' := if _ then _ else _; have ->: k' = k.
    - rewrite /k'; have /lez_eqVlt [<<-//|?]: 0 <= k by assumption.
      by rewrite expr_pred // mulKz // expf_eq0 /= log2_pow2 //#.
    by move=> i 2?; have := h1 i _; rewrite log2_pow2.

wp; while (
  let k = log2 len in
     size p = 256
  /\ 1 <= len <= 128
  /\ (exists k, 0 <= k /\ len = 2^k)
  /\ 0 <= start < 256
  /\ 2 * len %| start
  /\ start <= j <= start + len
  /\ m = 2^(7 - k) + start %/ 2^(k+1)
  /\ z = exp zeta_ (bitrev 8 m)
  /\ (forall i, 0 <= i < start %/ 2^k =>
        eqm (2^k) (2 * bitrev 8 i + 2^k) P (topoly p (i * 2^k) (2^k)))
  /\ (forall i, start %/ 2^(k+1) + 1 <= i < 256 %/ 2^(k+1) =>
        eqm (2^(k+1)) (2 * bitrev 8 i + 2^(k+1)) P (topoly p (i * 2^(k+1)) (2^(k+1))))
  /\ (let d = j - start in
      let e = 2 * bitrev 8 (start %/ 2^k) + 2^k in
      let r = (
        (topoly p (start + len + d) (len - d)) * exp X len +
         topoly p (start + d) (len - d)
      ) * exp X d in
           eqm (2^k) (e      ) P (topoly p (start      ) d + r)
        /\ eqm (2^k) (e + 256) P (topoly p (start + len) d + r)
     )
); last first.
- auto=> |> &hr 3? k 5? h1 h2 ?.

  have ?: 2^k <= 128 by smt().
  have ?: k <= 7 by rewrite &(IntOrder.ler_weexpn2r 2).
  have ?: start{hr} + 2*2^k <= 256.
  - suff ?: 2 * 2^k %| 256 by apply: foo => //#.
    rewrite -exprS 1:// (_ : 256 = 2^8) 1://.
    by apply: dvdz_exp2l => /#.
  have ?: !odd (start{hr} %/ 2^k).
  - apply/oddPn; rewrite -dvdzE.
    have /dvdzP[q ->>] : 2 * 2^k %| start{hr} by done.
    by rewrite mulrA mulzK 1:/# dvdz_mull dvdzz.

  do! split.
  - by rewrite lez_addl IntOrder.expr_ge0.
  - by ring.
  - by move=> i ??; apply: (h2 i _); split=> //#.
  - rewrite expr0 mulr1 topolyz0 add0r topoly_cat ~-1:/#.
    rewrite -mul2z -exprS ~-1://.
    pose i := start{hr} %/ 2 ^ (log2 (2 ^ k) + 1); have := h2 i _.
    - split=> [|_ @/i]; first by done.
      rewrite log2_pow2 // exprS // ltz_divLR 1:/# divzK //.
      by rewrite -exprS // (_ : 256 = 2^8) 1:// dvdz_exp2l /#.
    rewrite /i log2_pow2 ~-1:// divzK 1:exprS ~-1://.
    rewrite {2}exprSr 1:// divz_mul 1:/#.
    rewrite {2}exprS 1:// -mulrDr bitrev_div2 ~-1:/#.
    by rewrite &(eqm_fL); smt(bs2int_ge0).

  - rewrite expr0 mulr1 topolyz0 add0r topoly_cat ~-1:/#.
    rewrite -mul2z -exprS ~-1://.
    pose i := start{hr} %/ 2 ^ (log2 (2 ^ k) + 1); have := h2 i _.
    - split=> [|_ @/i]; first by done.
      rewrite log2_pow2 // exprS // ltz_divLR 1:/# divzK //.
      by rewrite -exprS // (_ : 256 = 2^8) 1:// dvdz_exp2l /#.
    rewrite /i log2_pow2 ~-1:// divzK 1:exprS ~-1://.
    rewrite {2}exprSr 1:// divz_mul 1:/#.
    rewrite {2}exprS 1:// -mulrDr bitrev_div2 ~-1:/#.
    by rewrite &(eqm_fR); smt(bs2int_ge0).

  move=> j a 4? _ eqpre eqpost eq1 eq2.
  have ->>: j = start{hr} + 2^k by smt().
  do! split.
  - smt().
  - done.
  - by rewrite dvdzD // dvdzz.
  - rewrite log2_pow2 ~-1:// -exprS ~-1://.
    by rewrite divzDr ?dvdzz divzz expf_eq0 /= b2i1 #ring.
  - move=> i; rewrite log2_pow2 ~-1:// divzDr.
    - by rewrite dvdz_mull dvdzz.
    rewrite mulzK ~-1:/# => ??; pose s := start{hr} %/ 2^k.
    have: (i < s) \/ (i = s) \/ (i = s + 1) by smt().
    case=> [?|[]->>]; first by smt(log2_pow2).
    - move: eq1; rewrite log2_pow2 1://.
      rewrite (_ : start{hr} + 2^k - start{hr} = 2^k) 1:#ring.
      rewrite subrr !topolyz0 !(mul0r, add0r, addr0) -/s.
      suff ->: s * 2^k = start{hr} by done.
      rewrite /s divzK // &(dvdz_trans (2 * 2^k)) -1://.
      by rewrite dvdz_mull dvdzz.
    - move: eq2; rewrite log2_pow2 1://.
      rewrite (_ : start{hr} + 2^k - start{hr} = 2^k) 1:#ring.
      rewrite subrr !topolyz0 !(mul0r, add0r, addr0) -/s.
      rewrite mulrSl; have ->: s * 2^k = start{hr}.
      - rewrite /s divzK // &(dvdz_trans (2 * 2^k)) -1://.
        by rewrite dvdz_mull dvdzz.
      by rewrite bitrevS_oddN ~-1://# mulrDr /= addrAC.

  - move=> i; rewrite log2_pow2 1:// -exprS 1://.
    by rewrite divzDr ?dvdzz divzz expf_eq0 /= b2i1; smt(log2_pow2).

auto=> |> &hr 3? k 7? eqpre eqpost eq1 eq2 ?.

have ?: 2^k <= 128 by smt().
have ?: k <= 7 by rewrite &(IntOrder.ler_weexpn2r 2).
have ?: start{hr} + 2*2^k <= 256.
- suff ?: 2 * 2^k %| 256 by apply: foo => //#.
  rewrite -exprS 1:// (_ : 256 = 2^8) 1://.
  by apply: dvdz_exp2l => /#.
have ?: 2^k %| start{hr}.
- by apply: (dvdz_trans (2*2^k)) => //; apply/dvdz_mull/dvdzz.
have ?: !odd (start{hr} %/ 2^k).
- apply/oddPn; rewrite -dvdzE.
  have /dvdzP[q ->>] : 2 * 2^k %| start{hr} by done.
  by rewrite mulrA mulzK 1:/# dvdz_mull dvdzz.

do! split.
- by rewrite !size_set.
- smt().
- smt().
- move=> i 2?; have ?: i * 2^k < j{hr}.
  - have: i < start{hr} %/ 2^(log2 (2^k)) by assumption.
    by rewrite log2_pow2 1:// ltz_divRL /#.
  have := eqpre i _; ~-1: smt().
  rewrite log2_pow2 1:// &(eqm_eqR) &(topoly_eq).
  move=> l /mem_range ?; rewrite !get_set_if !ifF -1://.
  - by rewrite negb_and; right => /#.
  - rewrite negb_and; right.
    suff: i * 2^k + 2^k < start{hr} + 2^k by smt().
    by rewrite &(IntOrder.ltr_add2r) -ltz_divRL; smt(log2_pow2).
- move=> i 2?; have ?: j{hr} + 2^k < i * 2 ^ (k + 1).
  - have ?: j{hr} + 2^ k < start{hr} + 2^(k+1).
    - by rewrite exprS 1:// mul2z addrA ltz_add2r.
    apply: (IntOrder.ltr_le_trans (start{hr} + 2^(k+1))) => //.
    rewrite -lez_divLR; first by smt(IntOrder.expr_gt0).
    - by rewrite dvdzD ?exprS // dvdzz.
    by rewrite divzDr 1:dvdzz divzz expf_eq0 /= b2i1; smt(log2_pow2).
  have := eqpost i _; ~-1: smt().
  rewrite log2_pow2 1:// &(eqm_eqR) &(topoly_eq).
  move=> l /mem_range ?; rewrite !get_set_if !ifF -1://.
  - by rewrite negb_and; right => /#.
  - by rewrite negb_and; right => /#.

- rewrite log2_pow2 1://; pose z := 2 * bitrev _ _ + _.
  pose t0 := p{hr}.[j{hr}]; pose t1 := p{hr}.[j{hr} + 2^k].
  pose wD := t0 + _; pose wB := t0 - _.
  rewrite [j{hr} + 1 - start{hr}]addrAC.
  pose l := j{hr} - start{hr}.
  pose pa := p{hr}.[_ <- _].[_ <- _].
  pose p1 := topoly _ _ _; pose p2 := topoly _ _ _; pose p3 := topoly _ _ _.
  have := eq1; rewrite log2_pow2 1:// -/l.
  pose q1 := topoly _ _ _; pose q2 := topoly _ _ _; pose q3 := topoly _ _ _.
  rewrite -/z; move=> /eqm_sym h; apply/eqm_sym; apply: eqm_trans h.

  have pajE: pa.[j{hr}] = wD.
  - by rewrite /pa !get_set_if ifF 1:/# ifT //#.
  have pajD2XkE: pa.[j{hr} + 2^k] = wB.
  - by rewrite /pa !get_set_if ifT ?size_set //#.
  have pa_dflE: forall i, i <> j{hr} /\ i <> j{hr} + 2^k => pa.[i] = p{hr}.[i].
  - by move=> i *; rewrite /pa !get_set_if !ifF //#.

  have p1E: p1 = q1 + wD ** exp X l.
  - rewrite /p1 topolyS ~-1:/# (_ : start{hr} + l = j{hr}) 1:/l 1:#ring.
    rewrite pajE; congr; rewrite /q1 &(topoly_eq).
    by move=> ? /mem_range *; apply: pa_dflE; smt().

  have q2E : q2 = polyC p{hr}.[2^k + j{hr}] + p2 * X.
  - rewrite /q2 (_ : 2^k - l = 2^k - (l+1) + 1) 1:#ring topolySl 1:/#.
    do 2! congr; first by congr; smt().
    by rewrite /p2 [_ + (l+1)]addrA &(topoly_eq) => ? /mem_range * /#.

  have q3E : q3 = polyC p{hr}.[j{hr}] + p3 * X.
  - rewrite /q3 (_ : 2^k - l = 2^k - (l+1) + 1) 1:#ring topolySl 1:/#.
    do 2! congr; first by congr; smt().
    by rewrite /p3 [_ + (l+1)]addrA &(topoly_eq) => ? /mem_range * /#.

  pose Ql := p1 + _; pose Qr := q1 + _.
  pose t := p{hr}.[j{hr} + 2^k] ** exp X (2^k) + polyC p{hr}.[j{hr}].
  have ->: Ql = Qr + (wD ** exp X l - t * exp X l).
  - rewrite /Ql /Qr -addrA p1E -addrA; congr.
    rewrite [(_ + q3) * exp X l + _]addrCA; congr; apply/eq_sym.
    rewrite exprS 1:/# mulrA -mulrBl; congr.
    rewrite mulrDl [_*X]mulrAC /t opprD addrACA; congr.
    - rewrite scalepE -mulrBl; congr; rewrite q2E.
      by rewrite addrAC [j{hr} + _]addrC subrr add0r.
    - by rewrite q3E addrAC subrr add0r.
  rewrite -{2}[Qr]addr0 &(eqmD2l) scalepE &(eqm_subl_addr) add0r.
  rewrite &(eqmMr) /t /wD /t0 /t1 polyCD addrC &(eqmD2r).
  rewrite mulrC polyCM -scalepE &(eqmZ) &(eqm_sym).
  pose z' := bitrev _ _; suff ->: z = z' by apply: eqm_base.

  rewrite /z' (bitrev_hibit 7) 1:/#.
  - split=> [|_]; first by rewrite divz_ge0 ?exprS /#.
    rewrite ltz_divLR; first smt(IntOrder.expr_gt0).
    by rewrite -exprD_nneg ~-1:/# (_ : _ + (k + 1) = 8) /= /#.
  by rewrite exprSr 1:// divz_mul 1:/# bitrev_div2 /#.

  (* FIXME: lots of duplication *)
- rewrite log2_pow2 1://; pose z := 2 * bitrev _ _ + _.
  pose t0 := p{hr}.[j{hr}]; pose t1 := p{hr}.[j{hr} + 2^k].
  pose wD := t0 + _; pose wB := t0 - _.
  rewrite [j{hr} + 1 - start{hr}]addrAC.
  pose l := j{hr} - start{hr}.
  pose pa := p{hr}.[_ <- _].[_ <- _].
  pose p1 := topoly _ _ _; pose p2 := topoly _ _ _; pose p3 := topoly _ _ _.
  have := eq2; rewrite log2_pow2 1:// -/l.
  pose q1 := topoly _ _ _; pose q2 := topoly _ _ _; pose q3 := topoly _ _ _.
  rewrite -/z; move=> /eqm_sym h; apply/eqm_sym; apply: eqm_trans h.

  have pajE: pa.[j{hr}] = wD.
  - by rewrite /pa !get_set_if ifF 1:/# ifT //#.
  have pajD2XkE: pa.[j{hr} + 2^k] = wB.
  - by rewrite /pa !get_set_if ifT ?size_set //#.
  have pa_dflE: forall i, i <> j{hr} /\ i <> j{hr} + 2^k => pa.[i] = p{hr}.[i].
  - by move=> i *; rewrite /pa !get_set_if !ifF //#.

  have p1E: p1 = q1 + wB ** exp X l.
  - rewrite /p1 topolyS 1:/# (_ : start{hr} + 2^k + l = j{hr} + 2^k) 1:/l 1:#ring.
    rewrite pajD2XkE; congr; rewrite /q1 &(topoly_eq).
    by move=> ? /mem_range *; apply: pa_dflE; smt().

  have q2E : q2 = polyC p{hr}.[2^k + j{hr}] + p2 * X.
  - rewrite /q2 (_ : 2^k - l = 2^k - (l+1) + 1) 1:#ring topolySl 1:/#.
    do 2! congr; first by congr; smt().
    by rewrite /p2 [_ + (l+1)]addrA &(topoly_eq) => ? /mem_range * /#.

  have q3E : q3 = polyC p{hr}.[j{hr}] + p3 * X.
  - rewrite /q3 (_ : 2^k - l = 2^k - (l+1) + 1) 1:#ring topolySl 1:/#.
    do 2! congr; first by congr; smt().
    by rewrite /p3 [_ + (l+1)]addrA &(topoly_eq) => ? /mem_range * /#.

  pose Ql := p1 + _; pose Qr := q1 + _.
  pose t := p{hr}.[j{hr} + 2^k] ** exp X (2^k) + polyC p{hr}.[j{hr}].
  have ->: Ql = Qr + (wB ** exp X l - t * exp X l).
  - rewrite /Ql /Qr -addrA p1E -addrA; congr.
    rewrite [(_ + q3) * exp X l + _]addrCA; congr; apply/eq_sym.
    rewrite exprS 1:/# mulrA -mulrBl; congr.
    rewrite mulrDl [_*X]mulrAC /t opprD addrACA; congr.
    - rewrite scalepE -mulrBl; congr; rewrite q2E.
      by rewrite addrAC [j{hr} + _]addrC subrr add0r.
    - by rewrite q3E addrAC subrr add0r.
  rewrite -{2}[Qr]addr0 &(eqmD2l) scalepE &(eqm_subl_addr) add0r.
  rewrite &(eqmMr) /t /wD /t0 /t1 polyCD addrC &(eqmD2r).
  rewrite mulrC -mulrN polyCM -scalepE &(eqmZ) &(eqm_sym).
  pose z' := bitrev _ _; rewrite -mulN1r -zeta_X256.
  rewrite mulrC -exprD_nneg //; first by apply: bs2int_ge0.
  suff ->: z = z' by apply: eqm_base.

  rewrite /z' (bitrev_hibit 7) 1:/#.
  - split=> [|_]; first by rewrite divz_ge0 ?exprS /#.
    rewrite ltz_divLR; first smt(IntOrder.expr_gt0).
    by rewrite -exprD_nneg ~-1:/# (_ : _ + (k + 1) = 8) /= /#.
  by rewrite exprSr 1:// divz_mul 1:/# bitrev_div2 /#.
qed.
