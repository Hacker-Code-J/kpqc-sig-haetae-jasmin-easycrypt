require import AllCore List IntDiv Ring StdOrder BitEncoding.
from Jasmin require import JWord.
require import Array256.
require import Fq Fastexp.
require import GFq Rq.
require import BArray1024 Hpoly_extract.
import Zq IntOrder BitReverse.

theory NTT_Fq.

clone include Fastexp with
  type CR.t <- coeff,
  op CR.zeror <- Zq.zero,
  op CR.oner <- Zq.one,
  op CR.(+) <- Zq.(+),
  op CR.([ - ]) <- Zq.([-]),
  op CR.( * ) <- Zq.( * ),
  op CR.invr  <- Zq.inv,
  op CR.exp  <- Zq.exp,
  op CR.ofint <- ZqField.ofint,
  pred CR.unit  <- Zq.unit
proof *.

realize CR.addrA by apply Zq.ZqRing.addrA.
realize CR.addrC by apply Zq.ZqRing.addrC.
realize CR.add0r by apply Zq.ZqRing.add0r.
realize CR.addNr by apply Zq.ZqRing.addNr.
realize CR.oner_neq0 by apply Zq.ZqRing.oner_neq0.
realize CR.mulrA by apply Zq.ZqRing.mulrA.
realize CR.mulrC by apply Zq.ZqRing.mulrC.
realize CR.mul1r by apply Zq.ZqRing.mul1r.
realize CR.mulrDl by apply Zq.ZqRing.mulrDl.
realize CR.mulVr by apply Zq.ZqRing.mulVr.
realize CR.unitP by apply Zq.ZqRing.unitP.
realize CR.unitout by apply Zq.ZqRing.unitout.

(* -------------------------------------------------------------------- *)
(* HAETAE NTT: q = 64513, N = 256, zroot = 426 (primitive 512th root).
   Forward NTT has 8 butterfly layers (len: 128 → 64 → ... → 1).
   Inverse NTT has 8 butterfly layers (len: 1 → 2 → ... → 128) plus
   a final scaling by inv(256).                                          *)
(* -------------------------------------------------------------------- *)

(* These are imperative specifications of the NTT algorithms whose control
   structure matches what is implemented.  *)

module NTT = {
 proc ntt(r : coeff Array256.t, zetas : coeff Array256.t) : coeff Array256.t = {
   var len, start, j, zetasctr;
   var t, zeta_;

   zetasctr <- 0;
   len <- 128;
   while (1 <= len) {
    start <- 0;
    while(start < 256) {
       zetasctr <- zetasctr + 1;
       zeta_ <- zetas.[zetasctr];
       j <- start;
       while (j < start + len) {
         t <- zeta_ * r.[j + len];
         r.[j + len] <- r.[j] + (-t);
         r.[j]       <- r.[j] + t;
         j <- j + 1;
       }
       start <- j + len;
     }
     len <- len %/ 2;
   }
   return r;
 }

 proc invntt(r : coeff Array256.t, zetas_inv : coeff Array256.t) : coeff Array256.t = {
   var len, start, j, zetasctr;
   var t, zeta_;

   zetasctr <- 0;
   len <- 1;
   while (len < 256) {
    start <- 0;
    while(start < 256) {
       zeta_ <- zetas_inv.[zetasctr];
       zetasctr <- zetasctr + 1;
       j <- start;
       while (j < start + len) {
        t <- r.[j];
        r.[j]       <- t + r.[j + len];
        r.[j + len] <- t + (-r.[j + len]);
        r.[j + len] <- zeta_ * r.[j + len];
         j <- j + 1;
       }
       start <- j + len;
     }
     len <- len * 2;
   }
   j <- 0;
   while (j < 256) {
     r.[j] <- r.[j] * zetas_inv.[255];
     j <- j + 1;
   }
   return r;
 }

}.

(* -------------------------------------------------------------------- *)
(* Losslessness of NTT procedures                                        *)
(* Each nested while loop terminates via a strictly-decreasing non-neg   *)
(* integer variant.  No probabilistic choices exist so losslessness is   *)
(* equivalent to termination.                                            *)
(* -------------------------------------------------------------------- *)

lemma ntt_middle_right start len j0 :
  0 < len =>
  ! j0 < start + len =>
  256 - (j0 + len) < 256 - start.
proof.
  move=> hlen0 hj0.
  have hle : start + len <= j0 by rewrite -lezNgt in hj0.
  rewrite ltr_subr_addr.
  have -> : 256 - (j0 + len) + start = start - (j0 + len) + 256 by ring.
  have -> : 256 = 0 + 256 by ring.
  rewrite ltr_add2r ltr_subl_addr add0r.
  have hsj0 : start <= j0.
  + apply (lez_trans _ _ _ _ hle).
    rewrite lez_addl.
    apply ltrW.
    exact hlen0.
  have hj0len : j0 < j0 + len.
  + rewrite ltz_addl.
    exact hlen0.
  exact (ler_lt_trans _ _ _ hsj0 hj0len).
qed.

lemma inv_middle_right start len j0 :
  0 < len =>
  ! j0 < start + len =>
  256 - (j0 + len) < 256 - start.
proof.
  move=> hlen0 hj0.
  have hle : start + len <= j0 by rewrite -lezNgt in hj0.
  rewrite ltr_subr_addr.
  have -> : 256 - (j0 + len) + start = start - (j0 + len) + 256 by ring.
  have -> : 256 = 0 + 256 by ring.
  rewrite ltr_add2r ltr_subl_addr add0r.
  have hsj0 : start <= j0.
  + apply (lez_trans _ _ _ _ hle).
    rewrite lez_addl.
    apply ltrW.
    exact hlen0.
  have hj0len : j0 < j0 + len.
  + rewrite ltz_addl.
    exact hlen0.
  exact (ler_lt_trans _ _ _ hsj0 hj0len).
qed.

lemma inv_outer_progress len :
  0 < len =>
  len < 256 =>
  forall start0,
    (256 - start0 <= 0 => ! start0 < 256) /\
    (! start0 < 256 => 0 < len * 2 /\ 256 - len * 2 < 256 - len).
proof.
move=> hlen hlt256 start0; split.
+ move=> h.
  rewrite -lezNgt.
  move: h.
  rewrite ler_subl_addr add0r.
  trivial.
move=> _.
split.
+ have -> : len * 2 = len + len by ring.
  have -> : 0 = 0 + 0 by ring.
  exact (ltr_add _ _ _ _ hlen hlen).
have -> : 256 - len * 2 = 256 - (len + len) by ring.
have -> : 256 - len = (256 - (len + len)) + len by ring.
rewrite ltr_addl.
exact hlen.
qed.

lemma ntt_init_progress len0 :
  (len0 <= 0 => ! 1 <= len0) /\ true.
proof.
  split.
  + move=> h.
    apply/negP.
    move=> h1.
    have h10 : 1 <= 0 by exact (lez_trans _ _ _ h1 h).
    trivial.
  + trivial.
qed.

(* Forward NTT:
   outer:  len starts at 128, halved each step  → variant = len
   middle: start advances by 2*len              → variant = 256 - start
   inner:  j increments by 1                   → variant = start + len - j  *)
lemma ntt_spec_ll : islossless NTT.ntt.
proof.
proc.
wp.
while (true) len.
+ move=> z.
  wp.
  while (0 < len) (256 - start).
  + move=> z'.
    wp.
    while (0 < len) (start + len - j).
    + move=> z''.
      wp.
      skip => &hr [[hlen hj] hz] /=.
      split; first exact hlen.
      rewrite -hz.
      have -> : start{hr} + len{hr} - (j{hr} + 1) = start{hr} + len{hr} - j{hr} - 1 by ring.
      have -> : start{hr} + len{hr} - j{hr} = (start{hr} + len{hr} - j{hr} - 1) + 1 by ring.
      rewrite ltz_addl.
      trivial.
    wp.
    skip => &hr [[hlen0 hstart0] hz'] /=.
    split; first exact hlen0.
    move=> j0; split.
    + move=> h.
      rewrite -lezNgt.
      move: h.
      rewrite ler_subl_addr add0r.
      trivial.
    move=> hj0.
    move=> hlen1.
    split; first exact hlen1.
    rewrite -hz'.
    apply (ntt_middle_right start{hr} len{hr} j0); first exact hlen1.
    exact hj0.
  auto => />.
  move=> hz1; split.
  + have h01 : 0 < 1 by trivial.
    exact (ltr_le_trans _ _ _ h01 hz1).
  move=> start0; split.
  + move=> _ h.
    rewrite -lezNgt.
    move: h.
    rewrite ler_subl_addr add0r.
    trivial.
  move=> _ hz0.
  rewrite ltz_divLR.
  + trivial.
  have -> : z * 2 = z + z by ring.
  rewrite ltz_addl.
  exact hz0.
  + wp.
    skip => &hr /= len0.
    exact (ntt_init_progress len0).
qed.

(* Inverse NTT:
   outer:  len starts at 1, doubled each step, stops when len ≥ 256
           → variant = 256 - len  (decreases by len each step, len ≥ 1)
   middle: start advances by 2*len              → variant = 256 - start
   inner:  j increments by 1                   → variant = start + len - j
   final:  j increments from 0 to 255          → variant = 256 - j         *)
lemma invntt_spec_ll : islossless NTT.invntt.
proof.
proc.
wp.
while (true) (256 - j).
+ move=> z.
  wp.
  skip => &hr [hj hz] /=.
  rewrite -hz.
  have -> : 256 - j{hr} = (256 - (j{hr} + 1)) + 1 by ring.
  rewrite ltz_addl.
  trivial.
wp.
while (0 < len) (256 - len).
+ move=> z.
  wp.
  while (0 < len) (256 - start).
  + move=> z'.
    wp.
    while (0 < len) (start + len - j).
    + move=> z''.
      wp.
      skip => &hr [[hlen hj] hz] /=.
      split; first exact hlen.
      rewrite -hz.
      have -> : start{hr} + len{hr} - (j{hr} + 1) = start{hr} + len{hr} - j{hr} - 1 by ring.
      have -> : start{hr} + len{hr} - j{hr} = (start{hr} + len{hr} - j{hr} - 1) + 1 by ring.
      rewrite ltz_addl.
      trivial.
    wp.
    skip => &hr [[hlen0 hstart0] hz'] /=.
    split; first exact hlen0.
    move=> j0; split.
    + move=> h.
      rewrite -lezNgt.
      move: h.
      rewrite ler_subl_addr add0r.
      trivial.
    move=> hj0.
    move=> hlen1.
    split; first exact hlen1.
    rewrite -hz'.
    apply (inv_middle_right start{hr} len{hr} j0); first exact hlen1.
    exact hj0.
  auto => />.
  move=> &hr hlen hlt256.
  exact (inv_outer_progress len{hr} hlen hlt256).
wp.
skip => &hr /=.
move=> len0; split.
+ move=> _ h.
  rewrite -lezNgt.
  move: h.
  rewrite ler_subl_addr add0r.
  trivial.
+ move=> _ _ j0 h.
  rewrite -lezNgt.
  move: h.
  rewrite ler_subl_addr add0r.
  trivial.
qed.


op perm256 ['t] (p : int -> int) (a : 't Array256.t) : 't Array256.t =
  Array256.init (fun i => a.[p i]).

op bsrev256 ['t] : 't Array256.t -> 't Array256.t =
  perm256 (bsrev 8).

op R = incoeff Fq.SignedReductions.R.

(* inv(256) mod q = 64261 = incoeff(-252) *)
op scale255 = incoeff (-252).

op array256_mont_inv (p : coeff Array256.t) =
  Array256.map (fun x => x * R) p.

op word_to_coeff (w : W32.t) : coeff =
  incoeff (W32.to_sint w).

op barray256_to_poly (rp : BArray1024.t) : coeff Array256.t =
  Array256.init (fun i => word_to_coeff (BArray1024.get32 rp i)).

op poly_repr (rp : BArray1024.t) (p : coeff Array256.t) : bool =
  barray256_to_poly rp = p.

op barray256_bound (rp : BArray1024.t) (sz : int) : bool =
  forall i, i \in range 0 256 => Fq.bw32 (BArray1024.get32 rp i) sz.

op poly_repr_bound (rp : BArray1024.t) (p : coeff Array256.t) (sz : int) : bool =
  poly_repr rp p /\ barray256_bound rp sz.

lemma bw32_weaken (w : W32.t) sz1 sz2 :
  0 <= sz1 <= sz2 =>
  Fq.bw32 w sz1 =>
  Fq.bw32 w sz2.
proof.
rewrite /Fq.bw32.
move=> [hsz10 hsz12] [hlo hhi].
have hpow : 2^sz1 <= 2^sz2.
+ by smt(StdOrder.IntOrder.ler_weexpn2l).
by smt().
qed.

lemma barray256_bound_weaken rp sz1 sz2 :
  0 <= sz1 <= sz2 =>
  barray256_bound rp sz1 =>
  barray256_bound rp sz2.
proof.
move=> hsz hbound i hi.
exact (bw32_weaken (BArray1024.get32 rp i) sz1 sz2 hsz (hbound i hi)).
qed.

lemma poly_repr_bound_repr rp p sz :
  poly_repr_bound rp p sz =>
  poly_repr rp p.
proof. by move=> [h _]. qed.

lemma poly_repr_bound_bound rp p sz :
  poly_repr_bound rp p sz =>
  barray256_bound rp sz.
proof. by move=> [_ h]. qed.

lemma barray256_to_polyE rp i :
  i \in range 0 256 =>
  (barray256_to_poly rp).[i] = word_to_coeff (BArray1024.get32 rp i).
proof.
move=> /mem_range hi.
by rewrite /barray256_to_poly initiE.
qed.

lemma poly_repr_get rp p i :
  poly_repr rp p =>
  i \in range 0 256 =>
  p.[i] = word_to_coeff (BArray1024.get32 rp i).
proof.
move=> h hi.
rewrite -h.
by rewrite barray256_to_polyE.
qed.

lemma poly_repr_bound_get rp p sz i :
  poly_repr_bound rp p sz =>
  i \in range 0 256 =>
  p.[i] = word_to_coeff (BArray1024.get32 rp i) /\
  Fq.bw32 (BArray1024.get32 rp i) sz.
proof.
move=> [hrepr hbound] hi.
split.
+ exact (poly_repr_get rp p i hrepr hi).
exact (hbound i hi).
qed.

lemma barray256_to_poly_set32E rp i w j :
  0 <= i < 256 =>
  j \in range 0 256 =>
  (barray256_to_poly (BArray1024.set32 rp i w)).[j] =
    if j = i then word_to_coeff w else (barray256_to_poly rp).[j].
proof.
move=> [hi0 hi256] /mem_range hj.
have hleft :
  (barray256_to_poly (BArray1024.set32 rp i w)).[j] =
  word_to_coeff (BArray1024.get32 (BArray1024.set32 rp i w) j).
+ by rewrite barray256_to_polyE 1:/#.
have hright :
  (barray256_to_poly rp).[j] = word_to_coeff (BArray1024.get32 rp j).
+ by rewrite barray256_to_polyE 1:/#.
have hset : 4 * (i + 1) <= 1024 by smt().
have hget :
  word_to_coeff (BArray1024.get32 (BArray1024.set32 rp i w) j) =
  word_to_coeff (if i = j then w else BArray1024.get32 rp j).
+ change (word_to_coeff (BArray1024.get32d (BArray1024.set32d rp (4 * i) w) (4 * j)) =
           word_to_coeff (if i = j then w else BArray1024.get32d rp (4 * j))).
   by rewrite BArray1024.get_set32E 1:/# 1:/#.
rewrite hleft hright hget.
case: (i = j) => [->|neqij].
+ by smt().
by smt().
qed.

lemma poly_repr_set32 rp p i w :
  poly_repr rp p =>
  0 <= i < 256 =>
  poly_repr (BArray1024.set32 rp i w) (p.[i <- word_to_coeff w]).
proof.
move=> hrepr hi.
apply/Array256.ext_eq => j /mem_range hj.
rewrite barray256_to_poly_set32E 1:/# 1:/#.
rewrite hrepr Array256.get_set_if /=.
case: (j = i) => _; by smt().
qed.

lemma barray256_bound_set32 rp i w sz :
  barray256_bound rp sz =>
  0 <= i < 256 =>
  Fq.bw32 w sz =>
  barray256_bound (BArray1024.set32 rp i w) sz.
proof.
move=> hbound hi hbw j hj.
have hget :
  BArray1024.get32 (BArray1024.set32 rp i w) j =
  if i = j then w else BArray1024.get32 rp j.
+ change (BArray1024.get32d (BArray1024.set32d rp (4 * i) w) (4 * j) =
          if i = j then w else BArray1024.get32d rp (4 * j)).
  by rewrite BArray1024.get_set32E 1:/# 1:/#.
rewrite hget.
case: (i = j) => hij.
+ exact hbw.
exact (hbound j hj).
qed.

lemma poly_repr_bound_set32 rp p i w sz :
  poly_repr_bound rp p sz =>
  0 <= i < 256 =>
  Fq.bw32 w sz =>
  poly_repr_bound (BArray1024.set32 rp i w)
    (p.[i <- word_to_coeff w]) sz.
proof.
move=> [hrepr hbound] hi hbw.
split.
+ exact (poly_repr_set32 rp p i w hrepr hi).
exact (barray256_bound_set32 rp i w sz hbound hi hbw).
qed.

lemma word_to_coeff_of_int z :
  W32.min_sint <= z <= W32.max_sint =>
  word_to_coeff (W32.of_int z) = incoeff z.
proof.
move=> hz.
by rewrite /word_to_coeff W32.to_sintK_small.
qed.

lemma w32_q_to_sint :
  W32.to_sint (W32.of_int q) = q.
proof.
  by rewrite W32.of_sintK /W32.smod /q /=.
qed.

lemma w32_negq_to_sint :
  W32.to_sint (W32.of_int (-q)) = -q.
proof.
  by rewrite W32.of_sintK /W32.smod /q /=.
qed.

lemma word_to_coeff_small z :
  `|z| < q =>
  word_to_coeff (W32.of_int z) = incoeff z.
proof.
move=> hz.
have hmin : W32.min_sint <= -q.
+ have hq := W32.to_sint_cmp (W32.of_int (-q)).
   by rewrite w32_negq_to_sint in hq; case: hq.
have hmax : q <= W32.max_sint.
+ have hq := W32.to_sint_cmp (W32.of_int q).
   by rewrite w32_q_to_sint in hq; case: hq.
apply word_to_coeff_of_int.
split; smt().
qed.

lemma incoeff_signed_repr z :
  `|z| < q =>
  incoeff z = incoeff (if 0 <= z then z else z + q).
proof.
move=> hz.
rewrite -eq_incoeff /q /=.
case: (0 <= z) => hz0; smt().
qed.

lemma word_to_coeff_repr z :
  `|z| < q =>
  word_to_coeff (W32.of_int z) = incoeff (if 0 <= z then z else z + q).
proof.
move=> hz.
rewrite word_to_coeff_small 1://.
by rewrite incoeff_signed_repr.
qed.

lemma word_to_coeff_neg16505 :
  word_to_coeff (W32.of_int (-16505)) = incoeff 48008.
proof.
by rewrite word_to_coeff_repr /q /=.
qed.

lemma word_to_coeff_26964 :
  word_to_coeff (W32.of_int 26964) = incoeff 26964.
proof.
by rewrite word_to_coeff_repr /q /=.
qed.

(* -------------------------------------------------------------------- *)
(* Mathematical definition of inverse NTT zetas.
   zetas_inv[k] = zroot^{-(bsrev8(k)+1)} for k=0..254,
   zetas_inv[255] = scale255 = inv(256).                                 *)
(* -------------------------------------------------------------------- *)

(* Zroot is a unit and its concrete inverse - needed for zetas_invE proof *)
lemma unit_zroot : Zq.unit zroot.
proof. by apply/unitE; rewrite /zroot -eq_incoeff /q /=. qed.

lemma inv_zroot : Zq.inv zroot = incoeff 6209.
proof.
  apply/(ZqRing.mulrI zroot); [apply unit_zroot|].
  rewrite ZqRing.mulrV; [apply unit_zroot|].
  by rewrite /zroot -incoeffM_mod /q /=.
qed.

op zetas_inv : coeff Array256.t =
  let vv = Array256.init (fun k => Zq.exp zroot (- (bsrev 8 k + 1))) in
      vv.[255 <- scale255].

lemma zetas_invE: zetas_inv = Array256.of_list witness
 [
  incoeff 6209; incoeff 39155; incoeff 49776; incoeff 23738; incoeff 3318; incoeff 56126; incoeff 2089; incoeff 14649;
  incoeff 17993; incoeff 13918; incoeff 54162; incoeff 54649; incoeff 21325; incoeff 53404; incoeff 31489; incoeff 36695;
  incoeff 38717; incoeff 44362; incoeff 33495; incoeff 57834; incoeff 23890; incoeff 18397; incoeff 19863; incoeff 21596;
  incoeff 57067; incoeff 21038; incoeff 36843; incoeff 23006; incoeff 32605; incoeff 46590; incoeff 24125; incoeff 15567;
  incoeff 63457; incoeff 1736; incoeff 42966; incoeff 26136; incoeff 15073; incoeff 28493; incoeff 11687; incoeff 62406;
  incoeff 58076; incoeff 19868; incoeff 40142; incoeff 46418; incoeff 32926; incoeff 15272; incoeff 55417; incoeff 56007;
  incoeff 15962; incoeff 4061; incoeff 52125; incoeff 24275; incoeff 31804; incoeff 49373; incoeff 12363; incoeff 51520;
  incoeff 48303; incoeff 51085; incoeff 54735; incoeff 46376; incoeff 56287; incoeff 63374; incoeff 52451; incoeff 42311;
  incoeff 29467; incoeff 25357; incoeff 63097; incoeff 60976; incoeff 36548; incoeff 14205; incoeff 45137; incoeff 63132;
  incoeff 40392; incoeff 62624; incoeff 1632; incoeff 32506; incoeff 20203; incoeff 22992; incoeff 52948; incoeff 32208;
  incoeff 21699; incoeff 42037; incoeff 24336; incoeff 59695; incoeff 7159; incoeff 62030; incoeff 19187; incoeff 32482;
  incoeff 2327; incoeff 54334; incoeff 22250; incoeff 23048; incoeff 9244; incoeff 63001; incoeff 27091; incoeff 29263;
  incoeff 30949; incoeff 61042; incoeff 59247; incoeff 56553; incoeff 59014; incoeff 1709; incoeff 58426; incoeff 55459;
  incoeff 19002; incoeff 12748; incoeff 57461; incoeff 13548; incoeff 21646; incoeff 22086; incoeff 62781; incoeff 12622;
  incoeff 36686; incoeff 34505; incoeff 31458; incoeff 27460; incoeff 34369; incoeff 14366; incoeff 737; incoeff 36421;
  incoeff 37539; incoeff 15997; incoeff 24976; incoeff 54733; incoeff 39116; incoeff 21713; incoeff 37421; incoeff 64087;
  incoeff 37420; incoeff 28411; incoeff 41914; incoeff 41550; incoeff 21815; incoeff 51621; incoeff 3488; incoeff 56824;
  incoeff 46534; incoeff 33955; incoeff 50102; incoeff 41774; incoeff 26249; incoeff 53129; incoeff 40811; incoeff 43852;
  incoeff 18415; incoeff 37661; incoeff 45056; incoeff 11948; incoeff 17623; incoeff 38963; incoeff 45024; incoeff 31550;
  incoeff 23607; incoeff 50630; incoeff 59602; incoeff 12472; incoeff 2651; incoeff 1018; incoeff 57452; incoeff 15029;
  incoeff 23622; incoeff 5153; incoeff 14639; incoeff 28229; incoeff 44407; incoeff 18391; incoeff 51971; incoeff 13776;
  incoeff 30727; incoeff 11556; incoeff 27959; incoeff 29791; incoeff 60350; incoeff 54251; incoeff 36324; incoeff 22393;
  incoeff 16090; incoeff 54679; incoeff 46917; incoeff 21107; incoeff 61256; incoeff 55694; incoeff 55910; incoeff 32226;
  incoeff 56903; incoeff 40857; incoeff 59644; incoeff 27065; incoeff 19062; incoeff 24379; incoeff 6635; incoeff 12063;
  incoeff 1735; incoeff 29893; incoeff 46337; incoeff 37700; incoeff 34311; incoeff 9574; incoeff 11161; incoeff 5600;
  incoeff 31897; incoeff 12565; incoeff 4547; incoeff 33090; incoeff 27155; incoeff 54572; incoeff 60397; incoeff 53685;
  incoeff 25947; incoeff 52648; incoeff 12778; incoeff 19070; incoeff 774; incoeff 1660; incoeff 41085; incoeff 13100;
  incoeff 61944; incoeff 21329; incoeff 27917; incoeff 15198; incoeff 43939; incoeff 30890; incoeff 22628; incoeff 25359;
  incoeff 42627; incoeff 60416; incoeff 11497; incoeff 57831; incoeff 48599; incoeff 31049; incoeff 10435; incoeff 39050;
  incoeff 53654; incoeff 59394; incoeff 18459; incoeff 59093; incoeff 19435; incoeff 41849; incoeff 19683; incoeff 51216;
  incoeff 52484; incoeff 58385; incoeff 41871; incoeff 55794; incoeff 52630; incoeff 41528; incoeff 60123; incoeff 19924;
  incoeff 58695; incoeff 39866; incoeff 51245; incoeff 47226; incoeff 44312; incoeff 48360; incoeff 35676; incoeff 64261
 ].
proof.
apply/Array256.ext_eq; move => i /mem_range mem_i_range.
rewrite /zetas_inv /= Array256.get_set_if /= /scale255 {1 2}/R /Fq.SignedReductions.R /=.
case: (i=255) => E.
 by rewrite E initiE //= -eq_incoeff /q /=.
rewrite initiE /=; first by rewrite -mem_range.
  rewrite -!ZqField.exprV inv_zroot.
  rewrite ZqField.exprS; [by rewrite bsrev_ge0|].
  rewrite -!(fastexp_nbitsP 8) ?bsrev_range //.
  rewrite /fastexp_nbits !int2bs_bsrev !revK /zroot.
  have incoeffQ_mod : forall (a : int) , incoeff (a * a %% q) = incoeff a * incoeff a.
  + by move => ?; rewrite -incoeffM_mod.
  do 8!(rewrite BS2Int.int2bs_rcons //= foldr_rcons /= -!incoeffQ_mod /q /=).
  rewrite BS2Int.int2bs0s /= ComRing.mul1r => {incoeffQ_mod}; move: i mem_i_range E.
rewrite /range /=; apply/List.allP.
by rewrite -JUtils.iotaredE /=  -!incoeffM_mod /= !incoeffK /q /=.
qed.

lemma scale255E :
  scale255 = inv (incoeff 256).
proof.
  apply/(ZqRing.mulrI (incoeff 256)).
  + by apply/unitE; rewrite -eq_incoeff /q.
  rewrite /scale255 -incoeffM_mod /q /= eq_sym -ZqRing.unitrE.
  by apply/unitE; rewrite -eq_incoeff /q.
qed.

lemma unit_R :
  Zq.unit R.
proof.
by apply/unitE; rewrite /R /Fq.SignedReductions.R -eq_incoeff /q /=.
qed.

lemma inv_R :
  inv R = incoeff 50386.
proof.
apply/(ZqRing.mulrI R); first exact unit_R.
rewrite ZqRing.mulrV; first exact unit_R.
by rewrite /R /Fq.SignedReductions.R /= -incoeffM /Zq.one -eq_incoeff /q /=.
qed.

(* These are powers of roots of unity in Mont form and
   bitwise permuted indices.  zetas_inv above needs to be
   defined, this axiom discharged, and then used to
   discharge other axioms below. *)
lemma zetas_inv_vals : array256_mont_inv zetas_inv =
    Array256.of_list witness
     [
      incoeff 20175; incoeff 56272; incoeff 37959; incoeff 32901; incoeff 35510; incoeff 12979; incoeff 47050; incoeff 56566;
      incoeff 12831; incoeff 39021; incoeff 14203; incoeff 21126; incoeff 55296; incoeff 61582; incoeff 8099; incoeff 50710;
      incoeff 41435; incoeff 48691; incoeff 27740; incoeff 22820; incoeff 16251; incoeff 56858; incoeff 20206; incoeff 994;
      incoeff 5823; incoeff 9488; incoeff 41289; incoeff 1035; incoeff 55624; incoeff 21944; incoeff 27010; incoeff 42592;
      incoeff 37579; incoeff 23751; incoeff 55605; incoeff 53743; incoeff 64448; incoeff 3528; incoeff 22805; incoeff 17737;
      incoeff 4800; incoeff 27298; incoeff 62752; incoeff 10226; incoeff 7729; incoeff 11242; incoeff 52444; incoeff 50631;
      incoeff 22243; incoeff 31368; incoeff 2202; incoeff 46231; incoeff 3304; incoeff 8253; incoeff 26851; incoeff 47252;
      incoeff 38877; incoeff 10865; incoeff 26985; incoeff 53874; incoeff 60705; incoeff 10170; incoeff 25912; incoeff 29735;
      incoeff 17374; incoeff 58433; incoeff 43059; incoeff 53841; incoeff 9939; incoeff 20316; incoeff 51230; incoeff 28190;
      incoeff 30274; incoeff 43091; incoeff 18166; incoeff 57131; incoeff 50871; incoeff 58593; incoeff 47019; incoeff 47331;
      incoeff 56771; incoeff 41074; incoeff 16630; incoeff 30332; incoeff 12882; incoeff 52133; incoeff 16160; incoeff 35992;
      incoeff 36259; incoeff 25921; incoeff 12543; incoeff 21900; incoeff 2648; incoeff 23016; incoeff 53542; incoeff 63488;
      incoeff 16319; incoeff 31332; incoeff 1311; incoeff 63824; incoeff 19194; incoeff 24162; incoeff 49649; incoeff 8796;
      incoeff 11808; incoeff 56831; incoeff 35666; incoeff 30317; incoeff 7401; incoeff 50880; incoeff 33533; incoeff 58749;
      incoeff 50847; incoeff 41038; incoeff 15739; incoeff 47925; incoeff 28772; incoeff 3529; incoeff 38958; incoeff 62049;
      incoeff 9190; incoeff 7374; incoeff 21224; incoeff 62856; incoeff 13857; incoeff 63726; incoeff 61163; incoeff 27989;
      incoeff 46842; incoeff 54953; incoeff 21442; incoeff 34151; incoeff 40669; incoeff 9874; incoeff 18586; incoeff 9522;
      incoeff 58637; incoeff 35074; incoeff 61669; incoeff 16405; incoeff 59191; incoeff 58600; incoeff 31064; incoeff 34950;
      incoeff 56584; incoeff 14501; incoeff 52463; incoeff 18832; incoeff 4127; incoeff 16186; incoeff 45782; incoeff 43011;
      incoeff 27727; incoeff 10623; incoeff 53252; incoeff 39528; incoeff 31327; incoeff 63353; incoeff 35803; incoeff 14941;
      incoeff 49003; incoeff 57754; incoeff 42382; incoeff 29051; incoeff 48006; incoeff 35445; incoeff 54723; incoeff 5342;
      incoeff 62707; incoeff 17631; incoeff 33161; incoeff 12442; incoeff 56202; incoeff 63025; incoeff 27685; incoeff 60543;
      incoeff 48967; incoeff 63678; incoeff 59975; incoeff 29942; incoeff 63915; incoeff 19555; incoeff 16267; incoeff 47057;
      incoeff 44160; incoeff 44700; incoeff 9604; incoeff 3761; incoeff 32399; incoeff 51816; incoeff 56699; incoeff 52922;
      incoeff 9430; incoeff 53898; incoeff 11459; incoeff 56916; incoeff 36823; incoeff 19129; incoeff 37980; incoeff 7941;
      incoeff 44897; incoeff 16608; incoeff 23970; incoeff 33905; incoeff 2391; incoeff 15130; incoeff 19646; incoeff 21464;
      incoeff 56620; incoeff 8577; incoeff 34870; incoeff 17941; incoeff 52731; incoeff 32076; incoeff 19725; incoeff 1296;
      incoeff 46274; incoeff 48067; incoeff 12296; incoeff 48209; incoeff 55130; incoeff 10049; incoeff 6789; incoeff 22562;
      incoeff 39261; incoeff 33693; incoeff 11361; incoeff 44370; incoeff 20035; incoeff 29133; incoeff 27527; incoeff 36366;
      incoeff 29104; incoeff 42082; incoeff 41578; incoeff 53832; incoeff 19553; incoeff 58272; incoeff 22946; incoeff 16039;
      incoeff 46914; incoeff 43105; incoeff 50769; incoeff 32369; incoeff 8851; incoeff 41654; incoeff 30985; incoeff 55118;
      incoeff 31218; incoeff 45449; incoeff 44270; incoeff 33767; incoeff 42284; incoeff 16505; incoeff 37549; incoeff 3836
     ].
proof.
  rewrite zetas_invE /array256_mont_inv /R /Fq.SignedReductions.R /scale255 /=.
  by rewrite -Array256.ext_eq_all /all_eq /= -!incoeffM_mod /q /=.
qed.

(* jzetas_inv stores Montgomery-form twiddle factors at indices 0..254.
   Index 255 is special: it stores f = mont^2/256 = -29720, used for the
   final scaling.  Therefore the full array equality is FALSE at index 255
   and we restrict the pointwise statement to i in [0, 254]. *)
(* The value stored at index 255 of jzetas_inv is f = -29720 = mont^2/256.
   word_to_coeff gives incoeff(-29720); the Montgomery relationship is:
   incoeff(-29720) * inv(R) = scale255 * R                                    *)
lemma jzetas_inv_255_get32E :
  BArray1024.get32 Hpoly_extract.jzetas_inv 255 = W32.of_int (-29720).
proof.
rewrite /Hpoly_extract.jzetas_inv.
rewrite BArray1024.get32_of_list32 1://.
do 300!(rewrite /=).
by [].
qed.

lemma jzetas_inv_255_wordE :
  word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas_inv 255) = incoeff (-29720).
proof.
rewrite jzetas_inv_255_get32E.
by rewrite (word_to_coeff_small (-29720)) 1:/#.
qed.

lemma jzetas_inv_poly_vals i :
  0 <= i < 255 =>
  (barray256_to_poly Hpoly_extract.jzetas_inv).[i] = (array256_mont_inv zetas_inv).[i].
proof.
move=> hi.
rewrite barray256_to_polyE 1:/#.
rewrite /Hpoly_extract.jzetas_inv.
rewrite BArray1024.get32_of_list32 1:/#.
rewrite zetas_inv_vals /=.
have hi_mem : i \in range 0 255 by rewrite mem_range.
move: hi_mem.
do 255!(rewrite range_ltn //=; move => [->> /=|];
          [by try rewrite /word_to_coeff; try rewrite W32.of_sintK;
              try rewrite /W32.smod /q /=; try rewrite -eq_incoeff /q /=; smt()|]).
by rewrite range_geq.
qed.

lemma jzetas_inv_get i :
  i \in range 0 255 =>
  (array256_mont_inv zetas_inv).[i] = word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas_inv i).
proof.
move=> /mem_range hi.
rewrite -(jzetas_inv_poly_vals i hi).
by rewrite barray256_to_polyE 1:/#.
qed.

lemma jzetas_inv_polyE :
  barray256_to_poly Hpoly_extract.jzetas_inv =
  (array256_mont_inv zetas_inv).[255 <- incoeff (-29720)].
proof.
apply/Array256.ext_eq => i /mem_range hi.
rewrite Array256.get_set_if /=.
case: (i = 255) => [->|neqi].
+ rewrite barray256_to_polyE 1:/#.
   by rewrite jzetas_inv_255_wordE.
+ have hi255 : 0 <= i < 255 by smt().
  rewrite (jzetas_inv_poly_vals i hi255).
   by [].
qed.

lemma zetas_inv_255_montE :
  (array256_mont_inv zetas_inv).[255] = scale255 * R.
proof.
  rewrite zetas_inv_vals get_of_list //=.
  by rewrite /scale255 /R -incoeffM_mod /q /=.
qed.

(* f = -29720 satisfies the Montgomery identity:
   incoeff(-29720) * inv(R) = scale255 * R
   Proof: multiply both sides by R and use -29720 ≡ scale255 * R^2 (mod q),
   which holds since (-252) * 14321^2 mod 64513 = (-252 * 4214) mod 64513
   = (-1061928) mod 64513 = 34793 = (-29720) mod 64513.                       *)
lemma jzetas_inv_255_scaleE :
  word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas_inv 255) * inv R = scale255 * R.
proof.
rewrite jzetas_inv_255_wordE.
by rewrite inv_R /scale255 /R -!incoeffM_mod /q /=.
qed.

op array256_mont (p : coeff Array256.t) =
  Array256.map (fun x => x * R) p.

(* -------------------------------------------------------------------- *)
(* Mathematical definition of forward NTT zetas.
   zetas[k] = zroot^{bsrev8(k)} for k=0..255.
   Index 0 is never accessed in the forward NTT (zetasctr starts at 1). *)
(* -------------------------------------------------------------------- *)

op zetas : coeff Array256.t =
    Array256.init (fun k => Zq.exp zroot (bsrev 8 k)).

lemma zetasE:
 zetas = Array256.of_list witness
          [
  incoeff 1; incoeff 28837; incoeff 16153; incoeff 20201; incoeff 17287; incoeff 13268; incoeff 24647; incoeff 5818;
  incoeff 44589; incoeff 4390; incoeff 22985; incoeff 11883; incoeff 8719; incoeff 22642; incoeff 6128; incoeff 12029;
  incoeff 13297; incoeff 44830; incoeff 22664; incoeff 45078; incoeff 5420; incoeff 46054; incoeff 5119; incoeff 10859;
  incoeff 25463; incoeff 54078; incoeff 33464; incoeff 15914; incoeff 6682; incoeff 53016; incoeff 4097; incoeff 21886;
  incoeff 39154; incoeff 41885; incoeff 33623; incoeff 20574; incoeff 49315; incoeff 36596; incoeff 43184; incoeff 2569;
  incoeff 51413; incoeff 23428; incoeff 62853; incoeff 63739; incoeff 45443; incoeff 51735; incoeff 11865; incoeff 38566;
  incoeff 10828; incoeff 4116; incoeff 9941; incoeff 37358; incoeff 31423; incoeff 59966; incoeff 51948; incoeff 32616;
  incoeff 58913; incoeff 53352; incoeff 54939; incoeff 30202; incoeff 26813; incoeff 18176; incoeff 34620; incoeff 62778;
  incoeff 52450; incoeff 57878; incoeff 40134; incoeff 45451; incoeff 37448; incoeff 4869; incoeff 23656; incoeff 7610;
  incoeff 32287; incoeff 8603; incoeff 8819; incoeff 3257; incoeff 43406; incoeff 17596; incoeff 9834; incoeff 48423;
  incoeff 42120; incoeff 28189; incoeff 10262; incoeff 4163; incoeff 34722; incoeff 36554; incoeff 52957; incoeff 33786;
  incoeff 50737; incoeff 12542; incoeff 46122; incoeff 20106; incoeff 36284; incoeff 49874; incoeff 59360; incoeff 40891;
  incoeff 49484; incoeff 7061; incoeff 63495; incoeff 61862; incoeff 52041; incoeff 4911; incoeff 13883; incoeff 40906;
  incoeff 32963; incoeff 19489; incoeff 25550; incoeff 46890; incoeff 52565; incoeff 19457; incoeff 26852; incoeff 46098;
  incoeff 20661; incoeff 23702; incoeff 11384; incoeff 38264; incoeff 22739; incoeff 14411; incoeff 30558; incoeff 17979;
  incoeff 7689; incoeff 61025; incoeff 12892; incoeff 42698; incoeff 22963; incoeff 22599; incoeff 36102; incoeff 27093;
  incoeff 426; incoeff 27092; incoeff 42800; incoeff 25397; incoeff 9780; incoeff 39537; incoeff 48516; incoeff 26974;
  incoeff 28092; incoeff 63776; incoeff 50147; incoeff 30144; incoeff 37053; incoeff 33055; incoeff 30008; incoeff 27827;
  incoeff 51891; incoeff 1732; incoeff 42427; incoeff 42867; incoeff 50965; incoeff 7052; incoeff 51765; incoeff 45511;
  incoeff 9054; incoeff 6087; incoeff 62804; incoeff 5499; incoeff 7960; incoeff 5266; incoeff 3471; incoeff 33564;
  incoeff 35250; incoeff 37422; incoeff 1512; incoeff 55269; incoeff 41465; incoeff 42263; incoeff 10179; incoeff 62186;
  incoeff 32031; incoeff 45326; incoeff 2483; incoeff 57354; incoeff 4818; incoeff 40177; incoeff 22476; incoeff 42814;
  incoeff 32305; incoeff 11565; incoeff 41521; incoeff 44310; incoeff 32007; incoeff 62881; incoeff 1889; incoeff 24121;
  incoeff 1381; incoeff 19376; incoeff 50308; incoeff 27965; incoeff 3537; incoeff 1416; incoeff 39156; incoeff 35046;
  incoeff 22202; incoeff 12062; incoeff 1139; incoeff 8226; incoeff 18137; incoeff 9778; incoeff 13428; incoeff 16210;
  incoeff 12993; incoeff 52150; incoeff 15140; incoeff 32709; incoeff 40238; incoeff 12388; incoeff 60452; incoeff 48551;
  incoeff 8506; incoeff 9096; incoeff 49241; incoeff 31587; incoeff 18095; incoeff 24371; incoeff 44645; incoeff 6437;
  incoeff 2107; incoeff 52826; incoeff 36020; incoeff 49440; incoeff 38377; incoeff 21547; incoeff 62777; incoeff 1056;
  incoeff 48946; incoeff 40388; incoeff 17923; incoeff 31908; incoeff 41507; incoeff 27670; incoeff 43475; incoeff 7446;
  incoeff 42917; incoeff 44650; incoeff 46116; incoeff 40623; incoeff 6679; incoeff 31018; incoeff 20151; incoeff 25796;
  incoeff 27818; incoeff 33024; incoeff 11109; incoeff 43188; incoeff 9864; incoeff 10351; incoeff 50595; incoeff 46520;
  incoeff 49864; incoeff 62424; incoeff 8387; incoeff 61195; incoeff 40775; incoeff 14737; incoeff 25358; incoeff 58304
 ].
proof.
  apply/Array256.ext_eq => i /mem_range mem_i_range.
  rewrite /zetas -?mem_range //.
  rewrite initiE -?mem_range //; move: mem_i_range.
  rewrite /= -(fastexp_nbitsP 8) ?bsrev_range //.
  rewrite /fastexp_nbits int2bs_bsrev revK /zroot.
  do 8!(rewrite BS2Int.int2bs_rcons //= foldr_rcons /= /q /=).
  rewrite BS2Int.int2bs0s /= ComRing.mul1r.
  do 256!(rewrite range_ltn //=; move => [->> /=|];
            [by rewrite -!incoeffM_mod !incoeffK /q|]).
  by rewrite range_geq.
qed.

(* These are powers of roots of unity in Mont form and
   bitwise permuted indices.  *)
lemma zetas_vals : array256_mont zetas =
    Array256.of_list witness
     [
      incoeff 14321; incoeff 26964; incoeff 48008; incoeff 22229; incoeff 30746; incoeff 20243; incoeff 19064; incoeff 33295;
      incoeff 9395; incoeff 33528; incoeff 22859; incoeff 55662; incoeff 32144; incoeff 13744; incoeff 21408; incoeff 17599;
      incoeff 48474; incoeff 41567; incoeff 6241; incoeff 44960; incoeff 10681; incoeff 22935; incoeff 22431; incoeff 35409;
      incoeff 28147; incoeff 36986; incoeff 35380; incoeff 44478; incoeff 20143; incoeff 53152; incoeff 30820; incoeff 25252;
      incoeff 41951; incoeff 57724; incoeff 54464; incoeff 9383; incoeff 16304; incoeff 52217; incoeff 16446; incoeff 18239;
      incoeff 63217; incoeff 44788; incoeff 32437; incoeff 11782; incoeff 46572; incoeff 29643; incoeff 55936; incoeff 7893;
      incoeff 43049; incoeff 44867; incoeff 49383; incoeff 62122; incoeff 30608; incoeff 40543; incoeff 47905; incoeff 19616;
      incoeff 56572; incoeff 26533; incoeff 45384; incoeff 27690; incoeff 7597; incoeff 53054; incoeff 10615; incoeff 55083;
      incoeff 11591; incoeff 7814; incoeff 12697; incoeff 32114; incoeff 60752; incoeff 54909; incoeff 19813; incoeff 20353;
      incoeff 17456; incoeff 48246; incoeff 44958; incoeff 598; incoeff 34571; incoeff 4538; incoeff 835; incoeff 15546;
      incoeff 3970; incoeff 36828; incoeff 1488; incoeff 8311; incoeff 52071; incoeff 31352; incoeff 46882; incoeff 1806;
      incoeff 59171; incoeff 9790; incoeff 29068; incoeff 16507; incoeff 35462; incoeff 22131; incoeff 6759; incoeff 15510;
      incoeff 49572; incoeff 28710; incoeff 1160; incoeff 33186; incoeff 24985; incoeff 11261; incoeff 53890; incoeff 36786;
      incoeff 21502; incoeff 18731; incoeff 48327; incoeff 60386; incoeff 45681; incoeff 12050; incoeff 50012; incoeff 7929;
      incoeff 29563; incoeff 33449; incoeff 5913; incoeff 5322; incoeff 48108; incoeff 2844; incoeff 29439; incoeff 5876;
      incoeff 54991; incoeff 45927; incoeff 54639; incoeff 23844; incoeff 30362; incoeff 43071; incoeff 9560; incoeff 17671;
      incoeff 36524; incoeff 3350; incoeff 787; incoeff 50656; incoeff 1657; incoeff 43289; incoeff 57139; incoeff 55323;
      incoeff 2464; incoeff 25555; incoeff 60984; incoeff 35741; incoeff 16588; incoeff 48774; incoeff 23475; incoeff 13666;
      incoeff 5764; incoeff 30980; incoeff 13633; incoeff 57112; incoeff 34196; incoeff 28847; incoeff 7682; incoeff 52705;
      incoeff 55717; incoeff 14864; incoeff 40351; incoeff 45319; incoeff 689; incoeff 63202; incoeff 33181; incoeff 48194;
      incoeff 1025; incoeff 10971; incoeff 41497; incoeff 61865; incoeff 42613; incoeff 51970; incoeff 38592; incoeff 28254;
      incoeff 28521; incoeff 48353; incoeff 12380; incoeff 51631; incoeff 34181; incoeff 47883; incoeff 23439; incoeff 7742;
      incoeff 17182; incoeff 17494; incoeff 5920; incoeff 13642; incoeff 7382; incoeff 46347; incoeff 21422; incoeff 34239;
      incoeff 36323; incoeff 13283; incoeff 44197; incoeff 54574; incoeff 10672; incoeff 21454; incoeff 6080; incoeff 47139;
      incoeff 34778; incoeff 38601; incoeff 54343; incoeff 3808; incoeff 10639; incoeff 37528; incoeff 53648; incoeff 25636;
      incoeff 17261; incoeff 37662; incoeff 56260; incoeff 61209; incoeff 18282; incoeff 62311; incoeff 33145; incoeff 42270;
      incoeff 13882; incoeff 12069; incoeff 53271; incoeff 56784; incoeff 54287; incoeff 1761; incoeff 37215; incoeff 59713;
      incoeff 46776; incoeff 41708; incoeff 60985; incoeff 65; incoeff 10770; incoeff 8908; incoeff 40762; incoeff 26934;
      incoeff 21921; incoeff 37503; incoeff 42569; incoeff 8889; incoeff 63478; incoeff 23224; incoeff 55025; incoeff 58690;
      incoeff 63519; incoeff 44307; incoeff 7655; incoeff 48262; incoeff 41693; incoeff 36773; incoeff 15822; incoeff 23078;
      incoeff 13803; incoeff 56414; incoeff 2931; incoeff 9217; incoeff 43387; incoeff 50310; incoeff 25492; incoeff 51682;
      incoeff 7947; incoeff 17463; incoeff 51534; incoeff 29003; incoeff 31612; incoeff 26554; incoeff 8241; incoeff 44338
     ].
proof.
  rewrite zetasE /array256_mont Array256.mapE /R /=.
  by rewrite -Array256.ext_eq_all /all_eq /= -!incoeffM_mod /q /=.
qed.

lemma jzetas_1_poly :
  (barray256_to_poly Hpoly_extract.jzetas).[1] = (array256_mont zetas).[1].
proof.
  rewrite barray256_to_polyE ?mem_range 1:/#.
  rewrite BArray1024.get32_of_list32 1://.
  rewrite zetas_vals get_of_list //=.
  by rewrite word_to_coeff_26964.
qed.

lemma jzetas_1_word_montE :
  word_to_coeff (W32.of_int 26964) = (array256_mont zetas).[1].
proof.
  rewrite zetas_vals get_of_list //=.
  by rewrite word_to_coeff_26964.
qed.

lemma jzetas_1_get32E :
  word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas 1) = (array256_mont zetas).[1].
proof.
  rewrite BArray1024.get32_of_list32 1://.
  rewrite zetas_vals get_of_list //=.
  by rewrite word_to_coeff_26964.
qed.

lemma jzetas_1_get32dE :
  word_to_coeff (BArray1024.get32d Hpoly_extract.jzetas (4 * 1)) = (array256_mont zetas).[1].
proof.
  rewrite BArray1024.get32_of_list32 1://.
  rewrite zetas_vals get_of_list //=.
  by rewrite word_to_coeff_26964.
qed.

lemma jzetas_polyE :
  barray256_to_poly Hpoly_extract.jzetas =
  (array256_mont zetas).[0 <- incoeff 0].
proof.
apply/Array256.ext_eq => i hi_range.
have hi : 0 <= i < 256 by exact hi_range.
have hi_mem : i \in range 0 256 by rewrite mem_range.
rewrite barray256_to_polyE 1:/#.
rewrite /Hpoly_extract.jzetas.
rewrite BArray1024.get32_of_list32 1:/#.
rewrite Array256.get_set_if /=.
case: (i = 0) => eqi.
+ by rewrite word_to_coeff_repr /q /=.
+ rewrite zetas_vals.
  have hi_tail : i \in range 1 256 by rewrite mem_range; smt().
  move: hi_tail.
  do 255!(rewrite range_ltn //=; move => [->> /=|];
            [by try rewrite /word_to_coeff; try rewrite W32.of_sintK;
                try rewrite /W32.smod /q /=; try rewrite -eq_incoeff /q /=; smt()|]).
  by rewrite range_geq.
qed.

(* jzetas stores Montgomery-form twiddle factors at indices 1..255.
   Index 0 is padding (value 0); it is never accessed in the forward NTT
   since zetasctr is incremented before the first access.  The full array
   equality is therefore FALSE at index 0 (jzetas[0]=0 but
   (array256_mont zetas)[0] = R = 14321), so we restrict to i in [1, 255]. *)
lemma jzetas_poly_vals i :
  1 <= i < 256 =>
  (barray256_to_poly Hpoly_extract.jzetas).[i] = (array256_mont zetas).[i].
proof.
move=> hi.
rewrite jzetas_polyE Array256.get_set_if /=.
case: (i = 0) => [eqi|neqi].
+ move: hi eqi => /#.
+ by [].
qed.

lemma jzetas_get i :
  1 <= i < 256 =>
  (array256_mont zetas).[i] = word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas i).
proof.
  move=> [hi1 hi2].
  rewrite -(jzetas_poly_vals i _) 1:/# /barray256_to_poly initiE 1:/# //.
qed.

lemma zetas_1_montE :
  (array256_mont zetas).[1] = incoeff 26964.
proof.
  by rewrite zetas_vals get_of_list //=.
qed.

lemma jzetas_1E :
  word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas 1) =
  (array256_mont zetas).[1].
proof.
  by rewrite -(jzetas_get 1 _).
qed.

lemma jzetas_1_wordE :
  word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas 1) = incoeff 26964.
proof.
  by rewrite jzetas_1E zetas_1_montE.
qed.

(* inv(256) mod q, needed for the final scaling proof *)
lemma exp_zroot_256 : Zq.exp zroot 256 = incoeff (-1).
proof.
have h128 : Zq.exp zroot 128 = incoeff 28837.
+ have hz : zetas.[1] = Zq.exp zroot 128.
+   by rewrite /zetas initiE ?mem_range //= bsrev1 //=.
  have hz1 : zetas.[1] = incoeff 28837 by rewrite zetasE get_of_list //=.
  by rewrite -hz hz1.
have -> : Zq.exp zroot 256 = Zq.exp zroot 128 * Zq.exp zroot 128.
+ rewrite (_ : 256 = 128 + 128) 1://.
   by rewrite (ZqField.exprD_nneg zroot 128 128) 1,2://.
rewrite h128 -incoeffM_mod /q /=.
by rewrite -eq_incoeff /q /=.
qed.

end NTT_Fq.
