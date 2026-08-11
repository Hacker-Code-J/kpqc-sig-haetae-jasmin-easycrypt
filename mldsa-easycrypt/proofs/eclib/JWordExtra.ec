(* -------------------------------------------------------------------- *)
require import AllCore List Ring IntDiv BitEncoding.
require import StdRing StdOrder.

from Jasmin require import JWord.

import BS2Int.

(* -------------------------------------------------------------------- *)
lemma w2bits_int2bsE (w : W32.t) : w2bits w = BS2Int.int2bs 32 (W32.to_uint w).
proof. rewrite to_uintE; smt(W32.size_w2bits BS2Int.bs2intK). qed.

(* -------------------------------------------------------------------- *)
abstract theory WE.
  op size : int.

  clone import BitWord as W with op size <- size.

  lemma msbE (w : t): msb w <=> w.[size - 1].
  proof.
  have ? := gt0_size; rewrite /msb /to_uint /w2bits.
  rewrite (mkseqS _ (size - 1)) 1:/# bs2int_rcons /=.
  pose s := mkseq _ _; have := bs2int_le2Xs s.
  rewrite size_mkseq lez_maxr 1:/#; case: w.[_] => /= ?.
  - by rewrite lez_addr bs2int_ge0.
  - by rewrite lezNgt.
  qed.

  lemma to_uintUD (w1 w2: W.t) : to_uint w2 <> 0 =>
    to_uint (w1 \udiv w2) = to_uint w1 %/ to_uint w2.
  proof. move=> @/(\udiv) @/ulift2; smt(to_uint_cmp to_uint_small). qed.

  lemma to_uintUM (w1 w2: W.t) : 
    to_uint (w1 \umod w2) = to_uint w1 %% to_uint w2.
  proof.
  rewrite /(\umod) /ulift2; apply to_uint_small.
  smt(to_uint_cmp to_uint_small JUtils.modz_cmp modz0).
  qed.

  lemma set_get (w : W.t) (i : int) : w.[i <- w.[i]] = w.
  proof. by apply/ext_eq=> j ?; rewrite get_set_if /#. qed.

  lemma sarwE (w : W.t) (i j : int) :
    (w `|>>>` i).[j] = (0 <= j < size && w.[min (size - 1) (j + i)]).
  proof. by rewrite sarE initE. qed.

  lemma sar0 (w : W.t) : w `|>>>` 0 = w.
  proof. by apply/ext_eq=> i ?; rewrite sarwE /#. qed.

  lemma sarD (w : W.t) (i j : int) :
    0 <= i => 0 <= j => w `|>>>` (i + j) = (w `|>>>` i) `|>>>` j.
  proof. by move=> *; apply/ext_eq=> k ?; rewrite !sarwE /= /#. qed.

  lemma sarSl (w : W.t) (i : int) :
    0 <= i => w `|>>>` (i + 1) = (w `|>>>` i) `|>>>` 1.
  proof. by move=> *; rewrite sarD. qed.

  lemma sarSr (w : W.t) (i : int) :
    0 <= i => w `|>>>` (i + 1) = (w `|>>>` 1) `|>>>` i.
  proof. by move=> *; rewrite addzC sarD. qed.

  lemma shr0 (w : W.t) : w `>>>` 0 = w.
  proof. by apply/ext_eq=> i ?; rewrite shrwE /#. qed.

  lemma shrD (w : W.t) (i j : int) :
    0 <= i => 0 <= j => w `>>>` (i + j) = (w `>>>` i) `>>>` j.
  proof.
  move=> *; apply/ext_eq=> k ?.
  by rewrite !shrwE /= #smt:(get_out).
  qed.

  lemma shrSl (w : W.t) (i : int) :
    0 <= i => w `>>>` (i + 1) = (w `>>>` i) `>>>` 1.
  proof. by move=> *; rewrite shrD. qed.

  lemma shrSr (w : W.t) (i : int) :
    0 <= i => w `>>>` (i + 1) = (w `>>>` 1) `>>>` i.
  proof. by move=> *; rewrite addzC shrD. qed.

  lemma sar1_shrE (w : W.t) :
    w `|>>>` 1 = (w `>>>` 1).[size - 1 <- msb w].
  proof.
  apply/ext_eq=> i rgi.
  by rewrite msbE sarE get_setE 1:/# !initE /#.
  qed.

  lemma to_uint_sar1 (w : W.t) :
    to_uint (w `|>>>` 1) = to_uint w %/ 2 + (2^(size - 1)) * b2i (msb w).
  proof.
  have ? := gt0_size; rewrite sar1_shrE {1}/W.to_uint.
  rewrite /w2bits (mkseqS _ (size - 1)) 1:/# /=.
  rewrite set_eqiE ~-1://# -(eq_in_mkseq ("_.[_]" (w `>>>` 1))).
  - by move=> i ?; rewrite get_set_if ifF //#.
  rewrite bs2int_rcons /= size_mkseq lez_maxr 1:/#; congr.
  pose s := mkseq _ _; rewrite (_ : bs2int s = bs2int (rcons s false)).
  - by rewrite bs2int_rcons.
  rewrite (_ : false = msb (w `>>>` 1)).
  - by rewrite msbE shrwE /= get_out.
  rewrite msbE /s -mkseqS 1:/# /= -/(W.w2bits (w `>>>` 1)).
  by rewrite -to_uintE to_uint_shr.
  qed.

  lemma to_sint_sar1 (w : W.t) :
    to_sint (w `|>>>` 1) = to_sint w %/ 2.
  proof.
  have ? := gt0_size; have ? := to_uint_cmp.
  rewrite !to_sintE to_uint_sar1; case _: (W.msb _) => /=; last first.
  - move/ltzNge=> ?; rewrite /smod !ifF // lezNgt //=.
    by rewrite b2i0 /= ltz_divLR //#.
  move=> @/msb ?; rewrite {1}/W.smod ifT 1:/#.
  rewrite /smod ifT // -addrA (_ : _ - _ = -2^(size - 1)).
  - by rewrite (IntID.exprS _ (size - 1)) ~-1:/# #ring.
  rewrite divzDr /=; first by rewrite dvdzN (dvdz_exp2l 2 1) /#.
  rewrite divNz // divzDl 1:(dvdz_exp2l 2 1) ~-1://# /=.
  by rewrite -half_modulus.
  qed.

  lemma to_sint_sar (w : W.t) (i : int) : 0 <= i =>
    to_sint (w `|>>>` i) = to_sint w %/ 2^i.
  proof.
  have ? := gt0_size; have ? := to_uint_cmp.
  elim: i => /= [|n ge0_n ih]; first by rewrite sar0.
  rewrite sarSl // to_sint_sar1 ih.
  rewrite -divz_mulp ~-1:// 1:IntOrder.expr_gt0 ~-1://.
  by rewrite -IntID.exprSr.
  qed.
end WE.

(* -------------------------------------------------------------------- *)
clone WE as WE8 with
  op     size <- 8,
  theory W    <- W8 { rename "_XX" as "_8" }.

(* -------------------------------------------------------------------- *)
clone WE as WE16 with
  op     size <- 16,
  theory W    <- W16 { rename "_XX" as "_16" } .

(* -------------------------------------------------------------------- *)
clone WE as WE32 with
  op     size <- 32,
  theory W    <- W32 { rename "_XX" as "_32" } .

(* -------------------------------------------------------------------- *)
clone WE as WE64 with
  op     size <- 64,
  theory W    <- W64 { rename "_XX" as "_64" } .

(* -------------------------------------------------------------------- *)
clone WE as WE128 with
  op     size <- 128,
  theory W    <- W128 { rename "_XX" as "_128" } .

(* -------------------------------------------------------------------- *)
clone WE as WE256 with
  op     size <- 256,
  theory W    <- W256 { rename "_XX" as "_256" } .
