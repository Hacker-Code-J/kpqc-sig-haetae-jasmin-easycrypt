(* Verification surface for the reference Jasmin extraction only.
   This file is intentionally narrower than NTTAlgebra.ec:
   it targets extract/Hpoly_loop.ec and stops at refinement to
   the imperative EasyCrypt NTT procedures in NTT_Fq.ec. *)

require import AllCore IntDiv CoreMap List Distr Ring StdOrder BitEncoding.
from Jasmin require import JWord JModel_x86.
import SLH64.

require import Array256 BArray1024.
require import Fq Fastexp.
require import GFq Rq.
require import Montgomery.
require import NTT_Fq.
require import Hpoly_loop.

import Zq IntOrder BitReverse.

theory RefJasminNTT.

lemma int_shr1_div2 x :
  0 <= x =>
  x `|>>` 1 = x %/ 2.
proof.
move=> _.
by rewrite /(`|>>`) /(`<<`) /=.
qed.

lemma int_shl1_mul2 x :
  x `<<` 1 = x * 2.
proof.
by rewrite /(`<<`) /=.
qed.

lemma word_to_coeff_add (a b : W32.t) (asz bsz : int) :
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  Fq.bw32 a asz =>
  Fq.bw32 b bsz =>
  NTT_Fq.word_to_coeff (a + b) =
    NTT_Fq.word_to_coeff a + NTT_Fq.word_to_coeff b.
proof.
pose aszb := 2^asz.
pose bszb := 2^bsz.
rewrite /Fq.bw32 /NTT_Fq.word_to_coeff.
move=> /= *.
have /= bounds_asz : 0 < aszb <= 2^30
  by split; [ apply gt0_pow2
            | move => *; rewrite /aszb; apply StdOrder.IntOrder.ler_weexpn2l => /> /#].
have /= bounds_bsz : 0 < bszb <= 2^30
  by split; [ apply gt0_pow2
            | move => *; rewrite /bszb; apply StdOrder.IntOrder.ler_weexpn2l => /> /#].
rewrite W32.to_sintD_small => />; first by smt().
by rewrite incoeffD.
qed.

lemma word_to_coeff_sub (a b : W32.t) (asz bsz : int) :
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  Fq.bw32 a asz =>
  Fq.bw32 b bsz =>
  NTT_Fq.word_to_coeff (a - b) =
    NTT_Fq.word_to_coeff a - NTT_Fq.word_to_coeff b.
proof.
pose aszb := 2^asz.
pose bszb := 2^bsz.
rewrite /Fq.bw32 /NTT_Fq.word_to_coeff.
move=> /= *.
have /= bounds_asz : 0 < aszb <= 2^30
  by split; [ apply gt0_pow2
            | move => *; rewrite /aszb; apply StdOrder.IntOrder.ler_weexpn2l => /> /#].
have /= bounds_bsz : 0 < bszb <= 2^30
  by split; [ apply gt0_pow2
            | move => *; rewrite /bszb; apply StdOrder.IntOrder.ler_weexpn2l => /> /#].
rewrite W32.to_sintB_small => />; first by smt().
by rewrite incoeffB.
qed.

lemma forward_butterfly_bounds s t asz tsz :
  0 <= asz < 31 =>
  0 <= tsz < 31 =>
  Fq.bw32 s asz =>
  Fq.bw32 t tsz =>
  Fq.bw32 (s + t) (max asz tsz + 1) /\
  Fq.bw32 (s - t) (max asz tsz + 1).
proof.
move=> hasz htsz hbws hbwt.
split.
+ exact (Fq.add_corr s t asz tsz hasz htsz hbws hbwt).
exact (Fq.sub_corr s t asz tsz hasz htsz hbws hbwt).
qed.

lemma inverse_butterfly_bounds t0 coeff asz bsz :
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  Fq.bw32 t0 asz =>
  Fq.bw32 coeff bsz =>
  Fq.bw32 (t0 + coeff) (max asz bsz + 1) /\
  Fq.bw32 (t0 - coeff) (max asz bsz + 1).
proof.
move=> hasz hbsz hbwt0 hbwcoeff.
split.
+ exact (Fq.add_corr t0 coeff asz bsz hasz hbsz hbwt0 hbwcoeff).
exact (Fq.sub_corr t0 coeff asz bsz hasz hbsz hbwt0 hbwcoeff).
qed.

lemma unit_R_ref : Zq.unit NTT_Fq.R.
proof.
by apply/unitE; rewrite /NTT_Fq.R /Fq.SignedReductions.R -eq_incoeff /q /=.
qed.

lemma inv_R_ref :
  inv NTT_Fq.R = incoeff 50386.
proof.
apply/(ZqRing.mulrI NTT_Fq.R); first exact unit_R_ref.
rewrite ZqRing.mulrV.
+ exact unit_R_ref.
by rewrite /NTT_Fq.R /Fq.SignedReductions.R /= -incoeffM /Zq.one -eq_incoeff /q /=.
qed.

lemma array256_mont_get p i :
  i \in range 0 256 =>
  (NTT_Fq.array256_mont p).[i] = p.[i] * NTT_Fq.R.
proof.
move=> /mem_range hi.
by rewrite /NTT_Fq.array256_mont /Array256.map initiE.
qed.

lemma mont_cancel p i :
  i \in range 0 256 =>
  (NTT_Fq.array256_mont p).[i] * inv NTT_Fq.R = p.[i].
proof.
move=> hi.
rewrite array256_mont_get 1:/# inv_R_ref.
have -> : p.[i] * NTT_Fq.R * incoeff 50386 = p.[i] * (NTT_Fq.R * incoeff 50386) by ring.
rewrite /NTT_Fq.R -incoeffM_mod /q /=.
by rewrite ZqRing.mulr1.
qed.

lemma jzetas_get_cancel i :
  1 <= i < 256 =>
  NTT_Fq.word_to_coeff (BArray1024.get32 Hpoly_loop.jzetas i) * inv NTT_Fq.R =
  NTT_Fq.zetas.[i].
proof.
move=> hi.
rewrite -NTT_Fq.jzetas_get 1:/#.
apply mont_cancel.
by rewrite mem_range; smt().
qed.

lemma array256_mont_inv_get p i :
  i \in range 0 256 =>
  (NTT_Fq.array256_mont_inv p).[i] = p.[i] * NTT_Fq.R.
proof.
move=> /mem_range hi.
by rewrite /NTT_Fq.array256_mont_inv /Array256.map initiE.
qed.

lemma mont_inv_cancel p i :
  i \in range 0 256 =>
  (NTT_Fq.array256_mont_inv p).[i] * inv NTT_Fq.R = p.[i].
proof.
move=> hi.
rewrite array256_mont_inv_get 1:/# inv_R_ref.
have -> : p.[i] * NTT_Fq.R * incoeff 50386 = p.[i] * (NTT_Fq.R * incoeff 50386) by ring.
rewrite /NTT_Fq.R -incoeffM_mod /q /=.
by rewrite ZqRing.mulr1.
qed.

lemma jzetas_inv_get_cancel i :
  i \in range 0 255 =>
  NTT_Fq.word_to_coeff (BArray1024.get32 Hpoly_loop.jzetas_inv i) * inv NTT_Fq.R =
  NTT_Fq.zetas_inv.[i].
proof.
move=> hi.
rewrite -NTT_Fq.jzetas_inv_get 1:/#.
apply mont_inv_cancel.
have /mem_range hi' := hi.
by rewrite mem_range; smt().
qed.

lemma jzetas_inv_255_scale_cancel :
  NTT_Fq.word_to_coeff (BArray1024.get32 Hpoly_loop.jzetas_inv 255) * inv NTT_Fq.R =
  NTT_Fq.scale255 * NTT_Fq.R.
proof.
exact NTT_Fq.jzetas_inv_255_scaleE.
qed.

lemma loop_fqmul_corr_h aa bb :
  hoare [Hpoly_loop.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    W32.to_sint res = Fq.SignedReductions.SREDC (aa * bb)].
proof.
proc.
wp.
call (Fq.fqmul_corr_h aa bb).
skip=> &hr [Ha Hb] /=.
by [].
qed.

lemma loop_fqmul_ll :
  islossless Hpoly_loop.M.__fqmul.
proof.
proc.
call Fq.fqmul_ll.
auto.
qed.

lemma fqmul_bw32_16 aa bb :
  - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb < Fq.SignedReductions.R %/ 2 * Fq.q =>
  hoare [Hpoly_loop.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    Fq.bw32 res 16].
proof.
move=> hbound.
conseq (loop_fqmul_corr_h aa bb).
move=> &hr [Ha Hb] result Hres /=.
rewrite /Fq.bw32.
have hq : 0 < Fq.q < Fq.SignedReductions.R %/ 2.
+ by rewrite /Fq.q /Fq.SignedReductions.R /=.
have hs := Fq.SignedReductions.SREDCp_corr (aa * bb) hq hbound.
rewrite Hres.
have hq16 : Fq.q < 2^16 by rewrite /Fq.q /=.
have hq16' : - (2^16) <= -Fq.q by smt().
have hs' : -Fq.q <= Fq.SignedReductions.SREDC (aa * bb) < Fq.q by have := hs; smt().
by smt().
qed.

lemma fqmul_word_to_coeff_mul aa bb :
  - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb < Fq.SignedReductions.R %/ 2 * Fq.q =>
  hoare [Hpoly_loop.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    NTT_Fq.word_to_coeff res = incoeff aa * incoeff bb * inv NTT_Fq.R].
proof.
move=> hbound.
conseq (loop_fqmul_corr_h aa bb).
move=> &hr [Ha Hb] result Hres /=.
rewrite /NTT_Fq.word_to_coeff Hres inv_R_ref -!incoeffM.
apply/eq_incoeff.
rewrite !incoeffK qE /=.
have hq : 0 < Fq.q < Fq.SignedReductions.R %/ 2.
+ by rewrite /Fq.q /Fq.SignedReductions.R /=.
have hs := Fq.SignedReductions.SREDCp_corr (aa * bb) hq hbound.
move: hs => [_ hsmod].
rewrite /Fq.q in hsmod.
rewrite hsmod.
smt(modzMml modzMmr).
qed.

lemma fqmul_word_to_coeff_mul_h aa bb :
  hoare [Hpoly_loop.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb <
      Fq.SignedReductions.R %/ 2 * Fq.q ==>
    NTT_Fq.word_to_coeff res = incoeff aa * incoeff bb * inv NTT_Fq.R].
proof.
conseq (loop_fqmul_corr_h aa bb).
+ by smt().
move=> &hr [Ha [Hb Hbound]] result Hres /=.
rewrite /NTT_Fq.word_to_coeff Hres inv_R_ref -!incoeffM.
apply/eq_incoeff.
rewrite !incoeffK qE /=.
have hq : 0 < Fq.q < Fq.SignedReductions.R %/ 2.
+ by rewrite /Fq.q /Fq.SignedReductions.R /=.
have hs := Fq.SignedReductions.SREDCp_corr (aa * bb) hq Hbound.
move: hs => [_ hsmod].
rewrite /Fq.q in hsmod.
rewrite hsmod.
smt(modzMml modzMmr).
qed.

lemma fqmul_word_to_coeff_mul_bound_h aa bb :
  hoare [Hpoly_loop.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb <
      Fq.SignedReductions.R %/ 2 * Fq.q ==>
    NTT_Fq.word_to_coeff res = incoeff aa * incoeff bb * inv NTT_Fq.R /\
    Fq.bw32 res 16].
proof.
conseq
  (fqmul_word_to_coeff_mul_h aa bb)
  (_: W32.to_sint a = aa /\ W32.to_sint b = bb /\
      - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb <
      Fq.SignedReductions.R %/ 2 * Fq.q ==> Fq.bw32 res 16).
+ by smt().
conseq (loop_fqmul_corr_h aa bb).
+ by smt().
move=> &hr [Ha [Hb Hbound]] result Hres /=.
rewrite /Fq.bw32.
have hq : 0 < Fq.q < Fq.SignedReductions.R %/ 2.
+ by rewrite /Fq.q /Fq.SignedReductions.R /=.
have hs := Fq.SignedReductions.SREDCp_corr (aa * bb) hq Hbound.
rewrite Hres.
have hq16 : Fq.q < 2^16 by rewrite /Fq.q /=.
have hs' : -Fq.q <= Fq.SignedReductions.SREDC (aa * bb) < Fq.q by have := hs; smt().
by smt().
qed.

lemma fqmul_word_to_coeff_mul_bound_ph aa bb :
  phoare [Hpoly_loop.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb <
      Fq.SignedReductions.R %/ 2 * Fq.q ==>
    NTT_Fq.word_to_coeff res = incoeff aa * incoeff bb * inv NTT_Fq.R /\
    Fq.bw32 res 16] = 1%r.
proof.
by conseq loop_fqmul_ll (fqmul_word_to_coeff_mul_bound_h aa bb).
qed.

op barray256_bound_by (rp : BArray1024.t) (bd : int -> int) : bool =
  forall i, i \in range 0 256 => Fq.bw32 (BArray1024.get32 rp i) (bd i).

op poly_repr_bound_by
  (rp : BArray1024.t) (p : coeff Array256.t) (bd : int -> int) : bool =
  NTT_Fq.poly_repr rp p /\ barray256_bound_by rp bd.

lemma barray256_bound_by_get rp bd i :
  barray256_bound_by rp bd =>
  i \in range 0 256 =>
  Fq.bw32 (BArray1024.get32 rp i) (bd i).
proof. by move=> h hi; exact (h i hi). qed.

lemma barray256_bound_by_weaken rp bd1 bd2 :
  (forall i, i \in range 0 256 => 0 <= bd1 i <= bd2 i) =>
  barray256_bound_by rp bd1 =>
  barray256_bound_by rp bd2.
proof.
move=> hle hbd i hi.
exact (NTT_Fq.bw32_weaken (BArray1024.get32 rp i) (bd1 i) (bd2 i)
         (hle i hi) (hbd i hi)).
qed.

lemma barray256_bound_by_set32 rp bd i w :
  barray256_bound_by rp bd =>
  0 <= i < 256 =>
  Fq.bw32 w (bd i) =>
  barray256_bound_by (BArray1024.set32 rp i w) bd.
proof.
move=> hbd hi hbw j hj.
have hget :
  BArray1024.get32 (BArray1024.set32 rp i w) j =
  if i = j then w else BArray1024.get32 rp j.
+ change (BArray1024.get32d (BArray1024.set32d rp (4 * i) w) (4 * j) =
          if i = j then w else BArray1024.get32d rp (4 * j)).
  by rewrite BArray1024.get_set32E 1:/# 1:/#.
rewrite hget.
case: (i = j) => hij.
+ by smt().
exact (hbd j hj).
qed.

lemma barray256_bound_by_set32_change rp bd bd' i w :
  barray256_bound_by rp bd =>
  0 <= i < 256 =>
  Fq.bw32 w (bd' i) =>
  (forall k, k \in range 0 256 => k <> i => 0 <= bd k <= bd' k) =>
  barray256_bound_by (BArray1024.set32 rp i w) bd'.
proof.
move=> hbd hi hbw hle j hj.
have hget :
  BArray1024.get32 (BArray1024.set32 rp i w) j =
  if i = j then w else BArray1024.get32 rp j.
+ change (BArray1024.get32d (BArray1024.set32d rp (4 * i) w) (4 * j) =
          if i = j then w else BArray1024.get32d rp (4 * j)).
  by rewrite BArray1024.get_set32E 1:/# 1:/#.
rewrite hget.
case: (i = j) => hij.
+ by smt().
have hneq : j <> i by smt().
exact (NTT_Fq.bw32_weaken (BArray1024.get32 rp j) (bd j) (bd' j)
         (hle j hj hneq) (hbd j hj)).
qed.

lemma poly_repr_bound_by_repr rp p bd :
  poly_repr_bound_by rp p bd =>
  NTT_Fq.poly_repr rp p.
proof. by move=> [h _]. qed.

lemma poly_repr_bound_by_bound rp p bd :
  poly_repr_bound_by rp p bd =>
  barray256_bound_by rp bd.
proof. by move=> [_ h]. qed.

lemma fqmul_product_bound_16_24 a b :
  Fq.bw32 a 16 =>
  Fq.bw32 b 24 =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint a * W32.to_sint b <
    Fq.SignedReductions.R %/ 2 * Fq.q.
proof.
rewrite /Fq.bw32 /Fq.SignedReductions.R /Fq.q /=.
smt().
qed.

lemma fqmul_product_bound_16_26 a b :
  Fq.bw32 a 16 =>
  Fq.bw32 b 26 =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint a * W32.to_sint b <
    Fq.SignedReductions.R %/ 2 * Fq.q.
proof.
rewrite /Fq.bw32 /Fq.SignedReductions.R /Fq.q /=.
smt().
qed.

lemma jzetas_bound16 i :
  1 <= i < 256 =>
  Fq.bw32 (BArray1024.get32 Hpoly_loop.jzetas i) 16.
proof.
move=> hi.
rewrite /Hpoly_loop.jzetas BArray1024.get32_of_list32 1:/#.
have hi_mem : i \in range 1 256 by rewrite mem_range.
move: hi_mem.
do 255!(rewrite range_ltn //=; move => [->> /=|];
          [by rewrite /Fq.bw32 W32.of_sintK /W32.smod /=; smt()|]).
by rewrite range_geq.
qed.

lemma jzetas_inv_bound16 i :
  0 <= i < 256 =>
  Fq.bw32 (BArray1024.get32 Hpoly_loop.jzetas_inv i) 16.
proof.
move=> hi.
rewrite /Hpoly_loop.jzetas_inv BArray1024.get32_of_list32 1:/#.
have hi_mem : i \in range 0 256 by rewrite mem_range.
move: hi_mem.
do 256!(rewrite range_ltn //=; move => [->> /=|];
          [by rewrite /Fq.bw32 W32.of_sintK /W32.smod /=; smt()|]).
by rewrite range_geq.
qed.

op const_bound (sz : int) : int -> int = fun _ => sz.

lemma barray256_bound_by_const rp sz :
  NTT_Fq.barray256_bound rp sz =>
  barray256_bound_by rp (const_bound sz).
proof. by move=> hbd i hi; rewrite /const_bound; exact (hbd i hi). qed.

lemma barray256_bound_by_const_bound rp sz :
  barray256_bound_by rp (const_bound sz) =>
  NTT_Fq.barray256_bound rp sz.
proof. by move=> hbd i hi; have := hbd i hi; rewrite /const_bound. qed.

op fwd_len_ok (len : int) : bool =
  len = 128 \/ len = 64 \/ len = 32 \/ len = 16 \/
  len = 8 \/ len = 4 \/ len = 2 \/ len = 1 \/ len = 0.

op fwd_stage_bound (len : int) : int =
  if len = 128 then 16 else
  if len = 64 then 17 else
  if len = 32 then 18 else
  if len = 16 then 19 else
  if len = 8 then 20 else
  if len = 4 then 21 else
  if len = 2 then 22 else
  if len = 1 then 23 else 24.

op fwd_zbase (len : int) : int =
  if len = 128 then 0 else
  if len = 64 then 1 else
  if len = 32 then 3 else
  if len = 16 then 7 else
  if len = 8 then 15 else
  if len = 4 then 31 else
  if len = 2 then 63 else
  if len = 1 then 127 else 255.

op fwd_middle_bound (sz start i : int) : int =
  if 0 <= i < start then sz + 1 else sz.

op fwd_inner_bound (sz len start j i : int) : int =
  if (0 <= i < start) \/ (start <= i < j) \/
     (start + len <= i < j + len)
  then sz + 1 else sz.

lemma fwd_stage_bound_range len :
  fwd_len_ok len =>
  0 <= fwd_stage_bound len <= 24.
proof. by rewrite /fwd_len_ok /fwd_stage_bound; smt(). qed.

lemma fwd_stage_bound_pos len :
  fwd_len_ok len =>
  0 <= fwd_stage_bound len.
proof. by move=> h; have := fwd_stage_bound_range len h; smt(). qed.

lemma fwd_stage_bound_lt31 len :
  fwd_len_ok len =>
  fwd_stage_bound len < 31.
proof. by move=> h; have := fwd_stage_bound_range len h; smt(). qed.

lemma fwd_stage_bound_ge16 len :
  fwd_len_ok len =>
  16 <= fwd_stage_bound len.
proof. by rewrite /fwd_len_ok /fwd_stage_bound; smt(). qed.

lemma fwd_stage_next len :
  fwd_len_ok len =>
  0 < len =>
  fwd_stage_bound (len %/ 2) = fwd_stage_bound len + 1.
proof. by rewrite /fwd_len_ok /fwd_stage_bound; smt(). qed.

lemma fwd_len_next_ok len :
  fwd_len_ok len =>
  0 < len =>
  fwd_len_ok (len %/ 2).
proof. by rewrite /fwd_len_ok; smt(). qed.

lemma fwd_zbase_next len :
  fwd_len_ok len =>
  0 < len =>
  fwd_zbase (len %/ 2) = fwd_zbase len + 256 %/ (2 * len).
proof. by rewrite /fwd_len_ok /fwd_zbase; smt(). qed.

lemma fwd_zbase_range len :
  fwd_len_ok len =>
  0 <= fwd_zbase len <= 255.
proof. by rewrite /fwd_len_ok /fwd_zbase; smt(). qed.

lemma fwd_read_range len start zc :
  fwd_len_ok len =>
  0 < len =>
  0 <= start < 256 =>
  start = 2 * len * (zc - fwd_zbase len) =>
  1 <= zc + 1 < 256.
proof. by rewrite /fwd_len_ok /fwd_zbase; smt(). qed.

lemma fwd_block_end_bound len start zc :
  fwd_len_ok len =>
  0 < len =>
  0 <= start < 256 =>
  start = 2 * len * (zc - fwd_zbase len) =>
  start + 2 * len <= 256.
proof. by rewrite /fwd_len_ok /fwd_zbase; smt(). qed.

lemma fwd_stage_zbase_exit len zc :
  fwd_len_ok len =>
  0 < len =>
  256 = 2 * len * (zc - fwd_zbase len) =>
  zc = fwd_zbase (len %/ 2).
proof. by rewrite /fwd_len_ok /fwd_zbase; smt(). qed.

lemma fwd_middle_to_inner sz len start i :
  fwd_middle_bound sz start i = fwd_inner_bound sz len start start i.
proof. by rewrite /fwd_middle_bound /fwd_inner_bound; smt(). qed.

lemma fwd_inner_current sz len start j :
  0 <= sz =>
  0 < len =>
  start <= j < start + len =>
  fwd_inner_bound sz len start j j = sz /\
  fwd_inner_bound sz len start j (j + len) = sz /\
  fwd_inner_bound sz len start (j + 1) j = sz + 1 /\
  fwd_inner_bound sz len start (j + 1) (j + len) = sz + 1.
proof. by rewrite /fwd_inner_bound; smt(). qed.

lemma fwd_inner_weaken_unchanged sz len start j k :
  0 <= sz =>
  0 < len =>
  start <= j < start + len =>
  k \in range 0 256 =>
  k <> j =>
  k <> j + len =>
  0 <= fwd_inner_bound sz len start j k <=
       fwd_inner_bound sz len start (j + 1) k.
proof. by rewrite /fwd_inner_bound mem_range; smt(). qed.

lemma fwd_inner_exit_to_middle sz len start i :
  0 <= start =>
  0 < len =>
  fwd_inner_bound sz len start (start + len) i =
  fwd_middle_bound sz (start + 2 * len) i.
proof.
move=> hstart hlen.
rewrite /fwd_inner_bound /fwd_middle_bound.
have -> : start + len + len = start + 2 * len by ring.
case: (0 <= i < start + 2 * len) => hmid.
+ case: (i < start) => hi_start.
  + have hdone :
      0 <= i < start \/
      start <= i < start + len \/
      start + len <= i < start + 2 * len by smt().
    by smt().
  case: (i < start + len) => hi_len.
  + have hdone :
      0 <= i < start \/
      start <= i < start + len \/
      start + len <= i < start + 2 * len by smt().
    by smt().
  have hdone :
    0 <= i < start \/
    start <= i < start + len \/
    start + len <= i < start + 2 * len by smt().
  by smt().
case: (0 <= i < start \/
       start <= i < start + len \/
       start + len <= i < start + 2 * len) => hdone.
+ by smt().
by [].
qed.

lemma fwd_middle_exit_const sz start i :
  0 <= i < 256 =>
  256 <= start =>
  fwd_middle_bound sz start i = sz + 1.
proof. by rewrite /fwd_middle_bound; smt(). qed.

lemma fwd_middle_start_const sz i :
  fwd_middle_bound sz 0 i = sz.
proof. by rewrite /fwd_middle_bound; smt(). qed.

lemma forward_twiddle_product
  rp p zc j len ai bi :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j + len < 256 =>
  W32.to_sint ai = W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas zc) =>
  W32.to_sint bi = W32.to_sint (BArray1024.get32 rp (j + len)) =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
    Fq.SignedReductions.R %/ 2 * Fq.q =>
  hoare [Hpoly_loop.M.__fqmul :
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = NTT_Fq.zetas.[zc] * p.[j + len]].
proof.
move=> hrepr hzc hjlen hai hbi hbound.
have hp : p.[j + len] = NTT_Fq.word_to_coeff bi.
+ have hp0 :
    p.[j + len] =
      NTT_Fq.word_to_coeff (BArray1024.get32 rp (j + len)).
  + by apply NTT_Fq.poly_repr_get; [exact hrepr | rewrite mem_range].
  rewrite /NTT_Fq.word_to_coeff in hp0.
  rewrite -hbi in hp0.
  exact hp0.
conseq (fqmul_word_to_coeff_mul (W32.to_sint ai) (W32.to_sint bi) hbound).
+ move=> &hr [Ha Hb] /=.
  by rewrite Ha Hb.
move=> &hr [Ha Hb] result Hres /=.
rewrite Hres hp /NTT_Fq.word_to_coeff hai.
have hz := jzetas_get_cancel zc hzc.
rewrite -hz /NTT_Fq.word_to_coeff.
by ring.
qed.

lemma forward_twiddle_product_bound_h
  rp p zc j len ai bi :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j + len < 256 =>
  W32.to_sint ai = W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas zc) =>
  W32.to_sint bi = W32.to_sint (BArray1024.get32 rp (j + len)) =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
    Fq.SignedReductions.R %/ 2 * Fq.q =>
  hoare [Hpoly_loop.M.__fqmul :
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = NTT_Fq.zetas.[zc] * p.[j + len] /\
    Fq.bw32 res 16].
proof.
move=> hrepr hzc hjlen hai hbi hbound.
conseq
  (forward_twiddle_product rp p zc j len ai bi hrepr hzc hjlen hai hbi hbound)
  (fqmul_bw32_16 (W32.to_sint ai) (W32.to_sint bi) hbound).
+ by smt().
qed.

lemma forward_twiddle_product_bound_ph
  rp p zc j len ai bi :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j + len < 256 =>
  W32.to_sint ai = W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas zc) =>
  W32.to_sint bi = W32.to_sint (BArray1024.get32 rp (j + len)) =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
    Fq.SignedReductions.R %/ 2 * Fq.q =>
  phoare [Hpoly_loop.M.__fqmul :
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = NTT_Fq.zetas.[zc] * p.[j + len] /\
    Fq.bw32 res 16] = 1%r.
proof.
move=> hrepr hzc hjlen hai hbi hbound.
by conseq loop_fqmul_ll
     (forward_twiddle_product_bound_h rp p zc j len ai bi
        hrepr hzc hjlen hai hbi hbound).
qed.

lemma forward_twiddle_product_bound_call_h
  rp p zc j len ai bi :
  hoare [Hpoly_loop.M.__fqmul :
    NTT_Fq.poly_repr rp p /\
    1 <= zc < 256 /\
    0 <= j + len < 256 /\
    W32.to_sint ai = W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas zc) /\
    W32.to_sint bi = W32.to_sint (BArray1024.get32 rp (j + len)) /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
      Fq.SignedReductions.R %/ 2 * Fq.q /\
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = NTT_Fq.zetas.[zc] * p.[j + len] /\
    Fq.bw32 res 16].
proof.
conseq (fqmul_word_to_coeff_mul_bound_h
          (W32.to_sint ai) (W32.to_sint bi)).
+ by move=> &hr [_ [_ [_ [_ [_ [hbound [ha hb]]]]]]]; rewrite ha hb.
move=> &hr [hrepr [hzc [hjlen [hai [hbi [hbound [ha hb]]]]]]] result [hres hbw] /=.
split; last exact hbw.
have hp : p.[j + len] = NTT_Fq.word_to_coeff bi.
+ have hp0 :
    p.[j + len] =
      NTT_Fq.word_to_coeff (BArray1024.get32 rp (j + len)).
  + by apply NTT_Fq.poly_repr_get; [exact hrepr | rewrite mem_range].
  rewrite /NTT_Fq.word_to_coeff in hp0.
  rewrite -hbi in hp0.
  exact hp0.
rewrite hres hp /NTT_Fq.word_to_coeff hai.
have hz := jzetas_get_cancel zc hzc.
rewrite -hz /NTT_Fq.word_to_coeff.
by ring.
qed.

lemma forward_twiddle_product_bound_call_ph
  rp p zc j len ai bi :
  phoare [Hpoly_loop.M.__fqmul :
    NTT_Fq.poly_repr rp p /\
    1 <= zc < 256 /\
    0 <= j + len < 256 /\
    W32.to_sint ai = W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas zc) /\
    W32.to_sint bi = W32.to_sint (BArray1024.get32 rp (j + len)) /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
      Fq.SignedReductions.R %/ 2 * Fq.q /\
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = NTT_Fq.zetas.[zc] * p.[j + len] /\
    Fq.bw32 res 16] = 1%r.
proof.
by conseq loop_fqmul_ll
     (forward_twiddle_product_bound_call_h rp p zc j len ai bi).
qed.

lemma forward_twiddle_value
  rp p zc j len ai bi t :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_loop.jzetas zc =>
  bi = BArray1024.get32 rp (j + len) =>
  NTT_Fq.word_to_coeff t =
    NTT_Fq.word_to_coeff ai * NTT_Fq.word_to_coeff bi * inv NTT_Fq.R =>
  NTT_Fq.word_to_coeff t = NTT_Fq.zetas.[zc] * p.[j + len].
proof.
move=> hrepr hzc hjlen hai hbi ht.
have hp : p.[j + len] = NTT_Fq.word_to_coeff bi.
+ have hp0 :
    p.[j + len] =
      NTT_Fq.word_to_coeff (BArray1024.get32 rp (j + len)).
  + by apply NTT_Fq.poly_repr_get; [exact hrepr | rewrite mem_range].
  by rewrite hp0 -hbi.
rewrite ht hp hai.
have hz := jzetas_get_cancel zc hzc.
rewrite -hz.
by ring.
qed.

lemma forward_butterfly_store
  rp p j len s t asz tsz :
  NTT_Fq.poly_repr rp p =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  s = BArray1024.get32 rp j =>
  0 <= asz < 31 =>
  0 <= tsz < 31 =>
  Fq.bw32 s asz =>
  Fq.bw32 t tsz =>
  NTT_Fq.poly_repr
    (BArray1024.set32 (BArray1024.set32 rp (j + len) (s - t)) j (s + t))
    ((p.[j + len <- p.[j] - NTT_Fq.word_to_coeff t]).[j <- p.[j] + NTT_Fq.word_to_coeff t]).
proof.
move=> hrepr hj hlen hjlen hs hasz htsz hbws hbwt.
have hpj : p.[j] = NTT_Fq.word_to_coeff s.
+ have hpj0 :
    p.[j] = NTT_Fq.word_to_coeff (BArray1024.get32 rp j).
  + by apply NTT_Fq.poly_repr_get; [exact hrepr | rewrite mem_range].
  by rewrite hpj0 -hs.
have hsub :
  NTT_Fq.word_to_coeff (s - t) = p.[j] - NTT_Fq.word_to_coeff t.
+ rewrite (word_to_coeff_sub s t asz tsz) //.
   by rewrite hpj.
have hsum :
  NTT_Fq.word_to_coeff (s + t) = p.[j] + NTT_Fq.word_to_coeff t.
+ rewrite (word_to_coeff_add s t asz tsz) //.
   by rewrite hpj.
have hrepr1 :
  NTT_Fq.poly_repr
    (BArray1024.set32 rp (j + len) (s - t))
    (p.[j + len <- p.[j] - NTT_Fq.word_to_coeff t]).
+ have htmp := NTT_Fq.poly_repr_set32 rp p (j + len) (s - t) hrepr hjlen.
   by rewrite hsub in htmp.
have hrepr2 :
  NTT_Fq.poly_repr
    (BArray1024.set32 (BArray1024.set32 rp (j + len) (s - t)) j (s + t))
    ((p.[j + len <- p.[j] - NTT_Fq.word_to_coeff t]).[j <- p.[j] + NTT_Fq.word_to_coeff t]).
+ have htmp :=
     NTT_Fq.poly_repr_set32
       (BArray1024.set32 rp (j + len) (s - t))
       (p.[j + len <- p.[j] - NTT_Fq.word_to_coeff t])
       j (s + t) hrepr1 hj.
   by rewrite hsum in htmp.
exact hrepr2.
qed.

lemma forward_butterfly_store_bound
  rp p j len s t sz :
  NTT_Fq.poly_repr_bound rp p sz =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  s = BArray1024.get32 rp j =>
  0 <= sz < 31 =>
  Fq.bw32 t 16 =>
  NTT_Fq.poly_repr_bound
    (BArray1024.set32 (BArray1024.set32 rp (j + len) (s - t)) j (s + t))
    ((p.[j + len <- p.[j] - NTT_Fq.word_to_coeff t]).[j <- p.[j] + NTT_Fq.word_to_coeff t])
    (max sz 16 + 1).
proof.
move=> hreprb hj hlen hjlen hs hsz hbwt.
have hrepr := NTT_Fq.poly_repr_bound_repr rp p sz hreprb.
have hbound := NTT_Fq.poly_repr_bound_bound rp p sz hreprb.
have hbws : Fq.bw32 s sz.
+ rewrite hs.
  apply hbound.
  by rewrite mem_range.
have h16 : 0 <= 16 < 31 by trivial.
have hrepr' :=
  forward_butterfly_store rp p j len s t sz 16
    hrepr hj hlen hjlen hs hsz h16 hbws hbwt.
split; first exact hrepr'.
have [hbwsum hbwsub] := forward_butterfly_bounds s t sz 16 hsz h16 hbws hbwt.
have hszw : 0 <= sz <= max sz 16 + 1 by smt().
have hbound_big :
  NTT_Fq.barray256_bound rp (max sz 16 + 1).
+ exact (NTT_Fq.barray256_bound_weaken rp sz (max sz 16 + 1) hszw hbound).
have hbound1 :
  NTT_Fq.barray256_bound
    (BArray1024.set32 rp (j + len) (s - t)) (max sz 16 + 1).
+ exact (NTT_Fq.barray256_bound_set32 rp (j + len) (s - t)
            (max sz 16 + 1) hbound_big hjlen hbwsub).
exact (NTT_Fq.barray256_bound_set32
  (BArray1024.set32 rp (j + len) (s - t)) j (s + t)
  (max sz 16 + 1) hbound1 hj hbwsum).
qed.

lemma forward_butterfly_store_bound_by
  rp p j len s t bd bd' asz :
  NTT_Fq.poly_repr rp p =>
  barray256_bound_by rp bd =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  s = BArray1024.get32 rp j =>
  bd j = asz =>
  bd (j + len) = asz =>
  16 <= asz =>
  0 <= asz < 31 =>
  Fq.bw32 t 16 =>
  bd' j = asz + 1 =>
  bd' (j + len) = asz + 1 =>
  (forall k, k \in range 0 256 => k <> j => k <> j + len =>
     0 <= bd k <= bd' k) =>
  poly_repr_bound_by
    (BArray1024.set32 (BArray1024.set32 rp (j + len) (s - t)) j (s + t))
    ((p.[j + len <- p.[j] - NTT_Fq.word_to_coeff t]).[j <- p.[j] + NTT_Fq.word_to_coeff t])
    bd'.
proof.
move=> hrepr hbd hj hlen hjlen hs hbdj hbdjl hasz16 hasz hbwt hbd'j hbd'jl hle.
have hbws : Fq.bw32 s asz.
+ rewrite hs -hbdj.
  have hjmem : j \in range 0 256 by rewrite mem_range; smt().
  exact (hbd j hjmem).
have h16 : 0 <= 16 < 31 by trivial.
have hrepr' :=
  forward_butterfly_store rp p j len s t asz 16
    hrepr hj hlen hjlen hs hasz h16 hbws hbwt.
split; first exact hrepr'.
have [hbwsum hbwsub] := forward_butterfly_bounds s t asz 16 hasz h16 hbws hbwt.
have hmax : max asz 16 + 1 = asz + 1 by smt().
have hsum' : Fq.bw32 (s + t) (bd' j) by rewrite hbd'j -hmax.
have hsub' : Fq.bw32 (s - t) (bd' (j + len)) by rewrite hbd'jl -hmax.
have hbound1 :
  barray256_bound_by (BArray1024.set32 rp (j + len) (s - t)) bd'.
+ apply (barray256_bound_by_set32_change rp bd bd' (j + len) (s - t)); try exact hbd; try exact hsub'.
  + by smt().
  move=> k hk hkneq.
  case: (k = j) => hkj.
  + rewrite hkj hbdj hbd'j.
    by smt().
  exact (hle k hk hkj hkneq).
apply (barray256_bound_by_set32 (BArray1024.set32 rp (j + len) (s - t)) bd' j (s + t)); try exact hbound1; try exact hsum'.
by smt().
qed.

lemma forward_spec_updateE (p : coeff Array256.t) j len t :
  0 < len =>
  (p.[j + len <- p.[j] - t]).[j <-
    (p.[j + len <- p.[j] - t]).[j] + t] =
  (p.[j + len <- p.[j] - t]).[j <- p.[j] + t].
proof.
move=> hlen.
apply/Array256.ext_eq => i hi.
rewrite !Array256.get_set_if /=.
by smt().
qed.

lemma forward_butterfly_step_bound_by
  rp p j len start s t sz :
  NTT_Fq.poly_repr rp p =>
  barray256_bound_by rp (fwd_inner_bound sz len start j) =>
  0 <= start =>
  0 < len =>
  start <= j < start + len =>
  0 <= j < 256 =>
  0 <= j + len < 256 =>
  s = BArray1024.get32 rp j =>
  16 <= sz =>
  0 <= sz < 31 =>
  Fq.bw32 t 16 =>
  poly_repr_bound_by
    (BArray1024.set32 (BArray1024.set32 rp (j + len) (s - t)) j (s + t))
    ((p.[j + len <- p.[j] - NTT_Fq.word_to_coeff t]).[j <-
       (p.[j + len <- p.[j] - NTT_Fq.word_to_coeff t]).[j] +
       NTT_Fq.word_to_coeff t])
    (fwd_inner_bound sz len start (j + 1)).
proof.
move=> hrepr hbd hstart hlen hjrange hj hjlen hs hsz16 hsz hbwt.
have [hcurj [hcurjl [hnextj hnextjl]]] :=
  fwd_inner_current sz len start j _ _ _.
+ by smt().
+ exact hlen.
+ exact hjrange.
have hstore :=
  forward_butterfly_store_bound_by
    rp p j len s t
    (fwd_inner_bound sz len start j)
    (fwd_inner_bound sz len start (j + 1))
    sz hrepr hbd hj hlen hjlen hs hcurj hcurjl
    hsz16 hsz hbwt hnextj hnextjl _.
+ move=> k hk hkj hkjl.
  have hsz0 : 0 <= sz by smt().
  exact (fwd_inner_weaken_unchanged sz len start j k
           hsz0 hlen hjrange hk hkj hkjl).
move: hstore => [hpoly hbound].
split; last exact hbound.
have hupd :=
  forward_spec_updateE p j len (NTT_Fq.word_to_coeff t) hlen.
by rewrite hupd.
qed.

lemma forward_twiddle_product_bound_from_inner
  rp len start j zc :
  barray256_bound_by rp
    (fwd_inner_bound (fwd_stage_bound len) len start j) =>
  fwd_len_ok len =>
  0 < len =>
  start <= j < start + len =>
  0 <= j + len < 256 =>
  1 <= zc < 256 =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas zc) *
    W32.to_sint (BArray1024.get32 rp (j + len)) <
    Fq.SignedReductions.R %/ 2 * Fq.q.
proof.
move=> hbd hlenok hlen hjrange hjlen hzc.
have hzbw := jzetas_bound16 zc hzc.
have [_ [hcurjl _]] :=
  fwd_inner_current (fwd_stage_bound len) len start j _ hlen hjrange.
+ exact (fwd_stage_bound_pos len hlenok).
have hraw :
  Fq.bw32 (BArray1024.get32 rp (j + len)) (fwd_stage_bound len).
+ have hjlmem : j + len \in range 0 256 by rewrite mem_range; smt().
  have := hbd (j + len) hjlmem.
  by rewrite hcurjl.
have hstage := fwd_stage_bound_range len hlenok.
have hbw24 :
  Fq.bw32 (BArray1024.get32 rp (j + len)) 24.
+ exact (NTT_Fq.bw32_weaken (BArray1024.get32 rp (j + len))
           (fwd_stage_bound len) 24 hstage hraw).
exact (fqmul_product_bound_16_24
  (BArray1024.get32 Hpoly_loop.jzetas zc)
  (BArray1024.get32 rp (j + len)) hzbw hbw24).
qed.

lemma forward_butterfly_repr
  rp p zc j len ai s b t asz bsz tsz :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_loop.jzetas zc =>
  s = BArray1024.get32 rp j =>
  b = BArray1024.get32 rp (j + len) =>
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  0 <= tsz < 31 =>
  Fq.bw32 s asz =>
  Fq.bw32 b bsz =>
  Fq.bw32 t tsz =>
  NTT_Fq.word_to_coeff t = NTT_Fq.zetas.[zc] * p.[j + len] =>
  NTT_Fq.poly_repr
	    (BArray1024.set32 (BArray1024.set32 rp (j + len) (s - t)) j (s + t))
	    ((p.[j + len <- p.[j] - (NTT_Fq.zetas.[zc] * p.[j + len])]).[j <- p.[j] + (NTT_Fq.zetas.[zc] * p.[j + len])]).
proof.
move=> hrepr hzc hj hlen hjlen hai hs hb hasz hbsz htsz hbws hbwb hbwt ht.
have hstore :=
  forward_butterfly_store rp p j len s t asz tsz
    hrepr hj hlen hjlen hs hasz htsz hbws hbwt.
rewrite ht in hstore.
exact hstore.
qed.

lemma forward_butterfly_step
  rp p zc j len ai s b t asz bsz tsz :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_loop.jzetas zc =>
  s = BArray1024.get32 rp j =>
  b = BArray1024.get32 rp (j + len) =>
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  0 <= tsz < 31 =>
  Fq.bw32 s asz =>
  Fq.bw32 b bsz =>
  Fq.bw32 t tsz =>
  NTT_Fq.word_to_coeff t =
    NTT_Fq.word_to_coeff ai * NTT_Fq.word_to_coeff b * inv NTT_Fq.R =>
  NTT_Fq.poly_repr
    (BArray1024.set32 (BArray1024.set32 rp (j + len) (s - t)) j (s + t))
    ((p.[j + len <- p.[j] - (NTT_Fq.zetas.[zc] * p.[j + len])]).[j <- p.[j] + (NTT_Fq.zetas.[zc] * p.[j + len])]).
proof.
move=> hrepr hzc hj hlen hjlen hai hs hb hasz hbsz htsz hbws hbwb hbwt ht.
have ht' : NTT_Fq.word_to_coeff t = NTT_Fq.zetas.[zc] * p.[j + len].
	+ apply (forward_twiddle_value rp p zc j len ai b t); try exact hrepr; try exact hzc; try exact hjlen; try exact hai; try exact hb; exact ht.
exact (forward_butterfly_repr rp p zc j len ai s b t asz bsz tsz
         hrepr hzc hj hlen hjlen hai hs hb hasz hbsz htsz hbws hbwb hbwt ht').
qed.

op inv_len_ok (len : int) : bool =
  len = 1 \/ len = 2 \/ len = 4 \/ len = 8 \/
  len = 16 \/ len = 32 \/ len = 64 \/ len = 128 \/
  len = 256.

op inv_stage_bound (len : int) : int =
  if len = 1 then 18 else
  if len = 2 then 19 else
  if len = 4 then 20 else
  if len = 8 then 21 else
  if len = 16 then 22 else
  if len = 32 then 23 else
  if len = 64 then 24 else
  if len = 128 then 25 else 26.

op inv_zbase (len : int) : int =
  if len = 1 then 0 else
  if len = 2 then 128 else
  if len = 4 then 192 else
  if len = 8 then 224 else
  if len = 16 then 240 else
  if len = 32 then 248 else
  if len = 64 then 252 else
  if len = 128 then 254 else 255.

op inv_middle_bound (sz start i : int) : int =
  if 0 <= i < start then sz + 1 else sz.

op inv_inner_bound (sz len start j i : int) : int =
  if (0 <= i < start) \/ (start <= i < j) \/
     (start + len <= i < j + len)
  then sz + 1 else sz.

lemma inv_stage_bound_range len :
  inv_len_ok len =>
  0 <= inv_stage_bound len <= 26.
proof. by rewrite /inv_len_ok /inv_stage_bound; smt(). qed.

lemma inv_stage_bound_pos len :
  inv_len_ok len =>
  0 <= inv_stage_bound len.
proof. by move=> h; have := inv_stage_bound_range len h; smt(). qed.

lemma inv_stage_bound_lt31 len :
  inv_len_ok len =>
  inv_stage_bound len < 31.
proof. by move=> h; have := inv_stage_bound_range len h; smt(). qed.

lemma inv_stage_bound_ge16 len :
  inv_len_ok len =>
  16 <= inv_stage_bound len.
proof. by rewrite /inv_len_ok /inv_stage_bound; smt(). qed.

lemma inv_stage_bound_ge18 len :
  inv_len_ok len =>
  18 <= inv_stage_bound len.
proof. by rewrite /inv_len_ok /inv_stage_bound; smt(). qed.

lemma inv_stage_next len :
  inv_len_ok len =>
  len < 256 =>
  inv_stage_bound (len * 2) = inv_stage_bound len + 1.
proof. by rewrite /inv_len_ok /inv_stage_bound; smt(). qed.

lemma inv_len_next_ok len :
  inv_len_ok len =>
  len < 256 =>
  inv_len_ok (len * 2).
proof. by rewrite /inv_len_ok; smt(). qed.

lemma inv_zbase_range len :
  inv_len_ok len =>
  0 <= inv_zbase len <= 255.
proof. by rewrite /inv_len_ok /inv_zbase; smt(). qed.

lemma inv_read_range len start zc :
  inv_len_ok len =>
  len < 256 =>
  0 <= start < 256 =>
  start = 2 * len * (zc - inv_zbase len) =>
  zc \in range 0 255.
proof. by rewrite /inv_len_ok /inv_zbase mem_range; smt(). qed.

lemma inv_block_end_bound len start zc :
  inv_len_ok len =>
  len < 256 =>
  0 <= start < 256 =>
  start = 2 * len * (zc - inv_zbase len) =>
  start + 2 * len <= 256.
proof. by rewrite /inv_len_ok /inv_zbase; smt(). qed.

lemma inv_stage_zbase_exit len zc :
  inv_len_ok len =>
  len < 256 =>
  256 = 2 * len * (zc - inv_zbase len) =>
  zc = inv_zbase (len * 2).
proof. by rewrite /inv_len_ok /inv_zbase; smt(). qed.

lemma inv_middle_to_inner sz len start i :
  inv_middle_bound sz start i = inv_inner_bound sz len start start i.
proof. by rewrite /inv_middle_bound /inv_inner_bound; smt(). qed.

lemma inv_inner_current sz len start j :
  0 <= sz =>
  0 < len =>
  start <= j < start + len =>
  inv_inner_bound sz len start j j = sz /\
  inv_inner_bound sz len start j (j + len) = sz /\
  inv_inner_bound sz len start (j + 1) j = sz + 1 /\
  inv_inner_bound sz len start (j + 1) (j + len) = sz + 1.
proof. by rewrite /inv_inner_bound; smt(). qed.

lemma inv_inner_weaken_unchanged sz len start j k :
  0 <= sz =>
  0 < len =>
  start <= j < start + len =>
  k \in range 0 256 =>
  k <> j =>
  k <> j + len =>
  0 <= inv_inner_bound sz len start j k <=
       inv_inner_bound sz len start (j + 1) k.
proof. by rewrite /inv_inner_bound mem_range; smt(). qed.

lemma inv_inner_exit_to_middle sz len start i :
  0 <= start =>
  0 < len =>
  inv_inner_bound sz len start (start + len) i =
  inv_middle_bound sz (start + 2 * len) i.
proof.
move=> hstart hlen.
rewrite /inv_inner_bound /inv_middle_bound.
have -> : start + len + len = start + 2 * len by ring.
case: (0 <= i < start + 2 * len) => hmid.
+ case: (i < start) => hi_start.
  + have hdone :
      0 <= i < start \/
      start <= i < start + len \/
      start + len <= i < start + 2 * len by smt().
    by smt().
  case: (i < start + len) => hi_len.
  + have hdone :
      0 <= i < start \/
      start <= i < start + len \/
      start + len <= i < start + 2 * len by smt().
    by smt().
  have hdone :
    0 <= i < start \/
    start <= i < start + len \/
    start + len <= i < start + 2 * len by smt().
  by smt().
case: (0 <= i < start \/
       start <= i < start + len \/
       start + len <= i < start + 2 * len) => hdone.
+ by smt().
by [].
qed.

lemma inv_middle_exit_const sz start i :
  0 <= i < 256 =>
  256 <= start =>
  inv_middle_bound sz start i = sz + 1.
proof. by rewrite /inv_middle_bound; smt(). qed.

lemma inv_middle_start_const sz i :
  inv_middle_bound sz 0 i = sz.
proof. by rewrite /inv_middle_bound; smt(). qed.

lemma inverse_spec_updateE (p : coeff Array256.t) z j len :
  0 < len =>
  (p.[j <- p.[j] + p.[j + len]]).[j + len <-
    z *
    ((p.[j <- p.[j] + p.[j + len]]).[j + len <-
      p.[j] - (p.[j <- p.[j] + p.[j + len]]).[j + len]]).[j + len]] =
  (p.[j <- p.[j] + p.[j + len]]).[j + len <-
    z * (p.[j] - p.[j + len])].
proof.
move=> hlen.
apply/Array256.ext_eq => i hi.
rewrite !Array256.get_set_if /=.
by smt().
qed.

lemma inverse_twiddle_product_bound_call_h
  zc ai bi diff :
  hoare [Hpoly_loop.M.__fqmul :
    zc \in range 0 255 /\
    ai = BArray1024.get32 Hpoly_loop.jzetas_inv zc /\
    NTT_Fq.word_to_coeff bi = diff /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
      Fq.SignedReductions.R %/ 2 * Fq.q /\
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = NTT_Fq.zetas_inv.[zc] * diff /\
    Fq.bw32 res 16].
proof.
conseq (fqmul_word_to_coeff_mul_bound_h
          (W32.to_sint ai) (W32.to_sint bi)).
+ by move=> &hr [_ [_ [_ [hbound [ha hb]]]]]; rewrite ha hb.
move=> &hr [hzc [hai [hbi [hbound [ha hb]]]]] result [hres hbw] /=.
split; last exact hbw.
rewrite hres -hbi /NTT_Fq.word_to_coeff hai.
have hz := jzetas_inv_get_cancel zc hzc.
rewrite -hz /NTT_Fq.word_to_coeff.
by ring.
qed.

lemma inverse_twiddle_product_bound_call_ph
  zc ai bi diff :
  phoare [Hpoly_loop.M.__fqmul :
    zc \in range 0 255 /\
    ai = BArray1024.get32 Hpoly_loop.jzetas_inv zc /\
    NTT_Fq.word_to_coeff bi = diff /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
      Fq.SignedReductions.R %/ 2 * Fq.q /\
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = NTT_Fq.zetas_inv.[zc] * diff /\
    Fq.bw32 res 16] = 1%r.
proof.
by conseq loop_fqmul_ll
     (inverse_twiddle_product_bound_call_h zc ai bi diff).
qed.

lemma inverse_twiddle_value
  rp p zc j len ai diff t :
  NTT_Fq.poly_repr rp p =>
  zc \in range 0 255 =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_loop.jzetas_inv zc =>
  diff = (p.[j] - p.[j + len]) =>
  NTT_Fq.word_to_coeff t =
    NTT_Fq.word_to_coeff ai * diff * inv NTT_Fq.R =>
  NTT_Fq.word_to_coeff t = NTT_Fq.zetas_inv.[zc] * diff.
proof.
move=> hrepr hzc hj hlen hjlen hai hdiff ht.
rewrite ht hai hdiff.
have hz := jzetas_inv_get_cancel zc hzc.
rewrite -hz.
by ring.
qed.

lemma inverse_butterfly_store
  rp p target j len t0 coeff t asz bsz tsz :
  NTT_Fq.poly_repr rp p =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  t0 = BArray1024.get32 rp j =>
  coeff = BArray1024.get32 rp (j + len) =>
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  0 <= tsz < 31 =>
  Fq.bw32 t0 asz =>
  Fq.bw32 coeff bsz =>
  Fq.bw32 t tsz =>
  NTT_Fq.word_to_coeff t = target =>
  NTT_Fq.poly_repr
    (BArray1024.set32 (BArray1024.set32 rp j (t0 + coeff)) (j + len) t)
    ((p.[j <- p.[j] + p.[j + len]]).[j + len <- target]).
proof.
move=> hrepr hj hlen hjlen ht0 hcoeff hasz hbsz htsz hbwt0 hbwcoeff hbwt ht.
have hpj : p.[j] = NTT_Fq.word_to_coeff t0.
+ have hpj0 :
    p.[j] = NTT_Fq.word_to_coeff (BArray1024.get32 rp j).
  + by apply NTT_Fq.poly_repr_get; [exact hrepr | rewrite mem_range].
  by rewrite hpj0 -ht0.
have hpjl : p.[j + len] = NTT_Fq.word_to_coeff coeff.
+ have hpjl0 :
    p.[j + len] =
      NTT_Fq.word_to_coeff (BArray1024.get32 rp (j + len)).
  + by apply NTT_Fq.poly_repr_get; [exact hrepr | rewrite mem_range].
  by rewrite hpjl0 -hcoeff.
have hsum :
  NTT_Fq.word_to_coeff (t0 + coeff) = p.[j] + p.[j + len].
+ rewrite (word_to_coeff_add t0 coeff asz bsz) //.
   by rewrite hpj hpjl.
have hrepr1 :
  NTT_Fq.poly_repr
    (BArray1024.set32 rp j (t0 + coeff))
    (p.[j <- p.[j] + p.[j + len]]).
+ have htmp := NTT_Fq.poly_repr_set32 rp p j (t0 + coeff) hrepr hj.
   by rewrite hsum in htmp.
have hrepr2 :
  NTT_Fq.poly_repr
    (BArray1024.set32 (BArray1024.set32 rp j (t0 + coeff)) (j + len) t)
    ((p.[j <- p.[j] + p.[j + len]]).[j + len <- target]).
+ have htmp :=
     NTT_Fq.poly_repr_set32
       (BArray1024.set32 rp j (t0 + coeff))
       (p.[j <- p.[j] + p.[j + len]])
       (j + len) t hrepr1 hjlen.
   by rewrite ht in htmp.
exact hrepr2.
qed.

lemma inverse_butterfly_store_bound
  rp p target j len t0 coeff t sz :
  NTT_Fq.poly_repr_bound rp p sz =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  t0 = BArray1024.get32 rp j =>
  coeff = BArray1024.get32 rp (j + len) =>
  0 <= sz < 31 =>
  Fq.bw32 t 16 =>
  NTT_Fq.word_to_coeff t = target =>
  NTT_Fq.poly_repr_bound
    (BArray1024.set32 (BArray1024.set32 rp j (t0 + coeff)) (j + len) t)
    ((p.[j <- p.[j] + p.[j + len]]).[j + len <- target])
    (max sz 16 + 1).
proof.
move=> hreprb hj hlen hjlen ht0 hcoeff hsz hbwt ht.
have hrepr := NTT_Fq.poly_repr_bound_repr rp p sz hreprb.
have hbound := NTT_Fq.poly_repr_bound_bound rp p sz hreprb.
have hbwt0 : Fq.bw32 t0 sz.
+ rewrite ht0.
  apply hbound.
  by rewrite mem_range.
have hbwcoeff : Fq.bw32 coeff sz.
+ rewrite hcoeff.
  apply hbound.
  by rewrite mem_range.
have h16 : 0 <= 16 < 31 by trivial.
have hrepr' :=
  inverse_butterfly_store rp p target j len t0 coeff t sz sz 16
    hrepr hj hlen hjlen ht0 hcoeff hsz hsz h16 hbwt0 hbwcoeff hbwt ht.
split; first exact hrepr'.
have hsum : Fq.bw32 (t0 + coeff) (max sz sz + 1).
+ exact (Fq.add_corr t0 coeff sz sz hsz hsz hbwt0 hbwcoeff).
have hsum_big : Fq.bw32 (t0 + coeff) (max sz 16 + 1).
+ have hle : 0 <= max sz sz + 1 <= max sz 16 + 1 by smt().
  exact (NTT_Fq.bw32_weaken (t0 + coeff) (max sz sz + 1)
           (max sz 16 + 1) hle hsum).
have ht_big : Fq.bw32 t (max sz 16 + 1).
+ have hle : 0 <= 16 <= max sz 16 + 1 by smt().
  exact (NTT_Fq.bw32_weaken t 16 (max sz 16 + 1) hle hbwt).
have hszw : 0 <= sz <= max sz 16 + 1 by smt().
have hbound_big :
  NTT_Fq.barray256_bound rp (max sz 16 + 1).
+ exact (NTT_Fq.barray256_bound_weaken rp sz (max sz 16 + 1) hszw hbound).
have hbound1 :
  NTT_Fq.barray256_bound
    (BArray1024.set32 rp j (t0 + coeff)) (max sz 16 + 1).
+ exact (NTT_Fq.barray256_bound_set32 rp j (t0 + coeff)
            (max sz 16 + 1) hbound_big hj hsum_big).
exact (NTT_Fq.barray256_bound_set32
  (BArray1024.set32 rp j (t0 + coeff)) (j + len) t
  (max sz 16 + 1) hbound1 hjlen ht_big).
qed.

lemma inverse_butterfly_store_bound_by
  rp p target j len t0 coeff t bd bd' asz :
  NTT_Fq.poly_repr rp p =>
  barray256_bound_by rp bd =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  t0 = BArray1024.get32 rp j =>
  coeff = BArray1024.get32 rp (j + len) =>
  bd j = asz =>
  bd (j + len) = asz =>
  16 <= asz =>
  0 <= asz < 31 =>
  Fq.bw32 t 16 =>
  NTT_Fq.word_to_coeff t = target =>
  bd' j = asz + 1 =>
  bd' (j + len) = asz + 1 =>
  (forall k, k \in range 0 256 => k <> j => k <> j + len =>
     0 <= bd k <= bd' k) =>
  poly_repr_bound_by
    (BArray1024.set32 (BArray1024.set32 rp j (t0 + coeff)) (j + len) t)
    ((p.[j <- p.[j] + p.[j + len]]).[j + len <- target])
    bd'.
proof.
move=> hrepr hbd hj hlen hjlen ht0 hcoeff hbdj hbdjl hasz16 hasz hbwt ht hbd'j hbd'jl hle.
have hbwt0 : Fq.bw32 t0 asz.
+ rewrite ht0 -hbdj.
  have hjmem : j \in range 0 256 by rewrite mem_range; smt().
  exact (hbd j hjmem).
have hbwcoeff : Fq.bw32 coeff asz.
+ rewrite hcoeff -hbdjl.
  have hjlmem : j + len \in range 0 256 by rewrite mem_range; smt().
  exact (hbd (j + len) hjlmem).
have h16 : 0 <= 16 < 31 by trivial.
have hrepr' :=
  inverse_butterfly_store rp p target j len t0 coeff t asz asz 16
    hrepr hj hlen hjlen ht0 hcoeff hasz hasz h16 hbwt0 hbwcoeff hbwt ht.
split; first exact hrepr'.
have [hbwsum _] := inverse_butterfly_bounds t0 coeff asz asz hasz hasz hbwt0 hbwcoeff.
have hmax : max asz asz + 1 = asz + 1 by smt().
have hsum' : Fq.bw32 (t0 + coeff) (bd' j) by rewrite hbd'j -hmax.
have ht' : Fq.bw32 t (bd' (j + len)).
+ rewrite hbd'jl.
  have hle16 : 0 <= 16 <= asz + 1 by smt().
  exact (NTT_Fq.bw32_weaken t 16 (asz + 1) hle16 hbwt).
have hbound1 :
  barray256_bound_by (BArray1024.set32 rp j (t0 + coeff)) bd'.
+ apply (barray256_bound_by_set32_change rp bd bd' j (t0 + coeff)); try exact hbd; try exact hsum'.
  + by smt().
  move=> k hk hkneq.
  case: (k = j + len) => hkjl.
  + rewrite hkjl hbdjl hbd'jl.
    by smt().
  exact (hle k hk hkneq hkjl).
apply (barray256_bound_by_set32 (BArray1024.set32 rp j (t0 + coeff)) bd' (j + len) t); try exact hbound1; try exact ht'.
by smt().
qed.

lemma inverse_butterfly_step_bound_by
  rp p zc j len start t0 coeff t sz :
  NTT_Fq.poly_repr rp p =>
  barray256_bound_by rp (inv_inner_bound sz len start j) =>
  0 <= start =>
  0 < len =>
  start <= j < start + len =>
  0 <= j < 256 =>
  0 <= j + len < 256 =>
  t0 = BArray1024.get32 rp j =>
  coeff = BArray1024.get32 rp (j + len) =>
  16 <= sz =>
  0 <= sz < 31 =>
  Fq.bw32 t 16 =>
  NTT_Fq.word_to_coeff t =
    NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len]) =>
  poly_repr_bound_by
    (BArray1024.set32 (BArray1024.set32 rp j (t0 + coeff)) (j + len) t)
    ((p.[j <- p.[j] + p.[j + len]]).[j + len <-
       NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len])])
    (inv_inner_bound sz len start (j + 1)).
proof.
move=> hrepr hbd hstart hlen hjrange hj hjlen ht0 hcoeff hsz16 hsz hbwt ht.
have [hcurj [hcurjl [hnextj hnextjl]]] :=
  inv_inner_current sz len start j _ _ _.
+ by smt().
+ exact hlen.
+ exact hjrange.
have hle :
  forall k, k \in range 0 256 => k <> j => k <> j + len =>
     0 <= inv_inner_bound sz len start j k <=
     inv_inner_bound sz len start (j + 1) k.
+ move=> k hk hkj hkjl.
  have hsz0 : 0 <= sz by smt().
  exact (inv_inner_weaken_unchanged sz len start j k
           hsz0 hlen hjrange hk hkj hkjl).
exact
  (inverse_butterfly_store_bound_by
    rp p (NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len]))
    j len t0 coeff t
    (inv_inner_bound sz len start j)
    (inv_inner_bound sz len start (j + 1))
    sz hrepr hbd hj hlen hjlen ht0 hcoeff hcurj hcurjl
    hsz16 hsz hbwt ht hnextj hnextjl hle).
qed.

lemma inverse_twiddle_product_bound_from_inner
  rp len start j :
  barray256_bound_by rp
    (inv_inner_bound (inv_stage_bound len) len start j) =>
  inv_len_ok len =>
  len < 256 =>
  start <= j < start + len =>
  0 <= j < 256 =>
  0 <= j + len < 256 =>
  Fq.bw32
    (BArray1024.get32 rp j - BArray1024.get32 rp (j + len))
    (inv_stage_bound len + 1).
proof.
move=> hbd hlenok hlenlt hjrange hj hjlen.
have hlenpos : 0 < len by move: hlenok hlenlt; rewrite /inv_len_ok; smt().
have [hcurj [hcurjl _]] :=
  inv_inner_current (inv_stage_bound len) len start j
    _ hlenpos hjrange.
+ exact (inv_stage_bound_pos len hlenok).
have hbwj : Fq.bw32 (BArray1024.get32 rp j) (inv_stage_bound len).
+ have hjmem : j \in range 0 256 by rewrite mem_range; smt().
  have := hbd j hjmem.
  by rewrite hcurj.
have hbwjl : Fq.bw32 (BArray1024.get32 rp (j + len)) (inv_stage_bound len).
+ have hjlmem : j + len \in range 0 256 by rewrite mem_range; smt().
  have := hbd (j + len) hjlmem.
  by rewrite hcurjl.
have hstage := inv_stage_bound_range len hlenok.
have hsz : 0 <= inv_stage_bound len < 31 by smt(inv_stage_bound_lt31).
exact (Fq.sub_corr
  (BArray1024.get32 rp j) (BArray1024.get32 rp (j + len))
  (inv_stage_bound len) (inv_stage_bound len)
  hsz hsz hbwj hbwjl).
qed.

lemma inverse_twiddle_product_call_bound_from_inner
  rp len start j zc :
  barray256_bound_by rp
    (inv_inner_bound (inv_stage_bound len) len start j) =>
  inv_len_ok len =>
  len < 256 =>
  start <= j < start + len =>
  0 <= j < 256 =>
  0 <= j + len < 256 =>
  zc \in range 0 255 =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas_inv zc) *
    W32.to_sint
      (BArray1024.get32 rp j - BArray1024.get32 rp (j + len)) <
    Fq.SignedReductions.R %/ 2 * Fq.q.
proof.
move=> hbd hlenok hlenlt hjrange hj hjlen hzc.
have /mem_range hzc_rng := hzc.
have hzbw := jzetas_inv_bound16 zc _.
+ by smt().
have hdiff :=
  inverse_twiddle_product_bound_from_inner
    rp len start j hbd hlenok hlenlt hjrange hj hjlen.
have hstage : 0 <= inv_stage_bound len + 1 <= 26.
+ rewrite /inv_len_ok /inv_stage_bound in hlenok.
  by smt().
have hdiff26 :
  Fq.bw32
    (BArray1024.get32 rp j - BArray1024.get32 rp (j + len)) 26.
+ exact (NTT_Fq.bw32_weaken
    (BArray1024.get32 rp j - BArray1024.get32 rp (j + len))
    (inv_stage_bound len + 1) 26 hstage hdiff).
exact (fqmul_product_bound_16_26
  (BArray1024.get32 Hpoly_loop.jzetas_inv zc)
  (BArray1024.get32 rp j - BArray1024.get32 rp (j + len))
  hzbw hdiff26).
qed.

lemma inverse_butterfly_step_full
  rp p zc j len ai t0 coeff t asz bsz tsz :
  NTT_Fq.poly_repr rp p =>
  zc \in range 0 255 =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_loop.jzetas_inv zc =>
  t0 = BArray1024.get32 rp j =>
  coeff = BArray1024.get32 rp (j + len) =>
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  0 <= tsz < 31 =>
  Fq.bw32 t0 asz =>
  Fq.bw32 coeff bsz =>
  Fq.bw32 t tsz =>
  NTT_Fq.word_to_coeff t =
    NTT_Fq.word_to_coeff ai * (p.[j] - p.[j + len]) * inv NTT_Fq.R =>
  NTT_Fq.poly_repr
    (BArray1024.set32 (BArray1024.set32 rp j (t0 + coeff)) (j + len) t)
    ((p.[j <- p.[j] + p.[j + len]]).[j + len <- NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len])]).
proof.
move=> hrepr hzc hj hlen hjlen hai ht0 hcoeff hasz hbsz htsz hbwt0 hbwcoeff hbwt ht.
have hpj : p.[j] = NTT_Fq.word_to_coeff t0.
+ have hpj0 :
    p.[j] = NTT_Fq.word_to_coeff (BArray1024.get32 rp j).
  + by apply NTT_Fq.poly_repr_get; [exact hrepr | rewrite mem_range].
  by rewrite hpj0 -ht0.
have hpjl : p.[j + len] = NTT_Fq.word_to_coeff coeff.
+ have hpjl0 :
    p.[j + len] =
      NTT_Fq.word_to_coeff (BArray1024.get32 rp (j + len)).
  + by apply NTT_Fq.poly_repr_get; [exact hrepr | rewrite mem_range].
  by rewrite hpjl0 -hcoeff.
have ht' : NTT_Fq.word_to_coeff t = NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len]).
+ apply (inverse_twiddle_value rp p zc j len ai (p.[j] - p.[j + len]) t); try exact hrepr; try exact hzc; try exact hj; try exact hlen; try exact hjlen; try exact hai; first by [].
   exact ht.
exact (inverse_butterfly_store rp p (NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len])) j len t0 coeff t asz bsz tsz
         hrepr hj hlen hjlen ht0 hcoeff hasz hbsz htsz hbwt0 hbwcoeff hbwt ht').
qed.

lemma inverse_butterfly_repr
  rp p zc j len ai t0 coeff t asz bsz tsz :
  NTT_Fq.poly_repr rp p =>
  zc \in range 0 255 =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_loop.jzetas_inv zc =>
  t0 = BArray1024.get32 rp j =>
  coeff = BArray1024.get32 rp (j + len) =>
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  0 <= tsz < 31 =>
  Fq.bw32 t0 asz =>
  Fq.bw32 coeff bsz =>
  Fq.bw32 t tsz =>
  NTT_Fq.word_to_coeff t =
    NTT_Fq.word_to_coeff ai * (p.[j] - p.[j + len]) * inv NTT_Fq.R =>
  NTT_Fq.poly_repr
    (BArray1024.set32 (BArray1024.set32 rp j (t0 + coeff)) (j + len) t)
    ((p.[j <- p.[j] + p.[j + len]]).[j + len <- NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len])]).
proof.
move=> hrepr hzc hj hlen hjlen hai ht0 hcoeff hasz hbsz htsz hbwt0 hbwcoeff hbwt ht.
have ht' : NTT_Fq.word_to_coeff t = NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len]).
+ apply (inverse_twiddle_value rp p zc j len ai (p.[j] - p.[j + len]) t); try exact hrepr; try exact hzc; try exact hj; try exact hlen; try exact hjlen; try exact hai; first by [].
  exact ht.
exact (inverse_butterfly_store rp p (NTT_Fq.zetas_inv.[zc] * (p.[j] - p.[j + len])) j len t0 coeff t asz bsz tsz
         hrepr hj hlen hjlen ht0 hcoeff hasz hbsz htsz hbwt0 hbwcoeff hbwt ht').
qed.

op final_mont_array (p : coeff Array256.t) (j : int) : coeff Array256.t =
  Array256.init (fun i => if 0 <= i < j then p.[i] * NTT_Fq.R else p.[i]).

op final_bound (j i : int) : int =
  if 0 <= i < j then 16 else 26.

lemma final_mont_array_start p :
  final_mont_array p 0 = p.
proof.
apply/Array256.ext_eq => i hi.
by rewrite /final_mont_array initiE //=; smt().
qed.

lemma final_mont_array_exit p :
  final_mont_array p 256 = NTT_Fq.array256_mont p.
proof.
apply/Array256.ext_eq => i hi.
have hi256 : 0 <= i < 256 by smt().
have hirange : i \in range 0 256 by rewrite mem_range; smt().
rewrite /final_mont_array initiE //=.
rewrite (array256_mont_get p i hirange).
by smt().
qed.

lemma final_mont_array_get_raw p j :
  0 <= j < 256 =>
  (final_mont_array p j).[j] = p.[j].
proof.
move=> hj.
by rewrite /final_mont_array initiE //=; smt().
qed.

lemma final_mont_array_setE p j :
  0 <= j < 256 =>
  (final_mont_array p j).[j <- p.[j] * NTT_Fq.scale255 * NTT_Fq.R] =
  final_mont_array (p.[j <- p.[j] * NTT_Fq.scale255]) (j + 1).
proof.
move=> hj.
apply/Array256.ext_eq => i hi.
rewrite !Array256.get_set_if /final_mont_array !initiE //=.
case: (i = j) => hij.
+ rewrite hij.
  have hjj : 0 <= j < j + 1 by smt().
  rewrite hjj /=.
  rewrite !Array256.get_set_if /=.
  have -> : 0 <= j < 256 by smt().
  rewrite /=.
  trivial.
rewrite !Array256.get_set_if /=.
rewrite hij /=.
have hsame : (0 <= i < j + 1) = (0 <= i < j) by smt().
rewrite hsame.
by smt().
qed.

lemma final_bound_start i :
  final_bound 0 i = 26.
proof. by rewrite /final_bound; smt(). qed.

lemma final_bound_next_unchanged j k :
  0 <= j < 256 =>
  k \in range 0 256 =>
  k <> j =>
  0 <= final_bound j k <= final_bound (j + 1) k.
proof. by rewrite /final_bound mem_range; smt(). qed.

lemma inverse_final_product_bound_call_h
  ai bi coeff :
  hoare [Hpoly_loop.M.__fqmul :
    ai = BArray1024.get32 Hpoly_loop.jzetas_inv 255 /\
    NTT_Fq.word_to_coeff bi = coeff /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
      Fq.SignedReductions.R %/ 2 * Fq.q /\
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = coeff * NTT_Fq.scale255 * NTT_Fq.R /\
    Fq.bw32 res 16].
proof.
conseq (fqmul_word_to_coeff_mul_bound_h
          (W32.to_sint ai) (W32.to_sint bi)).
+ by move=> &hr [_ [_ [hbound [ha hb]]]]; rewrite ha hb.
move=> &hr [hai [hbi [hbound [ha hb]]]] result [hres hbw] /=.
split; last exact hbw.
rewrite hres -hbi /NTT_Fq.word_to_coeff hai.
have -> :
  incoeff (W32.to_sint bi) * NTT_Fq.scale255 * NTT_Fq.R =
  incoeff (W32.to_sint bi) * (NTT_Fq.scale255 * NTT_Fq.R) by ring.
have hz := jzetas_inv_255_scale_cancel.
rewrite -hz /NTT_Fq.word_to_coeff.
by ring.
qed.

lemma inverse_final_product_bound_call_ph
  ai bi coeff :
  phoare [Hpoly_loop.M.__fqmul :
    ai = BArray1024.get32 Hpoly_loop.jzetas_inv 255 /\
    NTT_Fq.word_to_coeff bi = coeff /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
      Fq.SignedReductions.R %/ 2 * Fq.q /\
    a = ai /\ b = bi ==>
    NTT_Fq.word_to_coeff res = coeff * NTT_Fq.scale255 * NTT_Fq.R /\
    Fq.bw32 res 16] = 1%r.
proof.
by conseq loop_fqmul_ll
     (inverse_final_product_bound_call_h ai bi coeff).
qed.

lemma inverse_final_product_bound_from_inv rp j :
  barray256_bound_by rp (final_bound j) =>
  0 <= j < 256 =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas_inv 255) *
    W32.to_sint (BArray1024.get32 rp j) <
    Fq.SignedReductions.R %/ 2 * Fq.q.
proof.
move=> hbd hj.
have hzbw := jzetas_inv_bound16 255 _.
+ by smt().
have hraw : Fq.bw32 (BArray1024.get32 rp j) 26.
+ have hjmem : j \in range 0 256 by rewrite mem_range; smt().
  have := hbd j hjmem.
  by rewrite /final_bound; smt().
exact (fqmul_product_bound_16_26
  (BArray1024.get32 Hpoly_loop.jzetas_inv 255)
  (BArray1024.get32 rp j) hzbw hraw).
qed.

(* Public Jasmin wrappers are trivial wrappers around the core routines.
   Keep these proofs self-contained because the root Hpoly_loop import
   exposes the procedures but not generated wrapper lemmas. *)

equiv poly_ntt_jazz_ref :
  Hpoly_loop.M.poly_ntt_jazz ~ Hpoly_loop.M._poly_ntt :
  ={rp} ==> ={res}.
proof.
proc.
inline*.
sim.
qed.

equiv poly_invntt_jazz_ref :
  Hpoly_loop.M.poly_invntt_jazz ~ Hpoly_loop.M._poly_invntt :
  ={rp} ==> ={res}.
proof.
proc.
inline*.
sim.
qed.

equiv poly_ntt_core_ref :
  Hpoly_loop.M._poly_ntt ~ NTT_Fq.NTT.ntt :
  NTT_Fq.poly_repr_bound rp{1} r{2} 16 /\
  zetas{2} = NTT_Fq.zetas
  ==> NTT_Fq.poly_repr_bound res{1} res{2} 24.
proof.
proc.
wp.
while (
  NTT_Fq.poly_repr rp{1} r{2} /\
  barray256_bound_by rp{1}
    (const_bound (fwd_stage_bound len{1})) /\
  zetasp{1} = Hpoly_loop.jzetas /\
  zetas{2} = NTT_Fq.zetas /\
  zetasctr{1} = zetasctr{2} /\
  len{1} = len{2} /\
  fwd_len_ok len{1} /\
  zetasctr{1} = fwd_zbase len{1}
).
+ wp.
  while (
    NTT_Fq.poly_repr rp{1} r{2} /\
    barray256_bound_by rp{1}
      (fwd_middle_bound
        (fwd_stage_bound len{1}) start{1}) /\
    zetasp{1} = Hpoly_loop.jzetas /\
    zetas{2} = NTT_Fq.zetas /\
    zetasctr{1} = zetasctr{2} /\
    len{1} = len{2} /\
    fwd_len_ok len{1} /\
    0 < len{1} /\
    start{1} = start{2} /\
    0 <= start{1} <= 256 /\
    start{1} =
      2 * len{1} *
        (zetasctr{1} - fwd_zbase len{1})
  ).
  + wp.
    while (
      NTT_Fq.poly_repr rp{1} r{2} /\
      barray256_bound_by rp{1}
        (fwd_inner_bound
          (fwd_stage_bound len{1})
          len{1} start{1} j{1}) /\
      zetasp{1} = Hpoly_loop.jzetas /\
      zetas{2} = NTT_Fq.zetas /\
      zetasctr{1} = zetasctr{2} /\
      len{1} = len{2} /\
      fwd_len_ok len{1} /\
      0 < len{1} /\
      start{1} = start{2} /\
      0 <= start{1} < 256 /\
      start{1} + 2 * len{1} <= 256 /\
      start{1} =
        2 * len{1} *
        (zetasctr{1} - 1 - fwd_zbase len{1}) /\
      1 <= zetasctr{1} < 256 /\
      zeta_0{1} = BArray1024.get32 Hpoly_loop.jzetas zetasctr{1} /\
      zeta_{2} = NTT_Fq.zetas.[zetasctr{2}] /\
      j{1} = j{2} /\
      cmp{1} = start{1} + len{1} /\
      start{1} <= j{1} <= start{1} + len{1}
    ).
    + wp.
      sp.
      ecall{1} (forward_twiddle_product_bound_call_ph
        rp{1} r{2} zetasctr{2} j{2} len{2} zeta_0{1} coeff{1}).
      wp.
      skip.
      move=> &1 &2 /=.
      move=> [hs [hoff [hcoeff [hinv hguards]]]].
      move: hinv => [hrepr hinv].
      move: hinv => [hbd hinv].
      move: hinv => [hzetasp hinv].
      move: hinv => [hzetas hinv].
      move: hinv => [hzc_eq hinv].
      move: hinv => [hlen_eq hinv].
      move: hinv => [hlenok hinv].
      move: hinv => [hlen hinv].
      move: hinv => [hstart_eq hinv].
      move: hinv => [hstart_rng hinv].
      move: hinv => [hblock hinv].
      move: hinv => [hzctr hinv].
      move: hinv => [hzcrng hinv].
      move: hinv => [hzeta0 hinv].
      move: hinv => [hzeta hinv].
      move: hinv => [hj_eq [hcmp hjrng]].
      move: hstart_rng => [hstart0 hstartlt].
      move: hzcrng => [hzc_lo hzc_hi].
      move: hjrng => [hj_ge hj_le].
      move: hguards => [hj_guard1 hj_guard2].
      split.
      + split; first exact hrepr.
        split; first by smt().
        split; first by smt().
        split.
        + by rewrite hzeta0 hzc_eq.
        split.
        + by rewrite hcoeff hoff hj_eq hlen_eq.
        split.
        + rewrite hzeta0 hcoeff hoff.
          have hprod :=
            forward_twiddle_product_bound_from_inner
              rp{1} len{1} start{1} j{1} zetasctr{1}
              hbd hlenok hlen _ _ _.
          + by smt().
          + by smt().
          + by smt().
          move: hprod.
          by rewrite /Hpoly_loop.jzetas.
        move=> _.
        rewrite hzeta0 hcoeff hoff.
        have hprod :=
          forward_twiddle_product_bound_from_inner
            rp{1} len{1} start{1} j{1} zetasctr{1}
            hbd hlenok hlen _ _ _.
        + by smt().
        + by smt().
        + by smt().
        move: hprod.
        by rewrite /Hpoly_loop.jzetas.
      move=> _ result [ht hbwt].
      have hstep :=
        forward_butterfly_step_bound_by
          rp{1} r{2} j{1} len{1} start{1} s{1} result
          (fwd_stage_bound len{1})
          hrepr hbd _ hlen _ _ _ hs _ _ hbwt.
      + by smt().
      + by smt().
      + by smt().
      + by smt().
      + exact (fwd_stage_bound_ge16 len{1} hlenok).
      + by have := fwd_stage_bound_range len{1} hlenok; smt().
      move: hstep.
      rewrite ht -hzeta hj_eq hlen_eq.
      move=> [hpoly hbound].
      rewrite hoff hj_eq hlen_eq.
      split.
      + split; first exact hpoly.
        split; first exact hbound.
        by smt().
      by smt().
    wp.
    skip.
    move=> &1 &2 /=.
    move=> [hm hguards].
    move: hm => [hrepr hm].
    move: hm => [hbd hm].
    move: hm => [hzetasp hm].
    move: hm => [hzetas hm].
    move: hm => [hzc_eq hm].
    move: hm => [hlen_eq hm].
    move: hm => [hlenok hm].
    move: hm => [hlen hm].
    move: hm => [hstart_eq hm].
    move: hm => [hstart_rng hzctr].
    move: hguards => [hstart_guard1 hstart_guard2].
    move: hstart_rng => [hstart_ge hstart_le].
    have hstart_lt : 0 <= start{1} < 256 by smt().
    have hblock :=
      fwd_block_end_bound len{1} start{1} zetasctr{1}
        hlenok hlen hstart_lt hzctr.
    have hzcr :=
      fwd_read_range len{1} start{1} zetasctr{1}
        hlenok hlen hstart_lt hzctr.
    split.
    + split.
      + split; first exact hrepr.
        split.
        + move=> i hi.
          rewrite -fwd_middle_to_inner.
          exact (hbd i hi).
        split; first exact hzetasp.
        split; first exact hzetas.
        split; first by smt().
        split; first exact hlen_eq.
        split; first exact hlenok.
        split; first exact hlen.
        split; first exact hstart_eq.
        split; first exact hstart_lt.
        split; first exact hblock.
        split; first by smt().
        split; first exact hzcr.
        split; first by rewrite hzetasp.
        split; first by rewrite hzetas.
        split; first exact hstart_eq.
        by smt().
      by smt().
    move=> jL rpL jR rR hnotL hnotR hinv.
    move: hinv => [hreprL hinv].
    move: hinv => [hbdL hinv].
    move: hinv => [hzetaspL hinv].
    move: hinv => [hzetasL hinv].
    move: hinv => [hzcL hinv].
    move: hinv => [hlenL_eq hinv].
    move: hinv => [hlenL_ok hinv].
    move: hinv => [hlenL hinv].
    move: hinv => [hstartL_eq0 hinv].
    move: hinv => [hstartL_rng hinv].
    move: hinv => [hblockL hinv].
    move: hinv => [hzctrL hinv].
    move: hinv => [hzcrL hinv].
    move: hinv => [hzeta0L hinv].
    move: hinv => [hzetaL hinv].
    move: hinv => [hj_eqL [hcmpL hjrngL]].
    move: hstartL_rng => [hstartL_ge hstartL_lt].
    have hjL_ge : start{1} <= jL by smt().
    have hjL_le : jL <= start{1} + len{1} by smt().
    have hj_end : jL = start{1} + len{1} by smt().
    have hstart_new : jL + len{1} = start{1} + 2 * len{1} by smt().
    have hbdmid :
      barray256_bound_by rpL
        (fwd_middle_bound
          (fwd_stage_bound len{1}) (jL + len{1})).
    + move=> i hi.
      have htmp := hbdL i hi.
      have heq :=
        fwd_inner_exit_to_middle
          (fwd_stage_bound len{1}) len{1} start{1} i
          hstartL_ge hlenL.
      rewrite hstart_new.
      move: htmp.
      by rewrite hj_end heq.
    split.
    + split; first exact hreprL.
      split; first exact hbdmid.
      split; first exact hzetaspL.
      split; first exact hzetasL.
      split; first exact hzcL.
      split; first exact hlenL_eq.
      split; first exact hlenL_ok.
      split; first exact hlenL.
      split; first by smt().
      split; first by smt().
      by smt().
    by smt().
  wp.
  skip.
  move=> &1 &2 /=.
  move=> [ho hguards].
  move: ho => [hrepr ho].
  move: ho => [hbd ho].
  move: ho => [hzetasp ho].
  move: ho => [hzetas ho].
  move: ho => [hzc_eq ho].
  move: ho => [hlen_eq ho].
  move: ho => [hlenok hzbase].
  move: hguards => [hlen_pos hlen_guard].
  split.
  + split; first exact hrepr.
    split.
    + move=> i hi.
      rewrite fwd_middle_start_const /const_bound.
      exact (hbd i hi).
    split; first exact hzetasp.
    split; first exact hzetas.
    split; first exact hzc_eq.
    split; first exact hlen_eq.
    split; first exact hlenok.
    split; first exact hlen_pos.
    by smt().
  move=> rpL startL zcL rR startR zcR hnotL hnotR hm.
  move: hm => [hreprL hm].
  move: hm => [hbdL hm].
  move: hm => [hzetaspL hm].
  move: hm => [hzetasL hm].
  move: hm => [hzcL hm].
  move: hm => [hlenL_eq hm].
  move: hm => [hlenL_ok hm].
  move: hm => [hlenL_pos hm].
  move: hm => [hstart_eqL hm].
  move: hm => [hstart_rngL hstart_zcL].
  have hstart_end : startL = 256 by smt().
  have hshift : len{1} `|>>` 1 = len{1} %/ 2.
  + by apply int_shr1_div2; smt().
  have hstage_next :=
    fwd_stage_next len{1} hlenL_ok hlenL_pos.
  have hstage_shift :
    fwd_stage_bound (len{1} `|>>` 1) =
    fwd_stage_bound len{1} + 1.
  + by rewrite hshift hstage_next.
  have hlen_next :=
    fwd_len_next_ok len{1} hlenL_ok hlenL_pos.
  have hzbase_next :=
    fwd_stage_zbase_exit len{1} zcL
      hlenL_ok hlenL_pos _.
  + by smt().
  have hbdconst :
    barray256_bound_by rpL
      (const_bound
        (fwd_stage_bound (len{1} `|>>` 1))).
  + move=> i hi.
    have htmp := hbdL i hi.
    move: htmp.
    rewrite hstart_end.
    rewrite (fwd_middle_exit_const
               (fwd_stage_bound len{1}) 256 i _ _).
    + by move: hi; rewrite mem_range.
    + trivial.
    rewrite /const_bound.
    by smt().
  split.
  + split; first exact hreprL.
    split; first exact hbdconst.
    split; first exact hzetaspL.
    split; first exact hzetasL.
    split; first exact hzcL.
    split; first by smt().
    split; first by rewrite hshift; exact hlen_next.
    by rewrite hshift; exact hzbase_next.
  by rewrite hshift; smt().
wp.
skip.
move=> &1 &2 /=.
move=> [hpre hzetas2].
split.
+ split.
  + exact (NTT_Fq.poly_repr_bound_repr rp{1} r{2} 16 hpre).
  split.
  + rewrite /fwd_stage_bound.
    exact (barray256_bound_by_const rp{1} 16
             (NTT_Fq.poly_repr_bound_bound rp{1} r{2} 16 hpre)).
  split; first by [].
  split; first by rewrite /fwd_len_ok.
  by rewrite /fwd_zbase.
  by smt().
qed.

equiv poly_invntt_core_ref18 :
  Hpoly_loop.M._poly_invntt ~ NTT_Fq.NTT.invntt :
  NTT_Fq.poly_repr_bound rp{1} r{2} 18 /\
  zetas_inv{2} = NTT_Fq.zetas_inv
  ==> NTT_Fq.poly_repr_bound res{1} (NTT_Fq.array256_mont res{2}) 16.
proof.
proc.
wp.
while (
  NTT_Fq.poly_repr rp{1}
    (final_mont_array r{2} j{2}) /\
  barray256_bound_by rp{1}
    (final_bound j{1}) /\
  zetasp{1} = Hpoly_loop.jzetas_inv /\
  zetas_inv{2} = NTT_Fq.zetas_inv /\
  j{1} = j{2} /\
  0 <= j{1} <= 256 /\
  zeta_0{1} = BArray1024.get32 Hpoly_loop.jzetas_inv 255
).
+ wp.
  sp.
  ecall{1} (inverse_final_product_bound_call_ph
    zeta_0{1} coeff{1} r{2}.[j{2}]).
  wp.
  skip.
  move=> &1 &2 /=.
  move=> [hcoeff [hinv hguards]].
  move: hinv => [hrepr hinv].
  move: hinv => [hbd hinv].
  move: hinv => [hzetasp hinv].
  move: hinv => [hzetas hinv].
  move: hinv => [hj_eq hinv].
  move: hinv => [hj_rng hzeta0].
  move: hguards => [hj_guard1 hj_guard2].
  move: hj_rng => [hj_ge hj_le].
  split.
  + split; first exact hzeta0.
    split.
    + rewrite hcoeff.
      have hp :=
        NTT_Fq.poly_repr_get rp{1}
          (final_mont_array r{2} j{2}) j{1}
          hrepr _.
      + by rewrite mem_range; smt().
      move: hp.
      rewrite hj_eq (final_mont_array_get_raw r{2} j{2} _).
      + by smt().
      move=> hp.
      by rewrite -hp.
    split.
    + rewrite hcoeff.
      have hprod :=
        inverse_final_product_bound_from_inv
          rp{1} j{1} hbd _.
      + by smt().
      move: hprod.
      by rewrite hzeta0.
    move=> _.
    rewrite hcoeff.
    have hprod :=
      inverse_final_product_bound_from_inv
        rp{1} j{1} hbd _.
    + by smt().
    move: hprod.
    by rewrite hzeta0.
  move=> _ result [hres hbwr].
  split.
  + have hrepr' :
      NTT_Fq.poly_repr
        (BArray1024.set32 rp{1} j{1} result)
        ((final_mont_array r{2} j{2}).[j{2} <-
          r{2}.[j{2}] * NTT_Fq.scale255 * NTT_Fq.R]).
      + have htmp :=
        NTT_Fq.poly_repr_set32 rp{1}
          (final_mont_array r{2} j{2})
          j{1} result hrepr _.
      + by smt().
      have -> :
        (final_mont_array r{2} j{2}).[j{2} <-
          r{2}.[j{2}] * NTT_Fq.scale255 * NTT_Fq.R] =
        (final_mont_array r{2} j{2}).[j{1} <-
          NTT_Fq.word_to_coeff result].
      + by rewrite hj_eq hres.
      exact htmp.
    have htarget :
      (final_mont_array r{2} j{2}).[j{2} <-
        r{2}.[j{2}] * NTT_Fq.scale255 * NTT_Fq.R] =
      final_mont_array
        (r{2}.[j{2} <- r{2}.[j{2}] * zetas_inv{2}.[255]])
        (j{2} + 1).
    + rewrite hzetas.
      have -> : NTT_Fq.zetas_inv.[255] = NTT_Fq.scale255.
      + by rewrite /NTT_Fq.zetas_inv /=.
      apply (final_mont_array_setE r{2} j{2}).
      by smt().
    split.
    + by rewrite -htarget.
    split.
    + apply (barray256_bound_by_set32_change
        rp{1} (final_bound j{1})
        (final_bound (j{1} + 1)) j{1} result);
        try exact hbd.
      + by smt().
      + by rewrite /final_bound; smt().
      move=> k hk hkneq.
      exact (final_bound_next_unchanged
        j{1} k _ hk hkneq).
      by smt().
    by smt().
wp.
while (
  NTT_Fq.poly_repr rp{1} r{2} /\
  barray256_bound_by rp{1}
    (const_bound
      (inv_stage_bound len{1})) /\
  zetasp{1} = Hpoly_loop.jzetas_inv /\
  zetas_inv{2} = NTT_Fq.zetas_inv /\
  zetasctr{1} = zetasctr{2} /\
  len{1} = len{2} /\
  inv_len_ok len{1} /\
  zetasctr{1} = inv_zbase len{1}
).
+ wp.
  while (
    NTT_Fq.poly_repr rp{1} r{2} /\
    barray256_bound_by rp{1}
      (inv_middle_bound
        (inv_stage_bound len{1}) start{1}) /\
    zetasp{1} = Hpoly_loop.jzetas_inv /\
    zetas_inv{2} = NTT_Fq.zetas_inv /\
    zetasctr{1} = zetasctr{2} /\
    len{1} = len{2} /\
    inv_len_ok len{1} /\
    0 < len{1} /\
    len{1} < 256 /\
    start{1} = start{2} /\
    0 <= start{1} <= 256 /\
    start{1} =
      2 * len{1} *
        (zetasctr{1} - inv_zbase len{1})
  ).
  + wp.
    while (
      NTT_Fq.poly_repr rp{1} r{2} /\
      barray256_bound_by rp{1}
        (inv_inner_bound
          (inv_stage_bound len{1})
          len{1} start{1} j{1}) /\
      zetasp{1} = Hpoly_loop.jzetas_inv /\
      zetas_inv{2} = NTT_Fq.zetas_inv /\
      zetasctr{1} = zetasctr{2} /\
      len{1} = len{2} /\
      inv_len_ok len{1} /\
      0 < len{1} /\
      len{1} < 256 /\
      start{1} = start{2} /\
      0 <= start{1} < 256 /\
      start{1} + 2 * len{1} <= 256 /\
      start{1} =
        2 * len{1} *
        (zetasctr{1} - 1 - inv_zbase len{1}) /\
      (zetasctr{1} - 1) \in range 0 255 /\
      zeta_0{1} =
        BArray1024.get32 Hpoly_loop.jzetas_inv (zetasctr{1} - 1) /\
      zeta_{2} = NTT_Fq.zetas_inv.[zetasctr{2} - 1] /\
      j{1} = j{2} /\
      cmp{1} = start{1} + len{1} /\
      start{1} <= j{1} <= start{1} + len{1}
    ).
    + wp.
      sp.
      ecall{1} (inverse_twiddle_product_bound_call_ph
        (zetasctr{2} - 1) zeta_0{1} t{1}
        (r{2}.[j{2}] - r{2}.[j{2} + len{2}])).
      wp.
      skip.
      move=> &1 &2 /=.
      move=> [rp0 [hoff [hcoeff [hs [hrp [ht [hinv hguards]]]]]]].
      move: hinv => [hrepr hinv].
      move: hinv => [hbd hinv].
      move: hinv => [hzetasp hinv].
      move: hinv => [hzetas hinv].
      move: hinv => [hzc_eq hinv].
      move: hinv => [hlen_eq hinv].
      move: hinv => [hlenok hinv].
      move: hinv => [hlen_pos hinv].
      move: hinv => [hlen_lt hinv].
      move: hinv => [hstart_eq hinv].
      move: hinv => [hstart_rng hinv].
      move: hinv => [hblock hinv].
      move: hinv => [hstart_zc hinv].
      move: hinv => [hzcrng hinv].
      move: hinv => [hzeta0 hinv].
      move: hinv => [hzeta hinv].
      move: hinv => [hj_eq [hcmp hjrng]].
      move: hstart_rng => [hstart_ge hstart_lt].
      move: hjrng => [hj_ge hj_le].
      move: hguards => [hj_guard1 hj_guard2].
      have hjrng_strict : start{1} <= j{1} < start{1} + len{1} by smt().
      have hj_mem : 0 <= j{1} < 256 by smt().
      have hoff_rng : 0 <= j{1} + len{1} < 256 by smt().
      have hstage_lt :
        0 <= inv_stage_bound len{1} < 31.
      + have := inv_stage_bound_lt31 len{1} hlenok.
        have := inv_stage_bound_pos len{1} hlenok.
        by smt().
      have [hcurj [hcurjl _]] :=
        inv_inner_current
          (inv_stage_bound len{1})
          len{1} start{1} j{1} _ hlen_pos hjrng_strict.
      + exact (inv_stage_bound_pos len{1} hlenok).
      have hbwj :
        Fq.bw32 (BArray1024.get32 rp0 j{1})
          (inv_stage_bound len{1}).
      + have hjmem : j{1} \in range 0 256 by rewrite mem_range; smt().
        have := hbd j{1} hjmem.
        by rewrite hcurj.
      have hbwcoeff :
        Fq.bw32 coeff{1}
          (inv_stage_bound len{1}).
      + rewrite hcoeff hoff.
        have hjlmem : j{1} + len{1} \in range 0 256
          by rewrite mem_range; smt().
        have := hbd (j{1} + len{1}) hjlmem.
        by rewrite hcurjl.
      split.
      + split; first by rewrite -hzc_eq.
        split.
        + by rewrite hzeta0 -hzc_eq.
        split.
        + rewrite ht.
          rewrite (word_to_coeff_sub
            (BArray1024.get32 rp0 j{1}) coeff{1}
            (inv_stage_bound len{1})
            (inv_stage_bound len{1})) //.
          have hpj :
            r{2}.[j{2}] =
            NTT_Fq.word_to_coeff (BArray1024.get32 rp0 j{1}).
          + have hpj0 :=
              NTT_Fq.poly_repr_get rp0 r{2} j{1} hrepr _.
            + by rewrite mem_range; smt().
            move: hpj0.
            by rewrite hj_eq.
          have hpjl :
            r{2}.[j{2} + len{2}] =
            NTT_Fq.word_to_coeff coeff{1}.
          + have hpjl0 :=
              NTT_Fq.poly_repr_get rp0 r{2} (j{1} + len{1}) hrepr _.
            + by rewrite mem_range; smt().
            move: hpjl0.
            rewrite hcoeff hoff hj_eq hlen_eq.
            by [].
          by rewrite -hpj -hpjl.
        split.
        + rewrite hzeta0 ht hcoeff hoff.
          have hprod :=
            inverse_twiddle_product_call_bound_from_inner
              rp0 len{1} start{1} j{1} (zetasctr{1} - 1)
              hbd hlenok hlen_lt hjrng_strict hj_mem hoff_rng hzcrng.
          move: hprod => [hlo _].
          exact hlo.
        move=> _.
        rewrite hzeta0 ht hcoeff hoff.
        have hprod :=
          inverse_twiddle_product_call_bound_from_inner
            rp0 len{1} start{1} j{1} (zetasctr{1} - 1)
            hbd hlenok hlen_lt hjrng_strict hj_mem hoff_rng hzcrng.
        move: hprod => [_ hhi].
        exact hhi.
      move=> _ result [hres hbwt].
      have hstep :=
        inverse_butterfly_step_bound_by
          rp0 r{2} (zetasctr{1} - 1) j{1} len{1} start{1}
          (BArray1024.get32 rp0 j{1}) coeff{1} result
          (inv_stage_bound len{1})
          hrepr hbd hstart_ge hlen_pos hjrng_strict hj_mem hoff_rng
          _ _ _ _ hbwt _.
      + by [].
      + by rewrite hcoeff hoff.
      + exact (inv_stage_bound_ge16 len{1} hlenok).
      + exact hstage_lt.
      + rewrite hres hzc_eq hj_eq hlen_eq.
        by ring.
      move: hstep => [hpoly hbound].
      rewrite hrp hs hoff.
      split.
      + split.
        + rewrite (inverse_spec_updateE r{2} zeta_{2} j{2} len{2} _).
          + by smt().
          move: hpoly.
          by rewrite hzc_eq hj_eq hlen_eq -hzeta.
        split; first exact hbound.
        by smt().
      by smt().
    wp.
    skip.
    move=> &1 &2 /=.
    move=> [hm hguards].
    move: hm => [hrepr hm].
    move: hm => [hbd hm].
    move: hm => [hzetasp hm].
    move: hm => [hzetas hm].
    move: hm => [hzc_eq hm].
    move: hm => [hlen_eq hm].
    move: hm => [hlenok hm].
    move: hm => [hlen_pos hm].
    move: hm => [hlen_lt hm].
    move: hm => [hstart_eq hm].
    move: hm => [hstart_rng hstart_zc].
    move: hguards => [hstart_guard1 hstart_guard2].
    move: hstart_rng => [hstart_ge hstart_le].
    have hstart_lt : 0 <= start{1} < 256 by smt().
    have hblock :=
      inv_block_end_bound len{1} start{1} zetasctr{1}
        hlenok hlen_lt hstart_lt hstart_zc.
    have hzcr :=
      inv_read_range len{1} start{1} zetasctr{1}
        hlenok hlen_lt hstart_lt hstart_zc.
    split.
    + split.
      + split; first exact hrepr.
        split.
        + move=> i hi.
          rewrite -inv_middle_to_inner.
          exact (hbd i hi).
        split; first exact hzetasp.
        split; first exact hzetas.
        split; first by smt().
        split; first exact hlen_eq.
        split; first exact hlenok.
        split; first exact hlen_pos.
        split; first exact hlen_lt.
        split; first exact hstart_eq.
        split; first exact hstart_lt.
        split; first exact hblock.
        split; first by smt().
        split; first exact hzcr.
        split; first by rewrite hzetasp.
        split; first by rewrite hzetas.
        split; first exact hstart_eq.
        by smt().
      by smt().
    move=> jL rpL jR rR hnotL hnotR hinv.
    move: hinv => [hreprL hinv].
    move: hinv => [hbdL hinv].
    move: hinv => [hzetaspL hinv].
    move: hinv => [hzetasL hinv].
    move: hinv => [hzcL hinv].
    move: hinv => [hlenL_eq hinv].
    move: hinv => [hlenL_ok hinv].
    move: hinv => [hlenL_pos hinv].
    move: hinv => [hlenL_lt hinv].
    move: hinv => [hstartL_eq0 hinv].
    move: hinv => [hstartL_rng hinv].
    move: hinv => [hblockL hinv].
    move: hinv => [hzctrL hinv].
    move: hinv => [hzcrL hinv].
    move: hinv => [hzeta0L hinv].
    move: hinv => [hzetaL hinv].
    move: hinv => [hj_eqL [hcmpL hjrngL]].
    move: hstartL_rng => [hstartL_ge hstartL_lt].
    have hjL_ge : start{1} <= jL by smt().
    have hjL_le : jL <= start{1} + len{1} by smt().
    have hj_end : jL = start{1} + len{1} by smt().
    have hstart_new : jL + len{1} = start{1} + 2 * len{1} by smt().
    have hbdmid :
      barray256_bound_by rpL
        (inv_middle_bound
          (inv_stage_bound len{1}) (jL + len{1})).
    + move=> i hi.
      have htmp := hbdL i hi.
      have heq :=
        inv_inner_exit_to_middle
          (inv_stage_bound len{1}) len{1} start{1} i
          hstartL_ge hlenL_pos.
      rewrite hstart_new.
      move: htmp.
      by rewrite hj_end heq.
    split.
    + split; first exact hreprL.
      split; first exact hbdmid.
      split; first exact hzetaspL.
      split; first exact hzetasL.
      split; first exact hzcL.
      split; first exact hlenL_eq.
      split; first exact hlenL_ok.
      split; first exact hlenL_pos.
      split; first exact hlenL_lt.
      split; first by smt().
      split; first by smt().
      by smt().
    by smt().
  wp.
  skip.
  move=> &1 &2 /=.
  move=> [ho hguards].
  move: ho => [hrepr ho].
  move: ho => [hbd ho].
  move: ho => [hzetasp ho].
  move: ho => [hzetas ho].
  move: ho => [hzc_eq ho].
  move: ho => [hlen_eq ho].
  move: ho => [hlenok hzbase].
  move: hguards => [hlen_guard1 hlen_guard2].
  have hlen_pos : 0 < len{1}
    by move: hlenok; rewrite /inv_len_ok; smt().
  have hlen_lt : len{1} < 256 by smt().
  split.
  + split; first exact hrepr.
    split.
    + move=> i hi.
      rewrite inv_middle_start_const
              /const_bound.
      exact (hbd i hi).
    split; first exact hzetasp.
    split; first exact hzetas.
    split; first exact hzc_eq.
    split; first exact hlen_eq.
    split; first exact hlenok.
    split; first exact hlen_pos.
    split; first exact hlen_lt.
    by smt().
  move=> rpL startL zcL rR startR zcR hnotL hnotR hm.
  move: hm => [hreprL hm].
  move: hm => [hbdL hm].
  move: hm => [hzetaspL hm].
  move: hm => [hzetasL hm].
  move: hm => [hzcL hm].
  move: hm => [hlenL_eq hm].
  move: hm => [hlenL_ok hm].
  move: hm => [hlenL_pos hm].
  move: hm => [hlenL_lt hm].
  move: hm => [hstart_eqL hm].
  move: hm => [hstart_rngL hstart_zcL].
  have hstart_end : startL = 256 by smt().
  have hshift : len{1} `<<` 1 = len{1} * 2.
  + by rewrite int_shl1_mul2.
  have hstage_next :=
    inv_stage_next len{1} hlenL_ok hlenL_lt.
  have hstage_shift :
    inv_stage_bound (len{1} `<<` 1) =
    inv_stage_bound len{1} + 1.
  + by rewrite hshift hstage_next.
  have hlen_next :=
    inv_len_next_ok len{1} hlenL_ok hlenL_lt.
  have hzbase_next :=
    inv_stage_zbase_exit len{1} zcL
      hlenL_ok hlenL_lt _.
  + by smt().
  have hbdconst :
    barray256_bound_by rpL
      (const_bound
        (inv_stage_bound (len{1} `<<` 1))).
  + move=> i hi.
    have htmp := hbdL i hi.
    move: htmp.
    rewrite hstart_end.
    rewrite (inv_middle_exit_const
               (inv_stage_bound len{1}) 256 i _ _).
    + by move: hi; rewrite mem_range.
    + trivial.
    rewrite /const_bound.
    by smt().
  split.
  + split; first exact hreprL.
    split; first exact hbdconst.
    split; first exact hzetaspL.
    split; first exact hzetasL.
    split; first exact hzcL.
    split; first by smt().
    split; first by rewrite hshift; exact hlen_next.
    by rewrite hshift; exact hzbase_next.
  by rewrite hshift; smt().
wp.
skip.
move=> &1 &2 /=.
move=> [hpre hzetas2].
split.
+ split.
  + exact (NTT_Fq.poly_repr_bound_repr rp{1} r{2} 18 hpre).
  split.
  + rewrite /inv_stage_bound.
    exact (barray256_bound_by_const rp{1} 18
             (NTT_Fq.poly_repr_bound_bound rp{1} r{2} 18 hpre)).
  by rewrite /inv_len_ok /inv_zbase.
move=> rpL zetaspL zcL lenL rR zetasInvR zcR lenR ho.
move: ho => [hreprL ho].
move: ho => [hbdL ho].
move: ho => [hzetaspL ho].
move: ho => [hzetasL ho].
move: ho => [hzcL ho].
move: ho => [hlenL_eq ho].
move: ho => hlenL_ok.
have hstage_rng :=
  inv_stage_bound_range rpL hlenL_eq.
split.
+ split.
  + by rewrite final_mont_array_start.
  split.
  + move=> i hi.
    have htmp := hbdL i hi.
    move: htmp.
    rewrite /const_bound.
    move=> htmp.
    rewrite final_bound_start.
    exact (NTT_Fq.bw32_weaken
      _ (inv_stage_bound rpL) 26 hstage_rng htmp).
by smt().
move=> jL rpF jR rF hnotjL hnotjR hf.
move: hf => [hreprF hf].
move: hf => [hbdF hf].
move: hf => [hzetaspF hf].
move: hf => [hzetasF hf].
move: hf => [hj_eq hf].
have hj_exit : jL = 256 by smt().
have hjR_exit : jR = 256 by smt().
split.
+ move: hreprF.
  by rewrite hjR_exit final_mont_array_exit.
move=> i hi.
have htmp := hbdF i hi.
move: htmp.
rewrite hj_exit /final_bound.
by move: hi; rewrite mem_range; smt().
qed.

equiv poly_invntt_core_ref :
  Hpoly_loop.M._poly_invntt ~ NTT_Fq.NTT.invntt :
  NTT_Fq.poly_repr_bound rp{1} r{2} 16 /\
  zetas_inv{2} = NTT_Fq.zetas_inv
  ==> NTT_Fq.poly_repr_bound res{1} (NTT_Fq.array256_mont res{2}) 16.
proof.
conseq poly_invntt_core_ref18.
move=> &1 &2 /= [hpre hzetas].
have h1618 : 0 <= 16 <= 18 by smt().
split.
+ split.
  + exact (NTT_Fq.poly_repr_bound_repr rp{1} r{2} 16 hpre).
  exact
    (NTT_Fq.barray256_bound_weaken rp{1} 16 18
      h1618 (NTT_Fq.poly_repr_bound_bound rp{1} r{2} 16 hpre)).
exact hzetas.
qed.

end RefJasminNTT.
