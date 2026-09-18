require import AllCore List IntDiv CoreMap.
from Jasmin require import JWord JModel.
require import Montgomery.
require import Hpoly_extract.

(* ====================================================================
   Fq.ec — field arithmetic for HAETAE
   Prime:  q    = 64513
   Montgomery base: R = 2^32
   qinv = q^{-1} mod 2^32 = 940508161
   Rinv = R^{-1} mod q    = 50386
            (proof: 2^32 mod 64513 = 14321, and 14321 * 50386 mod 64513 = 1)
   All polynomial coefficients live in W32; intermediate products in W64.
   ==================================================================== *)

theory Fq.

op q : int = 64513.
lemma qE : q = 64513 by rewrite /q.

clone import SignedReductions with
    op k    <- 32,
    op q    <- q,
    op qinv <- 940508161,
    op Rinv <- 50386
    proof q_bnd    by (rewrite /R qE => />)
    proof q_odd1   by (rewrite qE => />)
    proof q_odd2   by (rewrite qE => />)
    proof qqinv    by (rewrite /R qE => />)
    proof Rinv_gt0 by (auto => />)
    proof RRinv    by (rewrite /R qE => />)
    proof qinv_bnd by (rewrite /R => />).

(* ====================================================================
   smod ↔ JWord conversion helpers
   ==================================================================== *)

lemma smod_W32 a :
  smod a W32.modulus = W32.smod (a %% W32.modulus)
  by rewrite smodE /W32.smod /=.

lemma smod_W64 a :
  smod a W64.modulus = W64.smod (a %% W64.modulus)
  by rewrite smodE /W64.smod /=.

(* ====================================================================
   Auxiliary bit-level lemmas for SAR_sem32.
   The mask 0xFFFF_FFFF_0000_0000 = 2^64 - 2^32 = 18446744069414584320
   has bits 32..63 set and bits 0..31 clear.
   ==================================================================== *)

lemma aux32_0 x :
  32 <= x < 64 =>
  (W64.of_int 18446744069414584320).[x] = true.
proof.
rewrite of_intwE => />.
rewrite /int_bit => />.
case (x = 32); first by move => -> />.
move => *; case (x = 33); first by move => -> />.
move => *; case (x = 34); first by move => -> />.
move => *; case (x = 35); first by move => -> />.
move => *; case (x = 36); first by move => -> />.
move => *; case (x = 37); first by move => -> />.
move => *; case (x = 38); first by move => -> />.
move => *; case (x = 39); first by move => -> />.
move => *; case (x = 40); first by move => -> />.
move => *; case (x = 41); first by move => -> />.
move => *; case (x = 42); first by move => -> />.
move => *; case (x = 43); first by move => -> />.
move => *; case (x = 44); first by move => -> />.
move => *; case (x = 45); first by move => -> />.
move => *; case (x = 46); first by move => -> />.
move => *; case (x = 47); first by move => -> />.
move => *; case (x = 48); first by move => -> />.
move => *; case (x = 49); first by move => -> />.
move => *; case (x = 50); first by move => -> />.
move => *; case (x = 51); first by move => -> />.
move => *; case (x = 52); first by move => -> />.
move => *; case (x = 53); first by move => -> />.
move => *; case (x = 54); first by move => -> />.
move => *; case (x = 55); first by move => -> />.
move => *; case (x = 56); first by move => -> />.
move => *; case (x = 57); first by move => -> />.
move => *; case (x = 58); first by move => -> />.
move => *; case (x = 59); first by move => -> />.
move => *; case (x = 60); first by move => -> />.
move => *; case (x = 61); first by move => -> />.
move => *; case (x = 62); first by move => -> />.
move => *; case (x = 63); first by move => -> />.
by smt().
qed.

lemma aux32_1 x :
  0 <= x < 32 =>
  (W64.of_int 18446744069414584320).[x] = false.
proof.
rewrite of_intwE => />.
rewrite /int_bit => />.
case (x = 0);  first by move => -> />.
move => *; case (x = 1);  first by move => -> />.
move => *; case (x = 2);  first by move => -> />.
move => *; case (x = 3);  first by move => -> />.
move => *; case (x = 4);  first by move => -> />.
move => *; case (x = 5);  first by move => -> />.
move => *; case (x = 6);  first by move => -> />.
move => *; case (x = 7);  first by move => -> />.
move => *; case (x = 8);  first by move => -> />.
move => *; case (x = 9);  first by move => -> />.
move => *; case (x = 10); first by move => -> />.
move => *; case (x = 11); first by move => -> />.
move => *; case (x = 12); first by move => -> />.
move => *; case (x = 13); first by move => -> />.
move => *; case (x = 14); first by move => -> />.
move => *; case (x = 15); first by move => -> />.
move => *; case (x = 16); first by move => -> />.
move => *; case (x = 17); first by move => -> />.
move => *; case (x = 18); first by move => -> />.
move => *; case (x = 19); first by move => -> />.
move => *; case (x = 20); first by move => -> />.
move => *; case (x = 21); first by move => -> />.
move => *; case (x = 22); first by move => -> />.
move => *; case (x = 23); first by move => -> />.
move => *; case (x = 24); first by move => -> />.
move => *; case (x = 25); first by move => -> />.
move => *; case (x = 26); first by move => -> />.
move => *; case (x = 27); first by move => -> />.
move => *; case (x = 28); first by move => -> />.
move => *; case (x = 29); first by move => -> />.
move => *; case (x = 30); first by move => -> />.
move => *; case (x = 31); first by move => -> />.
by smt().
qed.

lemma aux32_2 (a : W64.t) :
  (a `>>>` 32) + (of_int 18446744069414584320)%W64
              = (a `>>>` 32) `|` (of_int 18446744069414584320)%W64.
proof.
rewrite orw_xpnd.
have -> : (a `>>>` 32) `&` (of_int 18446744069414584320)%W64 = W64.of_int 0.
+ have ? : (0 <= to_uint (a `>>>` 32) < 4294967296) by
    rewrite to_uint_shr => />; smt(divz_ge0 ltz_divLR pow2_64 W64.to_uint_cmp).
  apply W64.ext_eq => x xbnd.
  case (0 <= x < 32); 1: by move => smallx; rewrite andwE aux32_1 => /> /#.
  move => largex; rewrite /(`>>>`) /of_int /bits2w /= /int2bs /= /mkseq /= !initiE //=.
  rewrite !(nth_map 0 false _ x (iota_ 0 64)); 1, 2: by smt(size_iota).
  by rewrite !nth_iota //=; smt(W64.get_out).
by ring.
qed.

(* ====================================================================
   Arithmetic right shift of W64 by 32:
     a `|>>` 32  =  W64.of_int (to_sint a / 2^32)
   ==================================================================== *)

lemma SAR_sem32 (a : W64.t) :
  a `|>>` W8.of_int 32 = W64.of_int (to_sint a %/ 2^32).
proof.
rewrite /(`|>>`) to_sintE /smod sarE.
rewrite W8.of_uintK; apply W64.ext_eq => x x_b; rewrite initiE => />.
case (9223372036854775808 <= to_uint a); last first. (* non-negative branch *)
+ move => ab; rewrite W64.of_intwE x_b /= /int_bit /=.
  rewrite /min /= get_to_uint /= (modz_small _ 18446744073709551616); 1: smt(W64.to_uint_cmp).
  case (63 < x + 32). (* upper bits above word width *)
  + move => hb /=; rewrite pdiv_small; 1: by smt(W64.to_uint_cmp).
    rewrite mod0z /=.
    have -> : to_uint a %/ 4294967296 %/ 2 ^ x = 0; last by smt(mod0z).
    apply (divz_eq0 (to_uint a %/ 4294967296) (2^x)); 1: by smt(gt0_pow2).
    split; 1: by smt(divz_ge0 W64.to_uint_cmp).
    have /= ? : 2^31 <= 2^x by apply StdOrder.IntOrder.ler_weexpn2l => // /#.
    by smt(leq_div2r).
  move => /= lb.
  have -> : to_uint a %/ 2 ^ (x + 32) = to_uint a %/ 4294967296 %/ 2 ^ x; last by smt().
  rewrite (_: 4294967296 = 2^32) // {1}(divz_eq (to_uint a) (2^32)) exprD_nneg //; 1: smt().
  by smt(divmod_mul gt0_pow2).

(* negative branch *)
move => neg.
rewrite divzDr //= (_: 4294967296 = 2^32) // -to_uint_shr //=.
rewrite of_intS to_uintK /W64.([-]) /ulift1 aux32_2 orwE /=.
case (63 < x + 32); last by move => x_tub; rewrite aux32_1 /= /#.
move => x_tlb; rewrite /min x_tlb aux32_0 /=; 1: by smt().
rewrite get_to_uint => />.
by smt(W64.to_uint_cmp pow2_64).
qed.

(* ====================================================================
   montgomery_reduce correctness
   Input:  a : W64  (the product a * b, as int64)
   Output: r : W32  with to_sint r = SREDC(to_sint a)
              where SREDC(x) = x * R^{-1} mod q, result in (-q, q)
   ==================================================================== *)

lemma montgomery_reduce_corr_h _a :
  hoare [M.__montgomery_reduce :
    W64.to_sint a = _a ==>
    W32.to_sint res = SREDC _a].
proof.
proc; wp; skip => &hr [#] /= <-.
rewrite /SREDC SAR_sem32 /=.
rewrite smod_W64 smod_W32 /truncateu32 /sigextu64 /=.
rewrite W32.of_sintK W64.of_uintK W64.to_sintE W32.to_sintE qE /= !modz_dvd /R /=.
rewrite dvdz_eq /=; smt().
smt().
have Hlow :
  W32.smod (to_uint (W32.of_int (to_uint a{hr} * 940508161))) =
  smod (to_uint a{hr} * 940508161) W32.modulus.
+ rewrite (smod_W32 (to_uint a{hr} * 940508161)).
  have -> :
    to_uint (W32.of_int (to_uint a{hr} * 940508161)) =
    (to_uint a{hr} * 940508161) %% W32.modulus.
+ exact (W32.of_uintK (to_uint a{hr} * 940508161)).
  by [].

rewrite Hlow.

have Hsigned :
  smod (W64.smod (to_uint a{hr}) * 940508161 * W32.modulus) W64.modulus =
  smod (to_uint a{hr} * 940508161 * W32.modulus) W64.modulus.
+ have Hr :
    W64.smod (to_uint a{hr}) = to_uint a{hr} \/
    W64.smod (to_uint a{hr}) = to_uint a{hr} - W64.modulus.
  + rewrite /W64.smod /=.
    by smt().
  elim Hr => [-> | ->].
  - by [].
  - rewrite !smodE.
    have -> :
      (((to_uint a{hr} - W64.modulus) * 940508161 * W32.modulus) %% W64.modulus) =
      ((to_uint a{hr} * 940508161 * W32.modulus) %% W64.modulus).
    + by smt().
    by [].

have Hm :
  smod (to_uint a{hr} * 940508161) W32.modulus =
  smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
  W32.modulus.
+ rewrite W64.to_sintE.
  rewrite Hsigned.
  by smt().

rewrite Hm.

have Hsub0 :
  to_uint
    (a{hr} -
     W64.of_int
       (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
        W32.modulus * 64513)) =
  (to_uint a{hr} -
   (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
    W32.modulus * 64513)) %% W64.modulus.
+ have -> :
    a{hr} -
    W64.of_int
      (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
       W32.modulus * 64513)
    =
    a{hr} +
    (-
     W64.of_int
       (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
        W32.modulus * 64513)).
  by [].
  rewrite W64.to_uintD W64.to_uintN.
  have Hcast :
    to_uint
      (W64.of_int
         (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
          W32.modulus * 64513)) =
    (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
     W32.modulus * 64513) %% W64.modulus.
  + exact
      (W64.of_uintK
         (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
          W32.modulus * 64513)).
  rewrite Hcast.
  by smt().

have Hsub1 :
  (to_sint a{hr} -
   (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
    W32.modulus * 64513)) %% W64.modulus =
  (to_uint a{hr} -
   (smod (to_sint a{hr} * 940508161 * W32.modulus) W64.modulus %/
    W32.modulus * 64513)) %% W64.modulus.
+ rewrite W64.to_sintE.
  have Hr :
    W64.smod (to_uint a{hr}) = to_uint a{hr} \/
    W64.smod (to_uint a{hr}) = to_uint a{hr} - W64.modulus.
  + rewrite /W64.smod /=.
    by smt().
  elim Hr => [-> | ->].
  - by smt().
  - by smt().

rewrite Hsub0 -Hsub1.
by [].
qed.

lemma montgomery_reduce_ll :
   islossless M.__montgomery_reduce by proc; islossless.

lemma montgomery_reduce_corr _a :
   phoare [M.__montgomery_reduce :
     W64.to_sint a = _a ==> 
     W32.to_sint res = SREDC _a] = 1%r. 
 proof. by conseq montgomery_reduce_ll (montgomery_reduce_corr_h _a). qed. 

(* ====================================================================
   fqmul correctness
   __fqmul(a, b)  computes  SREDC(to_sint a * to_sint b)  in W32.
   Key auxiliary fact:
     W64.to_sint (sigextu64 a * sigextu64 b) = W32.to_sint a * W32.to_sint b
   which holds because |to_sint a * to_sint b| < 2^62 << 2^63.
   ==================================================================== *)

lemma fqmul_corr_h _a _b :
  hoare [M.__fqmul :
    W32.to_sint a = _a /\ W32.to_sint b = _b ==>
    W32.to_sint res = SREDC (_a * _b)].
proof.
proc.
(* If proc. shows a trailing call to __montgomery_reduce, do this directly. *)
call (montgomery_reduce_corr_h (_a * _b)).
wp.
skip => &hr [#] /= Ha Hb.

have Hau : 0 <= W32.to_uint a{hr} < W32.modulus.
+ exact (W32.to_uint_cmp a{hr}).

have Hbu : 0 <= W32.to_uint b{hr} < W32.modulus.
+ exact (W32.to_uint_cmp b{hr}).

have Ha' : -2^31 <= _a < 2^31.
+ rewrite -Ha W32.to_sintE /W32.smod /=.
  case (2147483648 <= to_uint a{hr}).
  + move=> Hhi.
    have Hlt : to_uint a{hr} < 4294967296 by have := Hau; smt().
    by smt().
  + move=> Hlo.
    have Hge : 0 <= to_uint a{hr} by have := Hau; smt().
    by smt().

have Hb' : -2^31 <= _b < 2^31.
+ rewrite -Hb W32.to_sintE /W32.smod /=.
  case (2147483648 <= to_uint b{hr}).
  + move=> Hhi.
    have Hlt : to_uint b{hr} < 4294967296 by have := Hbu; smt().
    by smt().
  + move=> Hlo.
    have Hge : 0 <= to_uint b{hr} by have := Hbu; smt().
    by smt().

have Hra : -2^31 <= _a < 2^31.
+ exact Ha'.

have Hrb : -2^31 <= _b < 2^31.
+ exact Hb'.

have Hsmalla : - ptr_modulus %/ 2 <= _a < ptr_modulus %/ 2.
+ have Hral : -2^31 <= _a by have := Hra; smt().
  have Hrah : _a < 2^31 by have := Hra; smt().
  have Hhalf : 2^31 <= ptr_modulus %/ 2 by smt().

  have Hneg : - ptr_modulus %/ 2 <= - 2^31.
  + have := Hhalf.
    by smt().

  have Hlo : - ptr_modulus %/ 2 <= _a.
  + have := Hneg.
    have := Hral.
    by smt().

  have Hhi : _a < ptr_modulus %/ 2.
  + have := Hhalf.
    have := Hrah.
    by smt().

  have := Hlo.
  have := Hhi.
  by smt().

have Hsmallb : - ptr_modulus %/ 2 <= _b < ptr_modulus %/ 2.
+ have Hrbl : -2^31 <= _b by have := Hrb; smt().
  have Hrbh : _b < 2^31 by have := Hrb; smt().
  have Hhalf : 2^31 <= ptr_modulus %/ 2 by smt().

  have Hneg : - ptr_modulus %/ 2 <= - 2^31.
  + have := Hhalf.
    by smt().

  have Hlo : - ptr_modulus %/ 2 <= _b.
  + have := Hneg.
    have := Hrbl.
    by smt().

  have Hhi : _b < ptr_modulus %/ 2.
  + have := Hhalf.
    have := Hrbh.
    by smt().

  have := Hlo.
  have := Hhi.
  by smt().

have Hsa : W64.to_sint (sigextu64 a{hr}) = _a.
+ rewrite /sigextu64 W64.to_sintE Ha.
  rewrite (W64.of_uintK _a).
  rewrite -(smod_W64 _a).
  rewrite smod_small.
  - by [].
  - exact Hsmalla.

have Hsb : W64.to_sint (sigextu64 b{hr}) = _b.
+ rewrite /sigextu64 W64.to_sintE Hb.
  rewrite (W64.of_uintK _b).
  rewrite -(smod_W64 _b).
  rewrite smod_small.
  - by [].
  - exact Hsmallb.

have Hcasta : to_uint (sigextu64 a{hr}) = _a %% ptr_modulus.
+ rewrite /sigextu64 Ha.
  exact (W64.of_uintK _a).

have Hcastb : to_uint (sigextu64 b{hr}) = _b %% ptr_modulus.
+ rewrite /sigextu64 Hb.
  exact (W64.of_uintK _b).

have Hsmallprod : - ptr_modulus %/ 2 <= _a * _b < ptr_modulus %/ 2.
+ have := Hra.
  have := Hrb.
  by smt().

done.
done.

have Hts :
  to_sint (sigextu64 a{hr} * sigextu64 b{hr}) =
  W64.smod (to_uint (sigextu64 a{hr} * sigextu64 b{hr})).
+ exact (W64.to_sintE (sigextu64 a{hr} * sigextu64 b{hr})).

rewrite Hts.
rewrite W64.to_uintM.

have Hmod :
  ((_a %% ptr_modulus) * (_b %% ptr_modulus)) %% ptr_modulus =
  (_a * _b) %% ptr_modulus.
+ by smt().

have Hcasta : to_uint (sigextu64 a{hr}) = _a %% ptr_modulus.
+ rewrite /sigextu64 Ha.
  exact (W64.of_uintK _a).

have Hcastb : to_uint (sigextu64 b{hr}) = _b %% ptr_modulus.
+ rewrite /sigextu64 Hb.
  exact (W64.of_uintK _b).

rewrite Hcasta Hcastb.
rewrite Hmod.
rewrite -(smod_W64 (_a * _b)).
rewrite smod_small.
- by [].
- have := Hra.
  have := Hrb.
  by smt().
done.
qed.


lemma fqmul_ll : islossless M.__fqmul by proc; islossless.

lemma fqmul_corr _a _b :
  phoare [M.__fqmul :
    W32.to_sint a = _a /\ W32.to_sint b = _b ==>
    W32.to_sint res = SREDC (_a * _b)] = 1%r.
proof. by conseq fqmul_ll (fqmul_corr_h _a _b). qed.

 (* ====================================================================
    W32 coefficient bounds and ring arithmetic
    bw32 a sz  :=  -2^sz <= to_sint a < 2^sz
    ==================================================================== *)

 op bw32 (a : W32.t) (sz : int) =
   - 2^sz <= W32.to_sint a /\ W32.to_sint a < 2^sz.

 lemma exp_max a b :
   0 <= a => 0 <= b =>
   2^a <= 2^(max a b) /\ 2^b <= 2^(max a b)
   by smt(StdOrder.IntOrder.ler_weexpn2l).

 (* Addition: if |a| < 2^asz and |b| < 2^bsz then |a+b| < 2^(max asz bsz + 1),
    provided both fit in W32 signed range (sz < 31).                          *)
 lemma add_corr (a b : W32.t) (asz bsz : int) :
   0 <= asz < 31 => 0 <= bsz < 31 =>
   bw32 a asz =>
   bw32 b bsz =>
   bw32 (a + b) (max asz bsz + 1).
 proof.
 pose aszb := 2^asz.
 pose bszb := 2^bsz.
 move => /= *.
 have /= bounds_asz : 0 < aszb <= 2^30
   by split; [ apply gt0_pow2
             | move => *; rewrite /aszb; apply StdOrder.IntOrder.ler_weexpn2l => /> /#].
 have /= bounds_bsz : 0 < bszb <= 2^30
   by split; [ apply gt0_pow2
             | move => *; rewrite /bszb; apply StdOrder.IntOrder.ler_weexpn2l => /> /#].
 rewrite /bw32 !to_sintD_small => />; first by smt().
 rewrite (Ring.IntID.exprS 2 (max asz bsz)); 1: by smt().
 by smt(exp_max).
 qed.

 (* Subtraction: |a - b| < 2^(max asz bsz + 1) under the same conditions.    *)
 lemma sub_corr (a b : W32.t) (asz bsz : int) :
   0 <= asz < 31 => 0 <= bsz < 31 =>
   bw32 a asz =>
   bw32 b bsz =>
   bw32 (a - b) (max asz bsz + 1).
 proof.
 pose aszb := 2^asz.
 pose bszb := 2^bsz.
 move => /= *.
 have /= bounds_asz : 0 < aszb <= 2^30
   by split; [ apply gt0_pow2
             | move => *; rewrite /aszb; apply StdOrder.IntOrder.ler_weexpn2l => /> /#].
 have /= bounds_bsz : 0 < bszb <= 2^30
   by split; [ apply gt0_pow2
             | move => *; rewrite /bszb; apply StdOrder.IntOrder.ler_weexpn2l => /> /#].
 rewrite /bw32 !to_sintB_small => />; first by smt().
 rewrite (Ring.IntID.exprS 2 (max asz bsz)); 1: by smt().
 by smt(exp_max).
 qed.

end Fq.
