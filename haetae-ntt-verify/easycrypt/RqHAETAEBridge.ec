require import AllCore IntDiv List Ring StdOrder.

require import Array256.
require import GFq Rq NTTFullSpectralAction NTTRowProductSpec.
require import HAETAE_Params HAETAE_Algebra.

import Zq IntOrder.

theory RqHAETAEBridge.

op rq_poly_repr (rp : Rq.poly) (hp : HAETAE_Algebra.poly) : bool =
  HAETAE_Algebra.poly_wf hp /\
  forall i,
    0 <= i < HAETAE_Params.n =>
    incoeff (HAETAE_Algebra.poly_coeff hp i) = rp.[i].

op row3 ['a] (x0 x1 x2 : 'a) (i : int) : 'a =
  if i = 0 then x0 else if i = 1 then x1 else x2.

lemma rq_poly_repr_coeff rp hp i :
  rq_poly_repr rp hp =>
  0 <= i < HAETAE_Params.n =>
  incoeff (HAETAE_Algebra.poly_coeff hp i) = rp.[i].
proof. by move=> [_ hrepr] hi; apply hrepr. qed.

lemma rq_poly_zero_repr :
  rq_poly_repr Rq.zero HAETAE_Algebra.poly_zero.
proof.
split.
+ exact HAETAE_Algebra.poly_zero_wf.
move=> i hi.
rewrite /HAETAE_Algebra.poly_coeff /HAETAE_Algebra.poly_zero nth_nseq 1:/#.
by rewrite /Rq.zero Array256.createiE 1:/#.
qed.

lemma rq_poly_repr_zero_left ap :
  rq_poly_repr ap HAETAE_Algebra.poly_zero =>
  ap = Rq.zero.
proof.
move=> hrepr.
apply Array256.ext_eq => i hi.
rewrite -(rq_poly_repr_coeff ap HAETAE_Algebra.poly_zero i hrepr) 1:/#.
rewrite /HAETAE_Algebra.poly_coeff /HAETAE_Algebra.poly_zero nth_nseq 1:/#.
by rewrite /Rq.zero Array256.createiE 1:/#.
qed.

lemma rq_add_get a b i :
  0 <= i < 256 =>
  (Rq.(&+) a b).[i] = a.[i] + b.[i].
proof.
move=> hi.
by rewrite /Rq.(&+) Array256.map2iE.
qed.

lemma rq_add_row3E a0 a1 a2 :
  NTTRowProductSpec.poly_sum 3 (row3 a0 a1 a2) =
  Rq.(&+) a0 (Rq.(&+) a1 a2).
proof.
apply Array256.ext_eq => i hi.
rewrite NTTRowProductSpec.poly_sum_get 1:hi.
rewrite (Rq.BigDom.BAdd.big_int_recl 2 0
  (fun k => (row3 a0 a1 a2 k).[i])) 1:/# /=.
rewrite (Rq.BigDom.BAdd.big_int_recl 1 0
  (fun k => (row3 a0 a1 a2 (k + 1)).[i])) 1:/# /=.
rewrite Rq.BigDom.BAdd.big_int1 /=.
rewrite /row3 /=.
rewrite rq_add_get 1:hi.
rewrite rq_add_get 1:hi.
ring.
qed.

lemma coefficient_row_product3E
    (a0 a1 a2 b0 b1 b2 : Rq.poly) :
  NTTRowProductSpec.coefficient_row_product 3
    (fun _ col => row3 a0 a1 a2 col)
    (row3 b0 b1 b2) 0 =
  Rq.(&+) (Rq.(&*) a0 b0)
    (Rq.(&+) (Rq.(&*) a1 b1) (Rq.(&*) a2 b2)).
proof.
apply Array256.ext_eq => i hi.
rewrite NTTRowProductSpec.coefficient_row_product_get 1:hi.
rewrite (Rq.BigDom.BAdd.big_int_recl 2 0
  (fun col => (Rq.(&*) (row3 a0 a1 a2 col) (row3 b0 b1 b2 col)).[i])) 1:/# /=.
rewrite (Rq.BigDom.BAdd.big_int_recl 1 0
  (fun k =>
    (Rq.(&*) (row3 a0 a1 a2 (k + 1)) (row3 b0 b1 b2 (k + 1))).[i])) 1:/# /=.
rewrite Rq.BigDom.BAdd.big_int1 /=.
rewrite /row3 /=.
rewrite rq_add_get 1:hi.
rewrite rq_add_get 1:hi.
ring.
qed.

lemma coefficient_row_product3_atE
    (a : int -> int -> Rq.poly) (b : int -> Rq.poly) row :
  NTTRowProductSpec.coefficient_row_product 3 a b row =
  Rq.(&+) (Rq.(&*) (a row 0) (b 0))
    (Rq.(&+) (Rq.(&*) (a row 1) (b 1))
      (Rq.(&*) (a row 2) (b 2))).
proof.
apply Array256.ext_eq => i hi.
rewrite NTTRowProductSpec.coefficient_row_product_get 1:hi.
rewrite (Rq.BigDom.BAdd.big_int_recl 2 0
  (fun col => (Rq.(&*) (a row col) (b col)).[i])) 1:/# /=.
rewrite (Rq.BigDom.BAdd.big_int_recl 1 0
  (fun k => (Rq.(&*) (a row (k + 1)) (b (k + 1))).[i])) 1:/# /=.
rewrite Rq.BigDom.BAdd.big_int1 /=.
rewrite rq_add_get 1:hi.
rewrite rq_add_get 1:hi.
ring.
qed.

lemma rq_add_dot3E (x0 x1 x2 : Rq.poly) :
  Rq.(&+) x0 (Rq.(&+) x1 x2) =
  Rq.(&+) (Rq.(&+) (Rq.(&+) Rq.zero x0) x1) x2.
proof.
apply Array256.ext_eq => i hi.
rewrite rq_add_get 1:hi.
rewrite rq_add_get 1:hi.
rewrite rq_add_get 1:hi.
rewrite rq_add_get 1:hi.
rewrite rq_add_get 1:hi.
rewrite /Rq.zero Array256.createiE 1:hi.
ring.
qed.

lemma rq_poly_add_repr
    (ap bp : Rq.poly)
    (ah bh : HAETAE_Algebra.poly) :
  rq_poly_repr ap ah =>
  rq_poly_repr bp bh =>
  rq_poly_repr (Rq.(&+) ap bp) (HAETAE_Algebra.poly_add ah bh).
proof.
move=> hrepr_a hrepr_b.
split.
+ exact (HAETAE_Algebra.poly_add_wf ah bh).
move=> i hi.
rewrite /HAETAE_Algebra.poly_add.
case: (ah = HAETAE_Algebra.poly_zero /\ bh = HAETAE_Algebra.poly_zero) => hzero /=.
+ have hrepr_a0 : rq_poly_repr ap HAETAE_Algebra.poly_zero by smt().
   have hrepr_b0 : rq_poly_repr bp HAETAE_Algebra.poly_zero by smt().
   rewrite /HAETAE_Algebra.poly_coeff /HAETAE_Algebra.poly_zero nth_nseq 1:/#.
   rewrite rq_add_get 1:hi.
   rewrite -(rq_poly_repr_coeff ap HAETAE_Algebra.poly_zero i hrepr_a0 hi).
   rewrite -(rq_poly_repr_coeff bp HAETAE_Algebra.poly_zero i hrepr_b0 hi).
   rewrite (rq_poly_repr_coeff Rq.zero HAETAE_Algebra.poly_zero i rq_poly_zero_repr hi).
   rewrite /Rq.zero Array256.createiE 1:hi.
   by rewrite ZqRing.add0r /Zq.zero.
have ha := rq_poly_repr_coeff ap ah i hrepr_a hi.
have hb := rq_poly_repr_coeff bp bh i hrepr_b hi.
rewrite /HAETAE_Algebra.coeff_add /HAETAE_Algebra.poly_coeff.
rewrite nth_mkseq 1:/# /=.
have hq : HAETAE_Params.q = GFq.q.
+ by rewrite /HAETAE_Params.q GFq.qE.
rewrite /HAETAE_Algebra.coeff_mod hq incoeffD_mod.
rewrite rq_add_get 1:hi.
by rewrite ha hb.
qed.

lemma incoeff_sumz (xs : int list) :
  incoeff (sumz xs) =
  foldr (fun x acc => incoeff x + acc) Zq.zero xs.
proof.
elim: xs => [|x xs ih] /=.
+ by rewrite /Zq.zero.
rewrite /sumz /=.
rewrite incoeffD -ih /sumz.
trivial.
qed.

lemma rq_poly_mul_term_repr
    (ap bp : Rq.poly)
    (ah bh : HAETAE_Algebra.poly)
    i j :
  rq_poly_repr ap ah =>
  rq_poly_repr bp bh =>
  0 <= i < HAETAE_Params.n =>
  0 <= j < HAETAE_Params.n =>
  incoeff (HAETAE_Algebra.poly_mul_term ah bh i j) =
  NTTFullSpectralAction.negacyclic_term ap bp i j.
proof.
move=> hrepr_a hrepr_b hi hj.
rewrite /HAETAE_Algebra.poly_mul_term /NTTFullSpectralAction.negacyclic_term.
case: (j <= i) => hij.
+ rewrite -(rq_poly_repr_coeff ap ah j hrepr_a hj).
   have hij_bounds : 0 <= i - j < HAETAE_Params.n by smt().
   rewrite -(rq_poly_repr_coeff bp bh (i - j) hrepr_b hij_bounds).
   rewrite incoeffM.
   by rewrite ifT 1:/#.
+ rewrite -(rq_poly_repr_coeff ap ah j hrepr_a hj).
  have hwrap_index :
    HAETAE_Params.n + i - j = 256 + (i - j).
  + by rewrite /HAETAE_Params.n; ring.
  rewrite hwrap_index.
  have hwrap_bounds :
    0 <= 256 + (i - j) < HAETAE_Params.n.
  + by rewrite /HAETAE_Params.n; smt().
  rewrite -(rq_poly_repr_coeff bp bh
    (256 + (i - j)) hrepr_b hwrap_bounds).
  rewrite ifF 1:/#.
  by rewrite incoeffN incoeffM.
qed.

lemma rq_poly_mul_terms_foldr_repr
    (ap bp : Rq.poly)
    (ah bh : HAETAE_Algebra.poly)
    i (js : int list) :
  rq_poly_repr ap ah =>
  rq_poly_repr bp bh =>
  0 <= i < HAETAE_Params.n =>
  (forall j, j \in js => 0 <= j < HAETAE_Params.n) =>
  foldr
    (fun j acc =>
      incoeff (HAETAE_Algebra.poly_mul_term ah bh i j) + acc)
    Zq.zero js =
  foldr
    (fun j acc =>
      NTTFullSpectralAction.negacyclic_term ap bp i j + acc)
    Zq.zero js.
proof.
move=> hrepr_a hrepr_b hi.
elim: js => [|j js ihjs] hjs //=.
have hj : 0 <= j < HAETAE_Params.n.
+ apply hjs.
  by rewrite /=.
have htail :
  foldr
    (fun k acc =>
      incoeff (HAETAE_Algebra.poly_mul_term ah bh i k) + acc)
    Zq.zero js =
  foldr
    (fun k acc =>
      NTTFullSpectralAction.negacyclic_term ap bp i k + acc)
    Zq.zero js.
+ apply ihjs => k hk.
  apply hjs.
  by rewrite /= hk orbT.
rewrite (rq_poly_mul_term_repr ap bp ah bh i j
  hrepr_a hrepr_b hi hj).
by rewrite htail.
qed.

lemma rq_mul_zero_left (bp : Rq.poly) :
  Rq.(&*) Rq.zero bp = Rq.zero.
proof.
apply Array256.ext_eq => i hi.
rewrite NTTFullSpectralAction.rq_mul_coeff_foldr_to_bigi 1:hi.
rewrite /Rq.zero Array256.createiE 1:hi.
rewrite Rq.BigDom.BAdd.big_seq_cond Rq.BigDom.BAdd.big1 //=.
move=> j [hj _].
rewrite /NTTFullSpectralAction.negacyclic_term /Rq.zero.
rewrite mem_range in hj.
case: (0 <= i - j) => hij.
+ by rewrite Array256.createiE 1:hj ZqRing.mul0r.
+ by rewrite Array256.createiE 1:/# ZqRing.mul0r ZqRing.oppr0.
qed.

lemma rq_mul_zero_right (ap : Rq.poly) :
  Rq.(&*) ap Rq.zero = Rq.zero.
proof.
apply Array256.ext_eq => i hi.
rewrite NTTFullSpectralAction.rq_mul_coeff_foldr_to_bigi 1:hi.
rewrite /Rq.zero Array256.createiE 1:hi.
rewrite Rq.BigDom.BAdd.big_seq_cond Rq.BigDom.BAdd.big1 //=.
move=> j [hj _].
rewrite /NTTFullSpectralAction.negacyclic_term /Rq.zero.
rewrite mem_range in hj.
case: (0 <= i - j) => hij.
+ by rewrite Array256.createiE 1:/# ZqRing.mulr0.
+ by rewrite Array256.createiE 1:/# ZqRing.mulr0 ZqRing.oppr0.
qed.

lemma rq_poly_mul_repr
    (ap bp : Rq.poly)
    (ah bh : HAETAE_Algebra.poly) :
  rq_poly_repr ap ah =>
  rq_poly_repr bp bh =>
  rq_poly_repr (Rq.(&*) ap bp) (HAETAE_Algebra.poly_mul ah bh).
proof.
move=> hrepr_a hrepr_b.
split.
+ exact (HAETAE_Algebra.poly_mul_wf ah bh).
move=> i hi.
rewrite /HAETAE_Algebra.poly_mul.
case: (ah = HAETAE_Algebra.poly_zero) => hahzero.
+ have hrepr_a0 : rq_poly_repr ap HAETAE_Algebra.poly_zero.
  + by rewrite -hahzero.
   have -> : ap = Rq.zero by exact (rq_poly_repr_zero_left ap hrepr_a0).
   rewrite ifT 1:/#.
   rewrite /HAETAE_Algebra.poly_coeff /HAETAE_Algebra.poly_zero nth_nseq 1:/#.
   by rewrite rq_mul_zero_left /Rq.zero Array256.createiE 1:hi.
case: (bh = HAETAE_Algebra.poly_zero) => hbhzero.
+ have hrepr_b0 : rq_poly_repr bp HAETAE_Algebra.poly_zero.
  + by rewrite -hbhzero.
   have -> : bp = Rq.zero by exact (rq_poly_repr_zero_left bp hrepr_b0).
   rewrite ifT 1:/#.
   rewrite /HAETAE_Algebra.poly_coeff /HAETAE_Algebra.poly_zero nth_nseq 1:/#.
   by rewrite rq_mul_zero_right /Rq.zero Array256.createiE 1:hi.
rewrite ifF 1:/#.
rewrite /HAETAE_Algebra.poly_coeff nth_mkseq 1:/# /=.
rewrite /HAETAE_Algebra.coeff_mod.
have hq : HAETAE_Params.q = GFq.q.
+ by rewrite /HAETAE_Params.q GFq.qE.
rewrite hq -incoeff_mod.
rewrite NTTFullSpectralAction.rq_mul_coeff_foldr_to_bigi 1:/#.
rewrite /Rq.BigDom.BAdd.big /range /= filter_predT foldr_map.
rewrite incoeff_sumz.
rewrite foldr_map /HAETAE_Params.n.
apply (rq_poly_mul_terms_foldr_repr ap bp ah bh i
  (iota_ 0 256) hrepr_a hrepr_b hi).
move=> j.
by rewrite mem_iota /HAETAE_Params.n; smt().
qed.

lemma rq_poly_dot3_repr
    (a0 a1 a2 b0 b1 b2 : Rq.poly)
    (ah0 ah1 ah2 bh0 bh1 bh2 : HAETAE_Algebra.poly) :
  rq_poly_repr a0 ah0 =>
  rq_poly_repr a1 ah1 =>
  rq_poly_repr a2 ah2 =>
  rq_poly_repr b0 bh0 =>
  rq_poly_repr b1 bh1 =>
  rq_poly_repr b2 bh2 =>
  rq_poly_repr
    (NTTRowProductSpec.coefficient_row_product 3
      (fun _ col => row3 a0 a1 a2 col)
      (row3 b0 b1 b2) 0)
    (HAETAE_Algebra.poly_dot [ah0; ah1; ah2] [bh0; bh1; bh2]).
proof.
move=> hrepr_a0 hrepr_a1 hrepr_a2 hrepr_b0 hrepr_b1 hrepr_b2.
rewrite coefficient_row_product3E.
rewrite rq_add_dot3E.
rewrite /HAETAE_Algebra.poly_dot /=.
have hmul0 := rq_poly_mul_repr a0 b0 ah0 bh0 hrepr_a0 hrepr_b0.
have hmul1 := rq_poly_mul_repr a1 b1 ah1 bh1 hrepr_a1 hrepr_b1.
have hmul2 := rq_poly_mul_repr a2 b2 ah2 bh2 hrepr_a2 hrepr_b2.
have hsum0 := rq_poly_add_repr
  Rq.zero (Rq.(&*) a0 b0)
  HAETAE_Algebra.poly_zero
  (HAETAE_Algebra.poly_mul ah0 bh0)
  rq_poly_zero_repr hmul0.
have hsum01 := rq_poly_add_repr
  (Rq.(&+) Rq.zero (Rq.(&*) a0 b0))
  (Rq.(&*) a1 b1)
  (HAETAE_Algebra.poly_add
    HAETAE_Algebra.poly_zero
    (HAETAE_Algebra.poly_mul ah0 bh0))
  (HAETAE_Algebra.poly_mul ah1 bh1)
  hsum0 hmul1.
have hsum012 := rq_poly_add_repr
  (Rq.(&+)
    (Rq.(&+) Rq.zero (Rq.(&*) a0 b0))
    (Rq.(&*) a1 b1))
  (Rq.(&*) a2 b2)
  (HAETAE_Algebra.poly_add
    (HAETAE_Algebra.poly_add
      HAETAE_Algebra.poly_zero
      (HAETAE_Algebra.poly_mul ah0 bh0))
    (HAETAE_Algebra.poly_mul ah1 bh1))
  (HAETAE_Algebra.poly_mul ah2 bh2)
  hsum01 hmul2.
exact hsum012.
qed.

end RqHAETAEBridge.
