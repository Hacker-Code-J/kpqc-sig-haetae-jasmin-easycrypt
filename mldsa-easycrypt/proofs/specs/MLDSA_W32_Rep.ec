require import AllCore IntDiv List.

from Jasmin require import JWord.

require import GFq Rq VecMat.
require import Array256.

import Parameters Round ZModQ Zq PolyLVec PolyKVec PolyMat.

(******************************************************)
(* Representations of polys as 32-bit word arrays     *)
(******************************************************)

type wpoly = W32.t Array256.t.

op liftu_wpoly (pw : wpoly) : poly =
  map (fun w => incoeff (W32.to_uint w)) pw.

op lifts_wpoly (pw : wpoly) : poly =
  map (fun w => incoeff (W32.to_sint w)) pw.

op unlift_poly (p : poly) : wpoly = map (fun c => W32.of_int (asint c)) p.

op poly_urng(b : int, p : poly) = all (fun i => 0 <= asint i < b) p.
op poly_srng(bl bh : int, p : poly) = all (fun i => -bl <= crepr i <= bh) p.

op wpoly_urng(b : int, pw : wpoly) = all (fun i => 0 <= W32.to_uint i < b) pw.
op wpoly_srng(bl bh : int, pw : wpoly) = all (fun i => -bl <= W32.to_sint i <= bh) pw.
op wpoly_infnorm_lt(b : int, pw : wpoly) = wpoly_srng (b-1) (b-1) pw.

(* Monotonicity: tighter wpoly_srng implies wider wpoly_srng *)
lemma wpoly_srng_widen (p : wpoly) (a1 b1 a2 b2 : int) :
  a1 <= a2 => b1 <= b2 => wpoly_srng a1 b1 p => wpoly_srng a2 b2 p.
proof.
rewrite /wpoly_srng !allP => Ha Hb H x Hx.
by have := H x Hx; smt().
qed.

(* ------------------------------------------------------------------ *)
(* Abstract range predicates for the three word-level polynomial ops.  *)
(*                                                                      *)
(* Each operation has an input range and an output range that may      *)
(* differ from each other and from the other operations' ranges.       *)
(* All six are left abstract here and will be made concrete once the   *)
(* NTT bridge lemmas are fully worked out.                             *)
(*                                                                      *)
(* Expected instantiation path:                                        *)
(*   ntt_orng  => bmul_irng   (NTT output is valid basemul input)      *)
(*   bmul_orng => intt_irng   (basemul output is valid INTT input)     *)
(*   intt_orng => wpoly_srng B_lo B_hi  (INTT output has concrete rng) *)
(* ------------------------------------------------------------------ *)
op wpoly_ntt_irng  : wpoly -> bool.  (* valid input  to   NTT   *)
op wpoly_ntt_orng  : wpoly -> bool.  (* valid output from NTT   *)
op wpoly_intt_irng : wpoly -> bool.  (* valid input  to   INTT  *)
op wpoly_bmul_irng : wpoly -> bool.  (* valid input  to   basemul *)

(* ------------------------------------------------------------------ *)
(* Abstract output bound of polynomial__invert_ntt_montgomery.          *)
(*                                                                      *)
(* The concrete value depends on the specific Montgomery-NTT impl;      *)
(* the correctness of the keygen/sign chain depends only on the         *)
(* compatibility axiom below, which expresses the design invariant      *)
(* that invNTT's output is tight enough that add(_, s2) stays within    *)
(* conditionally_add_modulus's physical tolerance [-q+1, q-1].          *)
(*                                                                      *)
(* Matches the comment in mldsa-native sign.c (mld_compute_t0_t1_tr...):*)
(*   "the output of the invntt [must be] small enough such that the     *)
(*    addition of s2 does not result in absolute values >= MLDSA_Q"     *)
(* ------------------------------------------------------------------ *)
op invntt_obound : int.
axiom invntt_obound_fits_for_caddq :
  0 <= invntt_obound /\ invntt_obound + Eta <= q - 1.

(* ------------------------------------------------------------------ *)
(* Bridge lemmas: relations between abstract range predicates.         *)
(* Admitted pending concrete instantiation of the abstract ops.        *)
(* ------------------------------------------------------------------ *)
lemma wpoly_ntt_orng_bmul_irng (p : wpoly) : wpoly_ntt_orng p => wpoly_bmul_irng p.
admitted. (* bridge ntt orng bmul irng *)
(* basemul outputs satisfy |to_sint coeff| < q (Barrett/Montgomery final step),
   which is sufficient input range for invNTT *)
lemma wpoly_bmul_orng_intt_irng (p : wpoly) : wpoly_srng (q-1) (q-1) p => wpoly_intt_irng p.
admitted. (* bridge bmul orng intt irng *)
(* Fully reduced coefficients (in [0,q)) are valid basemul inputs *)
lemma wpoly_urng_bmul_irng (p : wpoly) : wpoly_urng q p => wpoly_bmul_irng p.
admitted. (* bmul accepts fully reduced coeffs (redundant) *)
(* Coefficients with |x| < q (signed, centered or not) are valid NTT inputs *)
lemma wpoly_srng_ntt_irng (p : wpoly) : wpoly_srng (q-1) (q-1) p => wpoly_ntt_irng p.
admitted. (* ntt accepts -(q-1) .. q-1 (probably redundant) *)

lemma wpoly_urng_lifts_eq_liftu (p : wpoly) :
  wpoly_urng q p => lifts_wpoly p = liftu_wpoly p.
proof.
rewrite /wpoly_urng /lifts_wpoly /liftu_wpoly allP /= => H.
apply Array256.tP => j jb.
rewrite !mapiE 1,2:/# /=; congr.
have := H j jb => /= Hr.
rewrite W32.to_sintE /smod.
have -> /= : ! (2 ^ (32 - 1) <= to_uint p.[j]) by smt().
done.
qed.

lemma wpoly_infnorm_liftE (b : int) (pw : wpoly) :
    0 < b <= q %/ 2 =>
    wpoly_infnorm_lt b pw => infnorm_lt (lifts_wpoly pw) b.
move => Hb.
rewrite /wpoly_infnorm_lt /infnorm_lt /wpoly_srng /lifts_wpoly !allP /=.
move => H j; rewrite mem_iota /= => Hj; have := H j _; 1: smt().
rewrite mapiE 1:/# /=.
move => [Hl Hr]; have /# := incoeffK_centered (to_sint pw.[j]) _; 1: smt().
qed.

lemma wpoly_infnorm_unliftE (b bl bh : int) (pw : wpoly) :
    0 < b <= q %/ 2 =>
    bl <= q %/ 2 => bh <= q %/ 2 =>
    wpoly_srng bl bh pw =>
    infnorm_lt (lifts_wpoly pw) b => wpoly_infnorm_lt b pw.
proof.
move => Hb Hbl Hbh Hrng Hinf.
rewrite /wpoly_infnorm_lt /wpoly_srng allP => k Hk.
move: Hinf; rewrite /infnorm_lt /lifts_wpoly allP /= => Hinf.
have /= Hk' := Hinf k _; 1: smt(mem_iota).
rewrite mapiE 1:/# /= in Hk'.
move: Hrng; rewrite /wpoly_srng allP => Hrng.
have /= Hrng_k := Hrng k _; 1: smt().
by have /# := incoeffK_centered (to_sint pw.[k]) _; 1: smt().
qed.


type wpolylvec = wpoly LArray.t.

op liftu_wpolylvec(wv : wpolylvec) : polylvec =
  map liftu_wpoly wv.

op lifts_wpolylvec (wv : wpolylvec) : polylvec =
  map lifts_wpoly wv.

op unlift_polylvec (v : polylvec) : wpolylvec = map unlift_poly v.

op polylvec_urng(p : polylvec, b : int) = all (poly_urng b) p.
op polylvec_srng(p : polylvec, bl bh : int) = all (poly_srng bl bh) p.

op wpolylvec_urng(pw : wpolylvec, b : int) = all (wpoly_urng b) pw.
op wpolylvec_srng(pw : wpolylvec, bl bh : int) = all (wpoly_srng bl bh) pw.
op wpolylvec_infnorm_lt(b : int, pw : wpolylvec) = wpolylvec_srng pw (b-1) (b-1).
op wpolylvec_ntt_irng (pw : wpolylvec) = all wpoly_ntt_irng  pw.
op wpolylvec_ntt_orng (pw : wpolylvec) = all wpoly_ntt_orng  pw.
op wpolylvec_intt_irng(pw : wpolylvec) = all wpoly_intt_irng pw.
op wpolylvec_bmul_irng(pw : wpolylvec) = all wpoly_bmul_irng pw.

lemma wpolylvec_ntt_orng_bmul_irng (pv : wpolylvec) :
  wpolylvec_ntt_orng pv => wpolylvec_bmul_irng pv.
proof.
rewrite /wpolylvec_ntt_orng /wpolylvec_bmul_irng !allP.
by move => H p Hp; exact (wpoly_ntt_orng_bmul_irng pv.[p] (H p Hp)).
qed.

lemma wpolylvec_srng_ntt_irng (pv : wpolylvec) :
  wpolylvec_srng pv (q-1) (q-1) => wpolylvec_ntt_irng pv.
proof.
rewrite /wpolylvec_srng /wpolylvec_ntt_irng !allP.
by move => H p Hp; exact (wpoly_srng_ntt_irng pv.[p] (H p Hp)).
qed.

(* Monotonicity of wpolylvec_srng *)
lemma wpolylvec_srng_widen (pv : wpolylvec) (a1 b1 a2 b2 : int) :
  a1 <= a2 => b1 <= b2 => wpolylvec_srng pv a1 b1 => wpolylvec_srng pv a2 b2.
proof.
rewrite /wpolylvec_srng !allP => Ha Hb H p Hp.
by apply (wpoly_srng_widen pv.[p] a1 b1 a2 b2 Ha Hb); apply H.
qed.

lemma wpolylvec_bmul_orng_intt_irng (pv : wpolylvec) :
  wpolylvec_srng pv (q-1) (q-1) => wpolylvec_intt_irng pv.
proof.
rewrite /wpolylvec_srng /wpolylvec_intt_irng !allP.
by move => H p Hp; exact (wpoly_bmul_orng_intt_irng pv.[p] (H p Hp)).
qed.

lemma wpolylvec_infnorm_liftE (b : int) (pw : wpolylvec) :
    0 < b <= q %/ 2 =>
    wpolylvec_infnorm_lt b pw => PolyLVec.infnorm_lt (lifts_wpolylvec pw) b.
proof.
move => Hb.
rewrite /wpolylvec_infnorm_lt /wpolylvec_srng /lifts_wpolylvec allP /= => H.
rewrite /infnorm_lt allP => i; rewrite mem_iota /= => Hi.
rewrite allP => k; rewrite mem_iota /= => Hk.
rewrite mapiE 1:/# /= mapiE 1:/# /=.
have := H i _; 1: smt().
rewrite /wpoly_srng allP => Hi'.
have /= := Hi' k _; 1: smt().
by  have /# := incoeffK_centered (to_sint pw.[i].[k]) _; 1: smt().
qed.

(* Reverse direction: spec infnorm implies word infnorm, given range ensuring incoeffK_centered applies *)
lemma wpolylvec_infnorm_unliftE (b bl bh : int) (pw : wpolylvec) :
    0 < b <= q %/ 2 =>
    bl + 1 <= q %/ 2 => bh <= q %/ 2 =>
    wpolylvec_srng pw bl bh =>
    PolyLVec.infnorm_lt (lifts_wpolylvec pw) b => wpolylvec_infnorm_lt b pw.
proof.
move => Hb Hbl Hbh Hrng Hinf.
rewrite /wpolylvec_infnorm_lt /wpolylvec_srng allP => i  Hi.
rewrite /wpoly_srng allP => k /= Hk.
move: Hinf; rewrite /PolyLVec.infnorm_lt /lifts_wpolylvec allP /= => Hinf.
have /= Hi' := Hinf i _; 1: smt(mem_iota).
move: Hi'; rewrite allP /= => Hi'.
have /= Hk' := Hi' k _; 1: smt(mem_iota).
rewrite mapiE 1:/# /= in Hk'.
move: Hrng; rewrite /wpolylvec_srng allP => Hrng.
have /= Hrng_i := Hrng i _; 1: smt().
move: Hrng_i; rewrite /wpoly_srng allP => /= Hrng_i.
have /= Hrng_k := Hrng_i k _; 1: smt().
have := Hk'; rewrite /lifts_wpoly mapiE 1:/# /=.
by  have/#  := incoeffK_centered (to_sint pw.[i].[k]) _; 1: smt().
qed.


type wpolykvec = wpoly KArray.t. 

op liftu_wpolykvec(wv : wpolykvec) : polykvec =
  map liftu_wpoly wv.

op lifts_wpolykvec (wv : wpolykvec) : polykvec =
  map lifts_wpoly wv.

op unlift_polykvec (v : polykvec) : wpolykvec = map unlift_poly v.

op polykvec_urng(p : polykvec, b : int) = all (poly_urng b) p.
op polykvec_srng(p : polykvec, bl bh : int) = all (poly_srng bl bh) p.

op wpolykvec_urng(pw : wpolykvec, b : int) = all (wpoly_urng b) pw.
op wpolykvec_srng(pw : wpolykvec, bl bh : int) = all (wpoly_srng bl bh) pw.
op wpolykvec_infnorm_lt(b : int, pw : wpolykvec) = wpolykvec_srng pw (b-1) (b-1).
op wpolykvec_ntt_irng (pw : wpolykvec) = all wpoly_ntt_irng  pw.
op wpolykvec_ntt_orng (pw : wpolykvec) = all wpoly_ntt_orng  pw.
op wpolykvec_intt_irng(pw : wpolykvec) = all wpoly_intt_irng pw.
op wpolykvec_bmul_irng(pw : wpolykvec) = all wpoly_bmul_irng pw.

lemma wpolykvec_ntt_orng_bmul_irng (pv : wpolykvec) :
  wpolykvec_ntt_orng pv => wpolykvec_bmul_irng pv.
proof.
rewrite /wpolykvec_ntt_orng /wpolykvec_bmul_irng !allP.
by move => H p Hp; exact (wpoly_ntt_orng_bmul_irng pv.[p] (H p Hp)).
qed.

lemma wpolykvec_bmul_orng_intt_irng (pv : wpolykvec) :
  wpolykvec_srng pv (q-1) (q-1) => wpolykvec_intt_irng pv.
proof.
rewrite /wpolykvec_srng /wpolykvec_intt_irng !allP.
by move => H p Hp; exact (wpoly_bmul_orng_intt_irng pv.[p] (H p Hp)).
qed.

lemma wpolykvec_srng_ntt_irng (pv : wpolykvec) :
  wpolykvec_srng pv (q-1) (q-1) => wpolykvec_ntt_irng pv.
proof.
rewrite /wpolykvec_srng /wpolykvec_ntt_irng !allP.
by move => H p Hp; exact (wpoly_srng_ntt_irng pv.[p] (H p Hp)).
qed.

(* Monotonicity of wpolykvec_urng *)
lemma wpolykvec_urng_widen (pv : wpolykvec) (b1 b2 : int) :
  b1 <= b2 => wpolykvec_urng pv b1 => wpolykvec_urng pv b2.
proof.
move => Hb; rewrite /wpolykvec_urng !allP => H p Hp.
by have := H p Hp; rewrite /wpoly_urng !allP; smt().
qed.

(* Fully reduced kvec coefficients give liftu = lifts *)
lemma wpolykvec_urng_lifts_eq_liftu (pv : wpolykvec) :
  wpolykvec_urng pv q => lifts_wpolykvec pv = liftu_wpolykvec pv.
proof.
rewrite /wpolykvec_urng KArray.allP => H.
rewrite /lifts_wpolykvec /liftu_wpolykvec.
apply KArray.tP => k kb.
rewrite !mapiE 1,2:/# /=.
by apply wpoly_urng_lifts_eq_liftu; apply (H k _); smt().
qed.

(* Monotonicity of wpolykvec_srng *)
lemma wpolykvec_srng_widen (pv : wpolykvec) (a1 b1 a2 b2 : int) :
  a1 <= a2 => b1 <= b2 => wpolykvec_srng pv a1 b1 => wpolykvec_srng pv a2 b2.
proof.
rewrite /wpolykvec_srng !allP => Ha Hb H p Hp.
by apply (wpoly_srng_widen pv.[p] a1 b1 a2 b2 Ha Hb); apply H.
qed.

lemma wpolykvec_infnorm_liftE (b : int) (pw : wpolykvec) :
    0 < b <= q %/ 2 =>
    wpolykvec_infnorm_lt b pw => PolyKVec.infnorm_lt (lifts_wpolykvec pw) b.
proof.
move => Hb.
rewrite /wpolykvec_infnorm_lt /wpolykvec_srng /lifts_wpolykvec allP /= => H.
rewrite /infnorm_lt allP => i; rewrite mem_iota /= => Hi.
rewrite allP => k; rewrite mem_iota /= => Hk.
rewrite mapiE 1:/# /= mapiE 1:/# /=.
have := H i _; 1: smt().
rewrite /wpoly_srng allP => Hi'.
have /= := Hi' k _; 1: smt().
by  have /# := incoeffK_centered (to_sint pw.[i].[k]) _; 1: smt().
qed.

lemma wpolykvec_infnorm_unliftE (b bl bh : int) (pw : wpolykvec) :
    0 < b <= q %/ 2 =>
    bl <= q %/ 2 => bh <= q %/ 2 =>
    wpolykvec_srng pw bl bh =>
    PolyKVec.infnorm_lt (lifts_wpolykvec pw) b => wpolykvec_infnorm_lt b pw.
proof.
move => Hb Hbl Hbh Hrng Hinf.
rewrite /wpolykvec_infnorm_lt /wpolykvec_srng allP => i Hi.
rewrite /wpoly_srng allP => k /= Hk.
move: Hinf; rewrite /PolyKVec.infnorm_lt /lifts_wpolykvec allP /= => Hinf.
have /= Hi' := Hinf i _; 1: smt(mem_iota).
move: Hi'; rewrite allP /= => Hi'.
have /= Hk' := Hi' k _; 1: smt(mem_iota).
rewrite mapiE 1:/# /= in Hk'.
move: Hrng; rewrite /wpolykvec_srng allP => Hrng.
have /= Hrng_i := Hrng i _; 1: smt().
move: Hrng_i; rewrite /wpoly_srng allP => /= Hrng_i.
have /= Hrng_k := Hrng_i k _; 1: smt().
have := Hk'; rewrite /lifts_wpoly mapiE 1:/# /=.
by have /# := incoeffK_centered (to_sint pw.[i].[k]) _; 1: smt().
qed.

type wpolymat = wpoly KLMatrix.t.

op liftu_wpolymat(wv : wpolymat) : polymat =
  map liftu_wpoly wv.

op lifts_wpolymat (wv : wpolymat) : polymat =
  map lifts_wpoly wv.

op unlift_polymat (v : polymat) : wpolymat = map unlift_poly v.

op polymat_urng(p : polymat, b : int) = all (poly_urng b) p.
op polymat_srng(p : polymat, bl bh : int) = all (poly_srng bl bh) p.

op wpolymat_urng(pw : wpolymat, b : int) = all (wpoly_urng b) pw.
op wpolymat_srng(pw : wpolymat, bl bh : int) = all (wpoly_srng bl bh) pw.
