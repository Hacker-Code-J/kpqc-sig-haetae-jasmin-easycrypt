(* Verification surface for the reference Jasmin extraction only.
   This file is intentionally narrower than NTTAlgebra.ec:
   it targets extract/Hpoly_extract.ec and stops at refinement to
   the imperative EasyCrypt NTT procedures in NTT_Fq.ec. *)

require import AllCore IntDiv CoreMap List Distr Ring StdOrder BitEncoding.
from Jasmin require import JWord JModel_x86.
import SLH64.

require import Array256 BArray1024.
require import Fq Fastexp.
require import GFq Rq.
require import Montgomery.
require import NTT_Fq.
require import Hpoly_extract.

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
  NTT_Fq.word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas i) * inv NTT_Fq.R =
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
  NTT_Fq.word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas_inv i) * inv NTT_Fq.R =
  NTT_Fq.zetas_inv.[i].
proof.
move=> hi.
rewrite -NTT_Fq.jzetas_inv_get 1:/#.
apply mont_inv_cancel.
have /mem_range hi' := hi.
by rewrite mem_range; smt().
qed.

lemma jzetas_inv_255_scale_cancel :
  NTT_Fq.word_to_coeff (BArray1024.get32 Hpoly_extract.jzetas_inv 255) * inv NTT_Fq.R =
  NTT_Fq.scale255 * NTT_Fq.R.
proof.
exact NTT_Fq.jzetas_inv_255_scaleE.
qed.

lemma fqmul_bw32_16 aa bb :
  - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb < Fq.SignedReductions.R %/ 2 * Fq.q =>
  hoare [Hpoly_extract.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    Fq.bw32 res 16].
proof.
move=> hbound.
conseq (Fq.fqmul_corr_h aa bb).
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
  hoare [Hpoly_extract.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    NTT_Fq.word_to_coeff res = incoeff aa * incoeff bb * inv NTT_Fq.R].
proof.
move=> hbound.
conseq (Fq.fqmul_corr_h aa bb).
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

lemma forward_twiddle_product
  rp p zc j len ai bi :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j + len < 256 =>
  W32.to_sint ai = W32.to_sint (BArray1024.get32 Hpoly_extract.jzetas zc) =>
  W32.to_sint bi = W32.to_sint (BArray1024.get32 rp (j + len)) =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint ai * W32.to_sint bi <
    Fq.SignedReductions.R %/ 2 * Fq.q =>
  hoare [Hpoly_extract.M.__fqmul :
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

lemma forward_twiddle_value
  rp p zc j len ai bi t :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_extract.jzetas zc =>
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

lemma forward_butterfly_repr
  rp p zc j len ai s b t asz bsz tsz :
  NTT_Fq.poly_repr rp p =>
  1 <= zc < 256 =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_extract.jzetas zc =>
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
  ai = BArray1024.get32 Hpoly_extract.jzetas zc =>
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

lemma inverse_twiddle_value
  rp p zc j len ai diff t :
  NTT_Fq.poly_repr rp p =>
  zc \in range 0 255 =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_extract.jzetas_inv zc =>
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

lemma inverse_butterfly_step_full
  rp p zc j len ai t0 coeff t asz bsz tsz :
  NTT_Fq.poly_repr rp p =>
  zc \in range 0 255 =>
  0 <= j < 256 =>
  0 < len =>
  0 <= j + len < 256 =>
  ai = BArray1024.get32 Hpoly_extract.jzetas_inv zc =>
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
  ai = BArray1024.get32 Hpoly_extract.jzetas_inv zc =>
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

(* Public Jasmin wrappers are trivial wrappers around the core routines.
   Keep these proofs self-contained because the root Hpoly_extract import
   exposes the procedures but not generated wrapper lemmas. *)

equiv poly_ntt_jazz_ref :
  Hpoly_extract.M.poly_ntt_jazz ~ Hpoly_extract.M._poly_ntt :
  ={rp} ==> ={res}.
proof.
proc.
inline*.
sim.
qed.

equiv poly_invntt_jazz_ref :
  Hpoly_extract.M.poly_invntt_jazz ~ Hpoly_extract.M._poly_invntt :
  ={rp} ==> ={res}.
proof.
proc.
inline*.
sim.
qed.

(* Narrow target for the remaining work:

   1. prove a direct forward core refinement
      Hpoly_extract.M._poly_ntt  ~  NTT_Fq.NTT.ntt

   2. prove a direct inverse core refinement
      Hpoly_extract.M._poly_invntt  ~  NTT_Fq.NTT.invntt

   under the bounded representation predicate `poly_repr_bound` from
   NTT_Fq.ec.  The bound component is necessary: the old field-only relation
   does not rule out signed W32 overflow in the add/sub butterfly stores. *)

end RefJasminNTT.
