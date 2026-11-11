require import AllCore IntDiv List Ring StdOrder BitEncoding.
require import Array256 GFq Rq NTT_Fq NTTFullSpec NTTFullAlgebra NTTProductExpansion.

import Zq IntOrder BitReverse.

theory NTTTransformAlgebra.

op pointwise (p q : Rq.poly) : Rq.poly =
  Array256.map2 (fun x y => x * y) p q.

op scale (c : coeff) (p : Rq.poly) : Rq.poly =
  Array256.map (fun x => c * x) p.

lemma pointwiseE p q i : 0 <= i < 256 =>
  (pointwise p q).[i] = p.[i] * q.[i].
proof. by move=> hi; rewrite /pointwise Array256.map2iE. qed.

lemma scaleE c p i : 0 <= i < 256 =>
  (scale c p).[i] = c * p.[i].
proof. by move=> hi; rewrite /scale Array256.mapiE. qed.

lemma full_ntt_scale c p :
  NTTFullSpec.full_ntt (scale c p) = scale c (NTTFullSpec.full_ntt p).
proof.
apply Array256.ext_eq => i hi.
rewrite /NTTFullSpec.full_ntt scaleE 1:hi !Array256.initiE 1,2:hi.
rewrite Rq.BigDom.BAdd.mulr_sumr.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
rewrite scaleE 1:hj.
by ring.
qed.

lemma full_invntt_scale c p :
  NTTFullSpec.full_invntt (scale c p) = scale c (NTTFullSpec.full_invntt p).
proof.
apply Array256.ext_eq => i hi.
rewrite /NTTFullSpec.full_invntt scaleE 1:hi !Array256.initiE 1,2:hi.
rewrite Rq.BigDom.BAdd.mulr_sumr.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
rewrite scaleE 1:hj.
by ring.
qed.

lemma zroot_odd_multiple d e m :
  0 <= e => e %% 2 = 1 => 2*d*m = 256*e =>
  Zq.exp zroot (2*d) <> Zq.one.
proof.
move=> he heodd hexp.
apply/negP=> hroot.
have h : Zq.exp (Zq.exp zroot (2*d)) m = Zq.exp Zq.one m by rewrite hroot.
rewrite -ZqField.exprM hexp ZqField.exprM NTT_Fq.exp_zroot_256 in h.
rewrite NTTFullAlgebra.incoeff_m1 -ZqRing.signr_odd 1:he in h.
have ho : odd e by rewrite oddP heodd.
by move: h; rewrite ho /= ZqRing.expr1 ZqRing.expr1z
 -NTTFullAlgebra.incoeff_m1 /Zq.one -eq_incoeff /q /=.
qed.

lemma even_div_step d c :
  0 < c => d = c * (d %/ c) => d %/ c %% 2 <> 1 =>
  d = (2*c) * (d %/ (2*c)).
proof.
move=> hc hd he.
have hr : 0 <= d %/ c %% 2 < 2 by smt(modz_ge0 ltz_pmod).
have hq := divz_eq (d %/ c) 2.
have hm := divz_mul d c 2 _.
+ by smt().
smt().
qed.

lemma zroot_even_nontrivial d : 1 <= d < 256 =>
  Zq.exp zroot (2*d) <> Zq.one.
proof.
move=> hd.
have hd1 : d = 1 * (d %/ 1) by rewrite divz1.
case (d %/ 1 %% 2 = 1) => h0.
+ apply (zroot_odd_multiple d (d %/ 1) 128); smt(divz_ge0).
have hd2 := even_div_step d 1 _ hd1 h0.
+ by [].
case (d %/ 2 %% 2 = 1) => h1.
+ apply (zroot_odd_multiple d (d %/ 2) 64); smt(divz_ge0).
have hd4 := even_div_step d 2 _ hd2 h1.
+ by [].
case (d %/ 4 %% 2 = 1) => h2.
+ apply (zroot_odd_multiple d (d %/ 4) 32); smt(divz_ge0).
have hd8 := even_div_step d 4 _ hd4 h2.
+ by [].
case (d %/ 8 %% 2 = 1) => h3.
+ apply (zroot_odd_multiple d (d %/ 8) 16); smt(divz_ge0).
have hd16 := even_div_step d 8 _ hd8 h3.
+ by [].
case (d %/ 16 %% 2 = 1) => h4.
+ apply (zroot_odd_multiple d (d %/ 16) 8); smt(divz_ge0).
have hd32 := even_div_step d 16 _ hd16 h4.
+ by [].
case (d %/ 32 %% 2 = 1) => h5.
+ apply (zroot_odd_multiple d (d %/ 32) 4); smt(divz_ge0).
have hd64 := even_div_step d 32 _ hd32 h5.
+ by [].
case (d %/ 64 %% 2 = 1) => h6.
+ apply (zroot_odd_multiple d (d %/ 64) 2); smt(divz_ge0).
have hd128 := even_div_step d 64 _ hd64 h6.
+ by [].
case (d %/ 128 %% 2 = 1) => h7.
+ apply (zroot_odd_multiple d (d %/ 128) 1); smt(divz_ge0).
have hd256 := even_div_step d 128 _ hd128 h7.
+ by [].
have hz : d %/ 256 = 0 by apply divz_small; smt().
by smt().
qed.

lemma zroot_even_nontrivial_signed d :
  -256 < d < 256 => d <> 0 => Zq.exp zroot (2*d) <> Zq.one.
proof.
move=> hd hn.
case (0 < d) => hp.
+ apply zroot_even_nontrivial; smt().
have h := zroot_even_nontrivial (d+256) _.
+ by smt().
have he : 2*(d+256) = 2*d + 512*1 by ring.
by move: h; rewrite he NTTFullAlgebra.exp_zroot_mod512.
qed.

lemma geometric_256 x :
  x <> Zq.one => Zq.exp x 256 = Zq.one =>
  Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp x j) 0 256 = Zq.zero.
proof.
move=> hn hx.
have hs := Rq.BigDom.subrXX Zq.one x 256 _.
+ by [].
have he : Rq.BigDom.BAdd.bigi predT
  (fun j => Zq.exp Zq.one (256-1-j) * Zq.exp x j) 0 256 =
  Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp x j) 0 256.
+ apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
  by rewrite ZqRing.expr1z ZqRing.mul1r.
move: hs; rewrite he.
change (Zq.exp Zq.one 256 - Zq.exp x 256 =
  (Zq.one - x) * Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp x j) 0 256 =>
  Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp x j) 0 256 = Zq.zero).
rewrite ZqRing.expr1z hx ZqRing.subrr eq_sym ZqField.mulf_eq0.
have hne : Zq.one - x <> Zq.zero by rewrite ZqRing.subr_eq0; smt().
by rewrite hne /=.
qed.

lemma zroot_even_geometric d : -256 < d < 256 => d <> 0 =>
  Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp zroot (2*d*j)) 0 256 = Zq.zero.
proof.
move=> hd hn.
have he : Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp zroot (2*d*j)) 0 256 =
  Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp (Zq.exp zroot (2*d)) j) 0 256.
+ apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
  by rewrite ZqField.exprM.
rewrite he; apply geometric_256.
+ by apply zroot_even_nontrivial_signed.
rewrite -ZqField.exprM.
have -> : 2*d*256 = 512*d by ring.
by apply NTTFullAlgebra.exp_zroot_512_mul.
qed.

lemma sum_br (f : int -> coeff) :
  Rq.BigDom.BAdd.bigi predT (fun j => f (br j)) 0 256 =
  Rq.BigDom.BAdd.bigi predT f 0 256.
proof.
have hperm : perm_eq (range 0 256) (map (bsrev 8) (range 0 256)).
+ rewrite perm_eq_sym.
  have h := bsrev_range_pow2_perm_eq 8 8 _.
  + by [].
  move: h; rewrite !NTTFullSpec.pow2_8 /=.
  have -> : map (( * ) 1) (range 0 256) = range 0 256.
  + by apply/id_map => x; ring.
  by [].
rewrite (Rq.BigDom.BAdd.eq_big_perm _ _ (range 0 256)
  (map (bsrev 8) (range 0 256))) 1:hperm.
rewrite Rq.BigDom.BAdd.big_mapT.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
by rewrite /br NTTFullSpec.bsrev8_involutive_256 1:mem_range.
qed.

lemma character_sum d : -256 < d < 256 =>
  Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp zroot ((2*br j+1)*d)) 0 256 =
  if d = 0 then incoeff 256 else Zq.zero.
proof.
move=> hd.
rewrite (sum_br (fun j => Zq.exp zroot ((2*j+1)*d))).
case (d = 0) => hd0.
+ rewrite hd0 /=.
  have he : Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp zroot ((2*j+1)*0)) 0 256 =
    Rq.BigDom.BAdd.bigi predT (fun _ => Zq.one) 0 256.
  + apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
    by rewrite ZqRing.expr0.
  rewrite he Rq.BigDom.BAdd.sumri_const 1:// /=.
  have h := intmul_asint (incoeff 256).
  by move: h; rewrite incoeffK /q /= eq_sym.
have he : Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp zroot ((2*j+1)*d)) 0 256 =
  Zq.exp zroot d *
  Rq.BigDom.BAdd.bigi predT (fun j => Zq.exp zroot (2*d*j)) 0 256.
+ rewrite Rq.BigDom.BAdd.mulr_sumr.
  apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
  have -> : (2*j+1)*d = d + 2*d*j by ring.
  rewrite ZqField.exprD.
  + by rewrite /zroot /Zq.zero -eq_incoeff /q.
  by [].
by rewrite he zroot_even_geometric 1:hd 1:hd0 ?ZqRing.mulr0.
qed.

lemma zroot_neq0 : zroot <> Zq.zero.
proof. by rewrite /zroot /Zq.zero -eq_incoeff /q. qed.

lemma inv256_mul : inv (incoeff 256) * incoeff 256 = Zq.one.
proof.
apply ZqField.mulVf.
by rewrite /Zq.zero -eq_incoeff /q.
qed.

lemma full_invntt_full_ntt p :
  NTTFullSpec.full_invntt (NTTFullSpec.full_ntt p) = p.
proof.
apply Array256.ext_eq => i hi.
rewrite /NTTFullSpec.full_invntt Array256.initiE 1:hi.
have he : Rq.BigDom.BAdd.bigi predT
  (fun j => inv (incoeff 256) * (NTTFullSpec.full_ntt p).[j] *
    Zq.exp zroot (-((2*br j+1)*i))) 0 256 =
  Rq.BigDom.BAdd.bigi predT (fun j =>
    Rq.BigDom.BAdd.bigi predT (fun k =>
      inv (incoeff 256) * p.[k] * Zq.exp zroot ((2*br j+1)*(k-i))) 0 256) 0 256.
+ apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
  rewrite /NTTFullSpec.full_ntt Array256.initiE 1:hj.
  rewrite Rq.BigDom.BAdd.mulr_sumr Rq.BigDom.BAdd.mulr_suml.
  apply Rq.BigDom.BAdd.eq_big_int => k hk /=.
  have hx : Zq.exp zroot ((2*br j+1)*(k-i)) =
    Zq.exp zroot ((2*br j+1)*k) * Zq.exp zroot (-((2*br j+1)*i)).
  + have -> : (2*br j+1)*(k-i) = (2*br j+1)*k + -((2*br j+1)*i) by ring.
    by rewrite ZqField.exprD 1:zroot_neq0.
  rewrite hx; ring.
change (Rq.BigDom.BAdd.bigi predT
  (fun j => inv (incoeff 256) * (NTTFullSpec.full_ntt p).[j] *
    Zq.exp zroot (-((2*br j+1)*i))) 0 256 = p.[i]).
rewrite he Rq.BigDom.BAdd.exchange_big.
have hs : Rq.BigDom.BAdd.bigi predT (fun k =>
  Rq.BigDom.BAdd.bigi predT (fun j =>
    inv (incoeff 256) * p.[k] * Zq.exp zroot ((2*br j+1)*(k-i))) 0 256) 0 256 =
  Rq.BigDom.BAdd.bigi predT (fun k =>
    if k = i then p.[i] else Zq.zero) 0 256.
+ apply Rq.BigDom.BAdd.eq_big_int => k hk /=.
  rewrite -Rq.BigDom.BAdd.mulr_sumr character_sum 1:/#.
  case (k = i) => hki.
  + rewrite hki /=.
    have -> : inv (incoeff 256) * p.[i] * incoeff 256 =
      (inv (incoeff 256) * incoeff 256) * p.[i] by ring.
    by rewrite inv256_mul ZqRing.mul1r.
  have -> : k-i <> 0 by smt().
  by rewrite /= ZqRing.mulr0.
rewrite hs (Rq.BigDom.BAdd.bigD1 _ _ i) 1:mem_range 1:hi 1:range_uniq /=.
have hz : Rq.BigDom.BAdd.big (predC1 i)
  (fun k => if k=i then p.[i] else Zq.zero) (range 0 256) = Zq.zero.
+ apply Rq.BigDom.BAdd.big1 => k hk /=.
  by case (k=i); smt().
by rewrite hz ZqRing.addr0.
qed.

lemma scale_scale c d p : scale c (scale d p) = scale (c*d) p.
proof.
apply Array256.ext_eq => i hi.
rewrite !scaleE //.
by ring.
qed.

lemma scale_one p : scale Zq.one p = p.
proof.
apply Array256.ext_eq => i hi.
by rewrite scaleE // ZqRing.mul1r.
qed.

lemma array256_mont_scale p : NTT_Fq.array256_mont p = scale NTT_Fq.R p.
proof.
apply Array256.ext_eq => i hi.
rewrite /NTT_Fq.array256_mont Array256.mapiE // scaleE //.
by rewrite /= ZqRing.mulrC.
qed.

lemma full_invntt_mont_cancel p :
  NTT_Fq.array256_mont (NTTFullSpec.full_invntt (scale (inv NTT_Fq.R) p)) =
  NTTFullSpec.full_invntt p.
proof.
rewrite full_invntt_scale array256_mont_scale scale_scale.
have hr : NTT_Fq.R * inv NTT_Fq.R = Zq.one.
+ by apply ZqRing.mulrV; exact NTT_Fq.unit_R.
by rewrite hr scale_one.
qed.

op evaluation (p : Rq.poly) (w : coeff) =
  Rq.BigDom.BAdd.bigi predT (fun j => p.[j] * Zq.exp w j) 0 256.

lemma full_ntt_evaluation p i : 0 <= i < 256 =>
  (NTTFullSpec.full_ntt p).[i] = evaluation p (Zq.exp zroot (2*br i+1)).
proof.
move=> hi; rewrite /NTTFullSpec.full_ntt Array256.initiE // /evaluation.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
by rewrite -ZqField.exprM.
qed.

lemma ntt_root_negacyclic i :
  Zq.exp (Zq.exp zroot (2*br i+1)) 256 = -Zq.one.
proof.
rewrite -ZqField.exprM.
have -> : (2*br i+1)*256 = 256 + 512*br i by ring.
by rewrite NTTFullAlgebra.exp_zroot_mod512 NTT_Fq.exp_zroot_256 NTTFullAlgebra.incoeff_m1.
qed.

lemma evaluation_mul_from_shift p q w :
  (forall k, 0 <= k < 256 =>
    Rq.BigDom.BAdd.bigi predT (fun i =>
      (if 0 <= i-k then q.[i-k] else -q.[256+(i-k)]) * Zq.exp w i) 0 256 =
    Zq.exp w k * evaluation q w) =>
  evaluation (p &* q) w = evaluation p w * evaluation q w.
proof.
move=> hshift.
rewrite /evaluation.
have he : Rq.BigDom.BAdd.bigi predT (fun i => (p &* q).[i] * Zq.exp w i) 0 256 =
  Rq.BigDom.BAdd.bigi predT (fun i =>
    Rq.BigDom.BAdd.bigi predT (fun k =>
      p.[k] * ((if 0 <= i-k then q.[i-k] else -q.[256+(i-k)]) * Zq.exp w i)) 0 256) 0 256.
+ apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
  rewrite NTTProductExpansion.rq_mul_coeff // Rq.BigDom.BAdd.mulr_suml.
  apply Rq.BigDom.BAdd.eq_big_int => k hk /=.
  by case (0 <= i-k) => h /=; ring.
rewrite he Rq.BigDom.BAdd.exchange_big.
have hs : Rq.BigDom.BAdd.bigi predT (fun k =>
    Rq.BigDom.BAdd.bigi predT (fun i =>
      p.[k] * ((if 0 <= i-k then q.[i-k] else -q.[256+(i-k)]) * Zq.exp w i)) 0 256) 0 256 =
  Rq.BigDom.BAdd.bigi predT (fun k => p.[k] * (Zq.exp w k * evaluation q w)) 0 256.
+ apply Rq.BigDom.BAdd.eq_big_int => k hk /=.
  by rewrite -Rq.BigDom.BAdd.mulr_sumr hshift.
rewrite hs -/evaluation Rq.BigDom.BAdd.mulr_suml.
apply Rq.BigDom.BAdd.eq_big_int => k hk /=.
rewrite /evaluation.
by ring.
qed.

lemma shift_evaluation q w k : Zq.exp w 256 = -Zq.one => 0 <= k < 256 =>
  Rq.BigDom.BAdd.bigi predT (fun i =>
    (if 0 <= i-k then q.[i-k] else -q.[256+(i-k)]) * Zq.exp w i) 0 256 =
  Zq.exp w k * evaluation q w.
proof.
move=> hw hk.
have hw0 : w <> Zq.zero.
+ have hp : Zq.exp w 256 <> Zq.zero.
  + by rewrite hw ZqRing.oppr_eq0 ZqRing.oner_neq0.
  by move: hp; rewrite ZqField.expf_eq0 /=.
have hhigh : Rq.BigDom.BAdd.bigi predT (fun i => q.[i-k] * Zq.exp w i) k 256 =
  Zq.exp w k * Rq.BigDom.BAdd.bigi predT (fun j => q.[j] * Zq.exp w j) 0 (256-k).
+ rewrite (Rq.BigDom.BAdd.big_addn 0 256 k) /= Rq.BigDom.BAdd.mulr_sumr.
  apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
  have -> : j+k-k = j by ring.
  rewrite (ZqField.exprD w j k hw0).
  by ring.
have hlow : Rq.BigDom.BAdd.bigi predT (fun i => -q.[256+(i-k)] * Zq.exp w i) 0 k =
  Zq.exp w k * Rq.BigDom.BAdd.bigi predT (fun j => q.[j] * Zq.exp w j) (256-k) 256.
+ rewrite Rq.BigDom.BAdd.mulr_sumr (Rq.BigDom.BAdd.big_addn 0 256 (256-k)) /=.
  have -> : 256-(256-k)=k by ring.
  apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
  have he : Zq.exp w k * Zq.exp w (i+(256-k)) = -Zq.exp w i.
  + rewrite -(ZqField.exprD w k (i+(256-k)) hw0).
    have -> : k+(i+(256-k)) = 256+i by ring.
    by rewrite (ZqField.exprD w 256 i hw0) hw ZqRing.mulN1r.
  have -> : 256+(i-k) = i+(256-k) by ring.
  have -> : Zq.exp w k * (q.[i+(256-k)] * Zq.exp w (i+(256-k))) =
    q.[i+(256-k)] * (Zq.exp w k * Zq.exp w (i+(256-k))) by ring.
  rewrite he; ring.
rewrite (Rq.BigDom.BAdd.big_cat_int k 0 256) 1,2:/#.
have hlo : Rq.BigDom.BAdd.bigi predT (fun i =>
    (if 0 <= i-k then q.[i-k] else -q.[256+(i-k)]) * Zq.exp w i) 0 k =
  Rq.BigDom.BAdd.bigi predT (fun i => -q.[256+(i-k)] * Zq.exp w i) 0 k.
+ apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
  have hn : !(0 <= i-k) by smt().
  rewrite hn /=; ring.
have hhi : Rq.BigDom.BAdd.bigi predT (fun i =>
    (if 0 <= i-k then q.[i-k] else -q.[256+(i-k)]) * Zq.exp w i) k 256 =
  Rq.BigDom.BAdd.bigi predT (fun i => q.[i-k] * Zq.exp w i) k 256.
+ apply Rq.BigDom.BAdd.eq_big_int => i hi /=.
  have hn : 0 <= i-k by smt().
  by rewrite hn /=.
rewrite hlo hhi hlow hhigh /evaluation.
rewrite (Rq.BigDom.BAdd.big_cat_int (256-k) 0 256) 1,2:/#.
by ring.
qed.

lemma full_ntt_mul_from_shift p q :
  (forall w k, Zq.exp w 256 = -Zq.one => 0 <= k < 256 =>
    Rq.BigDom.BAdd.bigi predT (fun i =>
      (if 0 <= i-k then q.[i-k] else -q.[256+(i-k)]) * Zq.exp w i) 0 256 =
    Zq.exp w k * evaluation q w) =>
  NTTFullSpec.full_ntt (p &* q) =
  pointwise (NTTFullSpec.full_ntt p) (NTTFullSpec.full_ntt q).
proof.
move=> hshift.
apply Array256.ext_eq => i hi.
rewrite pointwiseE // !full_ntt_evaluation //.
apply evaluation_mul_from_shift => k hk.
by apply hshift; first exact (ntt_root_negacyclic i).
qed.

lemma full_ntt_mul p q : NTTFullSpec.full_ntt (p &* q) =
  pointwise (NTTFullSpec.full_ntt p) (NTTFullSpec.full_ntt q).
proof.
apply full_ntt_mul_from_shift => w k hw hk.
by apply shift_evaluation.
qed.

lemma full_ntt_product_pipeline p q :
  NTT_Fq.array256_mont
    (NTTFullSpec.full_invntt
      (scale (inv NTT_Fq.R)
        (pointwise (NTTFullSpec.full_ntt p) (NTTFullSpec.full_ntt q)))) = p &* q.
proof.
by rewrite full_invntt_mont_cancel -full_ntt_mul full_invntt_full_ntt.
qed.

end NTTTransformAlgebra.
