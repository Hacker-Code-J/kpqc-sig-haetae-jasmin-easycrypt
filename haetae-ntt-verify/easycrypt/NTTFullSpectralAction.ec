require import AllCore IntDiv List Ring StdOrder BitEncoding.

require import Array256.
require import GFq Rq NTT_Fq NTTFullSpec NTTFullAlgebra NTTRowProductSpec.

import Zq IntOrder BitReverse.

theory NTTFullSpectralAction.

op negacyclic_term (a b : Rq.poly) (i k : int) : coeff =
  if 0 <= i - k
  then a.[k] * b.[i - k]
  else -(a.[k] * b.[256 + (i - k)]).

lemma rq_mul_coeff_foldr_to_bigi (a b : Rq.poly) (i : int) :
  0 <= i < 256 =>
  (Rq.(&*) a b).[i] =
    Rq.BigDom.BAdd.bigi predT (negacyclic_term a b i) 0 256.
proof.
move=> hi.
rewrite /Rq.(&*) Array256.initiE 1:/#.
rewrite /Rq.BigDom.BAdd.big /range /=.
rewrite filter_predT foldr_map.
apply eq_foldr => // k.
apply fun_ext => ci.
rewrite /negacyclic_term.
case (0 <= i - k) => hik /=; ring.
qed.

op negacyclic_index (i u : int) : int =
  if u <= i then i - u else 256 + i - u.

lemma negacyclic_index_range i u :
  0 <= i < 256 => 0 <= u < 256 =>
  0 <= negacyclic_index i u < 256.
proof. rewrite /negacyclic_index; case (u <= i) => _ /#. qed.

lemma negacyclic_index_involutive i u :
  0 <= i < 256 => 0 <= u < 256 =>
  negacyclic_index i (negacyclic_index i u) = u.
proof.
move=> hi hu.
rewrite /negacyclic_index.
case (u <= i) => hui /=.
+ have hinner : i - u <= i by smt().
  rewrite hinner /=.
  smt().
have hinner : !(256 + i - u <= i) by smt().
rewrite hinner /=.
smt().
qed.

lemma negacyclic_index_perm i :
  0 <= i < 256 =>
  perm_eq (range 0 256)
    (map (negacyclic_index i) (range 0 256)).
proof.
move=> hi.
apply uniq_perm_eq_size.
+ exact range_uniq.
+ rewrite map_inj_in_uniq 2:range_uniq.
  move=> x y /mem_range hx /mem_range hy heq.
  rewrite -(negacyclic_index_involutive i x hi hx).
  rewrite -(negacyclic_index_involutive i y hi hy).
  by rewrite heq.
+ by rewrite size_map.
move=> x /mem_range hx.
apply/mapP.
exists (negacyclic_index i x); split.
+ rewrite mem_range.
  exact (negacyclic_index_range i x hi hx).
by rewrite negacyclic_index_involutive.
qed.

lemma array256_mont_get p i :
  0 <= i < 256 =>
  (NTT_Fq.array256_mont p).[i] = p.[i] * NTT_Fq.R.
proof.
move=> hi.
by rewrite /NTT_Fq.array256_mont Array256.mapiE.
qed.

lemma montgomery_factor_cancel (x : coeff) :
  x * inv NTT_Fq.R * NTT_Fq.R = x.
proof.
have hunit : inv NTT_Fq.R * NTT_Fq.R = Zq.one.
+ exact (ZqRing.mulVr NTT_Fq.R NTT_Fq.unit_R).
have -> : x * inv NTT_Fq.R * NTT_Fq.R =
          x * (inv NTT_Fq.R * NTT_Fq.R) by ring.
by rewrite hunit ZqRing.mulr1.
qed.

lemma high_root_negation j i u :
  - (Zq.exp zroot
       (- ((2 * br j + 1) * (256 + i - u)))) =
    Zq.exp zroot ((2 * br j + 1) * (u - i)).
proof.
have -> :
    - ((2 * br j + 1) * (256 + i - u)) =
    ((2 * br j + 1) * (u - i) - 256) + 512 * (- br j) by ring.
rewrite NTTFullAlgebra.exp_zroot_mod512.
have -> :
    (2 * br j + 1) * (u - i) - 256 =
    (2 * br j + 1) * (u - i) + (-256) by ring.
rewrite ZqRing.exprD 1:NTT_Fq.unit_zroot
        NTTFullAlgebra.exp_zroot_m256
        NTTFullAlgebra.incoeff_m1.
ring.
qed.

op spectral_kernel
    (ahat p : Rq.poly) (i u j : int) : coeff =
  inv (incoeff 256) * ahat.[j] * p.[u] *
    Zq.exp zroot ((2 * br j + 1) * (u - i)).

lemma inverse_negacyclic_term_expand ahat p i u :
  0 <= i < 256 => 0 <= u < 256 =>
  negacyclic_term (NTTFullSpec.full_invntt ahat) p i
      (negacyclic_index i u) =
    Rq.BigDom.BAdd.bigi predT
      (spectral_kernel ahat p i u) 0 256.
proof.
move=> hi hu.
rewrite /negacyclic_term /negacyclic_index.
case (u <= i) => hui /=.
+ have hcond : 0 <= i - (i - u) by smt().
  rewrite hcond /=.
  have hpidx : i - (i - u) = u by ring.
  rewrite hpidx.
  have hk : 0 <= i - u < 256 by smt().
  rewrite /NTTFullSpec.full_invntt Array256.initiE 1:/#.
  rewrite Rq.BigDom.BAdd.mulr_suml.
  apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
  rewrite /spectral_kernel.
  have -> : - ((2 * br j + 1) * (i - u)) =
            (2 * br j + 1) * (u - i) by ring.
  ring.
have hcond : !(0 <= i - (256 + i - u)) by smt().
rewrite hcond /=.
have hpidx : 256 + (i - (256 + i - u)) = u by ring.
rewrite hpidx.
have hk : 0 <= 256 + i - u < 256 by smt().
rewrite /NTTFullSpec.full_invntt Array256.initiE 1:/#.
rewrite -ZqRing.mulNr.
rewrite Rq.BigDom.BAdd.sumrN.
rewrite Rq.BigDom.BAdd.mulr_suml.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
rewrite /spectral_kernel.
rewrite -high_root_negation.
ring.
qed.

lemma inverse_convolution_kernel ahat p i :
  0 <= i < 256 =>
  (Rq.(&*) (NTTFullSpec.full_invntt ahat) p).[i] =
    Rq.BigDom.BAdd.bigi predT
      (fun u =>
        Rq.BigDom.BAdd.bigi predT
          (spectral_kernel ahat p i u) 0 256)
      0 256.
proof.
move=> hi.
rewrite rq_mul_coeff_foldr_to_bigi 1:hi.
have hperm := negacyclic_index_perm i hi.
rewrite (Rq.BigDom.BAdd.eq_big_perm
  predT (negacyclic_term (NTTFullSpec.full_invntt ahat) p i)
  (range 0 256)
  (map (negacyclic_index i) (range 0 256))) 1:hperm.
rewrite Rq.BigDom.BAdd.big_mapT.
apply Rq.BigDom.BAdd.eq_big_int => u hu /=.
apply inverse_negacyclic_term_expand => //.
qed.

lemma montgomery_inverse_pointwise_kernel ahat p i :
  0 <= i < 256 =>
  (NTT_Fq.array256_mont
    (NTTFullSpec.full_invntt
      (NTTRowProductSpec.montgomery_pointwise_product ahat p))).[i] =
    Rq.BigDom.BAdd.bigi predT
      (fun j =>
        Rq.BigDom.BAdd.bigi predT
          (fun u => spectral_kernel ahat p i u j) 0 256)
      0 256.
proof.
move=> hi.
rewrite array256_mont_get 1:hi.
rewrite /NTTFullSpec.full_invntt Array256.initiE 1:/#.
rewrite Rq.BigDom.BAdd.mulr_suml.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
have hj' : 0 <= j < 256 by exact hj.
rewrite NTTRowProductSpec.montgomery_pointwise_product_get 1:hj'.
rewrite /NTTFullSpec.full_ntt Array256.initiE 1:/#.
have -> :
    inv (incoeff 256) *
      (ahat.[j] *
        Rq.BigDom.BAdd.bigi predT
          (fun u => p.[u] *
            Zq.exp zroot ((2 * br j + 1) * u)) 0 256 *
        inv NTT_Fq.R) *
      Zq.exp zroot (- ((2 * br j + 1) * i)) * NTT_Fq.R =
    (inv (incoeff 256) * ahat.[j] * inv NTT_Fq.R *
      Zq.exp zroot (- ((2 * br j + 1) * i)) * NTT_Fq.R) *
      Rq.BigDom.BAdd.bigi predT
        (fun u => p.[u] *
          Zq.exp zroot ((2 * br j + 1) * u)) 0 256 by ring.
rewrite Rq.BigDom.BAdd.mulr_sumr.
apply Rq.BigDom.BAdd.eq_big_int => u hu /=.
rewrite /spectral_kernel.
have hR : inv NTT_Fq.R * NTT_Fq.R = Zq.one.
+ exact (ZqRing.mulVr NTT_Fq.R NTT_Fq.unit_R).
have hexp :
    Zq.exp zroot ((2 * br j + 1) * u) *
    Zq.exp zroot (- ((2 * br j + 1) * i)) =
    Zq.exp zroot ((2 * br j + 1) * (u - i)).
+ rewrite -ZqRing.exprD 1:NTT_Fq.unit_zroot.
  congr; ring.
have -> :
    (inv (incoeff 256) * ahat.[j] * inv NTT_Fq.R *
       Zq.exp zroot (- ((2 * br j + 1) * i)) * NTT_Fq.R) *
      (p.[u] * Zq.exp zroot ((2 * br j + 1) * u)) =
    inv (incoeff 256) * ahat.[j] * p.[u] *
      (Zq.exp zroot ((2 * br j + 1) * u) *
       Zq.exp zroot (- ((2 * br j + 1) * i))) *
      (inv NTT_Fq.R * NTT_Fq.R) by ring.
by rewrite hR hexp ZqRing.mulr1.
qed.

lemma spectral_kernel_exchange ahat p i :
  Rq.BigDom.BAdd.bigi predT
    (fun j =>
      Rq.BigDom.BAdd.bigi predT
        (fun u => spectral_kernel ahat p i u j) 0 256)
    0 256 =
  Rq.BigDom.BAdd.bigi predT
    (fun u =>
      Rq.BigDom.BAdd.bigi predT
        (spectral_kernel ahat p i u) 0 256)
    0 256.
proof.
exact (Rq.BigDom.BAdd.exchange_big
  predT predT
  (fun j u => spectral_kernel ahat p i u j)
  (range 0 256) (range 0 256)).
qed.

lemma full_ntt_montgomery_spectral_action (ahat p : Rq.poly) :
  NTT_Fq.array256_mont
    (NTTFullSpec.full_invntt
      (Array256.init (fun j =>
        ahat.[j] * (NTTFullSpec.full_ntt p).[j] * inv NTT_Fq.R))) =
  Rq.(&*) (NTTFullSpec.full_invntt ahat) p.
proof.
apply Array256.ext_eq => i hi.
have hleft := montgomery_inverse_pointwise_kernel ahat p i hi.
rewrite /NTTRowProductSpec.montgomery_pointwise_product in hleft.
have hright := inverse_convolution_kernel ahat p i hi.
rewrite hleft hright.
exact (spectral_kernel_exchange ahat p i).
qed.

op inverse_row_kernel
    (polys : int -> Rq.poly) (i col j : int) : coeff =
  inv (incoeff 256) * (polys col).[j] *
    Zq.exp zroot (- ((2 * br j + 1) * i)) * NTT_Fq.R.

lemma inverse_row_poly_sum_left count polys i :
  0 <= i < 256 =>
  (NTTRowProductSpec.inverse_row
    (NTTRowProductSpec.poly_sum count polys)).[i] =
  Rq.BigDom.BAdd.bigi predT
    (fun j =>
      Rq.BigDom.BAdd.bigi predT
        (fun col => inverse_row_kernel polys i col j) 0 count)
    0 256.
proof.
move=> hi.
rewrite /NTTRowProductSpec.inverse_row array256_mont_get 1:hi.
rewrite /NTTFullSpec.full_invntt Array256.initiE 1:/#.
rewrite Rq.BigDom.BAdd.mulr_suml.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
rewrite NTTRowProductSpec.poly_sum_get 1:hj.
have -> :
    inv (incoeff 256) *
      Rq.BigDom.BAdd.bigi predT
        (fun col => (polys col).[j]) 0 count *
      Zq.exp zroot (- ((2 * br j + 1) * i)) * NTT_Fq.R =
    (inv (incoeff 256) *
      Zq.exp zroot (- ((2 * br j + 1) * i)) * NTT_Fq.R) *
      Rq.BigDom.BAdd.bigi predT
        (fun col => (polys col).[j]) 0 count by ring.
rewrite Rq.BigDom.BAdd.mulr_sumr.
apply Rq.BigDom.BAdd.eq_big_int => col hcol /=.
by rewrite /inverse_row_kernel; ring.
qed.

lemma inverse_row_poly_sum_right count polys i :
  0 <= i < 256 =>
  (NTTRowProductSpec.poly_sum count
    (fun col => NTTRowProductSpec.inverse_row (polys col))).[i] =
  Rq.BigDom.BAdd.bigi predT
    (fun col =>
      Rq.BigDom.BAdd.bigi predT
        (fun j => inverse_row_kernel polys i col j) 0 256)
    0 count.
proof.
move=> hi.
rewrite NTTRowProductSpec.poly_sum_get 1:hi.
apply Rq.BigDom.BAdd.eq_big_int => col hcol /=.
rewrite /NTTRowProductSpec.inverse_row array256_mont_get 1:hi.
rewrite /NTTFullSpec.full_invntt Array256.initiE 1:/#.
rewrite Rq.BigDom.BAdd.mulr_suml.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
by rewrite /inverse_row_kernel.
qed.

lemma inverse_row_poly_sum count polys :
  NTTRowProductSpec.inverse_row
    (NTTRowProductSpec.poly_sum count polys) =
  NTTRowProductSpec.poly_sum count
    (fun col => NTTRowProductSpec.inverse_row (polys col)).
proof.
apply Array256.ext_eq => i hi.
rewrite inverse_row_poly_sum_left 1:hi
        inverse_row_poly_sum_right 1:hi.
exact (Rq.BigDom.BAdd.exchange_big
  predT predT
  (fun j col => inverse_row_kernel polys i col j)
  (range 0 256) (range 0 count)).
qed.

lemma full_ntt_montgomery_row_product cols matrix_hat vector row :
  NTTRowProductSpec.inverse_row
    (NTTRowProductSpec.pointwise_row cols matrix_hat vector row) =
  NTTRowProductSpec.coefficient_row_product cols
    (fun r col => NTTFullSpec.full_invntt (matrix_hat r col))
    vector row.
proof.
rewrite NTTRowProductSpec.pointwise_row_as_poly_sum.
rewrite inverse_row_poly_sum.
rewrite NTTRowProductSpec.coefficient_row_product_as_poly_sum.
apply Array256.ext_eq => i hi.
rewrite !NTTRowProductSpec.poly_sum_get 1,2:hi.
apply Rq.BigDom.BAdd.eq_big_int => col hcol /=.
have h := full_ntt_montgomery_spectral_action
  (matrix_hat row col) (vector col).
rewrite /NTTRowProductSpec.inverse_row
        /NTTRowProductSpec.montgomery_pointwise_product.
by rewrite h.
qed.

lemma full_ntt_montgomery_row_product_from_reprs
    rows cols matrix_hat matrix vector_hat vector acc out row :
  0 <= row < rows =>
  NTTRowProductSpec.matrix_inverse_repr
    rows cols matrix_hat matrix =>
  NTTRowProductSpec.vector_forward_repr cols vector_hat vector =>
  NTTRowProductSpec.pointwise_row_repr
    cols acc matrix_hat vector_hat row =>
  NTTRowProductSpec.inverse_row_repr out acc =>
  out = NTTRowProductSpec.coefficient_row_product
    cols matrix vector row.
proof.
move=> hrow hmatrix hforward hpointwise hinverse.
move: hinverse; rewrite /NTTRowProductSpec.inverse_row_repr => ->.
move: hpointwise; rewrite /NTTRowProductSpec.pointwise_row_repr => ->.
rewrite (NTTRowProductSpec.pointwise_row_from_forward_repr
  cols matrix_hat vector_hat vector row hforward).
rewrite full_ntt_montgomery_row_product.
apply Array256.ext_eq => i hi.
rewrite !NTTRowProductSpec.coefficient_row_product_get 1,2:hi.
apply Rq.BigDom.BAdd.eq_big_int => col hcol /=.
have hentry := NTTRowProductSpec.matrix_inverse_reprE
  rows cols matrix_hat matrix row col hmatrix hrow hcol.
by rewrite -hentry.
qed.

end NTTFullSpectralAction.
