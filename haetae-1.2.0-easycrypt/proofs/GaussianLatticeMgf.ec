require import AllCore IntDiv List Real RealExp RealSeries Distr StdRing StdOrder StdBigop.
require import GaussianLatticeSum Gaussian76Spec Gaussian76Properties Gaussian76Folding
  HalfGaussianProperties ExponentialLipschitz HyperballTailSpec RawSquareMomentSpec.
import IntOrder RField RealOrder Bigreal Bigreal.BRA HalfGaussianProperties.

op glm_rho (d k : int) : real = RealExp.exp (-(k*k)%r / d%r).
op glm_half_rho (d k : int) : real = if 0 <= k then glm_rho d k else 0%r.
op glm_weight (m n k : int) : real =
  RealExp.exp (((n*n-m*m)*(k*k))%r / (n*n*g76_denominator)%r).

lemma glm_rho0 d : glm_rho d 0 = 1%r.
proof. by rewrite /glm_rho /= RealExp.exp0. qed.

lemma glm_rho_positive d k : 0%r < glm_rho d k.
proof. rewrite /glm_rho; exact (RealExp.exp_gt0 _). qed.

lemma glm_rho_symmetry d k : glm_rho d (-k) = glm_rho d k.
proof.
  rewrite /glm_rho.
  have h : (-k)*(-k)=k*k by ring.
  by rewrite h.
qed.

lemma glm_rho_decreasing d i j : 0 < d => 0 <= i <= j =>
  glm_rho d j <= glm_rho d i.
proof.
  move=> hd hij; rewrite /glm_rho; apply RealExp.exp_mono.
  have hsq : i*i <= j*j by smt().
  smt().
qed.

lemma glm_half_geometric_bound d k : 0 < d =>
  0%r <= glm_half_rho d k <= hg_geom (RealExp.exp (-1%r/d%r)) k.
proof.
  move=> hd; rewrite /glm_half_rho /hg_geom.
  case (0 <= k) => hk /=; last trivial.
  have hp := glm_rho_positive d k.
  have hpow : RealExp.exp (-1%r/d%r)^k = RealExp.exp (-k%r/d%r).
  + rewrite -RealExp.rpow_int 1:(ltrW _ _ (RealExp.exp_gt0 _))
      RealExp.rpowE 1:RealExp.exp_gt0 RealExp.lnK; congr; ring.
  rewrite hpow; split; first smt().
  move=> _.
  rewrite /glm_rho; apply RealExp.exp_mono.
  have hsq : k <= k*k by smt().
  smt().
qed.

lemma glm_half_summable d : 0 < d => RealSeries.summable (glm_half_rho d).
proof.
  move=> hd.
  have hp := RealExp.exp_gt0 (-1%r/d%r).
  have hu := RealExp.exp_mono_ltr (-1%r/d%r) 0%r.
  rewrite RealExp.exp0 in hu.
  have hr : 0%r <= RealExp.exp (-1%r/d%r) < 1%r by smt().
  have [hs _] := hg_geom_summable_bound (RealExp.exp (-1%r/d%r)) hr.
  apply (RealSeries.summable_le_pos _ _ hs) => k.
  exact (glm_half_geometric_bound d k hd).
qed.

lemma glm_rho_summable d : 0 < d => RealSeries.summable (glm_rho d).
proof.
  move=> hd; have hs := glm_half_summable d hd.
  have hinj : injective (fun k : int => -k) by move=> i j; smt().
  have hn := RealSeries.summable_inj (fun k : int => -k) (glm_half_rho d) hinj hs.
  have hb := RealSeries.summableD (glm_half_rho d) (fun k => glm_half_rho d (-k)) hs hn.
  apply (RealSeries.summable_le_pos _ _ hb) => k /=.
  have hp := glm_rho_positive d k.
  rewrite /glm_half_rho glm_rho_symmetry.
  case (0 <= k); case (0 <= -k); smt().
qed.

lemma glm_scaled_summable d m : 0 < d => 0 < m =>
  RealSeries.summable (fun k => glm_rho d (m*k)).
proof.
  move=> hd hm.
  have hinj : injective (fun k : int => m*k) by move=> i j; smt().
  exact (RealSeries.summable_inj (fun k : int => m*k) (glm_rho d) hinj
    (glm_rho_summable d hd)).
qed.

lemma glm_scaled_half d m : 0 < m =>
  gls_stride (glm_half_rho d) m = gls_stride (glm_rho d) m.
proof.
  move=> hm; apply fun_ext => k; rewrite /gls_stride /glm_half_rho.
  case (0 <= k) => hk /=; smt().
qed.

lemma glm_scaled_sum_half d m : 0 < d => 0 < m =>
  RealSeries.sum (fun k => glm_rho d (m*k)) = 2%r * gls_half_sum (glm_half_rho d) m.
proof.
  move=> hd hm.
  pose f := fun k => glm_rho d (m*k).
  have hs := glm_scaled_summable d m hd hm.
  have heven : forall k, f (-k) = f k.
  + move=> k; rewrite /f; have -> : m*(-k) = -(m*k) by ring.
    exact (glm_rho_symmetry d (m*k)).
  have hstride := gls_stride_summable (glm_rho d) m hm (glm_rho_summable d hd).
  pose positive := fun k => if k <> 0 then gls_stride (glm_rho d) m k else 0%r.
  have hp : RealSeries.summable positive by
    exact (RealSeries.summable_cond (gls_stride (glm_rho d) m) (fun k => k<>0) hstride).
  have hfold : RealSeries.sum f =
      RealSeries.sum (gls_stride (glm_rho d) m) + RealSeries.sum positive.
  + rewrite (g76_even_sum_fold f hs heven) -(RealSeries.sumD _ _ hstride hp).
    apply RealSeries.eq_sum => k /=.
    rewrite /gls_stride /positive /f.
    case (0 <= k); case (k=0); smt().
  have hz := RealSeries.sumD1 (gls_stride (glm_rho d) m) 0 hstride.
  rewrite /gls_stride /= glm_rho0 in hz.
  rewrite hfold /gls_half_sum (glm_scaled_half d m hm) /glm_half_rho /= glm_rho0.
  move: hz; rewrite /positive /gls_stride; smt().
qed.

lemma glm_half_comparison d m n : 0 < d => 0 < m => 0 < n =>
  `|m%r * gls_half_sum (glm_half_rho d) m -
      n%r * gls_half_sum (glm_half_rho d) n| <= (m+n-2)%r / 2%r.
proof.
  move=> hd hm hn.
  apply (gls_two_half_comparison (glm_half_rho d) m n hm hn
    (glm_half_summable d hd)).
  + move=> k hk; rewrite /glm_half_rho; smt().
  + move=> i j hij; rewrite /glm_half_rho.
    have hi : 0<=i by smt().
    have hj : 0<=j by smt().
    rewrite hi hj /=; exact (glm_rho_decreasing d i j hd hij).
  by rewrite /glm_half_rho /= glm_rho0.
qed.

lemma glm_denominator : g76_denominator = 2*ht_q*ht_q.
proof. by rewrite /g76_denominator /ht_q. qed.

lemma glm_normalizer_cell k : -ht_q <= k <= ht_q => 1%r/2%r <= g76_rho k.
proof.
  move=> hk.
  have hlin := exp_neg_linear_lower (1%r/2%r).
  have he : RealExp.exp (-1%r/2%r) <= g76_rho k.
  + rewrite /g76_rho; apply RealExp.exp_mono.
    have hsq : k*k <= ht_q*ht_q by move: hk; rewrite /ht_q; smt().
    rewrite /ht_q in hsq.
    rewrite /g76_denominator; smt().
  smt().
qed.

lemma glm_normalizer_lower : ht_q%r <= g76_normalizer.
proof.
  have hlist := RealSeries.ler_big_sum g76_rho (range (-ht_q) (ht_q+1))
    g76_rho_ge0 (range_uniq _ _) g76_rho_summable.
  have hconst : (2*ht_q+1)%r / 2%r <=
      Bigreal.BRA.bigi predT g76_rho (-ht_q) (ht_q+1).
  + have he : (2*ht_q+1)%r/2%r =
      Bigreal.BRA.bigi predT (fun _ => 1%r/2%r) (-ht_q) (ht_q+1).
    - by rewrite Bigreal.sumri_const 1:/# /ht_q /=.
    rewrite he; apply Bigreal.ler_sum_seq => k; rewrite mem_range => hk _.
    apply glm_normalizer_cell; smt().
  rewrite /g76_normalizer.
  have hq : ht_q%r <= (2*ht_q+1)%r/2%r by rewrite /ht_q /=; smt().
  exact (ler_trans _ _ _ hq (ler_trans _ _ _ hconst hlist)).
qed.

lemma glm_weight_density m n k : 0 < n =>
  g76_rho k * glm_weight m n k = glm_rho (n*n*g76_denominator) (m*k).
proof.
  move=> hn; rewrite /g76_rho /glm_weight /glm_rho -RealExp.expD.
  congr; rewrite !fromintM fromintB.
  have hden := g76_denominator_positive.
  field; smt().
qed.

lemma glm_weight_summable m n : 0 < m => 0 < n =>
  RealSeries.summable (fun k => g76_rho k * glm_weight m n k).
proof.
  move=> hm hn.
  have hd : 0 < n*n*g76_denominator by have := g76_denominator_positive; smt().
  have hs := glm_scaled_summable (n*n*g76_denominator) m hd hm.
  apply (RealSeries.eqL_summable _ _ hs) => k /=.
  by rewrite (glm_weight_density m n k hn).
qed.

lemma glm_weight_hasE m n : 0 < m => 0 < n => hasE g76_distr (glm_weight m n).
proof.
  move=> hm hn; rewrite /hasE.
  have hs := RealSeries.summableZ (fun k => g76_rho k * glm_weight m n k)
    (inv g76_normalizer) (glm_weight_summable m n hm hn).
  apply (RealSeries.eqL_summable _ _ hs) => k /=.
  rewrite g76_distr_mu1 /g76_pmf; ring.
qed.

lemma glm_weight_expectation m n : 0 < n =>
  E g76_distr (glm_weight m n) =
    RealSeries.sum (fun k => glm_rho (n*n*g76_denominator) (m*k)) / g76_normalizer.
proof.
  move=> hn; rewrite /E -RealSeries.sumZr.
  apply RealSeries.eq_sum => k /=.
  rewrite g76_distr_mu1 /g76_pmf -(glm_weight_density m n k hn); ring.
qed.

lemma glm_scaled_base n k : 0 < n =>
  glm_rho (n*n*g76_denominator) (n*k) = g76_rho k.
proof.
  move=> hn; rewrite /glm_rho /g76_rho; congr; rewrite !fromintM.
  have hden := g76_denominator_positive.
  field; smt().
qed.

lemma glm_scaled_base_sum n : 0 < n =>
  RealSeries.sum (fun k => glm_rho (n*n*g76_denominator) (n*k)) = g76_normalizer.
proof.
  move=> hn; rewrite /g76_normalizer; apply RealSeries.eq_sum => k /=.
  exact (glm_scaled_base n k hn).
qed.

lemma glm_weight_bound m n : 0 < m => 0 < n =>
  E g76_distr (glm_weight m n) <= n%r/m%r + (m+n-2)%r/(m*ht_q)%r.
proof.
  move=> hm hn.
  have hd : 0 < n*n*g76_denominator by have := g76_denominator_positive; smt().
  have hc := glm_half_comparison (n*n*g76_denominator) m n hd hm hn.
  have hsm := glm_scaled_sum_half (n*n*g76_denominator) m hd hm.
  have hsn := glm_scaled_sum_half (n*n*g76_denominator) n hd hn.
  rewrite (glm_scaled_base_sum n hn) in hsn.
  rewrite ler_norml in hc.
  have hbound : m%r * RealSeries.sum (fun k => glm_rho (n*n*g76_denominator) (m*k)) <=
      n%r*g76_normalizer + (m+n-2)%r by smt().
  have hz := g76_normalizer_positive.
  have hq := glm_normalizer_lower.
  have hq0 : 0 < ht_q by rewrite /ht_q.
  have hc0 : 0 <= m+n-2 by smt().
  rewrite (glm_weight_expectation m n hn) fromintM.
  apply (ler_trans (n%r/m%r+(m+n-2)%r/(m%r*g76_normalizer))).
  + have he : n%r/m%r+(m+n-2)%r/(m%r*g76_normalizer) =
      (n%r*g76_normalizer+(m+n-2)%r)/(m%r*g76_normalizer) by field; smt().
    rewrite he (ler_pdivl_mulr (m%r*g76_normalizer)) 1:/#.
    have he2 : (RealSeries.sum (fun k => glm_rho (n*n*g76_denominator) (m*k)) /
      g76_normalizer) * (m%r*g76_normalizer) =
      m%r*RealSeries.sum (fun k => glm_rho (n*n*g76_denominator) (m*k)) by field; smt().
    by rewrite he2.
  clear hd hc hsm hsn hbound.
  apply ler_add; first trivial.
  have hcpos : 0%r <= (m+n-2)%r by smt().
  apply (ler_wpmul2l _ hcpos).
  rewrite (ler_pinv (m%r*ht_q%r) (m%r*g76_normalizer)) 1..4:/#.
  apply ler_wpmul2l; smt().
qed.

lemma glm_plus_weight : rsm_gaussian_plus = glm_weight 9 10.
proof.
  apply fun_ext => k; rewrite /rsm_gaussian_plus /glm_weight /ht_tplus
    /ht_q /g76_denominator /= !fromintM; congr; ring.
qed.

lemma glm_minus_weight : rsm_gaussian_minus = glm_weight 8 7.
proof.
  apply fun_ext => k; rewrite /rsm_gaussian_minus /glm_weight /ht_tminus
    /ht_q /g76_denominator /= !fromintM; congr; ring.
qed.

lemma glm_plus_summable : RealSeries.summable (fun k => g76_rho k * rsm_gaussian_plus k).
proof. rewrite glm_plus_weight; apply glm_weight_summable; trivial. qed.

lemma glm_minus_summable : RealSeries.summable (fun k => g76_rho k * rsm_gaussian_minus k).
proof. rewrite glm_minus_weight; apply glm_weight_summable; trivial. qed.

lemma glm_plus_hasE : hasE g76_distr rsm_gaussian_plus.
proof. rewrite glm_plus_weight; apply glm_weight_hasE; trivial. qed.

lemma glm_minus_hasE : hasE g76_distr rsm_gaussian_minus.
proof. rewrite glm_minus_weight; apply glm_weight_hasE; trivial. qed.

lemma glm_plus_bound : E g76_distr rsm_gaussian_plus <= 10%r/9%r + 17%r/(9*ht_q)%r.
proof. rewrite glm_plus_weight; exact (glm_weight_bound 9 10 _ _); trivial. qed.

lemma glm_minus_bound : E g76_distr rsm_gaussian_minus <= 7%r/8%r + 13%r/(8*ht_q)%r.
proof. rewrite glm_minus_weight; exact (glm_weight_bound 8 7 _ _); trivial. qed.
