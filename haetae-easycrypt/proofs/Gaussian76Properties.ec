require import AllCore IntDiv List StdRing StdOrder StdBigop.
require import RealExp RealSeries Distr HalfGaussianProperties Gaussian76Spec.
import IntOrder RField RealOrder Bigreal Bigreal.BRA HalfGaussianProperties.

(* The geometric majorant depends only on the independent Gaussian scale. *)
op g76_geometric_ratio : real = RealExp.exp (-1%r / g76_denominator%r).

lemma g76_denominator_positive : 0 < g76_denominator.
proof. by rewrite /g76_denominator. qed.

lemma g76_geometric_ratio_range : 0%r < g76_geometric_ratio < 1%r.
proof.
  split; first by rewrite /g76_geometric_ratio; apply RealExp.exp_gt0.
  have h := RealExp.exp_mono_ltr (-1%r / g76_denominator%r) 0%r.
  rewrite RealExp.exp0 in h.
  rewrite /g76_geometric_ratio; move: h; rewrite /g76_denominator; smt().
qed.

lemma g76_rho_symmetry (k : int) : g76_rho (-k) = g76_rho k.
proof.
  rewrite /g76_rho.
  have -> : (-k)*(-k) = k*k by ring.
  trivial.
qed.

lemma g76_rho0 : g76_rho 0 = 1%r.
proof. by rewrite /g76_rho /= RealExp.exp0. qed.

lemma g76_rho_positive (k : int) : 0%r < g76_rho k.
proof. rewrite /g76_rho; apply RealExp.exp_gt0. qed.

lemma g76_rho_ge0 (k : int) : 0%r <= g76_rho k.
proof. exact (ltrW _ _ (g76_rho_positive k)). qed.

lemma g76_rho_power (k : int) : g76_rho k = g76_geometric_ratio ^ (k*k).
proof.
  rewrite /g76_rho /g76_geometric_ratio.
  rewrite -RealExp.rpow_int 1:(ltrW _ _ (RealExp.exp_gt0 _)).
  rewrite RealExp.rpowE 1:RealExp.exp_gt0 RealExp.lnK.
  congr; ring.
qed.

lemma g76_half_rho_ge0 (k : int) : 0%r <= g76_half_rho k.
proof.
  rewrite /g76_half_rho; case (0 <= k) => // _.
  exact (g76_rho_ge0 k).
qed.

lemma g76_half_geometric_bound (k : int) :
  0%r <= g76_half_rho k <= hg_geom g76_geometric_ratio k.
proof.
  split; first exact (g76_half_rho_ge0 k).
  case (0 <= k) => hk.
  + rewrite /g76_half_rho hk /= g76_rho_power /hg_geom hk /=.
    have [hq0 hq1] := g76_geometric_ratio_range.
    have h := ler_wiexpn2l g76_geometric_ratio _ (k*k) k _; smt().
  by rewrite /g76_half_rho /hg_geom hk.
qed.

lemma g76_half_summable : RealSeries.summable g76_half_rho.
proof.
  have [hq0 hq1] := g76_geometric_ratio_range.
  have [hs _] := hg_geom_summable_bound g76_geometric_ratio _; first smt().
  exact (RealSeries.summable_le_pos g76_half_rho (hg_geom g76_geometric_ratio)
    hs g76_half_geometric_bound).
qed.

lemma g76_reflected_half_summable :
  RealSeries.summable (fun k => g76_half_rho (-k)).
proof.
  have hi : injective (fun k : int => -k) by move=> x y; smt().
  exact (RealSeries.summable_inj (fun k : int => -k) g76_half_rho hi g76_half_summable).
qed.

(* Reflection covers every negative integer. The extra copy of the zero
   term is harmless for this summable nonnegative majorant. *)
lemma g76_signed_half_bound (k : int) :
  0%r <= g76_rho k <= g76_half_rho k + g76_half_rho (-k).
proof.
  have hp := g76_rho_ge0 k.
  rewrite /g76_half_rho g76_rho_symmetry.
  case (0 <= k) => hk; case (0 <= -k) => hn; smt().
qed.

lemma g76_rho_summable : RealSeries.summable g76_rho.
proof.
  have hs := RealSeries.summableD g76_half_rho (fun k => g76_half_rho (-k))
    g76_half_summable g76_reflected_half_summable.
  exact (RealSeries.summable_le_pos g76_rho
    (fun k => g76_half_rho k + g76_half_rho (-k)) hs g76_signed_half_bound).
qed.

lemma g76_normalizer_ge1 : 1%r <= g76_normalizer.
proof.
  have h := RealSeries.ler_big_sum g76_rho [0] g76_rho_ge0 _ g76_rho_summable;
    first trivial.
  by move: h; rewrite big_seq1 g76_rho0 /g76_normalizer.
qed.

lemma g76_normalizer_positive : 0%r < g76_normalizer.
proof. smt(g76_normalizer_ge1). qed.

lemma g76_pmf_positive (k : int) : 0%r < g76_pmf k.
proof.
  rewrite /g76_pmf.
  exact (divr_gt0 (g76_rho k) g76_normalizer
    (g76_rho_positive k) g76_normalizer_positive).
qed.

lemma g76_pmf_ge0 (k : int) : 0%r <= g76_pmf k.
proof. exact (ltrW _ _ (g76_pmf_positive k)). qed.

lemma g76_pmf_scaled : g76_pmf = (fun k => inv g76_normalizer * g76_rho k).
proof. apply fun_ext => k; rewrite /g76_pmf; ring. qed.

lemma g76_pmf_summable : RealSeries.summable g76_pmf.
proof.
  rewrite g76_pmf_scaled; apply RealSeries.summableZ.
  exact g76_rho_summable.
qed.

lemma g76_pmf_sum : RealSeries.sum g76_pmf = 1%r.
proof.
  rewrite g76_pmf_scaled RealSeries.sumZ -/(g76_normalizer).
  rewrite mulVr; smt(g76_normalizer_positive).
qed.

lemma g76_pmf_isdistr : Distr.isdistr g76_pmf.
proof.
  split; first exact g76_pmf_ge0.
  move=> J hJ; have h := RealSeries.ler_big_sum g76_pmf J
    g76_pmf_ge0 hJ g76_pmf_summable.
  by move: h; rewrite g76_pmf_sum.
qed.

lemma g76_distr_mu1 (k : int) : mu1 g76_distr k = g76_pmf k.
proof. by rewrite /g76_distr Distr.muK 1:g76_pmf_isdistr. qed.

lemma g76_distr_ll : is_lossless g76_distr.
proof.
  rewrite /is_lossless weightE.
  have he : mu1 g76_distr = g76_pmf.
  + apply fun_ext => k; exact (g76_distr_mu1 k).
  by rewrite he g76_pmf_sum.
qed.

lemma g76_distr_support (k : int) : k \in g76_distr.
proof.
  rewrite /Distr.support g76_distr_mu1.
  have h := g76_pmf_positive k; smt().
qed.
