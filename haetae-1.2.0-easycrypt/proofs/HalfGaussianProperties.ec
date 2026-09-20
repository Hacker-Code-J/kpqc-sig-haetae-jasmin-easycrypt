require import AllCore IntDiv List StdRing StdOrder StdBigop Discrete.
require import RealExp RealSeq RealSeries Distr HalfGaussianSpec.
import IntOrder RField RealOrder Bigreal Bigreal.BRA HalfGaussianSpec.

theory HalfGaussianProperties.

lemma hg16_q_range : 0%r < hg16_q < 1%r.
proof.
  split; first exact (RealExp.exp_gt0 (-1%r/512%r)).
  have h := RealExp.exp_mono_ltr (-1%r/512%r) 0%r.
  rewrite RealExp.exp0 in h; rewrite /hg16_q; smt().
qed.

lemma hg16_rho_ge0 k : 0%r <= hg16_rho k.
proof.
  rewrite /hg16_rho; case (0 <= k) => // hk.
  exact (ltrW _ _ (RealExp.exp_gt0 _)).
qed.

lemma hg16_rho_pos k : 0 <= k => 0%r < hg16_rho k.
proof. by move=> hk; rewrite /hg16_rho hk /=; apply RealExp.exp_gt0. qed.

lemma hg16_rho0 : hg16_rho 0 = 1%r.
proof. by rewrite /hg16_rho /= RealExp.exp0. qed.

lemma hg16_rho_power k : 0 <= k => hg16_rho k = hg16_q ^ (k*k).
proof.
  move=> hk; rewrite /hg16_rho hk /hg16_q /=.
  rewrite -RealExp.rpow_int 1:(ltrW _ _ (RealExp.exp_gt0 _)).
  rewrite RealExp.rpowE 1:RealExp.exp_gt0 RealExp.lnK.
  congr; ring.
qed.

(* A bounded family of finite nonnegative prefix sums yields an actual
   summable series and its limit, using the installed RealSeries library. *)
lemma hg_nat_summable_bound (f : int -> real) (M : real) :
  (forall k, k < 0 => f k = 0%r) =>
  (forall k, 0%r <= f k) =>
  (forall N, 0 <= N => Bigreal.BRA.bigi predT f 0 N <= M) =>
  RealSeries.summable f /\ RealSeries.sum f <= M /\
  RealSeq.convergeto (fun N => Bigreal.BRA.bigi predT f 0 N) (RealSeries.sum f).
proof.
  move=> hneg hpos hbound.
  have he : enumerate (fun k : int => Some k) (RealSeries.support f).
  + split; first by move=> i j x /= -> ->.
    move=> x hx; exists x; split; last trivial.
    rewrite /RealSeries.support in hx; smt().
  have hM : 0%r <= M.
  + have hz := hbound 0 _; first trivial.
    by move: hz; rewrite /bigi range_geq // big_nil.
  have hs : RealSeries.summable f.
  + apply (RealSeries.summable_from_bounded f (fun k : int => Some k) he).
    exists M => N; rewrite pmap_some map_id.
    rewrite (@eq_bigr _ _ f); first by move=> k _; rewrite /= ger0_norm 1:hpos.
    case (0 <= N) => hN; first exact (hbound N hN).
    by rewrite range_geq 1:/# big_nil.
  have hc : RealSeq.convergeto (fun N => Bigreal.BRA.bigi predT f 0 N) (RealSeries.sum f).
  + have hh := RealSeries.summable_cnvto f (fun k : int => Some k)
      (RealSeries.support f) he _ hs; first trivial.
    apply (RealSeq.eq_cnvto _ _ _ _ hh) => N.
    by rewrite /= (pmap_some (fun k : int=>k)) map_id.
  split; first exact hs.
  split; last exact hc.
  apply (RealSeq.le_cnvto_from _ (fun _ => M) _ M _ hc (RealSeq.cnvtoC M)).
  by exists 0 => N hN; apply hbound.
qed.

op hg_geom (r : real) (k : int) : real = if 0 <= k then r^k else 0%r.

lemma hg_geom_ge0 r k : 0%r <= r => 0%r <= hg_geom r k.
proof. move=> hr; rewrite /hg_geom; case (0<=k) => // _; exact (expr_ge0 k r hr). qed.

lemma hg_geom_summable_bound r : 0%r <= r < 1%r =>
  RealSeries.summable (hg_geom r) /\
  RealSeries.sum (hg_geom r) <= 1%r / (1%r-r).
proof.
  move=> hr.
  have [hs [hb hc]] := hg_nat_summable_bound (hg_geom r) (1%r/(1%r-r)) _ _ _.
  + by move=> k hk; rewrite /hg_geom; smt().
  + by move=> k; apply hg_geom_ge0; smt().
  + move=> N hN; rewrite (@eq_big_int _ _ _ (fun (k:int) => r^k)); first by move=> k hk; rewrite /hg_geom; smt().
    exact (Bigreal.sum_pow_le r N hN hr).
  by split.
qed.

lemma hg16_rho_geom k : 0%r <= hg16_rho k <= hg_geom hg16_q k.
proof.
  split; first exact (hg16_rho_ge0 k).
  case (0 <= k) => hk; last by rewrite /hg16_rho /hg_geom hk.
  rewrite hg16_rho_power 1:hk /hg_geom hk /=.
  have [hq0 hq1] := hg16_q_range.
  have h := ler_wiexpn2l hg16_q _ (k*k) k _; smt().
qed.

lemma hg16_summable : RealSeries.summable hg16_rho.
proof.
  have [hq0 hq1] := hg16_q_range.
  have [hs hb] := hg_geom_summable_bound hg16_q _; first smt().
  exact (RealSeries.summable_le_pos hg16_rho (hg_geom hg16_q) hs hg16_rho_geom).
qed.

lemma hg16_normalizer_ge1 : 1%r <= hg16_normalizer.
proof.
  have h := RealSeries.ler_big_sum hg16_rho [0] hg16_rho_ge0 _ hg16_summable;
    first trivial.
  by move: h; rewrite big_seq1 hg16_rho0 /hg16_normalizer.
qed.

lemma hg16_normalizer_pos : 0%r < hg16_normalizer.
proof. smt(hg16_normalizer_ge1). qed.

lemma hg16_partial_converges :
  RealSeq.convergeto hg16_partial hg16_normalizer.
proof.
  have he : enumerate (fun k : int => Some k) (RealSeries.support hg16_rho).
  + split; first by move=> i j x /= -> ->.
    move=> x hx; exists x; split; last trivial.
    rewrite /RealSeries.support /hg16_rho in hx; smt().
  have h := RealSeries.summable_cnvto hg16_rho (fun k : int => Some k)
    (RealSeries.support hg16_rho) he _ hg16_summable; first trivial.
  apply (RealSeq.eq_cnvto _ _ _ _ h) => N.
  by rewrite /hg16_partial /= (pmap_some (fun k : int=>k)) map_id.
qed.

lemma hg16_tail_ratio_range N : 0 <= N => 0%r < hg16_q ^ (2*N+1) < 1%r.
proof.
  move=> hN; have [hq0 hq1] := hg16_q_range; split.
  + exact (expr_gt0 _ _ hq0).
  rewrite exprn_ilt1 1:/# 1:/#; smt().
qed.

lemma hg16_tail_majorant N k : 0 <= N => 0 <= k =>
  hg16_rho (N+k) <= hg16_rho N * (hg16_q ^ (2*N+1)) ^ k.
proof.
  move=> hN hk; rewrite !hg16_rho_power 1..2:/#.
  rewrite -exprM -exprD_nneg 1..2:/#.
  have [hq0 hq1] := hg16_q_range.
  apply (ler_wiexpn2l hg16_q _ ((N+k)*(N+k)) (N*N+(2*N+1)*k)); smt().
qed.

lemma hg16_tail_summable (N : int) :
  RealSeries.summable (fun k => if N <= k then hg16_rho k else 0%r).
proof. exact (RealSeries.summable_cond hg16_rho (fun k=>N<=k) hg16_summable). qed.

lemma hg16_tail_ge0 N : 0%r <= hg16_tail N.
proof.
  rewrite /hg16_tail; apply RealSeries.ge0_sum => k.
  case (N<=k) => /=; smt(hg16_rho_ge0).
qed.

lemma hg16_tail_le N : 0 <= N => hg16_tail N <= hg16_tail_bound N.
proof.
  move=> hN; have [hr0 hr1] := hg16_tail_ratio_range N hN.
  have [hgs hgb] := hg_geom_summable_bound (hg16_q^(2*N+1)) _; first smt().
  have hm : forall k, 0%r <= (if 0<=k then hg16_rho (N+k) else 0%r) <=
      hg16_rho N * hg_geom (hg16_q^(2*N+1)) k.
  + move=> k; case (0<=k) => hk /=.
    - rewrite /hg_geom hk /=; split; first exact (hg16_rho_ge0 (N+k)).
      have h := hg16_tail_majorant N k hN hk; smt().
    by rewrite /hg_geom hk /=.
  have hscaled := RealSeries.summableZ _ (hg16_rho N) hgs.
  have hle := RealSeries.ler_sum_pos _ _ hm hscaled.
  rewrite RealSeries.sumZ in hle.
  have hbij : bijective (fun k : int => N+k).
  + exists (fun k : int => k-N); split.
    - by move=> k; ring.
    by move=> k; ring.
  have he := RealSeries.sum_reindex (fun k : int => N+k)
      (fun k => if N<=k then hg16_rho k else 0%r) hbij (hg16_tail_summable N).
  have heq : (fun k => if 0<=k then hg16_rho (N+k) else 0%r) =
      ((fun k => if N<=k then hg16_rho k else 0%r) \o (fun k=>N+k)).
  + apply fun_ext => k; rewrite /(\o); smt().
  have hle' := hle.
  rewrite heq he in hle'.
  have hmul := ler_wpmul2l (hg16_rho N) (hg16_rho_ge0 N) _ _ hgb.
  rewrite /= in hmul.
  rewrite /hg16_tail_bound /hg16_tail.
  exact (ler_trans _ _ _ hle' hmul).
qed.

lemma hg16_normalizer_split N : 0 <= N =>
  hg16_normalizer = hg16_partial N + hg16_tail N.
proof.
  move=> hN; rewrite /hg16_normalizer (RealSeries.sum_split hg16_rho (fun k=>k<N) hg16_summable).
  congr.
  + rewrite /hg16_partial (RealSeries.sumE_fin _ (range 0 N)) 1:range_uniq.
    - move=> k; rewrite /hg16_rho mem_range; smt().
    apply eq_big_int => k hk /=; smt().
  rewrite /hg16_tail; apply RealSeries.eq_sum => k /=; smt().
qed.

lemma hg16_normalizer_truncation N : 0 <= N =>
  0%r <= hg16_normalizer - hg16_partial N <= hg16_tail_bound N.
proof.
  move=> hN; rewrite (hg16_normalizer_split N hN).
  have hp := hg16_tail_ge0 N; have hb := hg16_tail_le N hN; smt().
qed.

lemma hg16_normalizer_truncation256 :
  0%r <= hg16_normalizer - hg16_partial 256 <=
    hg16_rho 256 / (1%r - hg16_q^513).
proof. exact (hg16_normalizer_truncation 256 _). qed.

lemma hg16_pmf_ge0 k : 0%r <= hg16_pmf k.
proof.
  rewrite /hg16_pmf; apply divr_ge0; smt(hg16_rho_ge0 hg16_normalizer_pos).
qed.

lemma hg16_pmf_scaled :
  hg16_pmf = (fun k => inv hg16_normalizer * hg16_rho k).
proof. apply fun_ext => k; rewrite /hg16_pmf; ring. qed.

lemma hg16_pmf_summable : RealSeries.summable hg16_pmf.
proof. by rewrite hg16_pmf_scaled; apply RealSeries.summableZ; exact hg16_summable. qed.

lemma hg16_pmf_sum : RealSeries.sum hg16_pmf = 1%r.
proof.
  rewrite hg16_pmf_scaled RealSeries.sumZ -/(hg16_normalizer).
  rewrite mulVr; smt(hg16_normalizer_pos).
qed.

lemma hg16_pmf_isdistr : Distr.isdistr hg16_pmf.
proof.
  split; first exact hg16_pmf_ge0.
  move=> J hJ; have h := RealSeries.ler_big_sum hg16_pmf J
    hg16_pmf_ge0 hJ hg16_pmf_summable.
  by move: h; rewrite hg16_pmf_sum.
qed.

lemma hg16_mu1 k : mu1 hg16_distr k = hg16_pmf k.
proof. by rewrite /hg16_distr Distr.muK 1:hg16_pmf_isdistr. qed.

lemma hg16_distr_ll : is_lossless hg16_distr.
proof.
  rewrite /is_lossless weightE.
  have he : mu1 hg16_distr = hg16_pmf by apply fun_ext => k; exact (hg16_mu1 k).
  by rewrite he hg16_pmf_sum.
qed.

lemma hg16_support k : (k \in hg16_distr) <=> 0 <= k.
proof.
  rewrite /Distr.support hg16_mu1 /hg16_pmf.
  case (0<=k) => hk.
  + have hp := hg16_rho_pos k hk; have hz := hg16_normalizer_pos.
    have hf := divr_gt0 (hg16_rho k) hg16_normalizer hp hz; smt().
  by rewrite /hg16_rho hk /=.
qed.

lemma hg16_cdfE k :
  hg16_cdf k = hg16_partial (k+1) / hg16_normalizer.
proof.
  rewrite /hg16_cdf muE.
  have he : (fun x => if x<=k then mu1 hg16_distr x else 0%r) =
      (fun x => (if x<=k then hg16_rho x else 0%r) * inv hg16_normalizer).
  + by apply fun_ext => x; rewrite hg16_mu1 /hg16_pmf; case (x<=k) => hx /=.
  rewrite he RealSeries.sumZr.
  congr; rewrite (RealSeries.sumE_fin _ (range 0 (k+1))) 1:range_uniq.
  + move=> x; rewrite /hg16_rho mem_range; smt().
  rewrite /hg16_partial; apply eq_big_int => x hx /=; smt().
qed.

lemma hg16_tail_probability N :
  mu hg16_distr (fun k=>N<=k) = hg16_tail N / hg16_normalizer.
proof.
  rewrite muE /hg16_tail.
  have he : (fun k => if N<=k then mu1 hg16_distr k else 0%r) =
      (fun k => (if N<=k then hg16_rho k else 0%r) * inv hg16_normalizer).
  + by apply fun_ext => k; rewrite hg16_mu1 /hg16_pmf; case (N<=k) => hk /=.
  by rewrite he RealSeries.sumZr.
qed.

lemma hg16_tail_probability_bound N : 0 <= N =>
  mu hg16_distr (fun k=>N<=k) <= hg16_tail_bound N / hg16_normalizer.
proof.
  move=> hN; rewrite hg16_tail_probability.
  apply ler_wpmul2r; first by apply invr_ge0; smt(hg16_normalizer_pos).
  exact (hg16_tail_le N hN).
qed.

end HalfGaussianProperties.
