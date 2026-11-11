require import AllCore IntDiv List Real RealSeries StdRing StdOrder StdBigop.
require import GaussianBlockReindex.
import IntOrder RField RealOrder Bigreal Bigreal.BRA.

op gls_stride (f : int -> real) (m k : int) : real =
  if 0 <= k then f (m*k) else 0%r.

op gls_next (f : int -> real) (m k : int) : real =
  if 0 <= k then f (m*(k+1)) else 0%r.

op gls_half_sum (f : int -> real) (m : int) : real =
  RealSeries.sum (gls_stride f m) - f 0 / 2%r.

op gls_block (f : int -> real) (m x : int) : real =
  RealSeries.sum (fun y => if 0 <= x /\ 0 <= y < m then f (m*x+y) else 0%r).

lemma gls_stride_summable f m : 0 < m => RealSeries.summable f =>
  RealSeries.summable (gls_stride f m).
proof.
  move=> hm hs.
  have hinj : injective (fun k : int => m*k) by move=> i j; smt().
  have h := RealSeries.summable_inj (fun k : int => m*k) f hinj hs.
  exact (RealSeries.summable_cond (f \o (fun k : int => m*k)) (fun k => 0 <= k) h).
qed.

lemma gls_next_summable f m : 0 < m => RealSeries.summable f =>
  RealSeries.summable (gls_next f m).
proof.
  move=> hm hs.
  have hinj : injective (fun k : int => m*(k+1)) by move=> i j; smt().
  have h := RealSeries.summable_inj (fun k : int => m*(k+1)) f hinj hs.
  exact (RealSeries.summable_cond (f \o (fun k : int => m*(k+1))) (fun k => 0 <= k) h).
qed.

lemma gls_next_sum f m : 0 < m => RealSeries.summable f =>
  RealSeries.sum (gls_next f m) = RealSeries.sum (gls_stride f m) - f 0.
proof.
  move=> hm hs.
  have hstride := gls_stride_summable f m hm hs.
  pose positive := fun k => if k <> 0 then gls_stride f m k else 0%r.
  have hp : RealSeries.summable positive by
    exact (RealSeries.summable_cond (gls_stride f m) (fun k => k <> 0) hstride).
  have hb : bijective (fun k : int => k+1).
  + exists (fun k : int => k-1); split; smt().
  have hr := RealSeries.sum_reindex (fun k : int => k+1) positive hb hp.
  have he : RealSeries.sum (gls_next f m) = RealSeries.sum positive.
  + rewrite -hr; apply RealSeries.eq_sum => k /=.
    rewrite /gls_next /positive /(\o) /gls_stride; smt().
  have hd := RealSeries.sumD1 (gls_stride f m) 0 hstride.
  rewrite /gls_stride /= in hd.
  rewrite he /positive /gls_stride; smt().
qed.

lemma gls_stride_one f : (forall k, k < 0 => f k = 0%r) =>
  gls_stride f 1 = f.
proof.
  move=> hn; apply fun_ext => k; rewrite /gls_stride /=.
  case (0 <= k); smt().
qed.

lemma gls_block_positive f m x : 0 < m => 0 <= x =>
  gls_block f m x = Bigreal.BRA.bigi predT (fun y => f (m*x+y)) 0 m.
proof.
  move=> hm hx; rewrite /gls_block hx /=.
  rewrite (RealSeries.sumE_fin _ (range 0 m)) 1:range_uniq.
  + move=> y; case (0 <= y < m) => hy /=; smt(mem_range).
  apply eq_big_seq => y; rewrite mem_range => hy /=.
  by rewrite hy.
qed.

lemma gls_block_bounds f m x : 0 < m =>
  (forall i j, 0 <= i <= j => f j <= f i) =>
  gls_stride f m x + (m-1)%r * gls_next f m x <= gls_block f m x <=
    m%r * gls_stride f m x.
proof.
  move=> hm hmono; case (0 <= x) => hx.
  + rewrite (gls_block_positive f m x hm hx) /gls_stride /gls_next hx /=.
    have hu : Bigreal.BRA.bigi predT (fun y => f (m*x+y)) 0 m <= m%r*f (m*x).
    + rewrite -(Bigreal.sumri_const (f (m*x)) 0 m _) 1:/# /=.
      apply Bigreal.ler_sum_seq => y; rewrite mem_range => hy _.
      apply hmono; smt().
    have hl : (m-1)%r*f (m*(x+1)) <=
        Bigreal.BRA.bigi predT (fun y => f (m*x+y)) 1 m.
    + rewrite -(Bigreal.sumri_const (f (m*(x+1))) 1 m _) 1:/#.
      apply Bigreal.ler_sum_seq => y; rewrite mem_range => hy _.
      apply hmono; smt().
    split; last by move=> _; exact hu.
    rewrite (big_ltn 0 m (fun y => f (m*x+y)) hm) /=; smt().
  rewrite /gls_stride /gls_next /gls_block hx /= RealSeries.sum0; trivial.
qed.

lemma gls_sum_bounds f m : 0 < m => RealSeries.summable f =>
  (forall k, k < 0 => f k = 0%r) =>
  (forall i j, 0 <= i <= j => f j <= f i) =>
  m%r * RealSeries.sum (gls_stride f m) - (m-1)%r*f 0 <= RealSeries.sum f <=
    m%r * RealSeries.sum (gls_stride f m).
proof.
  move=> hm hs hn hmono.
  have hstride := gls_stride_summable f m hm hs.
  have hnext := gls_next_summable f m hm hs.
  have hblock := gb_block_outer_summable m f hm hs hn.
  have hscaled := RealSeries.summableZ (gls_stride f m) m%r hstride.
  have hlow := RealSeries.summableD (gls_stride f m)
    (fun k => (m-1)%r * gls_next f m k) hstride
    (RealSeries.summableZ (gls_next f m) (m-1)%r hnext).
  have hu := RealSeries.ler_sum (gls_block f m)
    (fun k => m%r * gls_stride f m k) _ hblock hscaled.
  + move=> k; have h := gls_block_bounds f m k hm hmono; smt().
  have hl := RealSeries.ler_sum
    (fun k => gls_stride f m k + (m-1)%r * gls_next f m k)
    (gls_block f m) _ hlow hblock.
  + move=> k; have h := gls_block_bounds f m k hm hmono; smt().
  rewrite /gls_block (gb_block_sum m f hm hs hn) RealSeries.sumZ in hu.
  rewrite /gls_block (gb_block_sum m f hm hs hn)
    (RealSeries.sumD _ _ hstride (RealSeries.summableZ _ _ hnext))
    RealSeries.sumZ (gls_next_sum f m hm hs) fromintB /= in hl.
  clear hs hn hmono hstride hnext hblock hscaled hlow.
  rewrite fromintB /=; smt().
qed.

(* Half weight at zero centers the two monotone rectangle bounds. *)
lemma gls_half_comparison f m : 0 < m => RealSeries.summable f =>
  (forall k, k < 0 => f k = 0%r) =>
  (forall i j, 0 <= i <= j => f j <= f i) => f 0 = 1%r =>
  `|m%r * gls_half_sum f m - gls_half_sum f 1| <= (m-1)%r / 2%r.
proof.
  move=> hm hs hn hmono hzero.
  have h := gls_sum_bounds f m hm hs hn hmono.
  rewrite /gls_half_sum (gls_stride_one f hn) hzero ler_norml fromintB /=.
  move: h; rewrite hzero fromintB /=; smt().
qed.

lemma gls_two_half_comparison f m n : 0 < m => 0 < n => RealSeries.summable f =>
  (forall k, k < 0 => f k = 0%r) =>
  (forall i j, 0 <= i <= j => f j <= f i) => f 0 = 1%r =>
  `|m%r * gls_half_sum f m - n%r * gls_half_sum f n| <= (m+n-2)%r / 2%r.
proof.
  move=> hm hn hs hneg hmono hzero.
  have h1 := gls_half_comparison f m hm hs hneg hmono hzero.
  have h2 := gls_half_comparison f n hn hs hneg hmono hzero.
  rewrite ler_norml in h1.
  rewrite ler_norml in h2.
  rewrite ler_norml fromintB fromintD /=.
  move: h1 h2; rewrite !fromintB /=; smt().
qed.
