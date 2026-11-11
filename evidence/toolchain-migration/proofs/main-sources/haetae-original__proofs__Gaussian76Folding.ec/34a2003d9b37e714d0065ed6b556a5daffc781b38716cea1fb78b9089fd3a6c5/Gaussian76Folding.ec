require import AllCore IntDiv Real RealSeries Distr StdRing StdOrder.
require import Gaussian76Spec Gaussian76Properties.
import RField RealOrder.

(* Folding keeps zero once and joins the positive and negative copies of
   each strictly positive integer. *)
lemma g76_fold_summable (f : int -> real) :
  RealSeries.summable f =>
  RealSeries.summable (fun z =>
    if 0 <= z then (if z = 0 then 1%r else 2%r) * f z else 0%r).
proof.
  move=> hs.
  have hnonneg := RealSeries.summable_cond f (fun z => 0 <= z) hs.
  have hpos := RealSeries.summable_cond f (fun z => 0 < z) hs.
  have hboth := RealSeries.summableD _ _ hnonneg hpos.
  apply (RealSeries.eqL_summable _ _ hboth) => z /=.
  case (0 <= z); case (z = 0); smt().
qed.

lemma g76_even_sum_fold (f : int -> real) :
  RealSeries.summable f =>
  (forall z, f (-z) = f z) =>
  RealSeries.sum f = RealSeries.sum (fun z =>
    if 0 <= z then (if z = 0 then 1%r else 2%r) * f z else 0%r).
proof.
  move=> hs heven.
  have hnonneg := RealSeries.summable_cond f (fun z => 0 <= z) hs.
  have hpos := RealSeries.summable_cond f (fun z => 0 < z) hs.
  have hneg := RealSeries.summable_cond f (fun z => !(0 <= z)) hs.
  have hbij : bijective (fun z : int => -z).
  + exists (fun z : int => -z); split; smt().
  have hreflect := RealSeries.sum_reindex (fun z : int => -z)
    (fun z => if !(0 <= z) then f z else 0%r) hbij hneg.
  have hmirror :
    RealSeries.sum (fun z => if !(0 <= z) then f z else 0%r) =
    RealSeries.sum (fun z => if 0 < z then f z else 0%r).
  + rewrite -hreflect; apply RealSeries.eq_sum => z /=.
    rewrite /(\o) /= heven; smt().
  rewrite (RealSeries.sum_split f (fun z => 0 <= z) hs) hmirror.
  rewrite -(RealSeries.sumD _ _ hnonneg hpos).
  apply RealSeries.eq_sum => z /=.
  case (0 <= z); case (z = 0); smt().
qed.

lemma g76_event_summable (f : int -> real) (event : int -> bool) :
  RealSeries.summable f =>
  RealSeries.summable (fun z => f z * b2r (event z)).
proof.
  move=> hs.
  have hcond := RealSeries.summable_cond f event hs.
  apply (RealSeries.eqL_summable _ _ hcond) => z /=.
  by case (event z); rewrite /b2r /=.
qed.

lemma g76_fold_weight_negative (z : int) :
  z < 0 => g76_fold_weight z = 0%r.
proof. rewrite /g76_fold_weight; smt(). qed.

lemma g76_accept_weight_negative (z : int) :
  z < 0 => g76_accept_weight z = 0%r.
proof. rewrite /g76_accept_weight; smt(). qed.

lemma g76_fold_weight_ge0 (z : int) : 0%r <= g76_fold_weight z.
proof.
  have h := g76_rho_ge0 z; rewrite /g76_fold_weight.
  case (0 <= z); case (z = 0); smt().
qed.

lemma g76_accept_fold (z : int) :
  2%r * g76_accept_weight z = g76_fold_weight z.
proof.
  rewrite /g76_accept_weight /g76_fold_weight.
  case (0 <= z); case (z = 0); smt().
qed.

lemma g76_accept_weight_ge0 (z : int) : 0%r <= g76_accept_weight z.
proof. have := g76_fold_weight_ge0 z; have := g76_accept_fold z; smt(). qed.

lemma g76_fold_weight_summable : RealSeries.summable g76_fold_weight.
proof. rewrite /g76_fold_weight; exact (g76_fold_summable _ g76_rho_summable). qed.

lemma g76_fold_weight_sum : RealSeries.sum g76_fold_weight = g76_normalizer.
proof.
  rewrite /g76_normalizer /g76_fold_weight.
  have := g76_even_sum_fold _ g76_rho_summable g76_rho_symmetry; smt().
qed.

lemma g76_accept_weight_scaled :
  g76_accept_weight = (fun z => (1%r/2%r) * g76_fold_weight z).
proof. apply fun_ext => z; have := g76_accept_fold z; smt(). qed.

lemma g76_accept_weight_summable : RealSeries.summable g76_accept_weight.
proof.
  rewrite g76_accept_weight_scaled; apply RealSeries.summableZ.
  exact g76_fold_weight_summable.
qed.

lemma g76_accept_weight_sum :
  RealSeries.sum g76_accept_weight = g76_normalizer / 2%r.
proof.
  by rewrite g76_accept_weight_scaled RealSeries.sumZ g76_fold_weight_sum; ring.
qed.

lemma g76_fold_event_summable (S : int -> bool) :
  RealSeries.summable (fun z =>
    g76_fold_weight z * b2r (S (g76_round_magnitude z))).
proof. exact (g76_event_summable _ _ g76_fold_weight_summable). qed.

lemma g76_accept_event_summable (S : int -> bool) :
  RealSeries.summable (fun z =>
    g76_accept_weight z * b2r (S (g76_round_magnitude z))).
proof. exact (g76_event_summable _ _ g76_accept_weight_summable). qed.

lemma g76_signed_event_sum_fold (S : int -> bool) :
  RealSeries.sum (fun k => g76_rho k * b2r (S (g76_round_absolute k))) =
  RealSeries.sum (fun z =>
    g76_fold_weight z * b2r (S (g76_round_magnitude z))).
proof.
  have hs := g76_event_summable g76_rho
    (fun k => S (g76_round_absolute k)) g76_rho_summable.
  have heven : forall k,
    g76_rho (-k) * b2r (S (g76_round_absolute (-k))) =
    g76_rho k * b2r (S (g76_round_absolute k)).
  + move=> k; rewrite g76_rho_symmetry /g76_round_absolute.
    have -> : `|-k| = `|k| by smt().
    trivial.
  rewrite (g76_even_sum_fold _ hs heven).
  apply RealSeries.eq_sum => z /=; rewrite /g76_fold_weight.
  case (0 <= z) => hz; last by rewrite /=.
  rewrite /= /g76_round_absolute.
  have -> : `|z| = z by smt().
  ring.
qed.

lemma g76_rounded_event_law (S : int -> bool) :
  mu g76_rounded S =
  RealSeries.sum (fun z =>
    g76_fold_weight z * b2r (S (g76_round_magnitude z))) / g76_normalizer.
proof.
  rewrite /g76_rounded dmapE muE.
  rewrite -(g76_signed_event_sum_fold S) -RealSeries.sumZr.
  apply RealSeries.eq_sum => k /=.
  rewrite /(\o) g76_distr_mu1 /g76_pmf.
  by case (S (g76_round_absolute k)); rewrite /b2r /=.
qed.

lemma g76_fold_accept_event_sum (S : int -> bool) :
  RealSeries.sum (fun z =>
    g76_fold_weight z * b2r (S (g76_round_magnitude z))) =
  2%r * RealSeries.sum (fun z =>
    g76_accept_weight z * b2r (S (g76_round_magnitude z))).
proof.
  rewrite -RealSeries.sumZ; apply RealSeries.eq_sum => z /=.
  rewrite -g76_accept_fold; ring.
qed.

lemma g76_rounded_accept_event_law (S : int -> bool) :
  mu g76_rounded S =
  2%r * RealSeries.sum (fun z =>
    g76_accept_weight z * b2r (S (g76_round_magnitude z))) / g76_normalizer.
proof. by rewrite g76_rounded_event_law g76_fold_accept_event_sum. qed.
