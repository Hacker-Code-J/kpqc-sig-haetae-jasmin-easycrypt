require import AllCore IntDiv List Real Distr RealSeries StdRing StdOrder StdBigop.
require import Gaussian76Spec Gaussian76Properties Gaussian76Folding.
import IntOrder RField RealOrder Bigreal Bigreal.BRA.

(* Half-up rounding after a sixteen-bit shift.  Magnitude zero has a
   half-width bin because the unrounded magnitude is nonnegative. *)
op g76_round_bin_lower (r : int) : int = max 0 (65536*r-32768).
op g76_round_bin_upper (r : int) : int = 65536*r+32768.

lemma g76_round_quotient_bin z r : 0 <= z =>
  ((z+32768) %/ 65536 = r) =
    (0 <= r /\ g76_round_bin_lower r <= z < g76_round_bin_upper r).
proof.
  move=> hz.
  have hd := divz_eq (z+32768) 65536.
  have hm0 := modz_ge0 (z+32768) 65536 _; first trivial.
  have hm1 := ltz_pmod (z+32768) 65536 _; first trivial.
  rewrite /g76_round_bin_lower /g76_round_bin_upper /max.
  smt().
qed.

lemma g76_round_bin_lower_nonnegative r : 0 <= g76_round_bin_lower r.
proof. rewrite /g76_round_bin_lower /max; smt(). qed.

lemma g76_round_zero_bin :
  g76_round_bin_lower 0 = 0 /\ g76_round_bin_upper 0 = 32768.
proof. by rewrite /g76_round_bin_lower /g76_round_bin_upper /max. qed.

lemma g76_round_positive_bin r : 1 <= r =>
  g76_round_bin_lower r = 65536*r-32768 /\
  g76_round_bin_upper r = 65536*r+32768.
proof. rewrite /g76_round_bin_lower /g76_round_bin_upper /max; smt(). qed.

lemma g76_round_bin_bounds r : 0 <= r =>
  0 <= g76_round_bin_lower r < g76_round_bin_upper r.
proof. rewrite /g76_round_bin_lower /g76_round_bin_upper /max; smt(). qed.

lemma g76_round_bin_width r : 0 <= r =>
  g76_round_bin_upper r - g76_round_bin_lower r =
    if r = 0 then 32768 else 65536.
proof. rewrite /g76_round_bin_lower /g76_round_bin_upper /max; smt(). qed.

lemma g76_round_bin_member z r :
  z \in range (g76_round_bin_lower r) (g76_round_bin_upper r) =>
  0 <= z /\ 0 <= r.
proof.
  rewrite mem_range /g76_round_bin_lower /g76_round_bin_upper /max; smt().
qed.

lemma g76_round_finite_sum (weight : int -> real) r :
  (forall z, z < 0 => weight z = 0%r) =>
  RealSeries.sum (fun z => weight z * b2r ((z+32768) %/ 65536 = r)) =
    Bigreal.BRA.bigi predT weight (g76_round_bin_lower r) (g76_round_bin_upper r).
proof.
  move=> hneg.
  rewrite (RealSeries.sumE_fin _
    (range (g76_round_bin_lower r) (g76_round_bin_upper r))) 1:range_uniq.
  + move=> z hnz; rewrite mem_range.
    have hz : 0 <= z by smt().
    have he : (z+32768) %/ 65536 = r by move: hnz; rewrite /b2r; smt().
    have h := g76_round_quotient_bin z r hz; smt().
  rewrite /bigi; apply eq_big_seq => z hz /=.
  have [hz0 hr] := g76_round_bin_member z r hz.
  have h := g76_round_quotient_bin z r hz0.
  move: hz; rewrite mem_range => hz.
  have -> : (z+32768) %/ 65536 = r by smt().
  by rewrite /b2r /=.
qed.

lemma g76_round_magnitude_bin z r : 0 <= z =>
  (g76_round_magnitude z = r) =
    (0 <= r /\ g76_round_bin_lower r <= z < g76_round_bin_upper r).
proof. by rewrite /g76_round_magnitude; apply g76_round_quotient_bin. qed.

lemma g76_round_magnitude_nonnegative z : 0 <= z =>
  0 <= g76_round_magnitude z.
proof.
  move=> hz.
  have h := g76_round_magnitude_bin z (g76_round_magnitude z) hz; smt().
qed.

lemma g76_round_absolute_nonnegative k : 0 <= g76_round_absolute k.
proof.
  rewrite /g76_round_absolute; apply g76_round_magnitude_nonnegative.
  exact (IntOrder.normr_ge0 k).
qed.

lemma g76_rounded_negative r : r < 0 => mu1 g76_rounded r = 0%r.
proof.
  move=> hr; rewrite /g76_rounded dmap1E.
  apply mu0_false => k hk; rewrite /(\o) /pred1.
  have h := g76_round_absolute_nonnegative k; smt().
qed.

lemma g76_rounded_zero_ties :
  g76_round_absolute 32767 = 0 /\ g76_round_absolute (-32767) = 0 /\
  g76_round_absolute 32768 = 1 /\ g76_round_absolute (-32768) = 1.
proof. by rewrite /g76_round_absolute /g76_round_magnitude. qed.

lemma g76_rounded_bin_mass r :
  mu1 g76_rounded r =
    Bigreal.BRA.bigi predT g76_fold_weight
      (g76_round_bin_lower r) (g76_round_bin_upper r) / g76_normalizer.
proof.
  rewrite (g76_rounded_event_law (pred1 r)) /pred1 /= /g76_round_magnitude.
  by rewrite (g76_round_finite_sum g76_fold_weight r g76_fold_weight_negative).
qed.

lemma g76_rounded_mass r :
  mu1 g76_rounded r =
    if 0 <= r then
      Bigreal.BRA.bigi predT g76_fold_weight
        (g76_round_bin_lower r) (g76_round_bin_upper r) / g76_normalizer
    else 0%r.
proof.
  case (0 <= r) => hr; first exact (g76_rounded_bin_mass r).
  apply g76_rounded_negative; smt().
qed.

lemma g76_positive_bin_weight r : 1 <= r =>
  Bigreal.BRA.bigi predT g76_fold_weight
    (g76_round_bin_lower r) (g76_round_bin_upper r) =
  2%r * Bigreal.BRA.bigi predT g76_rho (65536*r-32768) (65536*r+32768).
proof.
  move=> hr; have [hl hu] := g76_round_positive_bin r hr.
  rewrite hl hu /bigi mulr_sumr.
  apply eq_big_seq => z; rewrite mem_range => hz /=.
  rewrite /g76_fold_weight.
  have -> : 0 <= z by smt().
  have -> : z <> 0 by smt().
  trivial.
qed.

lemma g76_zero_bin_weight :
  Bigreal.BRA.bigi predT g76_fold_weight 0 32768 =
    1%r + 2%r * Bigreal.BRA.bigi predT g76_rho 1 32768.
proof.
  rewrite (big_ltn 0 32768) 1:// /=.
  have hzero : g76_fold_weight 0 = 1%r by
    rewrite /g76_fold_weight /= g76_rho0.
  rewrite hzero; congr.
  rewrite /bigi mulr_sumr.
  apply eq_big_seq => z; rewrite mem_range => hz /=.
  rewrite /g76_fold_weight.
  have -> : 0 <= z by smt().
  have -> : z <> 0 by smt().
  trivial.
qed.

lemma g76_rounded_zero_mass :
  mu1 g76_rounded 0 =
    (1%r + 2%r * Bigreal.BRA.bigi predT g76_rho 1 32768) / g76_normalizer.
proof.
  by rewrite g76_rounded_bin_mass /g76_round_bin_lower /g76_round_bin_upper
    /max /= g76_zero_bin_weight.
qed.

lemma g76_rounded_positive_mass r : 1 <= r =>
  mu1 g76_rounded r =
    (2%r * Bigreal.BRA.bigi predT g76_rho (65536*r-32768) (65536*r+32768)) /
      g76_normalizer.
proof. by move=> hr; rewrite g76_rounded_bin_mass (g76_positive_bin_weight r hr). qed.
