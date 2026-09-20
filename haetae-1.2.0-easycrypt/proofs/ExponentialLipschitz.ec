require import AllCore StdRing StdOrder RealExp.
import RField RealOrder.

(* The installed logarithm bound and exp/ln inverse laws provide the
   supporting linear bound. No derivative or extra analytic premise is
   needed. This bound itself holds for every real x. *)
lemma exp_neg_linear_lower (x : real) :
  1%r - x <= RealExp.exp (-x).
proof.
  have h := RealExp.le_ln_up (RealExp.exp (-x)) (RealExp.exp_gt0 (-x)).
  rewrite RealExp.lnK in h; smt().
qed.

lemma exp_neg_ordered_difference (a b : real) :
  0%r <= a => a <= b =>
  0%r <= RealExp.exp (-a) - RealExp.exp (-b) <= b-a.
proof.
  move=> ha hab.
  have hmono := RealExp.exp_mono (-b) (-a).
  have ha1 : RealExp.exp (-a) <= 1%r.
  + have h := RealExp.exp_mono (-a) 0%r.
    rewrite RealExp.exp0 in h; smt().
  have hd1 : RealExp.exp (-(b-a)) <= 1%r.
  + have h := RealExp.exp_mono (-(b-a)) 0%r.
    rewrite RealExp.exp0 in h; smt().
  have hd0 : 0%r <= 1%r - RealExp.exp (-(b-a)) by smt().
  have hmul := ler_wpmul2r (1%r - RealExp.exp (-(b-a))) hd0
    (RealExp.exp (-a)) 1%r ha1.
  have hlin := exp_neg_linear_lower (b-a).
  have he : RealExp.exp (-b) = RealExp.exp (-a) * RealExp.exp (-(b-a)).
  + rewrite -RealExp.expD; congr; ring.
  smt().
qed.

lemma exp_neg_lipschitz (a b : real) :
  0%r <= a => 0%r <= b =>
  `|RealExp.exp (-a) - RealExp.exp (-b)| <= `|a-b|.
proof.
  move=> ha hb; case (a<=b) => hab.
  + have h := exp_neg_ordered_difference a b ha hab.
    rewrite (ger0_norm (RealExp.exp (-a) - RealExp.exp (-b))) 1:/#.
    rewrite (ler0_norm (a-b)) 1:/#; smt().
  have hba : b<=a by smt().
  have h := exp_neg_ordered_difference b a hb hba.
  rewrite (ler0_norm (RealExp.exp (-a) - RealExp.exp (-b))) 1:/#.
  rewrite (ger0_norm (a-b)) 1:/#; smt().
qed.

lemma exp_neg_perturbation (a b epsilon : real) :
  0%r <= a => 0%r <= b => `|a-b| <= epsilon =>
  `|RealExp.exp (-a) - RealExp.exp (-b)| <= epsilon.
proof.
  move=> ha hb he.
  exact (ler_trans _ _ _ (exp_neg_lipschitz a b ha hb) he).
qed.
