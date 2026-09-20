require import AllCore IntDiv List Real RealExp StdRing StdOrder.
require import ApproxExpSpec ApproxExpCertificate ApproxExpCertificateChecks
  Bernstein10Spec Bernstein10Correctness ExponentialGridComparison.
import RField RealOrder ExponentialGridComparison.

lemma aec_residual_nonnegative r :
  0%r <= aec_denominator%r * ae_scale%r * r => 0%r <= r.
proof.
  have h : 0%r < aec_denominator%r * ae_scale%r by
    rewrite /aec_denominator /ae_scale /=.
  smt().
qed.

lemma aec_cell_0_nonnegative t : 0%r <= t <= 1%r =>
  0%r <= aec_upper_residual (aec_cell 0 t) /\
  0%r <= aec_lower_residual (aec_cell 0 t).
proof.
  move=> ht.
  have hu := bernstein10_checked_nonnegative aec_upper_0_power
    aec_upper_0_bernstein t aec_upper_0_checked ht.
  have hl := bernstein10_checked_nonnegative aec_lower_0_power
    aec_lower_0_bernstein t aec_lower_0_checked ht.
  rewrite aec_upper_0_identity in hu.
  rewrite aec_lower_0_identity in hl.
  split; apply aec_residual_nonnegative; assumption.
qed.

lemma aec_cell_1_nonnegative t : 0%r <= t <= 1%r =>
  0%r <= aec_upper_residual (aec_cell 1 t) /\
  0%r <= aec_lower_residual (aec_cell 1 t).
proof.
  move=> ht.
  have hu := bernstein10_checked_nonnegative aec_upper_1_power
    aec_upper_1_bernstein t aec_upper_1_checked ht.
  have hl := bernstein10_checked_nonnegative aec_lower_1_power
    aec_lower_1_bernstein t aec_lower_1_checked ht.
  rewrite aec_upper_1_identity in hu.
  rewrite aec_lower_1_identity in hl.
  split; apply aec_residual_nonnegative; assumption.
qed.

lemma aec_cell_2_nonnegative t : 0%r <= t <= 1%r =>
  0%r <= aec_upper_residual (aec_cell 2 t) /\
  0%r <= aec_lower_residual (aec_cell 2 t).
proof.
  move=> ht.
  have hu := bernstein10_checked_nonnegative aec_upper_2_power
    aec_upper_2_bernstein t aec_upper_2_checked ht.
  have hl := bernstein10_checked_nonnegative aec_lower_2_power
    aec_lower_2_bernstein t aec_lower_2_checked ht.
  rewrite aec_upper_2_identity in hu.
  rewrite aec_lower_2_identity in hl.
  split; apply aec_residual_nonnegative; assumption.
qed.

lemma aec_residual_bounds z : 0%r <= z <= 2%r/3%r =>
  0%r <= aec_upper_residual z /\ 0%r <= aec_lower_residual z.
proof.
  move=> hz.
  case (z <= 2%r/9%r) => h0.
  + have ht : 0%r <= 9%r*z/2%r <= 1%r by smt().
    have he : z = aec_cell 0 (9%r*z/2%r) by rewrite /aec_cell /=; field.
    rewrite he; exact (aec_cell_0_nonnegative _ ht).
  case (z <= 4%r/9%r) => h1.
  + have ht : 0%r <= (9%r*z-2%r)/2%r <= 1%r by smt().
    have he : z = aec_cell 1 ((9%r*z-2%r)/2%r) by rewrite /aec_cell /=; field.
    rewrite he; exact (aec_cell_1_nonnegative _ ht).
  have ht : 0%r <= (9%r*z-4%r)/2%r <= 1%r by smt().
  have he : z = aec_cell 2 ((9%r*z-4%r)/2%r) by rewrite /aec_cell /=; field.
  rewrite he; exact (aec_cell_2_nonnegative _ ht).
qed.

lemma aec_recurrences z : 0%r <= z <= 2%r/3%r =>
  ae_scale%r * (ae_polynomial z + aec_error) <=
    (ae_scale+1)%r * (ae_polynomial (z+1%r/ae_scale%r) + aec_error) /\
  ae_scale%r * (ae_polynomial (z+1%r/ae_scale%r) - aec_error) <=
    (ae_scale-1)%r * (ae_polynomial z - aec_error).
proof.
  move=> hz; have h := aec_residual_bounds z hz.
  move: h; rewrite /aec_upper_residual /aec_lower_residual; smt().
qed.

lemma aec_grid_domain i : 0 <= i <= aec_domain_limit =>
  0%r <= i%r/ae_scale%r <= 2%r/3%r.
proof.
  rewrite /aec_domain_limit => hi.
  have hi0 : 0%r <= i%r by rewrite le_fromint; smt().
  have hib : i%r <= 187649984473770%r by rewrite le_fromint; smt().
  rewrite /ae_scale; smt().
qed.

lemma aec_initial_bounds :
  ae_polynomial 0%r - aec_error <= 1%r <= ae_polynomial 0%r + aec_error.
proof.
  rewrite aec_polynomial_power /aec_coefficients /aec_scale /power_eval /rev
    /aec_error /aec_error_units /ae_scale /=.
  smt().
qed.

lemma aec_domain_limit_iff x :
  ae_domain x = (0 <= x <= aec_domain_limit).
proof. by rewrite /ae_domain /ae_scale /aec_domain_limit; smt(). qed.

(* Finite-grid induction, with all analytic recurrence premises discharged by
   the concrete Bernstein certificates, covers every valid integer argument. *)
lemma approx_exp_polynomial_error x : ae_domain x =>
  `|ae_polynomial (x%r/ae_scale%r) -
    RealExp.exp (-(x%r/ae_scale%r))| <= 24%r/ae_scale%r.
proof.
  move=> hx.
  have hm : 1 < ae_scale by rewrite /ae_scale.
  have hL : 0 <= aec_domain_limit by rewrite /aec_domain_limit.
  have hE : 0%r <= aec_error by rewrite /aec_error /aec_error_units /ae_scale; smt().
  have hupper : forall i, 0 <= i < aec_domain_limit =>
      ae_scale%r*(ae_polynomial (i%r/ae_scale%r)+aec_error) <=
      (ae_scale+1)%r*(ae_polynomial ((i+1)%r/ae_scale%r)+aec_error).
  + move=> i hi.
    have hd := aec_grid_domain i _; first smt().
    have [hu _] := aec_recurrences (i%r/ae_scale%r) hd.
    have he : (i+1)%r/ae_scale%r = i%r/ae_scale%r + 1%r/ae_scale%r
      by rewrite fromintD; ring.
    by rewrite he.
  have hlower : forall i, 0 <= i < aec_domain_limit =>
      ae_scale%r*(ae_polynomial ((i+1)%r/ae_scale%r)-aec_error) <=
      (ae_scale-1)%r*(ae_polynomial (i%r/ae_scale%r)-aec_error).
  + move=> i hi.
    have hd := aec_grid_domain i _; first smt().
    have [_ hl] := aec_recurrences (i%r/ae_scale%r) hd.
    have he : (i+1)%r/ae_scale%r = i%r/ae_scale%r + 1%r/ae_scale%r
      by rewrite fromintD; ring.
    by rewrite he.
  have hxi : 0 <= x <= aec_domain_limit by move: hx; rewrite aec_domain_limit_iff.
  have h := eg_exp_grid_abs ae_scale aec_domain_limit ae_polynomial aec_error
    hm hL hE aec_initial_bounds hupper hlower x hxi.
  by move: h; rewrite /aec_error /aec_error_units.
qed.
