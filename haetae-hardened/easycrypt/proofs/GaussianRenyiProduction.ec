require import AllCore Real RealExp Distr StdRing StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 GaussianRenyiSpec GaussianRenyiMoment GaussianRenyiActual
  GaussianRenyiConditioning GaussianRenyiKernelBounds SigmaExpAcceptanceCorrectness
  SigmaConditionalSpec GaussianRetryCore GaussianRetryActual
  GaussianAttemptExpectation GaussianAttemptProduction.
import RField RealOrder.

(* 45.1 is represented exactly as 451/10, not a floating-point constant. *)
op grp_official_excess : real = 2%r ^ (-(451%r/10%r)).

lemma grp_epsilon_official : grn_epsilon < grp_official_excess.
proof.
  have hpow : grn_epsilon = 2%r ^ (-68)%r.
  + have h68 : (2%r)^68=295147905179352825856%r by ring.
    by rewrite RealExp.rpow_int 1:// exprN h68 /grn_epsilon; ring.
  rewrite hpow /grp_official_excess !RealExp.rpowE 1..2:// RealExp.exp_mono_ltr.
  have hln := RealExp.ln_gt0 2%r _; first trivial.
  smt().
qed.

lemma grp_mass_bounds p :
  grn_mass_bounds (sc_actual_conditioned p) (grx_exact_output p) /\
  grn_mass_bounds (grx_exact_output p) (sc_actual_conditioned p).
proof.
  rewrite -grx_actual_conditioned /grn_mass_bounds.
  split => value; have h := grx_output_relative p value;
    move: h; rewrite /grk_delta /grn_delta; smt().
qed.

lemma grp_renyi_bounds (p : BArray26.t) (order : int) : 2<=order<=1024 =>
  grn_renyi order (sc_actual_conditioned p) (grx_exact_output p) <= 1%r+grn_epsilon /\
  grn_renyi order (grx_exact_output p) (sc_actual_conditioned p) <= 1%r+grn_epsilon.
proof.
  move=> ho.
  have [hp hq] := grx_outputs_ll p.
  have [hfp hfq] := grx_outputs_finite p.
  rewrite grx_actual_conditioned in hp.
  rewrite grx_actual_conditioned in hfp.
  have [hb hbr] := grp_mass_bounds p.
  split.
  + exact (grn_finite_bound order (sc_actual_conditioned p) (grx_exact_output p)
      hp hq hfp hfq hb ho).
  exact (grn_finite_bound order (grx_exact_output p) (sc_actual_conditioned p)
    hq hp hfq hfp hbr ho).
qed.

lemma grp_official_bound (p : BArray26.t) (order : int) : 2<=order<=1024 =>
  grn_renyi order (sc_actual_conditioned p) (grx_exact_output p) < 1%r+grp_official_excess.
proof.
  move=> ho; have h := grp_renyi_bounds p order ho.
  have hm := grp_epsilon_official; smt().
qed.

(* These are direct 2*s-1 substitutions for the specification table's
   Security row. They do not establish mode-level security parameters. *)
lemma grp_table_orders (p : BArray26.t) :
  grn_renyi 239 (sc_actual_conditioned p) (grx_exact_output p) < 1%r+grp_official_excess /\
  grn_renyi 359 (sc_actual_conditioned p) (grx_exact_output p) < 1%r+grp_official_excess /\
  grn_renyi 519 (sc_actual_conditioned p) (grx_exact_output p) < 1%r+grp_official_excess.
proof.
  have h1 := grp_official_bound p 239 _; first trivial.
  have h2 := grp_official_bound p 359 _; first trivial.
  have h3 := grp_official_bound p 519 _; first trivial.
  smt().
qed.

(* Reuse the already checked production loops, including their exact
   erasure to the uncounted actual candidate loop. *)
lemma grp_hyperball_output_law (p : BArray26.t) (event : int -> bool) &m :
  Pr[GaussianProductionCounted.hyperball() @ &m : event res.`1] =
    mu (sc_actual_conditioned p) event.
proof.
  have h1 : Pr[GaussianProductionCounted.hyperball() @ &m : event res.`1] =
    Pr[GaussianCountedActual.sample(p) @ &m : event res.`1] by
      byequiv gap_hyperball_counted_equiv.
  have h2 : Pr[GaussianCountedActual.sample(p) @ &m : event res.`1] =
    Pr[GaussianRetryActual.sample(p) @ &m : event res] by byequiv gae_actual_erasure.
  by rewrite h1 h2 gr_actual_retry_law.
qed.

lemma grp_signer_output_law (p : BArray26.t) (event : int -> bool) &m :
  Pr[GaussianProductionCounted.signer() @ &m : event res.`1] =
    mu (sc_actual_conditioned p) event.
proof.
  have h1 : Pr[GaussianProductionCounted.signer() @ &m : event res.`1] =
    Pr[GaussianCountedActual.sample(p) @ &m : event res.`1] by
      byequiv gap_signer_counted_equiv.
  have h2 : Pr[GaussianCountedActual.sample(p) @ &m : event res.`1] =
    Pr[GaussianRetryActual.sample(p) @ &m : event res] by byequiv gae_actual_erasure.
  by rewrite h1 h2 gr_actual_retry_law.
qed.

module GaussianRenyiExact = {
  proc sample(p : BArray26.t) : int = {
    var output : int;
    output <@ GaussianRetry.sample(
      grk_pair (grx_proposal p) sigma_exp_acceptance_target grx_value);
    return output;
  }
}.

lemma grp_exact_pair_positive p :
  0%r < mu (grk_pair (grx_proposal p) sigma_exp_acceptance_target grx_value) gr_accept.
proof.
  have hr : forall bytes, bytes \in grx_proposal p =>
      0%r<=sigma_exp_acceptance_target bytes<=1%r by
    move=> bytes _; have h := grb_target_range bytes; smt().
  rewrite /gr_accept (grk_pair_acceptance _ _ _ hr).
  apply grk_normalizer_positive; first exact (grx_proposal_finite p).
  + exact (grx_proposal_ll p).
  by move=> bytes _; exact (grb_target_positive bytes).
qed.

lemma grp_exact_output_law (p0 : BArray26.t) (event : int -> bool) &m :
  Pr[GaussianRenyiExact.sample(p0) @ &m : event res] = mu (grx_exact_output p0) event.
proof.
  have hl := grk_pair_ll (grx_proposal p0) sigma_exp_acceptance_target grx_value (grx_proposal_ll p0).
  have hp := grp_exact_pair_positive p0.
  have he : gr_output (grk_pair (grx_proposal p0) sigma_exp_acceptance_target grx_value) =
      grx_exact_output p0 by rewrite /gr_output /gr_accept /grx_exact_output /grk_output.
  have hc := gr_retry_phoare
    (grk_pair (grx_proposal p0) sigma_exp_acceptance_target grx_value) event hl hp.
  rewrite he in hc.
  byphoare (_ : p=p0 ==> event res) => //.
  proc; call hc; auto.
qed.

lemma grp_exact_ll : islossless GaussianRenyiExact.sample.
proof.
  bypr => &m _; rewrite (grp_exact_output_law p{m} (fun _ => true) &m).
  have [_ h] := grx_outputs_ll p{m}; exact h.
qed.

lemma grp_production_comparison (p : BArray26.t) (order : int) &m : 2<=order<=1024 =>
  (forall event, Pr[GaussianProductionCounted.hyperball() @ &m : event res.`1] =
    mu (sc_actual_conditioned p) event) /\
  (forall event, Pr[GaussianProductionCounted.signer() @ &m : event res.`1] =
    mu (sc_actual_conditioned p) event) /\
  (forall event, Pr[GaussianRenyiExact.sample(p) @ &m : event res] =
    mu (grx_exact_output p) event) /\
  grn_renyi order (sc_actual_conditioned p) (grx_exact_output p) <= 1%r+grn_epsilon /\
  grn_renyi order (sc_actual_conditioned p) (grx_exact_output p) < 1%r+grp_official_excess.
proof.
  move=> ho.
  split; first by move=> event; exact (grp_hyperball_output_law p event &m).
  split; first by move=> event; exact (grp_signer_output_law p event &m).
  split; first by move=> event; exact (grp_exact_output_law p event &m).
  have [h _] := grp_renyi_bounds p order ho.
  split; [exact h | exact (grp_official_bound p order ho)].
qed.
