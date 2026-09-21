require import AllCore Real Distr SDist StdRing StdOrder.
require import SigmaConditionalSpec SigmaConditionalActual SigmaConditionalIdeal
  SigmaAcceptanceLowerBound ConditionalRatioBound SigmaJointCorrectness
  SigmaJoint203Bridge SigmaJointIdealCorrectness SigmaRawSpec.
import RField RealOrder.

op sc_joint_delta : real = 29%r / sr_scale%r + 1%r / (2^78)%r.
op sc_conditional_error : real = 16%r * sc_joint_delta.

lemma sc_pair_event_bounds (d : (int * bool) distr) (event : int -> bool) :
  0%r <= mu d (fun (r : int * bool) => r.`2 /\ event r.`1) <= mu d sc_accepted.
proof.
  have hlo := ge0_mu d (fun (r : int * bool) => r.`2 /\ event r.`1).
  have hhi := mu_sub d (fun (r : int * bool) => r.`2 /\ event r.`1) sc_accepted _.
  + move=> r; rewrite /sc_accepted; smt().
  smt().
qed.

(* These public distribution contracts discharge the positivity premises
   of native dcond; no acceptance lower bound is left to the caller. *)
lemma sc_actual_distribution_ll (p : BArray26.t) &m :
  is_lossless (sc_actual_conditioned p).
proof.
  apply (sc_actual_conditioned_ll p &m).
  have h := sc_actual_acceptance_lower p &m; smt().
qed.

lemma sc_ideal_distribution_ll &m : is_lossless sc_ideal_conditioned.
proof.
  apply (sc_ideal_conditioned_ll &m).
  have h := sc_ideal_acceptance_lower &m; smt().
qed.

lemma sc_actual_normalizer_bounds (p : BArray26.t) &m :
  1%r/7%r <= mu (sc_actual_pair p) sc_accepted <= 1%r.
proof.
  have hlo := sc_actual_acceptance_lower p &m.
  rewrite -(sc_actual_acceptance_law p &m) in hlo.
  have hhi := le1_mu (sc_actual_pair p) sc_accepted; smt().
qed.

lemma sc_ideal_normalizer_bounds &m :
  1%r/8%r <= mu sc_ideal_pair sc_accepted <= 1%r.
proof.
  have hlo := sc_ideal_acceptance_lower &m.
  rewrite -(sc_ideal_acceptance_law &m) in hlo.
  have hhi := le1_mu sc_ideal_pair sc_accepted; smt().
qed.

(* Both the event numerator and its own acceptance denominator may differ.
   The two denominators are not equated during normalization. *)
lemma sc_conditioned_event_error (p : BArray26.t) (event : int -> bool) &m :
  `|mu (sc_actual_conditioned p) event - mu sc_ideal_conditioned event| <=
    sc_conditional_error.
proof.
  have ha := sc_pair_event_bounds (sc_actual_pair p) event.
  rewrite (sc_actual_joint_law p event &m) (sc_actual_acceptance_law p &m) in ha.
  have hb := sc_pair_event_bounds sc_ideal_pair event.
  rewrite (sc_ideal_joint_law event &m) (sc_ideal_acceptance_law &m) in hb.
  have hscale : sc_conditional_error = 2%r * sc_joint_delta / (1%r/8%r) by
    rewrite /sc_conditional_error; field; trivial.
  rewrite (sc_actual_conditioned_law p event &m) (sc_ideal_conditioned_law event &m) hscale.
  apply (conditional_ratio_error_lower _ _ _ _ sc_joint_delta (1%r/8%r)).
  + smt().
  + have h := sc_actual_acceptance_lower p &m; smt().
  + have h := sc_ideal_acceptance_lower &m; smt().
  + exact ha.
  + exact hb.
  + have h := sj_joint_output_error p event &m.
    rewrite /sc_joint_delta; smt().
  have h := sj_joint_output_error p (fun (_ : int) => true) &m.
  move: h; rewrite /sc_joint_delta /=; smt().
qed.

(* Keep a common non-strict bound before taking the supremum over events.
   A family of strict event bounds alone would not imply a strict supremum. *)
lemma sc_conditioned_sdist (p : BArray26.t) &m :
  SDist.sdist (sc_actual_conditioned p) sc_ideal_conditioned <= sc_conditional_error.
proof.
  apply SDist.sdist_le_ub => event.
  exact (sc_conditioned_event_error p event &m).
qed.

lemma sc_conditional_error_margin :
  0%r <= sc_conditional_error /\ sc_conditional_error < 1%r / (2^39)%r.
proof. rewrite /sc_conditional_error /sc_joint_delta /sr_scale /=; smt(). qed.

lemma sc_conditioned_event_error_strict (p : BArray26.t) (event : int -> bool) &m :
  `|mu (sc_actual_conditioned p) event - mu sc_ideal_conditioned event| < 1%r / (2^39)%r.
proof.
  have h := sc_conditioned_event_error p event &m.
  have [_ hmargin] := sc_conditional_error_margin.
  exact (ler_lt_trans _ _ _ h hmargin).
qed.

lemma sc_conditioned_sdist_strict (p : BArray26.t) &m :
  SDist.sdist (sc_actual_conditioned p) sc_ideal_conditioned < 1%r / (2^39)%r.
proof.
  have h := sc_conditioned_sdist p &m.
  have [_ hmargin] := sc_conditional_error_margin.
  exact (ler_lt_trans _ _ _ h hmargin).
qed.

lemma sc_conditioned_distributions_correct (p : BArray26.t) &m :
  is_lossless (sc_actual_conditioned p) /\ is_lossless sc_ideal_conditioned /\
  SDist.sdist (sc_actual_conditioned p) sc_ideal_conditioned < 1%r / (2^39)%r.
proof.
  have ha := sc_actual_distribution_ll p &m.
  have hb := sc_ideal_distribution_ll &m.
  have hd := sc_conditioned_sdist_strict p &m.
  by rewrite ha hb hd.
qed.
