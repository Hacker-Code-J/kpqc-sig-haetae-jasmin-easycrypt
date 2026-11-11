require import AllCore List Real Distr DList StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 GaussianAcceptanceConstants GaussianAcceptanceIdeal
  SigmaConditionalSpec SigmaConditionalActual SigmaConditionalIdeal
  SigmaJointCorrectness SigmaJoint203Bridge GaussianRetryTail.
import RealOrder.

(* This averages the independent CDT, noise and rejection draws. It is not
   a lower bound after fixing the candidate's CDT and noise fields. *)
lemma gaa_acceptance_lower (p : BArray26.t) &m :
  19%r/20%r < mu (sc_actual_pair p) sc_accepted.
proof.
  have hi := gai_ideal_acceptance_lower.
  have [_ he] := sj_joint_output_error_strict p (fun _ => true) &m.
  move: he; rewrite /= -sc_actual_acceptance_law -sc_ideal_acceptance_law.
  rewrite ltr_norml.
  have hm := gac_acceptance_margin.
  smt().
qed.

lemma gaa_rejection_upper (p : BArray26.t) &m :
  mu (sc_actual_pair p) (predC sc_accepted) < 1%r/20%r.
proof.
  have h := gaa_acceptance_lower p &m.
  rewrite mu_not (sc_actual_pair_ll p); smt().
qed.

lemma gaa_extracted_acceptance (p : BArray26.t) &m :
  19%r/20%r < Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2].
proof. by rewrite -sc_actual_acceptance_law; exact (gaa_acceptance_lower p &m). qed.

lemma gaa_extracted_rejection (p : BArray26.t) &m :
  Pr[SigmaJoint203Experiment.sample(p) @ &m : !res.`2] < 1%r/20%r.
proof.
  have ha := gaa_extracted_acceptance p &m.
  have hl : Pr[SigmaJoint203Experiment.sample(p) @ &m : true] = 1%r
    by byphoare sigma_joint203_ll.
  rewrite Pr[mu_not]; smt().
qed.

(* A finite independent list of candidate trials has the corresponding
   geometric no-success tail. The empty prefix has probability one. *)
lemma gaa_iid_rejection_tail (p : BArray26.t) (n : int) &m :
  0 <= n =>
  mu (DList.dlist (sc_actual_pair p) n) (all (predC snd)) <= (1%r/20%r)^n.
proof.
  move=> hn.
  rewrite (gaussian_retry_tail_exact (sc_actual_pair p) n (sc_actual_pair_ll p) hn).
  have hp := gaa_acceptance_lower p &m.
  have hb := mu_bounded (sc_actual_pair p) snd.
  apply (ler_pexp n (1%r-mu (sc_actual_pair p) snd) (1%r/20%r) hn).
  move: hp; rewrite /sc_accepted; smt().
qed.
