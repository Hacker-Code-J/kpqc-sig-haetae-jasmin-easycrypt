require import AllCore Distr DInterval.
from Jasmin require import JModel_x86.
require import BArray26 SigmaConditionalSpec SigmaJoint203Bridge
  SigmaJointAttemptBridge SigmaRawNoiseSpec Rejection48Spec.

(* The distribution is the exact finite word observer of the actual
   extracted attempt, with its three independent uniform inputs. *)
lemma sc_actual_pair_ll (p : BArray26.t) :
  is_lossless (sc_actual_pair p).
proof.
  rewrite /sc_actual_pair.
  apply dlet_ll; first exact sj203_uniform_ll.
  move=> u _; apply dlet_ll; first exact sr_noise_uniform_ll.
  move=> y _ /=; apply dmap_ll.
  rewrite /rejection48_uniform; apply dinter_ll; trivial.
qed.

lemma sc_actual_joint_law (p : BArray26.t) (S : int -> bool) &m :
  mu (sc_actual_pair p) (fun (r : int * bool) => r.`2 /\ S r.`1) =
    Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2 /\ S res.`1].
proof.
  rewrite sigma_joint203_law /sc_actual_pair sj203_dlet_expectation.
  apply eq_exp => u _ /=.
  rewrite sj203_dlet_expectation.
  apply eq_exp => y _ /=.
  by rewrite dmapE /(\o) /= sigma_joint_fixed_output_mass.
qed.

lemma sc_actual_acceptance_law (p : BArray26.t) &m :
  mu (sc_actual_pair p) sc_accepted =
    Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2].
proof.
  have h := sc_actual_joint_law p (fun _ => true) &m.
  by move: h; rewrite /sc_accepted /=.
qed.

(* Native conditioning uses division by the acceptance mass.  This
   identity also follows the library's zero-mass convention; losslessness
   below carries the separate, explicit positivity premise. *)
lemma sc_actual_conditioned_law (p : BArray26.t) (S : int -> bool) &m :
  mu (sc_actual_conditioned p) S =
    Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2 /\ S res.`1] /
    Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2].
proof.
  rewrite /sc_actual_conditioned dmapE dcondE.
  rewrite (sc_actual_acceptance_law p &m).
  rewrite /predI /(\o) /sc_accepted /sc_output.
  by rewrite (sc_actual_joint_law p S &m).
qed.

lemma sc_actual_conditioned_ll (p : BArray26.t) &m :
  0%r < Pr[SigmaJoint203Experiment.sample(p) @ &m : res.`2] =>
  is_lossless (sc_actual_conditioned p).
proof.
  move=> hpos; rewrite /sc_actual_conditioned.
  apply dmap_ll; apply dcond_ll.
  by rewrite (sc_actual_acceptance_law p &m).
qed.
