require import AllCore IntDiv Real Distr DBool RealSeries StdOrder StdRing.
require import SigmaConditionalSpec SigmaJointSpec SigmaJointIdealCorrectness
  SigmaRawNoiseSpec HalfGaussianSpec HalfGaussianProperties.
import RField RealOrder HalfGaussianSpec HalfGaussianProperties.

(* Both nested draws retain their original laws. In particular, there is no
   finite cutoff on the Gaussian integer and no machine-word output cast. *)
lemma sc_ideal_pair_ll : is_lossless sc_ideal_pair.
proof.
  rewrite /sc_ideal_pair.
  apply dlet_ll; first exact hg16_distr_ll.
  move=> x _; apply dlet_ll; first exact sr_noise_uniform_ll.
  move=> y _; apply dmap_ll.
  exact (Biased.dbiased_ll (sj_acceptance x y)).
qed.

lemma sc_ideal_joint_kernel (event : int -> bool) :
  mu sc_ideal_pair (fun r => sc_accepted r /\ event (sc_output r)) = sj_ideal_joint event.
proof.
  rewrite /sc_ideal_pair dletE /sj_ideal_joint /E.
  apply RealSeries.eq_sum => x /=.
  rewrite dletE /sj_noise_kernel /E.
  rewrite (mulrC (mu1 hg16_distr x)).
  congr; apply RealSeries.eq_sum => y /=.
  rewrite dmapE /(\o) /sc_accepted /sc_output /= sj_ideal_bool_law.
  ring.
qed.

lemma sc_ideal_joint_law (event : int -> bool) &m :
  mu sc_ideal_pair (fun r => sc_accepted r /\ event (sc_output r)) =
    Pr[SigmaJointIdeal.sample() @ &m : res.`2 /\ event res.`1].
proof. by rewrite sc_ideal_joint_kernel sj_ideal_joint_law. qed.

lemma sc_ideal_acceptance_law &m :
  mu sc_ideal_pair sc_accepted = Pr[SigmaJointIdeal.sample() @ &m : res.`2].
proof.
  have h := sc_ideal_joint_law (fun (_ : int) => true) &m.
  by move: h; rewrite /sc_accepted /sc_output /=.
qed.

(* This is the native dcond ratio, including the library's convention at
   zero mass. Positive acceptance is needed separately for losslessness. *)
lemma sc_ideal_conditioned_law (event : int -> bool) &m :
  mu sc_ideal_conditioned event =
    Pr[SigmaJointIdeal.sample() @ &m : res.`2 /\ event res.`1] /
      Pr[SigmaJointIdeal.sample() @ &m : res.`2].
proof.
  by rewrite /sc_ideal_conditioned dmapE dcondE /predI /(\o)
    (sc_ideal_joint_law event &m) (sc_ideal_acceptance_law &m).
qed.

lemma sc_ideal_conditioned_ll &m :
  0%r < Pr[SigmaJointIdeal.sample() @ &m : res.`2] => is_lossless sc_ideal_conditioned.
proof.
  move=> hpositive; rewrite /sc_ideal_conditioned.
  apply dmap_ll; apply dcond_ll.
  by rewrite (sc_ideal_acceptance_law &m).
qed.
