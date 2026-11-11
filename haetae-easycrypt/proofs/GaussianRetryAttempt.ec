require import AllCore Distr RealSeries StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 SigmaConditionalSpec SigmaConditionalActual
  SigmaJoint203Bridge SigmaJointAttemptBridge SigmaRawNoiseSpec
  SigmaNoise72Bridge SigmaCDT83Patch SigmaRejection48Bridge Rejection48Spec
  SigmaAcceptanceLowerBound.
import RealOrder.

(* This law retains both outcomes, including a rejected candidate. It is
   therefore suitable for replacing calls inside a retry loop. *)
lemma gr_actual_word_pair_law (p0 : BArray26.t) (event : int * bool -> bool) &m :
  Pr[SigmaJoint203Word.sample(p0) @ &m : event res] =
    mu (sc_actual_pair p0) event.
proof.
  byphoare (_ : p = p0 ==> event res) => //.
  proc; inline SigmaJointNoise72Word.sample.
  inline SigmaJointRejection48Word.sample; wp.
  rndsem* 0.
  rnd (fun (pr : BArray26.t * int) =>
    event (W64.to_uint (sigma_rejection48_rounded pr.`1),
      rejection48_word (W64.of_int pr.`2) (sigma_rejection48_threshold pr.`1)
        (sigma_rejection48_rounded pr.`1) = W64.one)).
  skip; auto => />.
  rewrite /sc_actual_pair !sj203_dlet_expectation.
  apply eq_exp => u _ /=.
  rewrite !sj203_dlet_expectation.
  apply eq_exp => y _ /=.
  by rewrite !dmapE /(\o) /=.
qed.

lemma gr_actual_pair_law (p0 : BArray26.t) (event : int * bool -> bool) &m :
  Pr[SigmaJoint203Experiment.sample(p0) @ &m : event res] =
    mu (sc_actual_pair p0) event.
proof.
  rewrite -(gr_actual_word_pair_law p0 event &m).
  by byequiv sigma_joint203_equiv.
qed.

module GaussianActualPair = {
  proc sample(p : BArray26.t) : int * bool = {
    var r;
    r <$ sc_actual_pair p;
    return r;
  }
}.

lemma gr_pair_draw_law (p0 : BArray26.t) (event : int * bool -> bool) &m :
  Pr[GaussianActualPair.sample(p0) @ &m : event res] =
    mu (sc_actual_pair p0) event.
proof. byphoare (_ : p = p0 ==> event res) => //; proc; rnd; skip; auto. qed.

lemma gr_actual_pair_equiv :
  equiv [SigmaJoint203Experiment.sample ~ GaussianActualPair.sample :
    ={p} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 r hp.
  rewrite (gr_actual_pair_law p{1} (pred1 r) &1)
    (gr_pair_draw_law p{2} (pred1 r) &2).
  by rewrite hp.
qed.

lemma gr_actual_acceptance_lower (p : BArray26.t) &m :
  1%r / 7%r <= mu (sc_actual_pair p) sc_accepted.
proof.
  rewrite (sc_actual_acceptance_law p &m).
  exact (sc_actual_acceptance_lower p &m).
qed.

lemma gr_actual_acceptance_positive (p : BArray26.t) &m :
  0%r < mu (sc_actual_pair p) sc_accepted.
proof. have h := gr_actual_acceptance_lower p &m; smt(). qed.
