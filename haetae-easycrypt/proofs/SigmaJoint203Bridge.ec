require import AllCore IntDiv List Distr DInterval RealSeries StdRing StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 Rejection48Spec SigmaRejection48Bridge
  SigmaRawAcceptanceCorrectness SigmaRawNoiseSpec SigmaNoise72Bridge
  CDTDistributionBridge SigmaCDT83Patch SigmaJointAttemptBridge.
import RField RealOrder.

lemma sj203_uniform_ll : is_lossless (dinter 0 (cdt83_modulus-1)).
proof. apply dinter_ll; have := cdt83_modulus_positive; smt(). qed.

lemma sj203_dlet_expectation ['a 'b] (d : 'a distr)
    (g : 'a -> 'b distr) (event : 'b -> bool) :
  mu (dlet d g) event = E d (fun x => mu (g x) event).
proof.
  rewrite dletE /E; apply RealSeries.eq_sum => x /=; ring.
qed.

(* Every random input used by the actual extracted attempt is explicit:
   83 CDT bits, 72 noise bits, and 48 rejection bits. *)
module SigmaJoint203Experiment = {
  proc sample(p : BArray26.t) : int * bool = {
    var u : int;
    var result : int * bool;
    u <$ dinter 0 (cdt83_modulus-1);
    result <@ SigmaJointNoise72.sample(sj_cdt83_patch p u);
    return result;
  }
}.

(* This observer uses the previously verified machine-word result.  The
   ideal mathematical acceptance kernel is not used by this reduction. *)
module SigmaJoint203Word = {
  proc sample(p : BArray26.t) : int * bool = {
    var u : int;
    var result : int * bool;
    u <$ dinter 0 (cdt83_modulus-1);
    result <@ SigmaJointNoise72Word.sample(sj_cdt83_patch p u);
    return result;
  }
}.

lemma sigma_joint203_equiv :
  equiv [SigmaJoint203Experiment.sample ~ SigmaJoint203Word.sample :
    ={p} ==> ={res}].
proof.
  proc; call sigma_joint_noise72_equiv; rnd; skip; auto => />.
qed.

lemma sigma_joint203_word_law (p0 : BArray26.t) (S : int -> bool) &m :
  Pr[SigmaJoint203Word.sample(p0) @ &m : res.`2 /\ S res.`1] =
    E (dinter 0 (cdt83_modulus-1)) (fun u =>
      E sr_noise_uniform (fun y =>
        b2r (S (W64.to_uint (sigma_rejection48_rounded
          (sigma_noise72_patch (sj_cdt83_patch p0 u) y)))) *
        sr_actual_probability (sigma_noise72_patch (sj_cdt83_patch p0 u) y))).
proof.
  byphoare (_ : p = p0 ==> res.`2 /\ S res.`1) => //.
  proc; inline SigmaJointNoise72Word.sample.
  inline SigmaJointRejection48Word.sample; wp.
  rndsem* 0.
  rnd (fun (pr : BArray26.t * int) =>
    rejection48_word (W64.of_int pr.`2) (sigma_rejection48_threshold pr.`1)
      (sigma_rejection48_rounded pr.`1) = W64.one /\
    S (W64.to_uint (sigma_rejection48_rounded pr.`1))).
  skip; auto => />.
  rewrite sj203_dlet_expectation.
  apply eq_exp => u _ /=.
  rewrite sj203_dlet_expectation.
  apply eq_exp => y _ /=.
  by rewrite dmapE /(\o) /= sigma_joint_fixed_output_mass.
qed.

lemma sigma_joint203_law (p0 : BArray26.t) (S : int -> bool) &m :
  Pr[SigmaJoint203Experiment.sample(p0) @ &m : res.`2 /\ S res.`1] =
    E (dinter 0 (cdt83_modulus-1)) (fun u =>
      E sr_noise_uniform (fun y =>
        b2r (S (W64.to_uint (sigma_rejection48_rounded
          (sigma_noise72_patch (sj_cdt83_patch p0 u) y)))) *
        sr_actual_probability (sigma_noise72_patch (sj_cdt83_patch p0 u) y))).
proof.
  rewrite -(sigma_joint203_word_law p0 S &m).
  by byequiv sigma_joint203_equiv.
qed.

lemma sigma_joint203_ll : islossless SigmaJoint203Experiment.sample.
proof.
  proc; call sigma_joint_noise72_ll; rnd; skip; auto => />.
  exact sj203_uniform_ll.
qed.
