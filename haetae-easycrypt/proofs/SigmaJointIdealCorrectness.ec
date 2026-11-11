require import AllCore IntDiv Real Distr DBool StdRing StdOrder.
require import SigmaJointSpec SigmaJointKernelCorrectness SigmaRawNoiseSpec
  HalfGaussianSpec HalfGaussianProperties.
import RField RealOrder HalfGaussianSpec HalfGaussianProperties.

(* Independent ideal experiment, including the entire infinite Gaussian
   support. Its output is an integer, never a converted machine word. *)
module SigmaJointIdeal = {
  proc sample() : int * bool = {
    var x, y : int;
    var accepted : bool;
    x <$ hg16_distr;
    y <$ sr_noise_uniform;
    accepted <$ Biased.dbiased (sj_acceptance x y);
    return (sj_round x y, accepted);
  }
}.

lemma sj_ideal_bool_law (x y : int) (event : int -> bool) :
  mu (Biased.dbiased (sj_acceptance x y))
    (fun b => b /\ event (sj_round x y)) = sj_kernel x y event.
proof.
  rewrite Biased.dbiasedE Biased.clamp_id 1:sj_acceptance_range /= /sj_kernel /b2r.
  case (event (sj_round x y)); smt().
qed.

lemma sj_ideal_joint_law (event : int -> bool) &m :
  Pr[SigmaJointIdeal.sample() @ &m : res.`2 /\ event res.`1] = sj_ideal_joint event.
proof.
  byphoare (_ : true ==> res.`2 /\ event res.`1) => //.
  proc; wp; rndsem* 0.
  rnd (fun (xyb : int * int * bool) => xyb.`3 /\ event (sj_round xyb.`1 xyb.`2)).
  skip; auto => />.
  rewrite dletE /sj_ideal_joint /E.
  apply RealSeries.eq_sum => x /=.
  rewrite dletE /sj_noise_kernel /E.
  rewrite (mulrC (mu1 hg16_distr x)).
  congr; apply RealSeries.eq_sum => y /=.
  rewrite dmapE /(\o) /= sj_ideal_bool_law; ring.
qed.

lemma sj_ideal_joint_ll : islossless SigmaJointIdeal.sample.
proof.
  proc; wp; rnd; rnd; rnd; skip; auto => />.
  have hinner : forall x,
      mu sr_noise_uniform (fun y => weight (Biased.dbiased (sj_acceptance x y)) = 1%r) = 1%r.
  + move=> x.
    have he : (fun y => weight (Biased.dbiased (sj_acceptance x y)) = 1%r) =
        (fun (_ : int) => true).
    - apply fun_ext => y.
      have hb : weight (Biased.dbiased (sj_acceptance x y)) = 1%r by
        exact (Biased.dbiased_ll (sj_acceptance x y)).
      by rewrite hb.
    rewrite he; exact sr_noise_uniform_ll.
  have houter :
      (fun x => mu sr_noise_uniform
        (fun y => weight (Biased.dbiased (sj_acceptance x y)) = 1%r) = 1%r) =
      (fun (_ : int) => true).
  + apply fun_ext => x; by rewrite hinner.
  rewrite houter.
  exact hg16_distr_ll.
qed.
