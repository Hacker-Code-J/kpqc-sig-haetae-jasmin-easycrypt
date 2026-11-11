require import AllCore IntDiv List Distr DInterval RealSeries StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 SamplerTarget SigmaSpec SigmaCorrectness
  Rejection48Spec Rejection48Correctness SigmaRejection48Bridge SigmaRawAcceptanceCorrectness
  SigmaExpAcceptanceCorrectness
  SigmaRawNoiseSpec SigmaNoise72Bridge.
import RField RealOrder.

(* Both experiments call the actual extracted attempt.  They expose the
   returned rounded magnitude together with its acceptance flag. *)
module SigmaJointRejection48 = {
  proc sample(p : BArray26.t) : int * bool = {
    var u : int;
    var patched : BArray26.t;
    var result : W64.t * W64.t * W64.t * W64.t;
    u <$ rejection48_uniform;
    patched <- sigma_rejection48_patch p u;
    result <@ SamplerTarget.M.__sample_gauss_sigma76_regs(patched);
    return (W64.to_uint result.`1, result.`4 = W64.one);
  }
}.

module SigmaJointNoise72 = {
  proc sample(p : BArray26.t) : int * bool = {
    var y : int;
    var outcome : int * bool;
    y <$ sr_noise_uniform;
    outcome <@ SigmaJointRejection48.sample(sigma_noise72_patch p y);
    return outcome;
  }
}.

(* Proof observers retain the implementation's rounded word, threshold and
   rejection bit expression.  They are not an ideal Gaussian target. *)
module SigmaJointRejection48Word = {
  proc sample(p : BArray26.t) : int * bool = {
    var u : int;
    u <$ rejection48_uniform;
    return (W64.to_uint (sigma_rejection48_rounded p),
      rejection48_word (W64.of_int u) (sigma_rejection48_threshold p)
        (sigma_rejection48_rounded p) = W64.one);
  }
}.

module SigmaJointNoise72Word = {
  proc sample(p : BArray26.t) : int * bool = {
    var y : int;
    var outcome : int * bool;
    y <$ sr_noise_uniform;
    outcome <@ SigmaJointRejection48Word.sample(sigma_noise72_patch p y);
    return outcome;
  }
}.

lemma sigma_joint_rejection48_rounded p0 :
  hoare [SigmaJointRejection48.sample : p = p0 ==>
    res.`1 = W64.to_uint (sigma_rejection48_rounded p0)].
proof.
proc; wp.
ecall (sigma76_regs_correct (sigma_rejection48_patch p u)).
wp; rnd; skip; auto => />.
move=> u hu.
rewrite -/(sigma_rejection48_rounded (sigma_rejection48_patch p0 u))
  sigma_rejection48_patch_rounded.
trivial.
qed.

lemma sigma_joint_rejection48_projection :
  equiv [SigmaJointRejection48.sample ~ SigmaRejection48Experiment.sample :
    ={p} ==> res{1}.`2 = res{2}].
proof.
proc; wp.
call (_ : ={randp} ==> ={res}); first by proc; sim.
wp; rnd; skip; auto => />.
qed.

lemma sigma_joint_rejection48_exact p0 :
  equiv [SigmaJointRejection48.sample ~ SigmaRejection48Experiment.sample :
    ={p} /\ p{1} = p0 ==>
    res{1}.`2 = res{2} /\ res{1}.`1 = W64.to_uint (sigma_rejection48_rounded p0)].
proof.
by conseq sigma_joint_rejection48_projection (sigma_joint_rejection48_rounded p0) _ => /#.
qed.

lemma sigma_joint_rejection48_ll : islossless SigmaJointRejection48.sample.
proof.
proc; wp; call sigma76_regs_lossless; wp; rnd; skip; auto => />.
rewrite /rejection48_uniform; apply DInterval.dinter_ll; trivial.
qed.

lemma sigma_joint_rejection48_law p0 (S : int -> bool) &m :
  Pr[SigmaJointRejection48.sample(p0) @ &m : res.`2 /\ S res.`1] =
    b2r (S (W64.to_uint (sigma_rejection48_rounded p0))) * sr_actual_probability p0.
proof.
have he : Pr[SigmaJointRejection48.sample(p0) @ &m : res.`2 /\ S res.`1] =
    Pr[SigmaRejection48Experiment.sample(p0) @ &m :
      res /\ S (W64.to_uint (sigma_rejection48_rounded p0))].
+ by byequiv (sigma_joint_rejection48_exact p0) => /#.
rewrite he.
case (S (W64.to_uint (sigma_rejection48_rounded p0))) => hs.
+ by rewrite /b2r /= sr_actual_probability_law.
by rewrite /b2r /= Pr[mu_false].
qed.

lemma sigma_joint_noise72_ll : islossless SigmaJointNoise72.sample.
proof.
proc; call sigma_joint_rejection48_ll; rnd; skip; auto => />.
exact sr_noise_uniform_ll.
qed.

lemma sigma_joint_rejection48_equiv :
  equiv [SigmaJointRejection48.sample ~ SigmaJointRejection48Word.sample :
    ={p} ==> ={res}].
proof.
proc; wp.
ecall{1} (sigma76_regs_total_correct (sigma_rejection48_patch p{1} u{1})).
wp; rnd; skip.
move=> &1 &2 hp; rewrite hp /=.
move=> u hu.
have hurange : 0 <= u < 281474976710656 by
  move: hu; rewrite /rejection48_uniform DInterval.supp_dinter; smt().
rewrite hu /=.
move=> result ->.
by rewrite -/(sigma_rejection48_rounded (sigma_rejection48_patch p{2} u))
  sigma_rejection48_patch_rounded (sigma_rejection48_patched_acceptance p{2} u hurange).
qed.

lemma sigma_joint_noise72_equiv :
  equiv [SigmaJointNoise72.sample ~ SigmaJointNoise72Word.sample : ={p} ==> ={res}].
proof.
proc; call sigma_joint_rejection48_equiv; rnd; skip; auto => />.
qed.

lemma sigma_joint_fixed_output_mass p (S : int -> bool) :
  mu rejection48_uniform (fun u =>
    rejection48_word (W64.of_int u) (sigma_rejection48_threshold p)
      (sigma_rejection48_rounded p) = W64.one /\
    S (W64.to_uint (sigma_rejection48_rounded p))) =
    b2r (S (W64.to_uint (sigma_rejection48_rounded p))) * sr_actual_probability p.
proof.
have hf := sigma_exp_threshold_fit p.
have h := rejection48_word_probability (W64.to_uint (sigma_rejection48_threshold p))
  (sigma_rejection48_rounded p) hf.
rewrite W64.to_uintK in h.
case (S (W64.to_uint (sigma_rejection48_rounded p))) => hs.
+ rewrite /b2r /= /sr_actual_probability.
  exact h.
by rewrite /b2r /= mu0.
qed.

lemma sigma_joint_noise72_word_law p0 (S : int -> bool) &m :
  Pr[SigmaJointNoise72Word.sample(p0) @ &m : res.`2 /\ S res.`1] =
    Distr.E sr_noise_uniform (fun y =>
      b2r (S (W64.to_uint (sigma_rejection48_rounded (sigma_noise72_patch p0 y)))) *
      sr_actual_probability (sigma_noise72_patch p0 y)).
proof.
byphoare (_ : p = p0 ==> res.`2 /\ S res.`1) => //.
proc; inline SigmaJointRejection48Word.sample; wp.
rndsem* 0.
rnd (fun (pu : BArray26.t * int) =>
  rejection48_word (W64.of_int pu.`2) (sigma_rejection48_threshold pu.`1)
    (sigma_rejection48_rounded pu.`1) = W64.one /\
  S (W64.to_uint (sigma_rejection48_rounded pu.`1))).
skip; auto => />.
rewrite dletE /E.
apply RealSeries.eq_sum => y /=.
rewrite dmapE /(\o) /= sigma_joint_fixed_output_mass.
ring.
qed.

lemma sigma_joint_noise72_law p0 (S : int -> bool) &m :
  Pr[SigmaJointNoise72.sample(p0) @ &m : res.`2 /\ S res.`1] =
    Distr.E sr_noise_uniform (fun y =>
      b2r (S (W64.to_uint (sigma_rejection48_rounded (sigma_noise72_patch p0 y)))) *
      sr_actual_probability (sigma_noise72_patch p0 y)).
proof.
rewrite -(sigma_joint_noise72_word_law p0 S &m).
by byequiv sigma_joint_noise72_equiv.
qed.
