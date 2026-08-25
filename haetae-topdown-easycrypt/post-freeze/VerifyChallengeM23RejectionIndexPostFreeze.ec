require import AllCore Distr DInterval Dexcepted List Real StdOrder.

require import VerifyChallengeM23ProbabilisticSamplerPostFreeze.

theory VerifyChallengeM23RejectionIndexPostFreeze.

(* One accepted-index law for the ideal uniform-byte oracle.  This factors a
   variable-count byte rejection loop into the direct distribution dinter 0 i.
   It does not yet lift the law through all 58 shuffle steps, assert uniformity
   over final supports, or identify deterministic SHAKE bytes as iid uniform. *)

import VerifyChallengeM23ProbabilisticSamplerPostFreeze.
import RealOrder.

op rejected_index (i b : int) : bool = !(b <= i).

op direct_index (i : int) : int distr = dinter 0 i.

op accepted_byte (i : int) : int distr = uniform_byte \ rejected_index i.

lemma mode2_index_range i :
  mode2_start <= i < challenge_words =>
  0 <= i <= 255.
proof.
move=> hi.
have hcw : challenge_words = 256 by trivial.
have hri := current_index_range i hi.
smt().
qed.

lemma uniform_byte_uniform :
  is_uniform uniform_byte.
proof.
rewrite /uniform_byte.
exact (dinter_uni 0 255).
qed.

lemma direct_index_support i b :
  0 <= i =>
  (b \in direct_index i <=> 0 <= b <= i).
proof.
move=> hi.
rewrite /direct_index supp_dinter.
smt().
qed.

lemma accepted_byte_support i b :
  0 <= i <= 255 =>
  (b \in accepted_byte i <=> 0 <= b <= i).
proof.
move=> hi.
rewrite /accepted_byte supp_dexcepted /uniform_byte supp_dinter /rejected_index.
smt().
qed.

lemma accepted_byte_lossless i :
  0 <= i <= 255 =>
  is_lossless (accepted_byte i).
proof.
move=> hi.
rewrite /accepted_byte.
apply dexcepted_ll.
+ exact uniform_byte_lossless.
have hpos :
    0%r < mu uniform_byte (predC (rejected_index i)).
+ rewrite witness_support.
  exists 0.
  split.
  + rewrite /predC /rejected_index.
    smt().
  + rewrite /uniform_byte supp_dinter.
    smt().
move: hpos.
rewrite mu_not uniform_byte_lossless.
smt().
qed.

lemma accepted_byte_uniform i :
  is_uniform (accepted_byte i).
proof.
rewrite /accepted_byte.
apply dexcepted_uni.
exact uniform_byte_uniform.
qed.

lemma accepted_byte_eq_dinter i :
  0 <= i <= 255 =>
  accepted_byte i = dinter 0 i.
proof.
move=> hi.
have hll1 := accepted_byte_lossless i hi.
have hll2 : is_lossless (dinter 0 i) by apply dinter_ll; smt().
have huni1 := accepted_byte_uniform i.
have huni2 : is_uniform (dinter 0 i) by exact (dinter_uni 0 i).
have hsupp : support (accepted_byte i) = support (dinter 0 i).
+ apply fun_ext => b.
  rewrite accepted_byte_support 1:hi supp_dinter.
  trivial.
apply/eq_distr => b.
rewrite (mu1_uni (accepted_byte i) b huni1)
        (mu1_uni (dinter 0 i) b huni2).
rewrite hll1 hll2 hsupp.
trivial.
qed.

lemma accepted_byte_eq_direct i :
  0 <= i <= 255 => accepted_byte i = direct_index i.
proof.
move=> hi.
rewrite /direct_index.
exact (accepted_byte_eq_dinter i hi).
qed.

clone import WhileSamplingFixedTest as RejectionIndexSampling with
  type input <- int,
  type t <- int,
  op dt <- (fun _ : int => uniform_byte),
  op test <- rejected_index.

module DirectIndexSampler = {
  proc sample(i : int) : int = {
    var r : int;

    r <$ direct_index i;
    return r;
  }
}.

lemma direct_index_sampler_pr &m i P :
  0 <= i <= 255 =>
  Pr[DirectIndexSampler.sample(i) @ &m : P res] = mu (direct_index i) P.
proof.
move=> hi.
byphoare (: arg = i ==> P res) => //.
proc.
rnd P.
skip => />.
qed.

lemma rejection_index_excepted_pr &m i P :
  0 <= i <= 255 =>
  Pr[RejectionIndexSampling.SampleE.sample(i) @ &m : P res] =
  mu (direct_index i) P.
proof.
move=> hi.
rewrite RejectionIndexSampling.pr_sampleE.
change (mu (accepted_byte i) P = mu (direct_index i) P).
have heq := accepted_byte_eq_direct i hi.
rewrite heq.
trivial.
qed.

lemma rejection_index_loop_pr &m i P :
  0 <= i <= 255 =>
  Pr[RejectionIndexSampling.SampleW.sample(i) @ &m : P res] =
  mu (direct_index i) P.
proof.
move=> hi.
rewrite
  (RejectionIndexSampling.pr_sampleW
    &m i P uniform_byte_lossless).
change (mu (accepted_byte i) P = mu (direct_index i) P).
have heq := accepted_byte_eq_direct i hi.
rewrite heq.
trivial.
qed.

lemma rejection_index_loop_point &m i b :
  0 <= i <= 255 =>
  Pr[RejectionIndexSampling.SampleW.sample(i) @ &m : res = b] =
  mu (dinter 0 i) (pred1 b).
proof.
move=> hi.
have hpoint := rejection_index_loop_pr &m i (pred1 b) hi.
rewrite /direct_index in hpoint.
exact hpoint.
qed.

lemma rejection_index_excepted_point &m i b :
  0 <= i <= 255 =>
  Pr[RejectionIndexSampling.SampleE.sample(i) @ &m : res = b] =
  mu (dinter 0 i) (pred1 b).
proof.
move=> hi.
have hpoint := rejection_index_excepted_pr &m i (pred1 b) hi.
rewrite /direct_index in hpoint.
exact hpoint.
qed.

end VerifyChallengeM23RejectionIndexPostFreeze.
