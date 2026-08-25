require import AllCore DInterval Distr DMap DProd FSet List Real StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyChallengeM23FixedAcceptedSamplerPostFreeze
               VerifyChallengeM23RejectionIndexPostFreeze
               VerifyChallengeM23UniformRoundsPostFreeze
               VerifyChallengeM23UniformSubsetPostFreeze.

theory VerifyChallengeM23UniformSamplerBridgePostFreeze.

(* Operational bridge from the iterated reservoir distribution to the fixed
   accepted-index machine sampler.  This layer proves the exact support
   distribution and its point law; binomial support counting and transport
   through the grouped/flat rejection samplers remain separate. *)

module DirectIndex =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.DirectIndex.
module FixedAcceptedIndexSampler =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.FixedAcceptedIndexSampler.
module ReservoirSubsetSampler =
  VerifyChallengeM23UniformSubsetPostFreeze.ReservoirSubsetSampler.

op challenge_words : int =
  VerifyChallengeM23UniformSubsetPostFreeze.challenge_words.
op mode2_start : int =
  VerifyChallengeM23UniformSubsetPostFreeze.mode2_start.
op mode2_tau : int =
  VerifyChallengeM23UniformSubsetPostFreeze.mode2_tau.
op support_prefix =
  VerifyChallengeM23UniformSubsetPostFreeze.support_prefix.
op valid_subset =
  VerifyChallengeM23UniformSubsetPostFreeze.valid_subset.
op reservoir_step =
  VerifyChallengeM23UniformSubsetPostFreeze.reservoir_step.
op reservoir_pair_distr =
  VerifyChallengeM23UniformSubsetPostFreeze.reservoir_pair_distr.
op reservoir_lift =
  VerifyChallengeM23UniformSubsetPostFreeze.reservoir_lift.
op reservoir_rounds =
  VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds.

lemma reservoir_rounds0 :
  reservoir_rounds 0 = dunit FSet.fset0.
proof.
exact VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds0.
qed.

lemma mode2_round_constants :
  0 <= mode2_tau /\
  mode2_start + mode2_tau = challenge_words.
proof.
exact VerifyChallengeM23UniformRoundsPostFreeze.mode2_round_constants.
qed.

clone import DMapSampling as ReservoirDMapSampling with
  type t1 <- (int fset * int),
  type t2 <- int fset.

clone import ProdSampling as ReservoirProductSampling with
  type t1 <- int fset,
  type t2 <- int.

module ReservoirLiftPrograms = {
  proc raw(d : int fset distr, i : int) : int fset = {
    var r : int fset;

    r <$ reservoir_lift d i;
    return r;
  }

  proc mapped(d : int fset distr, i : int) : int fset = {
    var r : int fset;

    r <@ ReservoirDMapSampling.S.sample
      (reservoir_pair_distr d i,
       fun (p : int fset * int) => reservoir_step p.`1 i p.`2);
    return r;
  }

  proc paired(d : int fset distr, i : int) : int fset = {
    var r : int fset;

    r <@ ReservoirDMapSampling.S.map
      (reservoir_pair_distr d i,
       fun (p : int fset * int) => reservoir_step p.`1 i p.`2);
    return r;
  }

  proc product(d : int fset distr, i : int) : int fset = {
    var p : int fset * int;

    p <@ ReservoirProductSampling.S.sample(d, dinter 0 i);
    return reservoir_step p.`1 i p.`2;
  }

  proc sequential(d : int fset distr, i : int) : int fset = {
    var p : int fset * int;

    p <@ ReservoirProductSampling.S.sample2(d, dinter 0 i);
    return reservoir_step p.`1 i p.`2;
  }
}.

equiv reservoir_lift_raw_mapped :
  ReservoirLiftPrograms.raw ~ ReservoirLiftPrograms.mapped :
  ={d, i} ==> ={res}.
proof.
proc.
inline ReservoirDMapSampling.S.sample.
wp.
rnd.
auto => />.
qed.

equiv reservoir_lift_mapped_paired :
  ReservoirLiftPrograms.mapped ~ ReservoirLiftPrograms.paired :
  ={d, i} ==> ={res}.
proof.
proc.
call ReservoirDMapSampling.sample.
auto.
qed.

equiv reservoir_lift_paired_product :
  ReservoirLiftPrograms.paired ~ ReservoirLiftPrograms.product :
  ={d, i} ==> ={res}.
proof.
proc.
inline ReservoirDMapSampling.S.map
       ReservoirProductSampling.S.sample.
wp.
rnd.
auto => />.
qed.

equiv reservoir_lift_product_sequential :
  ReservoirLiftPrograms.product ~ ReservoirLiftPrograms.sequential :
  ={d, i} ==> ={res}.
proof.
proc.
call ReservoirProductSampling.sample_sample2.
auto.
qed.

equiv reservoir_lift_raw_sequential :
  ReservoirLiftPrograms.raw ~ ReservoirLiftPrograms.sequential :
  ={d, i} ==> ={res}.
proof.
transitivity ReservoirLiftPrograms.mapped
  (={arg} ==> ={res})
  (={arg} ==> ={res}) => //=; 1:smt().
+ conseq reservoir_lift_raw_mapped; smt().
+ transitivity ReservoirLiftPrograms.paired
    (={arg} ==> ={res})
    (={arg} ==> ={res}) => //=; 1:smt().
  + conseq reservoir_lift_mapped_paired; smt().
  + transitivity ReservoirLiftPrograms.product
      (={arg} ==> ={res})
      (={arg} ==> ={res}) => //=; 1:smt().
    * conseq reservoir_lift_paired_product; smt().
    * conseq reservoir_lift_product_sequential; smt().
qed.

module ReservoirRoundsPrograms = {
  proc direct(n : int) : int fset = {
    var s : int fset;

    s <$ reservoir_rounds n;
    return s;
  }

  proc step_raw(n : int) : int fset = {
    var s : int fset;

    s <@ ReservoirLiftPrograms.raw
      (reservoir_rounds (n - 1), mode2_start + (n - 1));
    return s;
  }

  proc cons(n : int) : int fset = {
    var s : int fset;

    s <@ ReservoirLiftPrograms.sequential
      (reservoir_rounds (n - 1), mode2_start + (n - 1));
    return s;
  }

  proc cons_flat(n : int) : int fset = {
    var s : int fset;
    var b : int;

    s <$ reservoir_rounds (n - 1);
    b <$ dinter 0 (mode2_start + (n - 1));
    return reservoir_step s (mode2_start + (n - 1)) b;
  }

  proc loop(n : int) : int fset = {
    var s : int fset;
    var j : int;
    var b : int;

    s <- FSet.fset0;
    j <- 0;
    while (j < n) {
      b <$ dinter 0 (mode2_start + j);
      s <- reservoir_step s (mode2_start + j) b;
      j <- j + 1;
    }
    return s;
  }
}.

equiv reservoir_rounds_direct_step_raw :
  ReservoirRoundsPrograms.direct ~ ReservoirRoundsPrograms.step_raw :
  ={n} /\ 0 < n{1} ==> ={res}.
proof.
proc.
inline ReservoirLiftPrograms.raw.
wp.
rnd.
auto => /> &1 hn.
have hprev : 0 <= n{1} - 1 by smt().
have hround :=
  VerifyChallengeM23UniformRoundsPostFreeze.reservoir_roundsS
    (n{1} - 1) hprev.
move: hround.
have -> : n{1} - 1 + 1 = n{1} by ring.
move=> hround.
have hround_local :
    reservoir_rounds n{1} =
    reservoir_lift
      (reservoir_rounds (n{1} - 1))
      (mode2_start + (n{1} - 1)).
+ exact hround.
rewrite hround_local.
trivial.
qed.

equiv reservoir_rounds_step_raw_cons :
  ReservoirRoundsPrograms.step_raw ~ ReservoirRoundsPrograms.cons :
  ={n} ==> ={res}.
proof.
proc.
call reservoir_lift_raw_sequential.
auto.
qed.

equiv reservoir_rounds_direct_cons :
  ReservoirRoundsPrograms.direct ~ ReservoirRoundsPrograms.cons :
  ={n} /\ 0 < n{1} ==> ={res}.
proof.
transitivity ReservoirRoundsPrograms.step_raw
  (={arg} /\ 0 < n{1} ==> ={res})
  (={arg} ==> ={res}) => //=; 1:smt().
+ conseq reservoir_rounds_direct_step_raw; smt().
+ conseq reservoir_rounds_step_raw_cons; smt().
qed.

equiv reservoir_rounds_cons_flat :
  ReservoirRoundsPrograms.cons ~ ReservoirRoundsPrograms.cons_flat :
  ={n} ==> ={res}.
proof.
proc.
inline ReservoirLiftPrograms.sequential
       ReservoirProductSampling.S.sample2.
auto.
qed.

equiv reservoir_rounds_direct_cons_flat :
  ReservoirRoundsPrograms.direct ~ ReservoirRoundsPrograms.cons_flat :
  ={n} /\ 0 < n{1} ==> ={res}.
proof.
transitivity ReservoirRoundsPrograms.cons
  (={arg} /\ 0 < n{1} ==> ={res})
  (={arg} ==> ={res}) => //=; 1:smt().
+ conseq reservoir_rounds_direct_cons; smt().
+ conseq reservoir_rounds_cons_flat; smt().
qed.

equiv reservoir_rounds_direct_loop :
  ReservoirRoundsPrograms.direct ~ ReservoirRoundsPrograms.loop :
  0 <= n{1} /\ ={n} ==> ={res}.
proof.
proc*; exists* n{1}; elim* => rounds.
move: (eq_refl rounds); case (rounds <= 0) => //= hrounds.
+ inline *.
  rcondf{2} 4; first by auto; smt().
  auto => />.
  move=> hnonneg.
  have -> : rounds = 0 by smt().
  rewrite reservoir_rounds0.
  split.
  + exact (dunit_ll FSet.fset0).
  + move=> _ s0.
    rewrite supp_dunit.
    trivial.
have {hrounds} hrounds : 0 <= rounds by smt().
call (_: rounds = n{1} /\ ={n} ==> ={res}) => //=.
elim rounds hrounds => //= [|rounds hrounds ih].
+ proc.
  rcondf{2} 3; first by auto.
  auto => />.
  rewrite reservoir_rounds0.
  split.
  + exact (dunit_ll FSet.fset0).
  + move=> _ s0.
    rewrite supp_dunit.
    trivial.
+ transitivity ReservoirRoundsPrograms.cons_flat
    (={n} /\ 0 < n{1} ==> ={res})
    (rounds + 1 = n{1} /\ ={n} /\ 0 < n{1} ==> ={res}) => //=;
    1:smt().
  + conseq reservoir_rounds_direct_cons_flat; smt().
  + proc.
    splitwhile{2} 3 : (j < n - 1).
    rcondt{2} 4.
    * auto.
      while (j < n); auto; smt().
    rcondf{2} 7.
    * auto.
      while (j < n); auto; smt().
    wp.
    rnd.
    outline {1} 1 ~ ReservoirRoundsPrograms.direct.
    rewrite equiv[{1} 1 ih].
    inline ReservoirRoundsPrograms.direct
           ReservoirRoundsPrograms.loop.
    wp.
    while
      (={j} /\
       s0{1} = s{2} /\
       n0{1} = n{2} - 1 /\
       0 <= j{1} <= n0{1}).
    * auto => />.
      move=> &2 hj0 hjle hjlt hjn b hb.
      split.
      + split; smt().
      + smt().
    * auto => />.
      move=> hpos jlast slast hjdone hsync hj0 hjle.
      have -> : jlast = rounds by smt().
      split.
      + move=> b hb; trivial.
      + move=> _ b hb.
        split; [exact hb | move=> _; trivial].
qed.

equiv reservoir_rounds_loop_subset :
  ReservoirRoundsPrograms.loop ~ ReservoirSubsetSampler.sample :
  n{1} = mode2_tau ==>
  res{1} = res{2}.`1 /\ res{2}.`2 = challenge_words.
proof.
proc.
while
  (n{1} = mode2_tau /\
   i{2} = mode2_start + j{1} /\
   s{1} = s{2} /\
   0 <= j{1} <= mode2_tau).
+ wp.
  rnd.
  auto => />; smt().
+ auto => />.
  have hconstants := mode2_round_constants.
  move: hconstants => [htau hfinal].
  smt().
qed.

equiv reservoir_rounds_direct_subset :
  ReservoirRoundsPrograms.direct ~ ReservoirSubsetSampler.sample :
  n{1} = mode2_tau ==>
  res{1} = res{2}.`1 /\ res{2}.`2 = challenge_words.
proof.
transitivity ReservoirRoundsPrograms.loop
  (0 <= n{1} /\ ={arg} ==> ={res})
  (n{1} = mode2_tau ==>
     res{1} = res{2}.`1 /\ res{2}.`2 = challenge_words) => //=.
+ move=> &1 hn.
  exists arg{1}.
  split.
  + split.
    * have hconstants := mode2_round_constants.
      move: hconstants => [htau _].
      smt().
    * trivial.
  + exact hn.
+ conseq reservoir_rounds_direct_loop; smt().
+ conseq reservoir_rounds_loop_subset; smt().
qed.

(* Machine projection bridge.  The accepted-index trace is intentionally
   ignored; support_prefix is the observable needed for uniformity. *)
equiv reservoir_fixed_support :
  ReservoirSubsetSampler.sample ~ FixedAcceptedIndexSampler.sample :
  true ==>
  res{1}.`2 = res{2}.`2 /\
  res{1}.`1 = support_prefix res{2}.`1 res{2}.`2.
proof.
proc.
inline DirectIndex.sample.
while
  (={i} /\
   mode2_start <= i{1} <= challenge_words /\
   s{1} = support_prefix cp{2} i{2}).
+ wp.
  rnd.
  auto => />.
  move=> &1 hstart hupper hloop_subset hloop_fixed
          hdist b hb hbdirect.
  have hbyte : 0 <= b <= i{1}.
  + move: hb.
    rewrite supp_dinter.
    smt().
  have hstep :=
    VerifyChallengeM23UniformSubsetPostFreeze.support_prefix_shuffle_step
      cp{1} i{1} b hbyte hloop_subset.
  split.
  + smt().
  + smt().
+ auto => />.
  change
    (FSet.fset0 =
     VerifyChallengeM23UniformSubsetPostFreeze.support_prefix
       VerifyChallengeM23UniformSubsetPostFreeze.mode2_zero_challenge
       VerifyChallengeM23UniformSubsetPostFreeze.mode2_start).
  rewrite VerifyChallengeM23UniformSubsetPostFreeze.mode2_support_init.
  trivial.
qed.

lemma reservoir_rounds_direct_pr &m n0 P :
  Pr[ReservoirRoundsPrograms.direct(n0) @ &m : P res] =
  mu (reservoir_rounds n0) P.
proof.
byphoare (_: n = n0 ==> P res) => //=.
proc.
rnd.
auto.
qed.

lemma reservoir_rounds_direct_subset_pr &m1 &m2 P :
  Pr[ReservoirRoundsPrograms.direct(mode2_tau) @ &m1 : P res] =
  Pr[ReservoirSubsetSampler.sample() @ &m2 : P res.`1].
proof.
byequiv reservoir_rounds_direct_subset => //=.
qed.

lemma reservoir_subset_pr &m P :
  Pr[ReservoirSubsetSampler.sample() @ &m : P res.`1] =
  mu (reservoir_rounds mode2_tau) P.
proof.
rewrite
  -(reservoir_rounds_direct_subset_pr &m &m P)
  (reservoir_rounds_direct_pr &m mode2_tau P).
trivial.
qed.

lemma reservoir_fixed_support_pr &m1 &m2 P :
  Pr[ReservoirSubsetSampler.sample() @ &m1 : P res.`1] =
  Pr[FixedAcceptedIndexSampler.sample() @ &m2 :
       P (support_prefix res.`1 res.`2)].
proof.
byequiv reservoir_fixed_support => //=.
move=> &1 &2 [_ hsupport].
rewrite hsupport.
trivial.
qed.

lemma fixed_support_pr &m P :
  Pr[FixedAcceptedIndexSampler.sample() @ &m :
       P (support_prefix res.`1 res.`2)] =
  mu (reservoir_rounds mode2_tau) P.
proof.
rewrite
  -(reservoir_fixed_support_pr &m &m P)
  (reservoir_subset_pr &m P).
trivial.
qed.

lemma fixed_support_point &m t :
  Pr[FixedAcceptedIndexSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = t] =
  if valid_subset challenge_words mode2_tau t
  then
    1%r /
    (size
       (Finite.to_seq
          (support (reservoir_rounds mode2_tau))))%r
  else 0%r.
proof.
rewrite (fixed_support_pr &m (pred1 t)).
exact
  (VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds_final_point t).
qed.

lemma fixed_support_uniform &m t u :
  valid_subset challenge_words mode2_tau t =>
  valid_subset challenge_words mode2_tau u =>
  Pr[FixedAcceptedIndexSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = t] =
  Pr[FixedAcceptedIndexSampler.sample() @ &m :
       support_prefix res.`1 res.`2 = u].
proof.
move=> ht hu.
rewrite !fixed_support_point ht hu.
trivial.
qed.

end VerifyChallengeM23UniformSamplerBridgePostFreeze.
