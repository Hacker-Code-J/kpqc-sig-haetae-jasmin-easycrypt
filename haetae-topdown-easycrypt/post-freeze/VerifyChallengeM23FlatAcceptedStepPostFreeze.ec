require import AllCore List Real StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyChallengeM23ProbabilisticSamplerPostFreeze
               VerifyChallengeM23RejectionIndexPostFreeze
               VerifyChallengeM23FixedAcceptedSamplerPostFreeze.

theory VerifyChallengeM23FlatAcceptedStepPostFreeze.

import IntOrder RealOrder.

module RejectionLoop =
  VerifyChallengeM23RejectionIndexPostFreeze.RejectionIndexSampling.SampleW.
module FlatMode2RejectionSampler =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.FlatMode2RejectionSampler.
module GroupedAcceptedIndexSampler =
  VerifyChallengeM23FixedAcceptedSamplerPostFreeze.GroupedAcceptedIndexSampler.

op challenge_words : int =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_words.
op mode2_start : int =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_start.
op mode2_zero_challenge : BArray1024.t =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.mode2_zero_challenge.
op challenge_shuffle_update =
  VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_shuffle_update.

(* One semantic chunk of the flat sampler: keep drawing bytes at the current
   index until one is accepted, then perform exactly one shuffle update. *)
module FlatAcceptedStep = {
  proc sample (cp : BArray1024.t, i : int) : BArray1024.t * int = {
    var b : int;

    b <$ VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte;
    while (VerifyChallengeM23RejectionIndexPostFreeze.rejected_index i b) {
      b <$ VerifyChallengeM23ProbabilisticSamplerPostFreeze.uniform_byte;
    }
    cp <- challenge_shuffle_update cp i b;
    i <- i + 1;
    return (cp, i);
  }
}.

module GroupedAcceptedStep = {
  proc sample (cp : BArray1024.t, i : int) : BArray1024.t * int = {
    var b : int;

    b <@ RejectionLoop.sample(i);
    cp <- challenge_shuffle_update cp i b;
    i <- i + 1;
    return (cp, i);
  }
}.

equiv flat_grouped_accepted_step :
  FlatAcceptedStep.sample ~ GroupedAcceptedStep.sample :
  ={arg} ==> ={res}.
proof.
proc.
inline RejectionLoop.sample
       VerifyChallengeM23RejectionIndexPostFreeze.RejectionIndexSampling.SampleWi.sample.
by sim.
qed.

module FlatAcceptedStepSampler = {
  proc sample () : BArray1024.t * int = {
    var cp : BArray1024.t;
    var i : int;

    cp <- mode2_zero_challenge;
    i <- mode2_start;
    while (i < challenge_words) {
      (cp, i) <@ FlatAcceptedStep.sample(cp, i);
    }
    return (cp, i);
  }
}.

module GroupedAcceptedStepSampler = {
  proc sample () : BArray1024.t * int = {
    var cp : BArray1024.t;
    var i : int;

    cp <- mode2_zero_challenge;
    i <- mode2_start;
    while (i < challenge_words) {
      (cp, i) <@ GroupedAcceptedStep.sample(cp, i);
    }
    return (cp, i);
  }
}.

equiv flat_grouped_accepted_step_samplers :
  FlatAcceptedStepSampler.sample ~ GroupedAcceptedStepSampler.sample :
  true ==> ={res}.
proof.
proc.
while (={cp, i}).
+ call flat_grouped_accepted_step.
  auto.
+ auto.
qed.

equiv grouped_step_existing_grouped_sampler :
  GroupedAcceptedStepSampler.sample ~ GroupedAcceptedIndexSampler.sample :
  true ==> ={res}.
proof.
proc.
inline GroupedAcceptedStep.sample.
while (={cp, i}).
+ wp.
  call (_ : ={arg} ==> ={res}).
  + sim.
  + auto => />.
+ auto => />.
qed.

equiv flat_step_existing_grouped_sampler :
  FlatAcceptedStepSampler.sample ~ GroupedAcceptedIndexSampler.sample :
  true ==> ={res}.
proof.
transitivity GroupedAcceptedStepSampler.sample
  (true ==> ={res})
  (true ==> ={res}).
+ done.
+ done.
+ exact flat_grouped_accepted_step_samplers.
+ exact grouped_step_existing_grouped_sampler.
qed.

(* The asynchronous outer-loop rule cuts the flat byte loop at the first
   iteration that advances i.  Its lockstep obligation is then exactly the
   rejection loop implemented by FlatAcceptedStep.  The byte trace and the
   accepted-index trace remain intentionally outside the result contract. *)
equiv flat_monolithic_accepted_steps :
  FlatMode2RejectionSampler.sample ~ FlatAcceptedStepSampler.sample :
  true ==> ={res}.
proof.
proc.
seq 3 2 :
  (={cp, i} /\
   Int.(<=) mode2_start i{1} /\
   Int.(<=) i{1} challenge_words).
+ auto => />.
async while
  [ (fun r => Real.(<) i%r r), (Int.(+) i{2} 1)%r ]
  [ (fun r => Real.(<) i%r r), (Int.(+) i{2} 1)%r ]
  ((Int.(<) i
      VerifyChallengeM23ProbabilisticSamplerPostFreeze.challenge_words){1})
  (true)
  : (={cp, i} /\
     Int.(<=) mode2_start i{1} /\
     Int.(<=) i{1} challenge_words).
+ move=> &1 &2 />.
  rewrite !lt_fromint.
  smt().
+ move=> &1 &2 />; smt().
+ done.
+ move=> &2; exfalso; smt().
+ move=> &1; exfalso; done.
+ move=> v1 v2.
  inline {2} FlatAcceptedStep.sample.
  rcondt {2} 1.
  + auto => />.
    rewrite lt_fromint.
    smt().
  rcondf {2} 8.
  + move=> &m.
    wp.
    while (i0 = i /\ v2 = (Int.(+) i0 1)%r).
    * auto.
    * auto => />; rewrite ltrr.
  unroll {1} 1.
  rcondt {1} 1.
  + auto => />.
    rewrite lt_fromint.
    smt().
  sp 0 2.
  auto.
  seq 2 1 :
    (={b, cp, i} /\
     cp0{2} = cp{2} /\
     i0{2} = i{2} /\
     Int.(<=) mode2_start i{1} /\
     Int.(<) i{1} challenge_words /\
     v1 = (Int.(+) i{1} 1)%r).
  + auto => />; smt().
  if {1}.
  + rcondf {2} 1.
    * auto => />; smt().
    rcondf {1} 3.
    * auto => />; rewrite ltrr; smt().
    auto => />; smt().
  + while
      (cp0{2} = cp{2} /\
       i0{2} = i{2} /\
       Int.(<=) mode2_start i0{2} /\
       Int.(<) i0{2} challenge_words /\
       v1 = (Int.(+) i0{2} 1)%r /\
       ={b} /\
       (if Int.(<=) b{2} i0{2} then
          cp{1} = challenge_shuffle_update cp0{2} i0{2} b{2} /\
          i{1} = Int.(+) i0{2} 1
        else
          cp{1} = cp0{2} /\ i{1} = i0{2})).
    * auto => />.
      rewrite
        /VerifyChallengeM23RejectionIndexPostFreeze.rejected_index.
      move=> &1 &2 hstart hupper.
      case (Int.(<=) b{2} i{2}) => hold.
      + done.
      move=> [-> ->] _ _ _ bL hb.
      rewrite ltrr /=.
      rewrite /challenge_shuffle_update.
      smt().
    * auto => />.
      rewrite
        /VerifyChallengeM23RejectionIndexPostFreeze.rejected_index.
      move=> &2 hstart hupper hreject.
      split.
      + move=> _.
        rewrite lt_fromint.
        smt().
      + move=> cpL iL bR _ hbacc.
        have hle : Int.(<=) bR i{2} by smt().
        rewrite hle /=.
        move=> [-> ->].
        smt().
+ rcondf 1; auto.
  move=> &hr />; smt().
+ rcondf 1; auto.
+ auto => />.
qed.

equiv flat_existing_grouped_sampler :
  FlatMode2RejectionSampler.sample ~ GroupedAcceptedIndexSampler.sample :
  true ==> ={res}.
proof.
transitivity FlatAcceptedStepSampler.sample
  (true ==> ={res})
  (true ==> ={res}).
+ done.
+ done.
+ exact flat_monolithic_accepted_steps.
+ exact flat_step_existing_grouped_sampler.
qed.

end VerifyChallengeM23FlatAcceptedStepPostFreeze.
