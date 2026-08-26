require import AllCore Distr List Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32.
require import HAETAE_Distributions.
require import TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
               Mode2FaithfulSecurityRawSeedDistributionPostFreeze
               Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
               Mode2FaithfulSecuritySampledProgressMassPostFreeze
               Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.

theory Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze.

import RealOrder.
import HAETAE_Distributions.
import TargetKeygenM23FullFirstAttempt.

(* This file samples exactly one checked first-attempt decision from the raw
   seed distribution.  It separates sampler nontermination mass from the
   memory-parameterized singular-reject probability, but does not claim retry
   semantics, packing, a numeric reject bound, full key generation, or any
   HAETAE.kg equality. *)

module SampledFirstAttemptDecision = {
  var raw_current : BArray32.t

  proc main() : first_attempt_trace = {
    var trace : first_attempt_trace;

    raw_current <$
      Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed;
    trace <@
      Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
        .CheckedMode2FirstAttemptDecision.run(
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192,
          raw_current);
    return trace;
  }
}.

lemma sampled_first_attempt_snapshot_correct :
  hoare [SampledFirstAttemptDecision.main : true ==>
    Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
      .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      SampledFirstAttemptDecision.raw_current res /\
    Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed
      SampledFirstAttemptDecision.raw_current \in dseed].
proof.
proc.
seq 1 :
  (SampledFirstAttemptDecision.raw_current \in
    Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed).
+ rnd; auto.
wp.
exlim SampledFirstAttemptDecision.raw_current => raw0.
call
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_snapshot_correct
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    raw0).
auto => />.
move=> hraw *.
exact
  (Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
    .draw_raw_seed_support_decodes_dseed raw0 hraw).
qed.

lemma checked_first_attempt_good_raw_ll (raw_init : BArray32.t) :
  phoare [Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
            .CheckedMode2FirstAttemptDecision.run :
    seedbuf =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128 /\
    raw_seed = raw_init /\
    Mode2FaithfulSecuritySampledProgressMassPostFreeze.raw_seed_has_progress
      raw_init
    ==> true] >= 1%r.
proof.
conseq
  (Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_mode2_first_attempt_decision_progress_ll
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128
    raw_init
    (Mode2FaithfulSecuritySampledProgressMassPostFreeze
      .selected_sampler_progress_witness raw_init).`1
    (Mode2FaithfulSecuritySampledProgressMassPostFreeze
      .selected_sampler_progress_witness raw_init).`2
    (Mode2FaithfulSecuritySampledProgressMassPostFreeze
      .selected_sampler_progress_witness raw_init).`3) => //=.
move=> &hr [hseed [hraw hgood]].
have hselected :=
  Mode2FaithfulSecuritySampledProgressMassPostFreeze
    .selected_sampler_progress_witness_valid raw_init hgood.
smt().
qed.

lemma sampled_first_attempt_termination_progress_mass :
  phoare [SampledFirstAttemptDecision.main : true ==> true] >=
  (mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    Mode2FaithfulSecuritySampledProgressMassPostFreeze.raw_seed_has_progress).
proof.
proc.
seq 1 :
  (Mode2FaithfulSecuritySampledProgressMassPostFreeze.raw_seed_has_progress
    SampledFirstAttemptDecision.raw_current)
  (mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    Mode2FaithfulSecuritySampledProgressMassPostFreeze.raw_seed_has_progress)
  1%r 0%r _ => //=.
+ by rnd
    Mode2FaithfulSecuritySampledProgressMassPostFreeze.raw_seed_has_progress;
    skip.
wp.
exlim SampledFirstAttemptDecision.raw_current => raw0.
call (checked_first_attempt_good_raw_ll raw0).
auto => />.
qed.

lemma sampled_first_attempt_termination_mass :
  phoare [SampledFirstAttemptDecision.main : true ==> true] >=
  (1%r -
   Mode2FaithfulSecuritySampledProgressMassPostFreeze.delta_sampler_progress).
proof.
rewrite
  -Mode2FaithfulSecuritySampledProgressMassPostFreeze
    .raw_seed_progress_good_massE.
exact sampled_first_attempt_termination_progress_mass.
qed.

lemma sampled_first_attempt_accept_reject_partition &m :
  Pr[SampledFirstAttemptDecision.main() @ &m :
       first_attempt_trace_accepted res] +
  Pr[SampledFirstAttemptDecision.main() @ &m :
       ! first_attempt_trace_accepted res] =
  Pr[SampledFirstAttemptDecision.main() @ &m : true].
proof.
rewrite Pr[mu_not].
ring.
qed.

lemma sampled_first_attempt_accept_mass_bound &m :
  Pr[SampledFirstAttemptDecision.main() @ &m :
       first_attempt_trace_accepted res] >=
  (1%r -
   Mode2FaithfulSecuritySampledProgressMassPostFreeze.delta_sampler_progress -
   Pr[SampledFirstAttemptDecision.main() @ &m :
        ! first_attempt_trace_accepted res]).
proof.
have hterm :
    Pr[SampledFirstAttemptDecision.main() @ &m : true] >=
    (1%r -
     Mode2FaithfulSecuritySampledProgressMassPostFreeze
       .delta_sampler_progress).
+ by byphoare sampled_first_attempt_termination_mass.
have hpartition := sampled_first_attempt_accept_reject_partition &m.
smt().
qed.

end Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze.
