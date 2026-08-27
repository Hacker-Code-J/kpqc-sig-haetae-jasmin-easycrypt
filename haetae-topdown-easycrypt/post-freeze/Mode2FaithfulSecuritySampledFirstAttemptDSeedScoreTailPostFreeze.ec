require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32.
require import HAETAE_Algebra HAETAE_Distributions.
require import TargetKeygenM23FullFirstAttempt.
require import Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
               Mode2FaithfulSecurityRawSeedDistributionPostFreeze
               Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
               Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
               Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze
               Mode2FaithfulSecuritySampledFirstAttemptRejectCertificatePostFreeze
               Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
               Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze
               Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze.

theory Mode2FaithfulSecuritySampledFirstAttemptDSeedScoreTailPostFreeze.

import RealOrder.
import HAETAE_Algebra.
import HAETAE_Distributions.
import TargetKeygenM23FullFirstAttempt.
import Mode2FaithfulSecurityRawSeedDistributionPostFreeze.
import Mode2FaithfulSecuritySampledFirstAttemptRejectCertificatePostFreeze.
import Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenDefectAccumulationPostFreeze.

module SampledFirst =
  Mode2FaithfulSecuritySampledFirstAttemptMassPostFreeze
    .SampledFirstAttemptDecision.

module SampledBounded =
  Mode2FaithfulSecuritySampledBoundedKeygenMassPostFreeze
    .SampledBoundedKeygenDecision.

op dseed_raw_seed (sd : seed) : BArray32.t =
  Mode2FaithfulSecurityRawSeedDistributionPostFreeze
    .raw_seed_of_security_seed sd.

op raw_dseed_seed (raw : BArray32.t) : seed =
  Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed raw.

(* This bridge only swaps the first-attempt seed source from the raw
   pushforward distribution back to the original [dseed] sampler and proves
   that the exact singular-score tail mass is unchanged.  It does not assert
   XOF pseudorandomness, numeric tail bounds, ideal eta laws, retry semantics,
   full key generation, or equality with [HAETAE.kg]. *)

module SampledDSeedFirstAttemptDecision = {
  var sd_current : seed
  var raw_current : BArray32.t

  proc main() : first_attempt_trace = {
    var trace : first_attempt_trace;

    sd_current <$ dseed;
    raw_current <- dseed_raw_seed sd_current;
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

lemma draw_raw_seed_support_raw_dseed_roundtrip raw :
  raw \in Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed =>
  dseed_raw_seed (raw_dseed_seed raw) = raw.
proof.
rewrite
  /Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
  supp_dmap.
move=> [sd [hsd ->]].
rewrite /raw_dseed_seed /dseed_raw_seed.
rewrite
  Mode2FaithfulSecurityRawSeedDistributionPostFreeze
    .raw_security_seed_roundtrip //.
qed.

lemma draw_raw_seed_mu1_raw_dseed_seedE raw :
  raw \in
    Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed =>
  mu1 Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed raw =
  mu1 dseed (raw_dseed_seed raw).
proof.
move=> hraw.
rewrite
  /Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
  dmap1E /mu1.
apply mu_eq_support => sd hsd.
rewrite /pred1 /(\o) /=.
have hsdround :=
  Mode2FaithfulSecurityRawSeedDistributionPostFreeze
    .raw_security_seed_roundtrip sd hsd.
have hrawround :=
  draw_raw_seed_support_raw_dseed_roundtrip raw hraw.
apply/eq_iff.
split.
+ move=> heq.
  by rewrite -hsdround heq.
+ move=> heq.
  rewrite heq.
  exact hrawround.
qed.

lemma sampled_dseed_first_attempt_score_tail_equiv :
  equiv [SampledDSeedFirstAttemptDecision.main ~ SampledFirst.main :
    true ==>
    SampledDSeedFirstAttemptDecision.raw_current{1} =
      SampledFirst.raw_current{2} /\
    res{1} = res{2} /\
    (sampled_first_attempt_score_tail res{1} <=>
     sampled_first_attempt_score_tail res{2})].
proof.
proc.
seq 2 1 :
  (SampledDSeedFirstAttemptDecision.raw_current{1} =
     SampledFirst.raw_current{2} /\
   SampledDSeedFirstAttemptDecision.sd_current{1} =
     raw_dseed_seed SampledFirst.raw_current{2}).
+ wp.
  rnd dseed_raw_seed raw_dseed_seed; auto => />.
  split.
  + move=> raw hraw.
    by rewrite (draw_raw_seed_support_raw_dseed_roundtrip raw hraw).
  move=> hinverse.
  split.
  + exact draw_raw_seed_mu1_raw_dseed_seedE.
  move=> hmass sd hsd.
  split.
  + rewrite
      /Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
      supp_dmap.
    exists sd.
    split; first exact hsd.
    by rewrite /dseed_raw_seed.
  move=> hmember.
  rewrite /dseed_raw_seed /raw_dseed_seed.
  by rewrite
    (Mode2FaithfulSecurityRawSeedDistributionPostFreeze
      .raw_security_seed_roundtrip sd hsd).
exlim SampledFirst.raw_current{2} => raw0.
call
  (Mode2FaithfulSecurityBoundedKeygenZeroFuelBridgePostFreeze
    .checked_mode2_first_attempt_decision_self_snapshot raw0).
auto => />.
qed.

lemma sampled_dseed_first_attempt_score_tail_massE &m :
  Pr[SampledDSeedFirstAttemptDecision.main() @ &m :
       sampled_first_attempt_score_tail res] =
  Pr[SampledFirst.main() @ &m :
       sampled_first_attempt_score_tail res].
proof.
byequiv sampled_dseed_first_attempt_score_tail_equiv => //=.
qed.

op sampled_dseed_first_attempt_score_tail_probability_certificate
    (epsilon tail_mass : real) : bool =
  0%r <= epsilon <= 1%r /\ tail_mass <= epsilon.

lemma sampled_dseed_first_attempt_score_tail_probability_certificateE
    epsilon &m :
  sampled_dseed_first_attempt_score_tail_probability_certificate
    epsilon
    Pr[SampledDSeedFirstAttemptDecision.main() @ &m :
         sampled_first_attempt_score_tail res] <=>
  sampled_first_attempt_reject_probability_certificate
    epsilon
    Pr[SampledFirst.main() @ &m :
         ! first_attempt_trace_accepted res].
proof.
rewrite /sampled_dseed_first_attempt_score_tail_probability_certificate
        /sampled_first_attempt_reject_probability_certificate.
rewrite sampled_dseed_first_attempt_score_tail_massE.
rewrite sampled_first_attempt_reject_score_tail_massE.
done.
qed.

lemma sampled_bounded_keygen_success_lower_bound_from_dseed_score_tail_certificate
    fuel0 epsilon &m :
  0 <= fuel0 =>
  sampled_dseed_first_attempt_score_tail_probability_certificate
    epsilon
    Pr[SampledDSeedFirstAttemptDecision.main() @ &m :
         sampled_first_attempt_score_tail res] =>
  Pr[SampledBounded.main(fuel0) @ &m :
       sampled_bounded_keygen_first_accept
         SampledBounded.raw_current fuel0 res] +
  Pr[SampledBounded.main(fuel0) @ &m :
       sampled_bounded_keygen_rejected_tail_accept
         SampledBounded.raw_current fuel0 res] >=
  1%r -
  delta_bounded_keygen_progress fuel0 -
  epsilon -
  finite_additive_defect_prefix
    delta_bounded_keygen_progress fuel0.
proof.
move=> hfuel hcert.
have hscore :
    sampled_first_attempt_reject_probability_certificate
      epsilon
      Pr[SampledFirst.main() @ &m :
           sampled_first_attempt_score_tail res].
+ move: hcert.
  rewrite /sampled_dseed_first_attempt_score_tail_probability_certificate
          /sampled_first_attempt_reject_probability_certificate.
  rewrite sampled_dseed_first_attempt_score_tail_massE.
  done.
exact
  (sampled_bounded_keygen_success_lower_bound_from_score_tail_certificate
    fuel0 epsilon &m hfuel hscore).
qed.

end Mode2FaithfulSecuritySampledFirstAttemptDSeedScoreTailPostFreeze.
