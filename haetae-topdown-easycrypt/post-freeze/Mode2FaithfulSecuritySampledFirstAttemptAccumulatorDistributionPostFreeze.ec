require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32.
require import
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorProbability
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23FirstAttemptAccumulator
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze.

import RealOrder.
import
  KeygenM23SingularFFTAccumulatorProbability
  TargetKeygenM23FullFirstAttempt
  TargetKeygenM23FirstAttemptAccumulator
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze.

theory Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze.

module SampledDSeed =
  Mode2FaithfulSecuritySampledFirstAttemptAccumulatorProbabilityPostFreeze
    .SampledDSeed.

(* The concrete first-attempt sampler is currently connected only to
   deterministic stream/range facts.  This layer therefore does not invent an
   XOF law or numeric tail.  It exposes the exact ideal-distribution
   obligations and charges one global actual-to-ideal headroom gap, instead of
   multiplying that gap by every prefix and coordinate site. *)

op ideal_accumulator_prefix_lower_tail_certificate
    (dideal : mode2_accumulator_sample distr) (epsilon_lower : real) : bool =
  0%r <= epsilon_lower <= 1%r /\
  forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu dideal (fun sample =>
      mode2_accumulator_prefix_lower_bad_at sample processed j) <=
    epsilon_lower.

op ideal_accumulator_prefix_upper_tail_certificate
    (dideal : mode2_accumulator_sample distr) (epsilon_upper : real) : bool =
  0%r <= epsilon_upper <= 1%r /\
  forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu dideal (fun sample =>
      mode2_accumulator_prefix_upper_bad_at sample processed j) <=
    epsilon_upper.

op ideal_accumulator_coordinate_real_tail_certificate
    (dideal : mode2_accumulator_sample distr) (epsilon_real : real) : bool =
  0%r <= epsilon_real <= 1%r /\
  forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu dideal (fun sample =>
      mode2_accumulator_coordinate_real_bad_at sample slot j) <=
    epsilon_real.

op ideal_accumulator_coordinate_imag_tail_certificate
    (dideal : mode2_accumulator_sample distr) (epsilon_imag : real) : bool =
  0%r <= epsilon_imag <= 1%r /\
  forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu dideal (fun sample =>
      mode2_accumulator_coordinate_imag_bad_at sample slot j) <=
    epsilon_imag.

op ideal_accumulator_local_tail_certificate
    (dideal : mode2_accumulator_sample distr)
    (epsilon_lower epsilon_upper epsilon_real epsilon_imag : real) : bool =
  ideal_accumulator_prefix_lower_tail_certificate dideal epsilon_lower /\
  ideal_accumulator_prefix_upper_tail_certificate dideal epsilon_upper /\
  ideal_accumulator_coordinate_real_tail_certificate dideal epsilon_real /\
  ideal_accumulator_coordinate_imag_tail_certificate dideal epsilon_imag.

op sampled_dseed_accumulator_headroom_distribution_bridge_certificate
    (actual_bad ideal_bad delta_xof : real) : bool =
  0%r <= delta_xof <= 1%r /\
  0%r <= ideal_bad <= 1%r /\
  actual_bad <= ideal_bad + delta_xof.

op sampled_dseed_checked_snapshot_accumulator_unsafe
    (raw : BArray32.t) (trace : first_attempt_trace) : bool =
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw trace /\
  ! first_attempt_trace_accumulator_safe trace.

op sampled_dseed_checked_snapshot_accumulator_error_failure
    (raw : BArray32.t) (trace : first_attempt_trace) (j : int) : bool =
  Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze
    .checked_first_attempt_snapshot_facts
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
      raw trace /\
  ! first_attempt_trace_accumulator_error_at trace j.

lemma sampled_dseed_accumulator_headroom_distribution_bridge_certificateE
    actual_bad ideal_bad delta_xof :
  sampled_dseed_accumulator_headroom_distribution_bridge_certificate
    actual_bad ideal_bad delta_xof =>
  actual_bad <= ideal_bad + delta_xof.
proof.
rewrite
  /sampled_dseed_accumulator_headroom_distribution_bridge_certificate.
smt().
qed.

lemma ideal_accumulator_headroom_bad_mu_le_split
    (dideal : mode2_accumulator_sample distr)
    epsilon_lower epsilon_upper epsilon_real epsilon_imag :
  ideal_accumulator_local_tail_certificate
    dideal epsilon_lower epsilon_upper epsilon_real epsilon_imag =>
  mu dideal mode2_accumulator_trace_headroom_bad <=
    1536%r * (epsilon_lower + epsilon_upper) +
    1280%r * (epsilon_real + epsilon_imag).
proof.
rewrite /ideal_accumulator_local_tail_certificate.
move=> [hlower [hupper [hreal himag]]].
move: hlower; rewrite /ideal_accumulator_prefix_lower_tail_certificate.
move=> [_ hlower].
move: hupper; rewrite /ideal_accumulator_prefix_upper_tail_certificate.
move=> [_ hupper].
move: hreal; rewrite /ideal_accumulator_coordinate_real_tail_certificate.
move=> [_ hreal].
move: himag; rewrite /ideal_accumulator_coordinate_imag_tail_certificate.
move=> [_ himag].
exact
  (mode2_accumulator_headroom_bad_event_mu_le_split
    dideal epsilon_lower epsilon_upper epsilon_real epsilon_imag
    hlower hupper hreal himag).
qed.

lemma sampled_dseed_first_attempt_accumulator_headroom_pr_le_ideal_split
    (dideal : mode2_accumulator_sample distr)
    delta_xof epsilon_lower epsilon_upper epsilon_real epsilon_imag &m :
  sampled_dseed_accumulator_headroom_distribution_bridge_certificate
    (Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res])
    (mu dideal mode2_accumulator_trace_headroom_bad)
    delta_xof =>
  ideal_accumulator_local_tail_certificate
    dideal epsilon_lower epsilon_upper epsilon_real epsilon_imag =>
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res] <=
    1536%r * (epsilon_lower + epsilon_upper) +
    1280%r * (epsilon_real + epsilon_imag) +
    delta_xof.
proof.
move=> hbridge hlocal.
have hactual :=
  sampled_dseed_accumulator_headroom_distribution_bridge_certificateE
    (Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res])
    (mu dideal mode2_accumulator_trace_headroom_bad)
    delta_xof hbridge.
have hideal :=
  ideal_accumulator_headroom_bad_mu_le_split
    dideal epsilon_lower epsilon_upper epsilon_real epsilon_imag hlocal.
smt().
qed.

lemma sampled_dseed_checked_snapshot_accumulator_unsafe_pr_le_ideal_split
    (dideal : mode2_accumulator_sample distr)
    delta_xof epsilon_lower epsilon_upper epsilon_real epsilon_imag &m :
  sampled_dseed_accumulator_headroom_distribution_bridge_certificate
    (Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res])
    (mu dideal mode2_accumulator_trace_headroom_bad)
    delta_xof =>
  ideal_accumulator_local_tail_certificate
    dideal epsilon_lower epsilon_upper epsilon_real epsilon_imag =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_checked_snapshot_accumulator_unsafe
         SampledDSeed.raw_current res] <=
    1536%r * (epsilon_lower + epsilon_upper) +
    1280%r * (epsilon_real + epsilon_imag) +
    delta_xof.
proof.
move=> hbridge hlocal.
have hunsafe :
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_checked_snapshot_accumulator_unsafe
         SampledDSeed.raw_current res] <=
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res].
+ rewrite /sampled_dseed_checked_snapshot_accumulator_unsafe.
  exact
    (sampled_dseed_checked_snapshot_accumulator_unsafe_pr_le_headroom_bad &m).
have hheadroom :=
  sampled_dseed_first_attempt_accumulator_headroom_pr_le_ideal_split
    dideal delta_xof epsilon_lower epsilon_upper epsilon_real epsilon_imag
    &m hbridge hlocal.
exact (ler_trans _ _ _ hunsafe hheadroom).
qed.

lemma sampled_dseed_checked_snapshot_accumulator_error_failure_pr_le_ideal_split
    (dideal : mode2_accumulator_sample distr) (j : int)
    delta_xof epsilon_lower epsilon_upper epsilon_real epsilon_imag &m :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  sampled_dseed_accumulator_headroom_distribution_bridge_certificate
    (Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res])
    (mu dideal mode2_accumulator_trace_headroom_bad)
    delta_xof =>
  ideal_accumulator_local_tail_certificate
    dideal epsilon_lower epsilon_upper epsilon_real epsilon_imag =>
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_checked_snapshot_accumulator_error_failure
         SampledDSeed.raw_current res j] <=
    1536%r * (epsilon_lower + epsilon_upper) +
    1280%r * (epsilon_real + epsilon_imag) +
    delta_xof.
proof.
move=> hj hbridge hlocal.
have herror :
  Pr[SampledDSeed.main() @ &m :
       sampled_dseed_checked_snapshot_accumulator_error_failure
         SampledDSeed.raw_current res j] <=
  Pr[SampledDSeed.main() @ &m :
       first_attempt_trace_accumulator_headroom_bad res].
+ rewrite /sampled_dseed_checked_snapshot_accumulator_error_failure.
  exact
    (sampled_dseed_checked_snapshot_accumulator_error_failure_pr_le_headroom_bad
      j &m hj).
have hheadroom :=
  sampled_dseed_first_attempt_accumulator_headroom_pr_le_ideal_split
    dideal delta_xof epsilon_lower epsilon_upper epsilon_real epsilon_imag
    &m hbridge hlocal.
exact (ler_trans _ _ _ herror hheadroom).
qed.

end Mode2FaithfulSecuritySampledFirstAttemptAccumulatorDistributionPostFreeze.
