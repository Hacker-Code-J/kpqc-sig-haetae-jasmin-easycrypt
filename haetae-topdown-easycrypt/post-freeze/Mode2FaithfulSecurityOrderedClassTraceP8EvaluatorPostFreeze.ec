require import AllCore Distr List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  KeygenM23SingularFFTSpec
  KeygenM23SingularSpec
  Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptAcceptedClassTraceP8PostFreeze
  Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import Mode2FaithfulSecurityAccumulatorJointCouplingPostFreeze.
import Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.
import Mode2FaithfulSecuritySampledFirstAttemptAcceptedClassTraceP8PostFreeze.
import Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze.

theory Mode2FaithfulSecurityOrderedClassTraceP8EvaluatorPostFreeze.

(* This file is only a deterministic ordered-trace diagnostic evaluator for the
   accepted first-attempt class-trace carrier.  It reuses the existing P8
   component-cap recurrences, but it does not add any ideal trace mass bound,
   conditioning lemma, independence claim, or new security theorem beyond the
   generic accepted-class-trace bridge instantiated below. *)

op ordered_class_trace_row
    (rows : int list list) (row : int) : int -> int =
  fun j => nth 0 (nth [] rows row) j.

op ordered_class_trace_re_profile8_interval
    (rows : int list list) (row k : int) : rinterval =
  certified_class_re_profile8_interval
    (ordered_class_trace_row rows row) k mode2_class_trace_words.

op ordered_class_trace_im_profile8_interval
    (rows : int list list) (row k : int) : rinterval =
  certified_class_im_profile8_interval
    (ordered_class_trace_row rows row) k mode2_class_trace_words.

op ordered_class_trace_bias_re_interval
    (rows : int list list) (row k : int) : rinterval =
  ideal_final_s2_class_bias_re_interval
    (ordered_class_trace_row rows row) k mode2_class_trace_words.

op ordered_class_trace_bias_im_interval
    (rows : int list list) (row k : int) : rinterval =
  ideal_final_s2_class_bias_im_interval
    (ordered_class_trace_row rows row) k mode2_class_trace_words.

op ordered_class_trace_s2_real_residual_headroom
    (rows : int list list) (row k : int) : real =
  ideal_mode2_upper_prefix_s2_component_cap -
  interval_abs_upper (ordered_class_trace_bias_re_interval rows row k).

op ordered_class_trace_s2_imag_residual_headroom
    (rows : int list list) (row k : int) : real =
  ideal_mode2_upper_prefix_s2_component_cap -
  interval_abs_upper (ordered_class_trace_bias_im_interval rows row k).

op ordered_class_trace_s2_real_markov8_rhs
    (rows : int list list) (row k : int) : real =
  interval_abs_upper (ordered_class_trace_re_profile8_interval rows row k) /
  (ordered_class_trace_s2_real_residual_headroom rows row k ^ 8).

op ordered_class_trace_s2_imag_markov8_rhs
    (rows : int list list) (row k : int) : real =
  interval_abs_upper (ordered_class_trace_im_profile8_interval rows row k) /
  (ordered_class_trace_s2_imag_residual_headroom rows row k ^ 8).

op ordered_class_trace_s2_markov8_rhs
    (rows : int list list) (row k : int) : real =
  ordered_class_trace_s2_real_markov8_rhs rows row k +
  ordered_class_trace_s2_imag_markov8_rhs rows row k.

op ordered_class_trace_component_markov8_rhs
    (rows : int list list) (slot k : int) : real =
  if slot < KeygenM23SingularFFTSpec.mode2_s1_count_i then
    ideal_mode2_upper_prefix_s1_markov8_rhs k
  else
    ordered_class_trace_s2_markov8_rhs
      rows (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) k.

op ordered_class_trace_component_markov8_row_sum
    (rows : int list list) (slot : int) : real =
  BRA.bigi predT
    (fun k => ordered_class_trace_component_markov8_rhs rows slot k)
    0 KeygenM23SingularSpec.singular_words_i.

op ordered_class_trace_component_markov8_sum
    (rows : int list list) : real =
  BRA.bigi predT
    (ordered_class_trace_component_markov8_row_sum rows)
    0 KeygenM23SingularFFTSpec.mode2_slice_count_i.

op ordered_class_trace_positive_s2_headrooms
    (rows : int list list) : bool =
  forall row k,
    0 <= row < mode2_class_trace_rows =>
    0 <= k < mode2_class_trace_words =>
    0%r < ordered_class_trace_s2_real_residual_headroom rows row k /\
    0%r < ordered_class_trace_s2_imag_residual_headroom rows row k.

op ordered_class_trace_p8_admissible
    (rows : int list list) : bool =
  ordered_class_trace_wf rows /\ ordered_class_trace_positive_s2_headrooms rows.

op trace_p8_union_bound (rows : int list list) : real =
  if ordered_class_trace_p8_admissible rows then
    ordered_class_trace_component_markov8_sum rows
  else 1%r.

op ordered_class_trace_p8_bad (rows : int list list) : bool =
  1%r / 2%r <= trace_p8_union_bound rows.

lemma trace_p8_union_bound_admissibleE rows :
  ordered_class_trace_p8_admissible rows =>
  trace_p8_union_bound rows =
    ordered_class_trace_component_markov8_sum rows.
proof.
by rewrite /trace_p8_union_bound => ->.
qed.

lemma ordered_class_trace_p8_bad_admissibleE rows :
  ordered_class_trace_p8_admissible rows =>
  (ordered_class_trace_p8_bad rows <=>
   1%r / 2%r <= ordered_class_trace_component_markov8_sum rows).
proof.
move=> hadmissible.
rewrite /ordered_class_trace_p8_bad
        (trace_p8_union_bound_admissibleE rows hadmissible).
trivial.
qed.

lemma ordered_class_trace_p8_bad_of_not_admissible rows :
  ! ordered_class_trace_p8_admissible rows =>
  ordered_class_trace_p8_bad rows.
proof.
move=> hbad.
rewrite /ordered_class_trace_p8_bad /trace_p8_union_bound hbad.
smt().
qed.

op zero_seed_accepted_ordered_class_trace : int list list = [
  zero_seed_accepted_row0_classes;
  zero_seed_accepted_row1_classes
].

op zero_seed_accepted_ordered_class_trace_structure_certificate : bool =
  ordered_class_trace_wf zero_seed_accepted_ordered_class_trace /\
  forall row,
    ordered_class_trace_row zero_seed_accepted_ordered_class_trace row =
    zero_seed_accepted_trace row.

op zero_seed_accepted_ordered_class_trace_p8_numeric_certificate : bool =
  zero_seed_accepted_ordered_class_trace_structure_certificate /\
  ideal_mode2_upper_prefix_p8_numeric_certificate.

lemma zero_seed_accepted_ordered_class_trace_wf :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_wf zero_seed_accepted_ordered_class_trace.
proof.
rewrite /zero_seed_accepted_ordered_class_trace_structure_certificate.
smt().
qed.

lemma zero_seed_accepted_ordered_class_trace_rowE row :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_row zero_seed_accepted_ordered_class_trace row =
  zero_seed_accepted_trace row.
proof.
rewrite /zero_seed_accepted_ordered_class_trace_structure_certificate.
smt().
qed.

lemma zero_seed_accepted_ordered_class_trace_re_profile8_intervalE row k :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_re_profile8_interval
    zero_seed_accepted_ordered_class_trace row k =
  zero_seed_accepted_re_profile8_interval row k.
proof.
move=> hstructure.
rewrite /ordered_class_trace_re_profile8_interval.
rewrite (zero_seed_accepted_re_profile8_intervalE row k).
rewrite (zero_seed_accepted_ordered_class_trace_rowE row hstructure).
trivial.
qed.

lemma zero_seed_accepted_ordered_class_trace_im_profile8_intervalE row k :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_im_profile8_interval
    zero_seed_accepted_ordered_class_trace row k =
  zero_seed_accepted_im_profile8_interval row k.
proof.
move=> hstructure.
rewrite /ordered_class_trace_im_profile8_interval.
rewrite (zero_seed_accepted_im_profile8_intervalE row k).
rewrite (zero_seed_accepted_ordered_class_trace_rowE row hstructure).
trivial.
qed.

lemma zero_seed_accepted_ordered_class_trace_bias_re_intervalE row k :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_bias_re_interval
    zero_seed_accepted_ordered_class_trace row k =
  zero_seed_accepted_bias_re_interval row k.
proof.
move=> hstructure.
rewrite /ordered_class_trace_bias_re_interval
        /zero_seed_accepted_bias_re_interval.
rewrite (zero_seed_accepted_ordered_class_trace_rowE row hstructure).
trivial.
qed.

lemma zero_seed_accepted_ordered_class_trace_bias_im_intervalE row k :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_bias_im_interval
    zero_seed_accepted_ordered_class_trace row k =
  zero_seed_accepted_bias_im_interval row k.
proof.
move=> hstructure.
rewrite /ordered_class_trace_bias_im_interval
        /zero_seed_accepted_bias_im_interval.
rewrite (zero_seed_accepted_ordered_class_trace_rowE row hstructure).
trivial.
qed.

lemma zero_seed_accepted_ordered_class_trace_positive_s2_headrooms :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  ordered_class_trace_positive_s2_headrooms
    zero_seed_accepted_ordered_class_trace.
proof.
move=> hstructure hnumeric.
rewrite /ordered_class_trace_positive_s2_headrooms.
move=> row k hrow hk.
have [hre him] :=
  ideal_mode2_upper_prefix_s2_headrooms_positive row k hnumeric hrow hk.
rewrite /ordered_class_trace_s2_real_residual_headroom
        /ordered_class_trace_s2_imag_residual_headroom.
rewrite (zero_seed_accepted_ordered_class_trace_bias_re_intervalE
  row k hstructure).
rewrite (zero_seed_accepted_ordered_class_trace_bias_im_intervalE
  row k hstructure).
split.
+ exact hre.
exact him.
qed.

lemma zero_seed_accepted_ordered_class_trace_admissible :
  zero_seed_accepted_ordered_class_trace_p8_numeric_certificate =>
  ordered_class_trace_p8_admissible zero_seed_accepted_ordered_class_trace.
proof.
rewrite /zero_seed_accepted_ordered_class_trace_p8_numeric_certificate.
move=> [hstructure hnumeric].
rewrite /ordered_class_trace_p8_admissible.
split.
+ exact (zero_seed_accepted_ordered_class_trace_wf hstructure).
exact
  (zero_seed_accepted_ordered_class_trace_positive_s2_headrooms
    hstructure hnumeric).
qed.

lemma zero_seed_accepted_ordered_class_trace_s2_real_markov8_rhsE row k :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_s2_real_markov8_rhs
    zero_seed_accepted_ordered_class_trace row k =
  ideal_mode2_upper_prefix_s2_real_markov8_rhs row k.
proof.
move=> hstructure.
rewrite /ordered_class_trace_s2_real_markov8_rhs
        /ideal_mode2_upper_prefix_s2_real_markov8_rhs.
rewrite (zero_seed_accepted_ordered_class_trace_re_profile8_intervalE
  row k hstructure).
rewrite /ordered_class_trace_s2_real_residual_headroom
        (zero_seed_accepted_ordered_class_trace_bias_re_intervalE
          row k hstructure).
trivial.
qed.

lemma zero_seed_accepted_ordered_class_trace_s2_imag_markov8_rhsE row k :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_s2_imag_markov8_rhs
    zero_seed_accepted_ordered_class_trace row k =
  ideal_mode2_upper_prefix_s2_imag_markov8_rhs row k.
proof.
move=> hstructure.
rewrite /ordered_class_trace_s2_imag_markov8_rhs
        /ideal_mode2_upper_prefix_s2_imag_markov8_rhs.
rewrite (zero_seed_accepted_ordered_class_trace_im_profile8_intervalE
  row k hstructure).
rewrite /ordered_class_trace_s2_imag_residual_headroom
        (zero_seed_accepted_ordered_class_trace_bias_im_intervalE
          row k hstructure).
trivial.
qed.

lemma zero_seed_accepted_ordered_class_trace_component_markov8_rhsE slot k :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_component_markov8_rhs
    zero_seed_accepted_ordered_class_trace slot k =
  ideal_mode2_upper_prefix_component_markov8_rhs slot k.
proof.
move=> hstructure.
rewrite /ordered_class_trace_component_markov8_rhs
        /ideal_mode2_upper_prefix_component_markov8_rhs.
case (slot < KeygenM23SingularFFTSpec.mode2_s1_count_i) => hs1.
+ trivial.
rewrite /ordered_class_trace_s2_markov8_rhs
        /ideal_mode2_upper_prefix_s2_markov8_rhs.
rewrite
  (zero_seed_accepted_ordered_class_trace_s2_real_markov8_rhsE
    (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) k hstructure).
rewrite
  (zero_seed_accepted_ordered_class_trace_s2_imag_markov8_rhsE
    (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) k hstructure).
trivial.
qed.

lemma zero_seed_accepted_ordered_class_trace_component_markov8_sumE :
  zero_seed_accepted_ordered_class_trace_structure_certificate =>
  ordered_class_trace_component_markov8_sum
    zero_seed_accepted_ordered_class_trace =
  ideal_mode2_upper_prefix_component_markov8_sum.
proof.
move=> hstructure.
rewrite /ordered_class_trace_component_markov8_sum
        /ideal_mode2_upper_prefix_component_markov8_sum.
apply BRA.eq_big_seq => slot hslot.
rewrite /ordered_class_trace_component_markov8_row_sum
        /ideal_mode2_upper_prefix_component_markov8_row_sum.
apply BRA.eq_big_seq => k hk.
exact
  (zero_seed_accepted_ordered_class_trace_component_markov8_rhsE
    slot k hstructure).
qed.

lemma zero_seed_accepted_ordered_class_trace_trace_p8_union_boundE :
  zero_seed_accepted_ordered_class_trace_p8_numeric_certificate =>
  trace_p8_union_bound zero_seed_accepted_ordered_class_trace =
  ideal_mode2_upper_prefix_component_markov8_sum.
proof.
move=> hnumeric.
rewrite /trace_p8_union_bound.
rewrite (zero_seed_accepted_ordered_class_trace_admissible hnumeric).
move: hnumeric.
rewrite /zero_seed_accepted_ordered_class_trace_p8_numeric_certificate.
move=> [hstructure _].
exact
  (zero_seed_accepted_ordered_class_trace_component_markov8_sumE hstructure).
qed.

lemma zero_seed_accepted_ordered_class_trace_not_p8_bad :
  zero_seed_accepted_ordered_class_trace_p8_numeric_certificate =>
  ! ordered_class_trace_p8_bad zero_seed_accepted_ordered_class_trace.
proof.
move=> hnumeric.
rewrite /ordered_class_trace_p8_bad.
rewrite zero_seed_accepted_ordered_class_trace_trace_p8_union_boundE 1:hnumeric.
move: hnumeric.
rewrite /zero_seed_accepted_ordered_class_trace_p8_numeric_certificate
        /ideal_mode2_upper_prefix_p8_numeric_certificate
        /ideal_mode2_reduced_headroom_p8_target.
smt().
qed.

lemma sampled_dseed_first_attempt_accepted_ordered_class_trace_p8_pr_le_certificate
    (djoint : ideal_mode2_accumulator_joint_sample distr)
    delta_xof epsilon_p8 &m :
  0%r <= delta_xof <= 1%r =>
  ideal_mode2_joint_accepted_class_trace_p8_probability_certificate
    djoint ordered_class_trace_p8_bad epsilon_p8 =>
  (forall (E : ideal_mode2_accumulator_joint_sample -> bool),
    Pr[SampledDSeed.main() @ &m :
         E (trace_local_joint_sample res)] <=
    mu djoint E + delta_xof) =>
  Pr[SampledDSeedFirstAttemptClassTrace.main() @ &m :
       accepted_class_trace_p8_bad ordered_class_trace_p8_bad res] <=
  epsilon_p8 + delta_xof.
proof.
move=> hdelta hcert hgap.
exact
  (sampled_dseed_first_attempt_accepted_class_trace_p8_pr_le_certificate
    djoint ordered_class_trace_p8_bad delta_xof epsilon_p8 &m
    hdelta hcert hgap).
qed.

end Mode2FaithfulSecurityOrderedClassTraceP8EvaluatorPostFreeze.
