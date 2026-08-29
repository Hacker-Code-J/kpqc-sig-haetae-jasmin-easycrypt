require import AllCore DList Distr Finite FSet IntDiv List Mu_mem Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import BArray8192.
require import
  KeygenM23ComplexReal
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorProbability
  KeygenM23SingularFFTAccumulatorSafety
  Mode2FaithfulSecurityAccumulatorUpperHeadroomPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealAccumulatorAllSlotCoordinateP8CertificatePostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8UnionLimitationPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze.

import RealOrder Bigreal Bigreal.BRM RField.
import KeygenM23ComplexReal.
import KeygenM23SingularFFTAccumulatorBridge.
import KeygenM23SingularFFTAccumulatorProbability.
import KeygenM23SingularFFTAccumulatorSafety.
import Mode2FaithfulSecurityAccumulatorUpperHeadroomPostFreeze.
import Mode2FaithfulSecurityIdealAccumulatorAllSlotCoordinateP8CertificatePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8UnionLimitationPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze.

theory Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze.

(* The original analytic headroom predicate asks a symmetric error envelope
   to prove that every prefix is nonnegative.  The lower-free safety theory
   derives that fact from the already-safe machine prefix instead.  This file
   therefore bounds only the remaining upper-prefix and coordinate conditions
   with a single stricter component-cap event.  The result stays conditional
   on the deterministic raw_seed=0 accepted s2 class trace and the explicit
   numeric certificate; random contexts, retries, and unconditional keygen
   remain outside its scope. *)

op ideal_mode2_upper_prefix_s1_component_cap : real = 50%r.

op ideal_mode2_upper_prefix_s2_component_cap : real = 65%r.

op ideal_mode2_reduced_headroom_p8_target : real = 1%r / 2%r.

op ideal_mode2_upper_prefix_slot_component_cap (slot : int) : real =
  if slot < KeygenM23SingularFFTSpec.mode2_s1_count_i then
    ideal_mode2_upper_prefix_s1_component_cap
  else ideal_mode2_upper_prefix_s2_component_cap.

op ideal_mode2_upper_prefix_component_real_bad_at
    (sample : mode2_accumulator_sample) (slot k : int) : bool =
  ideal_mode2_upper_prefix_slot_component_cap slot <
    `|creal (mode2_ideal_fft_at sample.`1 sample.`2 slot k)|.

op ideal_mode2_upper_prefix_component_imag_bad_at
    (sample : mode2_accumulator_sample) (slot k : int) : bool =
  ideal_mode2_upper_prefix_slot_component_cap slot <
    `|cimag (mode2_ideal_fft_at sample.`1 sample.`2 slot k)|.

op ideal_mode2_upper_prefix_component_bad_at
    (sample : mode2_accumulator_sample) (slot k : int) : bool =
  ideal_mode2_upper_prefix_component_real_bad_at sample slot k \/
  ideal_mode2_upper_prefix_component_imag_bad_at sample slot k.

op ideal_mode2_upper_prefix_component_bad
    (sample : mode2_accumulator_sample) : bool =
  exists slot,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i /\
    exists k,
      0 <= k < KeygenM23SingularSpec.singular_words_i /\
      ideal_mode2_upper_prefix_component_bad_at sample slot k.

op ideal_mode2_component_step_budget (cap : real) : real =
  2%r * cap ^ 2 +
  4%r * mode2_fft_endpoint_eps * cap +
  1%r / 65536%r + 2%r * mode2_fft_endpoint_eps ^ 2.

op ideal_mode2_upper_prefix_s1_step_budget : real =
  ideal_mode2_component_step_budget
    ideal_mode2_upper_prefix_s1_component_cap.

op ideal_mode2_upper_prefix_s2_step_budget : real =
  ideal_mode2_component_step_budget
    ideal_mode2_upper_prefix_s2_component_cap.

op ideal_mode2_upper_prefix_full_budget : real =
  3%r * ideal_mode2_upper_prefix_s1_step_budget +
  2%r * ideal_mode2_upper_prefix_s2_step_budget.

op ideal_mode2_upper_prefix_budget (processed : int) : real =
  if processed < KeygenM23SingularFFTSpec.mode2_s1_count_i then
    processed%r * ideal_mode2_upper_prefix_s1_step_budget
  else
    3%r * ideal_mode2_upper_prefix_s1_step_budget +
    (processed - KeygenM23SingularFFTSpec.mode2_s1_count_i)%r *
      ideal_mode2_upper_prefix_s2_step_budget.

op ideal_mode2_combined_energy_prefix
    (sample : mode2_accumulator_sample) (processed k : int) : real =
  mode2_ideal_energy_prefix sample.`1 sample.`2 processed k +
  mode2_energy_error_prefix sample.`1 sample.`2 processed k.

lemma ideal_mode2_upper_prefix_caps_positive :
  0%r < ideal_mode2_upper_prefix_s1_component_cap /\
  0%r < ideal_mode2_upper_prefix_s2_component_cap.
proof.
rewrite /ideal_mode2_upper_prefix_s1_component_cap
        /ideal_mode2_upper_prefix_s2_component_cap.
trivial.
qed.

lemma ideal_mode2_square_le_cap2 (x cap : real) :
  0%r <= cap =>
  `|x| <= cap =>
  x ^ 2 <= cap ^ 2.
proof.
move=> hcap hbound.
have habs0 : 0%r <= `|x| by exact (normr_ge0 x).
have hrange : 0%r <= `|x| <= cap by smt().
have hpow := ler_pexp 2 `|x| cap _ hrange.
+ trivial.
move: hpow.
rewrite -normrX_nat 1:/#.
rewrite ger0_norm 1:(ge0_sqr x).
trivial.
qed.

lemma ideal_mode2_component_step_le_budget z cap :
  0%r <= cap =>
  `|creal z| <= cap =>
  `|cimag z| <= cap =>
  cnorm2 z + sqabs_ideal_error_budget mode2_fft_endpoint_eps z <=
    ideal_mode2_component_step_budget cap.
proof.
move=> hcap hre him.
have hre2 := ideal_mode2_square_le_cap2 (creal z) cap hcap hre.
have him2 := ideal_mode2_square_le_cap2 (cimag z) cap hcap him.
have heps := mode2_fft_endpoint_eps_ge0.
have hreinner :
    2%r * `|creal z| + mode2_fft_endpoint_eps <=
    2%r * cap + mode2_fft_endpoint_eps by smt().
have himinner :
    2%r * `|cimag z| + mode2_fft_endpoint_eps <=
    2%r * cap + mode2_fft_endpoint_eps by smt().
have hreerr :=
  ler_wpmul2l mode2_fft_endpoint_eps heps
    (2%r * `|creal z| + mode2_fft_endpoint_eps)
    (2%r * cap + mode2_fft_endpoint_eps) hreinner.
have himerr :=
  ler_wpmul2l mode2_fft_endpoint_eps heps
    (2%r * `|cimag z| + mode2_fft_endpoint_eps)
    (2%r * cap + mode2_fft_endpoint_eps) himinner.
have henergy :
    creal z ^ 2 + cimag z ^ 2 <= cap ^ 2 + cap ^ 2 by smt().
have herror :
    1%r / 65536%r +
      (mode2_fft_endpoint_eps *
         (2%r * `|creal z| + mode2_fft_endpoint_eps) +
       mode2_fft_endpoint_eps *
         (2%r * `|cimag z| + mode2_fft_endpoint_eps)) <=
    1%r / 65536%r +
      (mode2_fft_endpoint_eps *
         (2%r * cap + mode2_fft_endpoint_eps) +
       mode2_fft_endpoint_eps *
         (2%r * cap + mode2_fft_endpoint_eps)) by smt().
have hsum :
    (creal z ^ 2 + cimag z ^ 2) +
      (1%r / 65536%r +
       (mode2_fft_endpoint_eps *
          (2%r * `|creal z| + mode2_fft_endpoint_eps) +
        mode2_fft_endpoint_eps *
          (2%r * `|cimag z| + mode2_fft_endpoint_eps))) <=
    (cap ^ 2 + cap ^ 2) +
      (1%r / 65536%r +
       (mode2_fft_endpoint_eps *
          (2%r * cap + mode2_fft_endpoint_eps) +
        mode2_fft_endpoint_eps *
          (2%r * cap + mode2_fft_endpoint_eps))).
+ apply ler_add.
  + exact henergy.
  exact herror.
rewrite /cnorm2 /sqabs_ideal_error_budget
        /cnorm2_perturbation_budget
        /ideal_mode2_component_step_budget.
apply
  (ler_trans
    ((cap ^ 2 + cap ^ 2) +
      (1%r / 65536%r +
       (mode2_fft_endpoint_eps *
          (2%r * cap + mode2_fft_endpoint_eps) +
        mode2_fft_endpoint_eps *
          (2%r * cap + mode2_fft_endpoint_eps))))).
+ move: hsum.
  have -> :
      (creal z * creal z + cimag z * cimag z) +
        (1%r / 65536%r +
         (mode2_fft_endpoint_eps *
            (2%r * `|creal z| + mode2_fft_endpoint_eps) +
          mode2_fft_endpoint_eps *
            (2%r * `|cimag z| + mode2_fft_endpoint_eps))) =
      (creal z ^ 2 + cimag z ^ 2) +
        (1%r / 65536%r +
         (mode2_fft_endpoint_eps *
            (2%r * `|creal z| + mode2_fft_endpoint_eps) +
          mode2_fft_endpoint_eps *
            (2%r * `|cimag z| + mode2_fft_endpoint_eps))) by ring.
  trivial.
have -> :
    (cap ^ 2 + cap ^ 2) +
      (1%r / 65536%r +
       (mode2_fft_endpoint_eps *
          (2%r * cap + mode2_fft_endpoint_eps) +
        mode2_fft_endpoint_eps *
          (2%r * cap + mode2_fft_endpoint_eps))) =
    2%r * cap ^ 2 + 4%r * mode2_fft_endpoint_eps * cap +
      1%r / 65536%r + 2%r * mode2_fft_endpoint_eps ^ 2 by ring.
trivial.
qed.

lemma ideal_mode2_upper_prefix_full_budget_lt_signed_limit :
  ideal_mode2_upper_prefix_full_budget < accumulator_q16_signed_limit.
proof.
have -> :
    ideal_mode2_upper_prefix_full_budget =
      70160156797765%r / 2147483648%r.
+ rewrite /ideal_mode2_upper_prefix_full_budget
          /ideal_mode2_upper_prefix_s1_step_budget
          /ideal_mode2_upper_prefix_s2_step_budget
          /ideal_mode2_component_step_budget
          /ideal_mode2_upper_prefix_s1_component_cap
          /ideal_mode2_upper_prefix_s2_component_cap
          /mode2_fft_endpoint_eps.
  field; smt().
rewrite /accumulator_q16_signed_limit.
smt().
qed.

lemma ideal_mode2_upper_prefix_budget0 :
  ideal_mode2_upper_prefix_budget 0 = 0%r.
proof.
rewrite /ideal_mode2_upper_prefix_budget
        /KeygenM23SingularFFTSpec.mode2_s1_count_i.
ring.
qed.

lemma ideal_mode2_upper_prefix_budgetS processed :
  0 <= processed < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  ideal_mode2_upper_prefix_budget (processed + 1) =
    ideal_mode2_upper_prefix_budget processed +
      ideal_mode2_component_step_budget
        (ideal_mode2_upper_prefix_slot_component_cap processed).
proof.
move=> hprocessed.
rewrite /ideal_mode2_upper_prefix_budget
        /ideal_mode2_upper_prefix_slot_component_cap
        /ideal_mode2_upper_prefix_s1_step_budget
        /ideal_mode2_upper_prefix_s2_step_budget
        /KeygenM23SingularFFTSpec.mode2_s1_count_i
        /KeygenM23SingularFFTSpec.mode2_slice_count_i.
case (processed < 3) => hp3.
+ case (processed + 1 < 3) => hp2; smt().
rewrite ifF 1:/#.
ring.
qed.

lemma ideal_mode2_upper_prefix_s1_step_budget_exact :
  ideal_mode2_upper_prefix_s1_step_budget =
    11033245819457%r / 2147483648%r.
proof.
rewrite /ideal_mode2_upper_prefix_s1_step_budget
        /ideal_mode2_component_step_budget
        /ideal_mode2_upper_prefix_s1_component_cap
        /mode2_fft_endpoint_eps.
field; smt().
qed.

lemma ideal_mode2_upper_prefix_s2_step_budget_exact :
  ideal_mode2_upper_prefix_s2_step_budget =
    18530209669697%r / 2147483648%r.
proof.
rewrite /ideal_mode2_upper_prefix_s2_step_budget
        /ideal_mode2_component_step_budget
        /ideal_mode2_upper_prefix_s2_component_cap
        /mode2_fft_endpoint_eps.
field; smt().
qed.

lemma ideal_mode2_upper_prefix_budget_le_full processed :
  0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  ideal_mode2_upper_prefix_budget processed <=
    ideal_mode2_upper_prefix_full_budget.
proof.
move=> hprocessed.
rewrite /ideal_mode2_upper_prefix_budget
        /ideal_mode2_upper_prefix_full_budget
        /KeygenM23SingularFFTSpec.mode2_s1_count_i
        /KeygenM23SingularFFTSpec.mode2_slice_count_i.
have hs1nonneg : 0%r <= ideal_mode2_upper_prefix_s1_step_budget.
+ rewrite ideal_mode2_upper_prefix_s1_step_budget_exact.
  smt().
have hs2nonneg : 0%r <= ideal_mode2_upper_prefix_s2_step_budget.
+ rewrite ideal_mode2_upper_prefix_s2_step_budget_exact.
  smt().
case (processed < 3) => hp3; smt().
qed.

lemma ideal_mode2_combined_energy_prefix0 sample k :
  ideal_mode2_combined_energy_prefix sample 0 k = 0%r.
proof.
rewrite /ideal_mode2_combined_energy_prefix
        mode2_ideal_energy_prefix0 mode2_energy_error_prefix0.
ring.
qed.

lemma ideal_mode2_combined_energy_prefixS sample processed k :
  0 <= processed =>
  ideal_mode2_combined_energy_prefix sample (processed + 1) k =
  ideal_mode2_combined_energy_prefix sample processed k +
    (cnorm2 (mode2_ideal_fft_at sample.`1 sample.`2 processed k) +
     sqabs_ideal_error_budget mode2_fft_endpoint_eps
       (mode2_ideal_fft_at sample.`1 sample.`2 processed k)).
proof.
move=> hprocessed.
rewrite /ideal_mode2_combined_energy_prefix
        mode2_ideal_energy_prefixS 1:hprocessed
        mode2_energy_error_prefixS 1:hprocessed.
ring.
qed.

lemma ideal_mode2_upper_prefix_component_good_at
    sample slot k :
  ! ideal_mode2_upper_prefix_component_bad sample =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  `|creal (mode2_ideal_fft_at sample.`1 sample.`2 slot k)| <=
    ideal_mode2_upper_prefix_slot_component_cap slot /\
  `|cimag (mode2_ideal_fft_at sample.`1 sample.`2 slot k)| <=
    ideal_mode2_upper_prefix_slot_component_cap slot.
proof.
rewrite /ideal_mode2_upper_prefix_component_bad
        /ideal_mode2_upper_prefix_component_bad_at
        /ideal_mode2_upper_prefix_component_real_bad_at
        /ideal_mode2_upper_prefix_component_imag_bad_at.
smt().
qed.

lemma ideal_mode2_combined_energy_prefix_le_budget
    sample processed k :
  0 <= processed =>
  processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  ! ideal_mode2_upper_prefix_component_bad sample =>
  ideal_mode2_combined_energy_prefix sample processed k <=
    ideal_mode2_upper_prefix_budget processed.
proof.
move: processed.
apply intind.
+ move=> _ _ _.
  rewrite ideal_mode2_combined_energy_prefix0
          ideal_mode2_upper_prefix_budget0.
  trivial.
move=> processed hprocessed ih hcap hk hgood.
have hslot :
    0 <= processed < KeygenM23SingularFFTSpec.mode2_slice_count_i by smt().
have hprev := ih _ hk hgood.
+ smt().
have [hre him] :=
  ideal_mode2_upper_prefix_component_good_at
    sample processed k hgood hslot hk.
have hcapnonneg :
    0%r <= ideal_mode2_upper_prefix_slot_component_cap processed.
+ rewrite /ideal_mode2_upper_prefix_slot_component_cap.
  rewrite /ideal_mode2_upper_prefix_s1_component_cap
          /ideal_mode2_upper_prefix_s2_component_cap.
  case (processed < KeygenM23SingularFFTSpec.mode2_s1_count_i); trivial.
have hstep :=
  ideal_mode2_component_step_le_budget
    (mode2_ideal_fft_at sample.`1 sample.`2 processed k)
    (ideal_mode2_upper_prefix_slot_component_cap processed)
    hcapnonneg hre him.
rewrite ideal_mode2_combined_energy_prefixS 1:hprocessed
        ideal_mode2_upper_prefix_budgetS 1:hslot.
smt().
qed.

lemma ideal_mode2_upper_prefix_coordinate_headroom_of_component_good
    sample slot k :
  ! ideal_mode2_upper_prefix_component_bad sample =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  mode2_accumulator_coordinate_headroom
    sample.`1 sample.`2 slot k.
proof.
move=> hgood hslot hk.
have [hre him] :=
  ideal_mode2_upper_prefix_component_good_at
    sample slot k hgood hslot hk.
rewrite /mode2_accumulator_coordinate_headroom.
have hcaple :
    ideal_mode2_upper_prefix_slot_component_cap slot +
      mode2_fft_endpoint_eps <= accumulator_q16_coordinate_cap.
+ rewrite /ideal_mode2_upper_prefix_slot_component_cap
          /ideal_mode2_upper_prefix_s1_component_cap
          /ideal_mode2_upper_prefix_s2_component_cap
          /mode2_fft_endpoint_eps
          /accumulator_q16_coordinate_cap.
  case (slot < KeygenM23SingularFFTSpec.mode2_s1_count_i); smt().
smt().
qed.

lemma ideal_mode2_upper_prefix_headroom_of_component_good
    sample processed k :
  0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  ! ideal_mode2_upper_prefix_component_bad sample =>
  mode2_accumulator_prefix_upper_headroom
    sample.`1 sample.`2 processed k.
proof.
move=> hprocessed hk hgood.
rewrite /mode2_accumulator_prefix_upper_headroom.
have hprefix :=
  ideal_mode2_combined_energy_prefix_le_budget
    sample processed k _ _ hk hgood.
+ smt().
+ smt().
have hbudget := ideal_mode2_upper_prefix_budget_le_full processed hprocessed.
have hfull := ideal_mode2_upper_prefix_full_budget_lt_signed_limit.
rewrite /ideal_mode2_combined_energy_prefix in hprefix.
smt().
qed.

lemma ideal_mode2_upper_headroom_trace_of_component_good sample :
  ! ideal_mode2_upper_prefix_component_bad sample =>
  mode2_accumulator_upper_headroom_trace
    sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i.
proof.
move=> hgood.
rewrite /mode2_accumulator_upper_headroom_trace.
split.
+ rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i.
  smt().
move=> slot k hslot hk.
rewrite /mode2_accumulator_upper_headroom_step.
split.
+ exact
    (ideal_mode2_upper_prefix_coordinate_headroom_of_component_good
      sample slot k hgood hslot hk).
apply
  (ideal_mode2_upper_prefix_headroom_of_component_good
    sample (slot + 1) k).
+ smt().
+ exact hk.
exact hgood.
qed.

lemma ideal_mode2_component_good_implies_no_upper_headroom_bad
    (sample : mode2_accumulator_sample) :
  ! ideal_mode2_upper_prefix_component_bad sample =>
  ! mode2_accumulator_upper_headroom_bad_event
      sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i.
proof.
move=> hcomponent.
have htrace := ideal_mode2_upper_headroom_trace_of_component_good
  sample hcomponent.
have hiff := mode2_accumulator_upper_headroom_trace_iff_no_bad_event
  sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i _.
+ rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i.
  smt().
exact (iffLR _ _ hiff htrace).
qed.

lemma ideal_mode2_upper_headroom_bad_implies_component_bad
    (sample : mode2_accumulator_sample) :
  mode2_accumulator_upper_headroom_bad_event
    sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  ideal_mode2_upper_prefix_component_bad sample.
proof.
move=> hbad.
have hnotbad := ideal_mode2_component_good_implies_no_upper_headroom_bad
  sample.
smt().
qed.

op ideal_mode2_upper_prefix_s1_real_markov8_rhs (k : int) : real =
  interval_abs_upper (homogeneous_class4_re_profile8_interval k) /
  (256%r * ideal_mode2_upper_prefix_s1_component_cap ^ 8).

op ideal_mode2_upper_prefix_s1_imag_markov8_rhs (k : int) : real =
  interval_abs_upper (homogeneous_class4_im_profile8_interval k) /
  (256%r * ideal_mode2_upper_prefix_s1_component_cap ^ 8).

op ideal_mode2_upper_prefix_s1_markov8_rhs (k : int) : real =
  ideal_mode2_upper_prefix_s1_real_markov8_rhs k +
  ideal_mode2_upper_prefix_s1_imag_markov8_rhs k.

op ideal_mode2_upper_prefix_s2_real_residual_headroom
    (row k : int) : real =
  ideal_mode2_upper_prefix_s2_component_cap -
  interval_abs_upper (zero_seed_accepted_bias_re_interval row k).

op ideal_mode2_upper_prefix_s2_imag_residual_headroom
    (row k : int) : real =
  ideal_mode2_upper_prefix_s2_component_cap -
  interval_abs_upper (zero_seed_accepted_bias_im_interval row k).

op ideal_mode2_upper_prefix_s2_real_markov8_rhs
    (row k : int) : real =
  interval_abs_upper (zero_seed_accepted_re_profile8_interval row k) /
  (ideal_mode2_upper_prefix_s2_real_residual_headroom row k ^ 8).

op ideal_mode2_upper_prefix_s2_imag_markov8_rhs
    (row k : int) : real =
  interval_abs_upper (zero_seed_accepted_im_profile8_interval row k) /
  (ideal_mode2_upper_prefix_s2_imag_residual_headroom row k ^ 8).

op ideal_mode2_upper_prefix_s2_markov8_rhs (row k : int) : real =
  ideal_mode2_upper_prefix_s2_real_markov8_rhs row k +
  ideal_mode2_upper_prefix_s2_imag_markov8_rhs row k.

op ideal_mode2_upper_prefix_component_markov8_rhs
    (slot k : int) : real =
  if slot < KeygenM23SingularFFTSpec.mode2_s1_count_i then
    ideal_mode2_upper_prefix_s1_markov8_rhs k
  else
    ideal_mode2_upper_prefix_s2_markov8_rhs
      (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) k.

op ideal_mode2_upper_prefix_component_markov8_row_sum
    (slot : int) : real =
  BRA.bigi predT
    (fun k => ideal_mode2_upper_prefix_component_markov8_rhs slot k)
    0 KeygenM23SingularSpec.singular_words_i.

op ideal_mode2_upper_prefix_component_markov8_sum : real =
  BRA.bigi predT
    ideal_mode2_upper_prefix_component_markov8_row_sum
    0 KeygenM23SingularFFTSpec.mode2_slice_count_i.

op ideal_mode2_upper_prefix_p8_numeric_certificate : bool =
  ideal_mode2_upper_prefix_full_budget < accumulator_q16_signed_limit /\
  (forall row k,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    0 <= k < KeygenM23SingularSpec.singular_words_i =>
    0%r < ideal_mode2_upper_prefix_s2_real_residual_headroom row k /\
    0%r < ideal_mode2_upper_prefix_s2_imag_residual_headroom row k) /\
  ideal_mode2_upper_prefix_component_markov8_sum <
    ideal_mode2_reduced_headroom_p8_target.

lemma ideal_mode2_same_denominator_abs_upper
    (a c denominator : real) :
  0%r < denominator =>
  `|a| <= c =>
  a / denominator <= c / denominator.
proof.
move=> hden habs.
have ha : a <= c by
  exact (ler_trans _ _ _ (ler_norm a) habs).
rewrite ler_pdivr_mulr 1:hden.
have -> : c / denominator * denominator = c by field; smt().
exact ha.
qed.

lemma ideal_mode2_upper_prefix_s1_real_tail_mu_le_p8 k :
  0 <= k =>
  mu (ideal_mode2_s1_row_fft_distribution k)
    (fun z => ideal_mode2_upper_prefix_s1_component_cap <= `|creal z|) <=
  ideal_mode2_upper_prefix_s1_real_markov8_rhs k.
proof.
move=> hk.
have hcap : 0%r < ideal_mode2_upper_prefix_s1_component_cap by
  rewrite /ideal_mode2_upper_prefix_s1_component_cap; trivial.
have htail :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .finite_eighth_moment_markov
      (ideal_mode2_s1_row_fft_distribution k)
      creal ideal_mode2_upper_prefix_s1_component_cap
      (ideal_mode2_s1_row_fft_distribution_finite k) hcap.
rewrite ideal_mode2_s1_row_fft_real_moment8E in htail.
apply
  (ler_trans
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
     256%r /
     (ideal_mode2_upper_prefix_s1_component_cap ^ 8))).
+ exact htail.
have [hprofile _] := ideal_mode2_s1_class4_profile8_abs_upper k hk.
have hden :
    0%r < 256%r * ideal_mode2_upper_prefix_s1_component_cap ^ 8.
+ have hpow := expr_gt0 8 _ hcap.
  smt().
have hform :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
      256%r /
      (ideal_mode2_upper_prefix_s1_component_cap ^ 8) =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
      (256%r * ideal_mode2_upper_prefix_s1_component_cap ^ 8) by
  field; smt().
rewrite hform /ideal_mode2_upper_prefix_s1_real_markov8_rhs.
exact
  (ideal_mode2_same_denominator_abs_upper
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256)
    (interval_abs_upper (homogeneous_class4_re_profile8_interval k))
    (256%r * ideal_mode2_upper_prefix_s1_component_cap ^ 8)
    hden hprofile).
qed.

lemma ideal_mode2_upper_prefix_s1_imag_tail_mu_le_p8 k :
  0 <= k =>
  mu (ideal_mode2_s1_row_fft_distribution k)
    (fun z => ideal_mode2_upper_prefix_s1_component_cap <= `|cimag z|) <=
  ideal_mode2_upper_prefix_s1_imag_markov8_rhs k.
proof.
move=> hk.
have hcap : 0%r < ideal_mode2_upper_prefix_s1_component_cap by
  rewrite /ideal_mode2_upper_prefix_s1_component_cap; trivial.
have htail :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .finite_eighth_moment_markov
      (ideal_mode2_s1_row_fft_distribution k)
      cimag ideal_mode2_upper_prefix_s1_component_cap
      (ideal_mode2_s1_row_fft_distribution_finite k) hcap.
rewrite ideal_mode2_s1_row_fft_imag_moment8E in htail.
apply
  (ler_trans
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
     256%r /
     (ideal_mode2_upper_prefix_s1_component_cap ^ 8))).
+ exact htail.
have [_ hprofile] := ideal_mode2_s1_class4_profile8_abs_upper k hk.
have hden :
    0%r < 256%r * ideal_mode2_upper_prefix_s1_component_cap ^ 8.
+ have hpow := expr_gt0 8 _ hcap.
  smt().
have hform :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
      256%r /
      (ideal_mode2_upper_prefix_s1_component_cap ^ 8) =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8
          ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256 /
      (256%r * ideal_mode2_upper_prefix_s1_component_cap ^ 8) by
  field; smt().
rewrite hform /ideal_mode2_upper_prefix_s1_imag_markov8_rhs.
exact
  (ideal_mode2_same_denominator_abs_upper
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8
        ideal_mode2_s1_class4_pre_bp ideal_mode2_s1_class4_avec 0 k 256)
    (interval_abs_upper (homogeneous_class4_im_profile8_interval k))
    (256%r * ideal_mode2_upper_prefix_s1_component_cap ^ 8)
    hden hprofile).
qed.

lemma ideal_mode2_accumulator_s1_cap_real_bad_mu_le_p8
    pre_bp avec slot k :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      ideal_mode2_upper_prefix_s1_component_cap <
      `|creal (mode2_ideal_fft_at sample.`1 sample.`2 slot k)|) <=
  ideal_mode2_upper_prefix_s1_real_markov8_rhs k.
proof.
move=> hslot hk.
rewrite
  (ideal_mode2_accumulator_s1_slot_fft_muE
    pre_bp avec slot k
    (fun z => ideal_mode2_upper_prefix_s1_component_cap < `|creal z|)
    hslot).
apply
  (ler_trans
    (mu (ideal_mode2_s1_row_fft_distribution k)
      (fun z => ideal_mode2_upper_prefix_s1_component_cap <= `|creal z|))).
+ apply mu_le => z hz hbad.
  smt().
apply (ideal_mode2_upper_prefix_s1_real_tail_mu_le_p8 k).
smt().
qed.

lemma ideal_mode2_accumulator_s1_cap_imag_bad_mu_le_p8
    pre_bp avec slot k :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      ideal_mode2_upper_prefix_s1_component_cap <
      `|cimag (mode2_ideal_fft_at sample.`1 sample.`2 slot k)|) <=
  ideal_mode2_upper_prefix_s1_imag_markov8_rhs k.
proof.
move=> hslot hk.
rewrite
  (ideal_mode2_accumulator_s1_slot_fft_muE
    pre_bp avec slot k
    (fun z => ideal_mode2_upper_prefix_s1_component_cap < `|cimag z|)
    hslot).
apply
  (ler_trans
    (mu (ideal_mode2_s1_row_fft_distribution k)
      (fun z => ideal_mode2_upper_prefix_s1_component_cap <= `|cimag z|))).
+ apply mu_le => z hz hbad.
  smt().
apply (ideal_mode2_upper_prefix_s1_imag_tail_mu_le_p8 k).
smt().
qed.

lemma ideal_mode2_upper_prefix_s2_headrooms_positive row k :
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  0%r < ideal_mode2_upper_prefix_s2_real_residual_headroom row k /\
  0%r < ideal_mode2_upper_prefix_s2_imag_residual_headroom row k.
proof.
rewrite /ideal_mode2_upper_prefix_p8_numeric_certificate.
move=> [_ [hheads _]] hrow hk.
exact (hheads row k hrow hk).
qed.

lemma ideal_mode2_accumulator_s2_cap_real_bad_mu_le_p8
    pre_bp avec row k :
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      ideal_mode2_upper_prefix_s2_component_cap <
      `|creal
          (mode2_ideal_fft_at sample.`1 sample.`2
            (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k)|) <=
  ideal_mode2_upper_prefix_s2_real_markov8_rhs row k.
proof.
move=> hnumeric hctx hrow hk htrace.
rewrite
  (ideal_mode2_accumulator_s2_slot_fft_muE
    pre_bp avec row k
    (fun z => ideal_mode2_upper_prefix_s2_component_cap < `|creal z|)
    hctx hrow).
rewrite
  (ideal_final_s2_output_residual_muE
    pre_bp avec row k
    (fun z => ideal_mode2_upper_prefix_s2_component_cap < `|creal z|)
    hrow).
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)
      (fun z =>
        ideal_mode2_upper_prefix_s2_real_residual_headroom row k <=
          `|creal z|))).
+ apply mu_le => z hz hbad.
  have [hbias _] := zero_seed_accepted_bias_component_abs_upper
    pre_bp avec row k _ htrace.
  + smt().
  have htri := ler_norm_add
    (creal
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k))
    (creal z).
  rewrite /ideal_mode2_upper_prefix_s2_real_residual_headroom.
  smt().
have [hhead _] :=
  ideal_mode2_upper_prefix_s2_headrooms_positive row k hnumeric hrow hk.
have hfin :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_fft_finite
      pre_bp avec row k hrow.
have htail :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .finite_eighth_moment_markov
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)
      creal
      (ideal_mode2_upper_prefix_s2_real_residual_headroom row k)
      hfin hhead.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_full_row_residual_fft_real_moment8E
      pre_bp avec row k hrow) in htail.
apply
  (ler_trans
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
     (ideal_mode2_upper_prefix_s2_real_residual_headroom row k ^ 8))).
+ exact htail.
have [hprofile _] :=
  ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
    pre_bp avec row k 256 _.
+ smt().
rewrite htrace in hprofile.
rewrite -zero_seed_accepted_re_profile8_intervalE in hprofile.
have hden :
    0%r < ideal_mode2_upper_prefix_s2_real_residual_headroom row k ^ 8 by
  exact (expr_gt0 8 _ hhead).
rewrite /ideal_mode2_upper_prefix_s2_real_markov8_rhs.
exact
  (ideal_mode2_same_denominator_abs_upper
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256)
    (interval_abs_upper (zero_seed_accepted_re_profile8_interval row k))
    (ideal_mode2_upper_prefix_s2_real_residual_headroom row k ^ 8)
    hden hprofile).
qed.

lemma ideal_mode2_accumulator_s2_cap_imag_bad_mu_le_p8
    pre_bp avec row k :
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      ideal_mode2_upper_prefix_s2_component_cap <
      `|cimag
          (mode2_ideal_fft_at sample.`1 sample.`2
            (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k)|) <=
  ideal_mode2_upper_prefix_s2_imag_markov8_rhs row k.
proof.
move=> hnumeric hctx hrow hk htrace.
rewrite
  (ideal_mode2_accumulator_s2_slot_fft_muE
    pre_bp avec row k
    (fun z => ideal_mode2_upper_prefix_s2_component_cap < `|cimag z|)
    hctx hrow).
rewrite
  (ideal_final_s2_output_residual_muE
    pre_bp avec row k
    (fun z => ideal_mode2_upper_prefix_s2_component_cap < `|cimag z|)
    hrow).
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)
      (fun z =>
        ideal_mode2_upper_prefix_s2_imag_residual_headroom row k <=
          `|cimag z|))).
+ apply mu_le => z hz hbad.
  have [_ hbias] := zero_seed_accepted_bias_component_abs_upper
    pre_bp avec row k _ htrace.
  + smt().
  have htri := ler_norm_add
    (cimag
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k))
    (cimag z).
  rewrite /ideal_mode2_upper_prefix_s2_imag_residual_headroom.
  smt().
have [_ hhead] :=
  ideal_mode2_upper_prefix_s2_headrooms_positive row k hnumeric hrow hk.
have hfin :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_fft_finite
      pre_bp avec row k hrow.
have htail :=
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentTailPostFreeze
    .finite_eighth_moment_markov
      (Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze
        .ideal_final_s2_full_row_residual_odd_dft256_distribution
          pre_bp avec row k)
      cimag
      (ideal_mode2_upper_prefix_s2_imag_residual_headroom row k)
      hfin hhead.
rewrite
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_full_row_residual_fft_imag_moment8E
      pre_bp avec row k hrow) in htail.
apply
  (ler_trans
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
     (ideal_mode2_upper_prefix_s2_imag_residual_headroom row k ^ 8))).
+ exact htail.
have [_ hprofile] :=
  ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
    pre_bp avec row k 256 _.
+ smt().
rewrite htrace in hprofile.
rewrite -zero_seed_accepted_im_profile8_intervalE in hprofile.
have hden :
    0%r < ideal_mode2_upper_prefix_s2_imag_residual_headroom row k ^ 8 by
  exact (expr_gt0 8 _ hhead).
rewrite /ideal_mode2_upper_prefix_s2_imag_markov8_rhs.
exact
  (ideal_mode2_same_denominator_abs_upper
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256)
    (interval_abs_upper (zero_seed_accepted_im_profile8_interval row k))
    (ideal_mode2_upper_prefix_s2_imag_residual_headroom row k ^ 8)
    hden hprofile).
qed.

lemma ideal_mode2_upper_prefix_component_bad_at_mu_le_p8
    pre_bp avec slot k :
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= k < KeygenM23SingularSpec.singular_words_i =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      ideal_mode2_upper_prefix_component_bad_at sample slot k) <=
  ideal_mode2_upper_prefix_component_markov8_rhs slot k.
proof.
move=> hnumeric hctx htrace hslot hk.
rewrite /ideal_mode2_upper_prefix_component_bad_at
        /ideal_mode2_upper_prefix_component_real_bad_at
        /ideal_mode2_upper_prefix_component_imag_bad_at
        /ideal_mode2_upper_prefix_component_markov8_rhs
        /ideal_mode2_upper_prefix_slot_component_cap.
case (slot < KeygenM23SingularFFTSpec.mode2_s1_count_i) => hs1.
+ rewrite /ideal_mode2_upper_prefix_s1_markov8_rhs.
  have hslot_s1 :
      0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i by smt().
  apply
    (ler_trans
      (mu
        (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
          .ideal_mode2_accumulator_distribution pre_bp avec)
        (fun (sample : mode2_accumulator_sample) =>
          ideal_mode2_upper_prefix_s1_component_cap <
            `|creal (mode2_ideal_fft_at sample.`1 sample.`2 slot k)|) +
       mu
        (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
          .ideal_mode2_accumulator_distribution pre_bp avec)
        (fun (sample : mode2_accumulator_sample) =>
          ideal_mode2_upper_prefix_s1_component_cap <
            `|cimag (mode2_ideal_fft_at sample.`1 sample.`2 slot k)|))).
  + exact
      (mu_or_le
        (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
          .ideal_mode2_accumulator_distribution pre_bp avec) _ _).
  apply ler_add.
  + exact (ideal_mode2_accumulator_s1_cap_real_bad_mu_le_p8
      pre_bp avec slot k hslot_s1 hk).
  exact (ideal_mode2_accumulator_s1_cap_imag_bad_mu_le_p8
    pre_bp avec slot k hslot_s1 hk).
rewrite /ideal_mode2_upper_prefix_s2_markov8_rhs.
have hrow :
    0 <= slot - KeygenM23SingularFFTSpec.mode2_s1_count_i <
      KeygenM23SingularFFTSpec.mode2_s2_count_i.
+ move: hslot hs1.
  rewrite /KeygenM23SingularFFTSpec.mode2_s1_count_i
          /KeygenM23SingularFFTSpec.mode2_s2_count_i
          /KeygenM23SingularFFTSpec.mode2_slice_count_i.
  smt().
have hslotE :
    KeygenM23SingularFFTSpec.mode2_s1_count_i +
      (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) = slot by ring.
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec)
      (fun (sample : mode2_accumulator_sample) =>
        ideal_mode2_upper_prefix_s2_component_cap <
          `|creal (mode2_ideal_fft_at sample.`1 sample.`2 slot k)|) +
     mu
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec)
      (fun (sample : mode2_accumulator_sample) =>
        ideal_mode2_upper_prefix_s2_component_cap <
          `|cimag (mode2_ideal_fft_at sample.`1 sample.`2 slot k)|))).
+ exact
    (mu_or_le
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec) _ _).
apply ler_add.
+ rewrite -hslotE.
  exact
    (ideal_mode2_accumulator_s2_cap_real_bad_mu_le_p8
      pre_bp avec
      (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) k
      hnumeric hctx hrow hk (htrace _ hrow)).
rewrite -hslotE.
exact
  (ideal_mode2_accumulator_s2_cap_imag_bad_mu_le_p8
    pre_bp avec
    (slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) k
    hnumeric hctx hrow hk (htrace _ hrow)).
qed.

lemma ideal_mode2_upper_prefix_component_bad_mu_le_p8_sum
    pre_bp avec :
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    ideal_mode2_upper_prefix_component_bad <=
  ideal_mode2_upper_prefix_component_markov8_sum.
proof.
move=> hnumeric hctx htrace.
rewrite /ideal_mode2_upper_prefix_component_bad
        /ideal_mode2_upper_prefix_component_markov8_sum
        /ideal_mode2_upper_prefix_component_markov8_row_sum
        /ideal_mode2_accumulator_rowk_range_sum.
apply
  (ideal_mode2_accumulator_rowk_range_bad_mu_le
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun slot k sample =>
      ideal_mode2_upper_prefix_component_bad_at sample slot k)
    ideal_mode2_upper_prefix_component_markov8_rhs
    KeygenM23SingularFFTSpec.mode2_slice_count_i
    KeygenM23SingularSpec.singular_words_i).
+ rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i; trivial.
+ rewrite /KeygenM23SingularSpec.singular_words_i; trivial.
move=> slot k hslot hk.
exact
  (ideal_mode2_upper_prefix_component_bad_at_mu_le_p8
    pre_bp avec slot k hnumeric hctx htrace hslot hk).
qed.

lemma ideal_mode2_upper_prefix_bad_mu_le_component_cap_sum
    pre_bp avec :
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      mode2_accumulator_upper_headroom_bad_event
        sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i) <=
  ideal_mode2_upper_prefix_component_markov8_sum.
proof.
move=> hnumeric hctx htrace.
apply
  (ler_trans
    (mu
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec)
      ideal_mode2_upper_prefix_component_bad)).
+ apply mu_le => sample hsample hbad.
  exact (ideal_mode2_upper_headroom_bad_implies_component_bad sample hbad).
exact
  (ideal_mode2_upper_prefix_component_bad_mu_le_p8_sum
    pre_bp avec hnumeric hctx htrace).
qed.

lemma ideal_mode2_reduced_headroom_bad_mu_lt_one_half
    pre_bp avec :
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      mode2_accumulator_upper_headroom_bad_event
        sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i) <
  1%r / 2%r.
proof.
move=> hnumeric hctx htrace.
have hbound := ideal_mode2_upper_prefix_bad_mu_le_component_cap_sum
  pre_bp avec hnumeric hctx htrace.
have hsum :
    ideal_mode2_upper_prefix_component_markov8_sum <
      ideal_mode2_reduced_headroom_p8_target.
+ move: hnumeric.
  rewrite /ideal_mode2_upper_prefix_p8_numeric_certificate.
  smt().
rewrite /ideal_mode2_reduced_headroom_p8_target in hsum.
exact (ler_lt_trans _ _ _ hbound hsum).
qed.

lemma ideal_mode2_accumulator_unsafe_mu_lt_one_half
    pre_bp avec :
  ideal_mode2_upper_prefix_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  (forall sample,
    sample \in
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec) =>
    mode2_accumulator_inputs_bound2 sample.`1 sample.`2) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun (sample : mode2_accumulator_sample) =>
      ! actual_mode2_accumulate_safe_trace
          sample.`1 sample.`2
          KeygenM23SingularFFTSpec.mode2_slice_count_i) <
  1%r / 2%r.
proof.
move=> hnumeric hctx htrace hinputs.
apply
  (ler_lt_trans
    (mu
      (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
        .ideal_mode2_accumulator_distribution pre_bp avec)
      (fun (sample : mode2_accumulator_sample) =>
        mode2_accumulator_upper_headroom_bad_event
          sample.`1 sample.`2
          KeygenM23SingularFFTSpec.mode2_slice_count_i))).
+ apply mu_le => sample hsample hunsafe.
  have hsafe_if_good :
      ! mode2_accumulator_upper_headroom_bad_event
          sample.`1 sample.`2
          KeygenM23SingularFFTSpec.mode2_slice_count_i =>
      actual_mode2_accumulate_safe_trace
        sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i.
  + move=> hgood.
    have hrange :
        0 <= KeygenM23SingularFFTSpec.mode2_slice_count_i <=
          KeygenM23SingularFFTSpec.mode2_slice_count_i by
      rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i; smt().
    have hiff := mode2_accumulator_upper_headroom_trace_iff_no_bad_event
      sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i hrange.
    have hheadroom := iffRL _ _ hiff hgood.
    have hzero : 0 <= KeygenM23SingularFFTSpec.mode2_slice_count_i by
      rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i; smt().
    have hcap :
        KeygenM23SingularFFTSpec.mode2_slice_count_i <=
          KeygenM23SingularFFTSpec.mode2_slice_count_i by trivial.
    exact
      (mode2_actual_accumulate_safe_from_upper_headroom
        sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i
        hzero hcap (hinputs sample hsample) hheadroom).
  case
    (mode2_accumulator_upper_headroom_bad_event
      sample.`1 sample.`2 KeygenM23SingularFFTSpec.mode2_slice_count_i)
    => hbadcase.
  + trivial.
  have hnotbad :
      ! mode2_accumulator_upper_headroom_bad_event
          sample.`1 sample.`2
          KeygenM23SingularFFTSpec.mode2_slice_count_i by
    rewrite hbadcase.
  have hsafe := hsafe_if_good hnotbad.
  smt().
exact
  (ideal_mode2_reduced_headroom_bad_mu_lt_one_half
    pre_bp avec hnumeric hctx htrace).
qed.

end Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze.
