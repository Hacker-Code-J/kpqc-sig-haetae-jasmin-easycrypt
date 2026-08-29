require import AllCore DList Distr FSet IntDiv List Mu_mem Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorProbability
  KeygenM23SingularFFTAccumulatorSafety
  KeygenM23SingularFFTSpec
  KeygenM23SingularSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8UnionLimitationPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal.
import KeygenM23IdealRootDFT.
import KeygenM23SingularFFTAccumulatorProbability.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8UnionLimitationPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze.

(* This file replaces the uniform worst-case bias headroom in the deterministic
   raw_seed=0 accepted-context P8 union with certified root- and component-
   specific bias intervals.  It proves a subunit bound only for finalized-s2
   accumulator slots [3,4], under explicit trace and numeric-certificate
   premises.  It does not cover the three s1 slots, prefix-energy events,
   random contexts, retry termination, or an unconditional keygen law. *)

op ideal_final_s2_class_bias_oracle (cls : int) : real =
  if cls = 0 then -1%r / 3%r
  else if cls = 1 then 1%r / 3%r
  else if cls = 2 then 0%r
  else if cls = 3 then -1%r / 3%r
  else if cls = 4 then 0%r
  else if cls = 5 then 1%r / 3%r
  else 0%r.

lemma ideal_final_s2_mean_class_bias_oracleE b a :
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_mean b a =
  ideal_final_s2_class_bias_oracle
    (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .ideal_final_s2_class_index b a).
proof.
have hexh :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_exhaustive b a.
move: hexh => [h0 | [h1 | [h2 | [h3 | [h4 | h5]]]]].
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.mean_rho0 b a h0.
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_rho0 in h0.
  rewrite hm /ideal_final_s2_class_bias_oracle h0.
  trivial.
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.mean_rhoq1 b a h1.
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_rhoq1 in h1.
  rewrite hm /ideal_final_s2_class_bias_oracle h1.
  trivial.
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.mean_mod0 b a h2.
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_mod0 in h2.
  rewrite hm /ideal_final_s2_class_bias_oracle h2.
  trivial.
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.mean_mod1 b a h3.
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_mod1 in h3.
  rewrite hm /ideal_final_s2_class_bias_oracle h3.
  trivial.
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.mean_mod2 b a h4.
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_mod2 in h4.
  rewrite hm /ideal_final_s2_class_bias_oracle h4.
  trivial.
have hm :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.mean_mod3 b a h5.
rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
          .ideal_final_s2_class_mod3 in h5.
rewrite hm /ideal_final_s2_class_bias_oracle h5.
trivial.
qed.

lemma ideal_final_s2_bias_row_class_oracleE pre_bp avec row j :
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_row pre_bp avec row j =
  ideal_final_s2_class_bias_oracle
    (ideal_final_s2_row_class_trace pre_bp avec row j).
proof.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_row
  /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_bias_at
  /ideal_final_s2_row_class_trace
  /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_class_at
  /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_row_index
  /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_index.
exact (ideal_final_s2_mean_class_bias_oracleE _ _).
qed.

lemma ideal_final_s2_bias_slice_class_oracleE pre_bp avec row :
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_slice pre_bp avec row =
  (fun j =>
    cof_real
      (ideal_final_s2_class_bias_oracle
        (ideal_final_s2_row_class_trace pre_bp avec row j))).
proof.
apply fun_ext => j.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_slice
  ideal_final_s2_bias_row_class_oracleE.
trivial.
qed.

op ideal_final_s2_class_bias_re_profile
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      creal (cpow (odd_root k) j) *
      ideal_final_s2_class_bias_oracle (trace j))
    0 n.

op ideal_final_s2_class_bias_im_profile
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      cimag (cpow (odd_root k) j) *
      ideal_final_s2_class_bias_oracle (trace j))
    0 n.

op ideal_final_s2_class_bias_re_term_interval
    (trace : int -> int) (k j : int) : rinterval =
  interval_mul
    (certified_odd_root_re_interval k j)
    (interval_point (ideal_final_s2_class_bias_oracle (trace j))).

op ideal_final_s2_class_bias_im_term_interval
    (trace : int -> int) (k j : int) : rinterval =
  interval_mul
    (certified_odd_root_im_interval k j)
    (interval_point (ideal_final_s2_class_bias_oracle (trace j))).

op ideal_final_s2_class_bias_re_interval
    (trace : int -> int) (k n : int) : rinterval =
  interval_bigi
    (fun j => ideal_final_s2_class_bias_re_term_interval trace k j) n.

op ideal_final_s2_class_bias_im_interval
    (trace : int -> int) (k n : int) : rinterval =
  interval_bigi
    (fun j => ideal_final_s2_class_bias_im_term_interval trace k j) n.

lemma ideal_final_s2_class_bias_re_interval_valid trace k :
  0 <= k =>
  interval_valid (ideal_final_s2_class_bias_re_interval trace k 256).
proof.
move=> hk.
rewrite /ideal_final_s2_class_bias_re_interval.
apply interval_bigi_valid => j hj.
rewrite /ideal_final_s2_class_bias_re_term_interval.
have [[hroot _] _] := certified_odd_root_power_intervals_sound k j hk _.
+ smt().
exact
  (interval_mul_valid
    (certified_odd_root_re_interval k j)
    (interval_point (ideal_final_s2_class_bias_oracle (trace j)))
    hroot (interval_point_valid _)).
qed.

lemma ideal_final_s2_class_bias_im_interval_valid trace k :
  0 <= k =>
  interval_valid (ideal_final_s2_class_bias_im_interval trace k 256).
proof.
move=> hk.
rewrite /ideal_final_s2_class_bias_im_interval.
apply interval_bigi_valid => j hj.
rewrite /ideal_final_s2_class_bias_im_term_interval.
have [_ [hroot _]] := certified_odd_root_power_intervals_sound k j hk _.
+ smt().
exact
  (interval_mul_valid
    (certified_odd_root_im_interval k j)
    (interval_point (ideal_final_s2_class_bias_oracle (trace j)))
    hroot (interval_point_valid _)).
qed.

lemma ideal_final_s2_class_bias_re_interval_holds trace k :
  0 <= k =>
  interval_holds
    (ideal_final_s2_class_bias_re_interval trace k 256)
    (ideal_final_s2_class_bias_re_profile trace k 256).
proof.
move=> hk.
rewrite /ideal_final_s2_class_bias_re_interval
        /ideal_final_s2_class_bias_re_profile.
apply interval_bigi_holds.
+ move=> j hj.
  rewrite /ideal_final_s2_class_bias_re_term_interval.
  have [[hroot _] _] := certified_odd_root_power_intervals_sound k j hk _.
  + smt().
  exact
    (interval_mul_valid
      (certified_odd_root_re_interval k j)
      (interval_point (ideal_final_s2_class_bias_oracle (trace j)))
      hroot (interval_point_valid _)).
move=> j hj.
rewrite /ideal_final_s2_class_bias_re_term_interval.
have [[hrootv hrooth] _] :=
  certified_odd_root_power_intervals_sound k j hk _.
+ smt().
have hmul :=
  interval_mul_holds
    (certified_odd_root_re_interval k j)
    (interval_point (ideal_final_s2_class_bias_oracle (trace j)))
    (creal (cpow (odd_root k) j))
    (ideal_final_s2_class_bias_oracle (trace j))
    hrootv (interval_point_valid _)
    hrooth (interval_point_holds _).
exact hmul.
qed.

lemma ideal_final_s2_class_bias_im_interval_holds trace k :
  0 <= k =>
  interval_holds
    (ideal_final_s2_class_bias_im_interval trace k 256)
    (ideal_final_s2_class_bias_im_profile trace k 256).
proof.
move=> hk.
rewrite /ideal_final_s2_class_bias_im_interval
        /ideal_final_s2_class_bias_im_profile.
apply interval_bigi_holds.
+ move=> j hj.
  rewrite /ideal_final_s2_class_bias_im_term_interval.
  have [_ [hroot _]] := certified_odd_root_power_intervals_sound k j hk _.
  + smt().
  exact
    (interval_mul_valid
      (certified_odd_root_im_interval k j)
      (interval_point (ideal_final_s2_class_bias_oracle (trace j)))
      hroot (interval_point_valid _)).
move=> j hj.
rewrite /ideal_final_s2_class_bias_im_term_interval.
have [_ [hrootv hrooth]] :=
  certified_odd_root_power_intervals_sound k j hk _.
+ smt().
have hmul :=
  interval_mul_holds
    (certified_odd_root_im_interval k j)
    (interval_point (ideal_final_s2_class_bias_oracle (trace j)))
    (cimag (cpow (odd_root k) j))
    (ideal_final_s2_class_bias_oracle (trace j))
    hrootv (interval_point_valid _)
    hrooth (interval_point_holds _).
exact hmul.
qed.

lemma ideal_final_s2_bias_re_class_profileE pre_bp avec row k :
  creal
    (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
      .ideal_final_s2_bias_odd_dft256 pre_bp avec row k) =
  ideal_final_s2_class_bias_re_profile
    (ideal_final_s2_row_class_trace pre_bp avec row) k 256.
proof.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_odd_dft256
  ideal_final_s2_bias_slice_class_oracleE
  /odd_dft256
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze.creal_csum256
  /ideal_final_s2_class_bias_re_profile.
apply BRA.eq_big_seq => j hj.
change
  (ideal_final_s2_class_bias_oracle
      (ideal_final_s2_row_class_trace pre_bp avec row j) *
     creal (cpow (odd_root k) j) =
   creal (cpow (odd_root k) j) *
     ideal_final_s2_class_bias_oracle
       (ideal_final_s2_row_class_trace pre_bp avec row j)).
ring.
qed.

lemma ideal_final_s2_bias_im_class_profileE pre_bp avec row k :
  cimag
    (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
      .ideal_final_s2_bias_odd_dft256 pre_bp avec row k) =
  ideal_final_s2_class_bias_im_profile
    (ideal_final_s2_row_class_trace pre_bp avec row) k 256.
proof.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
    .ideal_final_s2_bias_odd_dft256
  ideal_final_s2_bias_slice_class_oracleE
  /odd_dft256
  Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze.cimag_csum256
  /ideal_final_s2_class_bias_im_profile.
apply BRA.eq_big_seq => j hj.
change
  (ideal_final_s2_class_bias_oracle
      (ideal_final_s2_row_class_trace pre_bp avec row j) *
     cimag (cpow (odd_root k) j) =
   cimag (cpow (odd_root k) j) *
     ideal_final_s2_class_bias_oracle
       (ideal_final_s2_row_class_trace pre_bp avec row j)).
ring.
qed.

op zero_seed_accepted_bias_re_interval (row k : int) : rinterval =
  ideal_final_s2_class_bias_re_interval
    (zero_seed_accepted_trace row) k 256.

op zero_seed_accepted_bias_im_interval (row k : int) : rinterval =
  ideal_final_s2_class_bias_im_interval
    (zero_seed_accepted_trace row) k 256.

lemma zero_seed_accepted_bias_re_interval_holds pre_bp avec row k :
  0 <= k =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  interval_holds
    (zero_seed_accepted_bias_re_interval row k)
    (creal
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)).
proof.
move=> hk htrace.
have h := ideal_final_s2_class_bias_re_interval_holds
  (zero_seed_accepted_trace row) k hk.
have he := ideal_final_s2_bias_re_class_profileE pre_bp avec row k.
rewrite htrace in he.
rewrite /zero_seed_accepted_bias_re_interval he.
exact h.
qed.

lemma zero_seed_accepted_bias_im_interval_holds pre_bp avec row k :
  0 <= k =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  interval_holds
    (zero_seed_accepted_bias_im_interval row k)
    (cimag
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)).
proof.
move=> hk htrace.
have h := ideal_final_s2_class_bias_im_interval_holds
  (zero_seed_accepted_trace row) k hk.
have he := ideal_final_s2_bias_im_class_profileE pre_bp avec row k.
rewrite htrace in he.
rewrite /zero_seed_accepted_bias_im_interval he.
exact h.
qed.

lemma zero_seed_accepted_bias_component_abs_upper pre_bp avec row k :
  0 <= k =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  `|creal
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)| <=
    interval_abs_upper (zero_seed_accepted_bias_re_interval row k) /\
  `|cimag
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k)| <=
    interval_abs_upper (zero_seed_accepted_bias_im_interval row k).
proof.
move=> hk htrace.
split.
+ exact
    (interval_holds_abs_le
      (zero_seed_accepted_bias_re_interval row k)
      (creal
        (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
          .ideal_final_s2_bias_odd_dft256 pre_bp avec row k))
      (zero_seed_accepted_bias_re_interval_holds
        pre_bp avec row k hk htrace)).
exact
  (interval_holds_abs_le
    (zero_seed_accepted_bias_im_interval row k)
    (cimag
      (Mode2FaithfulSecurityIdealFinalS2BiasFFTBoundPostFreeze
        .ideal_final_s2_bias_odd_dft256 pre_bp avec row k))
    (zero_seed_accepted_bias_im_interval_holds
      pre_bp avec row k hk htrace)).
qed.

op zero_seed_accepted_trace_real_headroom (row k : int) : real =
  KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap -
  KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps -
  interval_abs_upper (zero_seed_accepted_bias_re_interval row k).

op zero_seed_accepted_trace_imag_headroom (row k : int) : real =
  KeygenM23SingularFFTAccumulatorSafety.accumulator_q16_coordinate_cap -
  KeygenM23SingularFFTAccumulatorBridge.mode2_fft_endpoint_eps -
  interval_abs_upper (zero_seed_accepted_bias_im_interval row k).

op zero_seed_accepted_trace_min_headroom : real =
  343115213004429423019%r / 3000000000000000000%r.

op zero_seed_accepted_trace_real_markov8_rhs (row k : int) : real =
  interval_abs_upper (zero_seed_accepted_re_profile8_interval row k) /
  (zero_seed_accepted_trace_real_headroom row k ^ 8).

op zero_seed_accepted_trace_imag_markov8_rhs (row k : int) : real =
  interval_abs_upper (zero_seed_accepted_im_profile8_interval row k) /
  (zero_seed_accepted_trace_imag_headroom row k ^ 8).

op zero_seed_accepted_trace_headroom_markov8_rhs (row k : int) : real =
  zero_seed_accepted_trace_real_markov8_rhs row k +
  zero_seed_accepted_trace_imag_markov8_rhs row k.

op zero_seed_accepted_trace_headroom_markov8_row_sum (row : int) : real =
  BRA.bigi predT
    (fun k => zero_seed_accepted_trace_headroom_markov8_rhs row k)
    0 256.

op zero_seed_accepted_trace_headroom_markov8_sum : real =
  BRA.bigi predT
    zero_seed_accepted_trace_headroom_markov8_row_sum
    0 2.

op zero_seed_accepted_trace_headroom_p8_target : real = 1%r / 1024%r.

op zero_seed_accepted_trace_headroom_p8_numeric_certificate : bool =
  zero_seed_accepted_trace_real_headroom 0 158 =
    zero_seed_accepted_trace_min_headroom /\
  (forall row k,
    0 <= row < 2 =>
    0 <= k < 256 =>
    zero_seed_accepted_trace_min_headroom <=
      zero_seed_accepted_trace_real_headroom row k /\
    zero_seed_accepted_trace_min_headroom <=
      zero_seed_accepted_trace_imag_headroom row k) /\
  zero_seed_accepted_trace_headroom_markov8_sum <
    zero_seed_accepted_trace_headroom_p8_target.

lemma zero_seed_accepted_trace_min_headroom_gt0 :
  0%r < zero_seed_accepted_trace_min_headroom.
proof.
rewrite /zero_seed_accepted_trace_min_headroom.
smt().
qed.

lemma zero_seed_accepted_trace_headrooms_positive row k :
  zero_seed_accepted_trace_headroom_p8_numeric_certificate =>
  0 <= row < 2 =>
  0 <= k < 256 =>
  0%r < zero_seed_accepted_trace_real_headroom row k /\
  0%r < zero_seed_accepted_trace_imag_headroom row k.
proof.
rewrite /zero_seed_accepted_trace_headroom_p8_numeric_certificate.
move=> [_ [hheads _]] hrow hk.
have [hre him] := hheads row k hrow hk.
have hmin := zero_seed_accepted_trace_min_headroom_gt0.
smt().
qed.

lemma zero_seed_accepted_trace_headroom_lower_le_actual pre_bp avec row k :
  0 <= k =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  zero_seed_accepted_trace_real_headroom row k <=
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k /\
  zero_seed_accepted_trace_imag_headroom row k <=
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k.
proof.
move=> hk htrace.
have [hre him] :=
  zero_seed_accepted_bias_component_abs_upper
    pre_bp avec row k hk htrace.
rewrite /zero_seed_accepted_trace_real_headroom
        /zero_seed_accepted_trace_imag_headroom
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_full_row_residual_real_headroom
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_full_row_residual_imag_headroom.
smt().
qed.

lemma ideal_mode2_accumulator_s2_slot_real_bad_mu_le_zero_seed_trace_headroom
    pre_bp avec row k :
  zero_seed_accepted_trace_headroom_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < 2 =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_real_bad_at sample
        (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) <=
  zero_seed_accepted_trace_real_markov8_rhs row k.
proof.
move=> hnumeric hctx hrow hk htrace.
have htail :=
  ideal_mode2_accumulator_s2_slot_real_bad_mu_le_markov8
    pre_bp avec row k hctx hrow hk.
apply (ler_trans
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8))).
+ exact htail.
rewrite /zero_seed_accepted_trace_real_markov8_rhs.
have hk0 : 0 <= k by smt().
have [hprofile _] :=
  ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
    pre_bp avec row k 256 hk0.
rewrite htrace in hprofile.
rewrite -zero_seed_accepted_re_profile8_intervalE in hprofile.
have hac :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256 <=
    interval_abs_upper (zero_seed_accepted_re_profile8_interval row k).
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact hprofile.
have hc :
    0%r <= interval_abs_upper
      (zero_seed_accepted_re_profile8_interval row k).
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256|).
  + exact (normr_ge0 _).
  exact hprofile.
have [hhead _] :=
  zero_seed_accepted_trace_headroom_lower_le_actual
    pre_bp avec row k hk0 htrace.
have [hlocalpos _] :=
  zero_seed_accepted_trace_headrooms_positive row k hnumeric hrow hk.
have hmpos :
    0%r < zero_seed_accepted_trace_real_headroom row k ^ 8 by
  exact (expr_gt0 8 _ hlocalpos).
have hrange :
    0%r <= zero_seed_accepted_trace_real_headroom row k <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k by
  smt().
have hpowmono := ler_pexp 8
  (zero_seed_accepted_trace_real_headroom row k)
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k)
  _ hrange.
+ trivial.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_div_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k 256)
      (interval_abs_upper (zero_seed_accepted_re_profile8_interval row k))
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 8)
      (zero_seed_accepted_trace_real_headroom row k ^ 8)
      hmpos hpowmono hc hac).
qed.

lemma ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_zero_seed_trace_headroom
    pre_bp avec row k :
  zero_seed_accepted_trace_headroom_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < 2 =>
  0 <= k < 256 =>
  ideal_final_s2_row_class_trace pre_bp avec row =
    zero_seed_accepted_trace row =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun sample =>
      mode2_accumulator_coordinate_imag_bad_at sample
        (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k) <=
  zero_seed_accepted_trace_imag_markov8_rhs row k.
proof.
move=> hnumeric hctx hrow hk htrace.
have htail :=
  ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_markov8
    pre_bp avec row k hctx hrow hk.
apply (ler_trans
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 /
   (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8))).
+ exact htail.
rewrite /zero_seed_accepted_trace_imag_markov8_rhs.
have hk0 : 0 <= k by smt().
have [_ hprofile] :=
  ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
    pre_bp avec row k 256 hk0.
rewrite htrace in hprofile.
rewrite -zero_seed_accepted_im_profile8_intervalE in hprofile.
have hac :
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256 <=
    interval_abs_upper (zero_seed_accepted_im_profile8_interval row k).
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256|).
  + exact (ler_norm _).
  exact hprofile.
have hc :
    0%r <= interval_abs_upper
      (zero_seed_accepted_im_profile8_interval row k).
+ apply (ler_trans
    `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256|).
  + exact (normr_ge0 _).
  exact hprofile.
have [_ hhead] :=
  zero_seed_accepted_trace_headroom_lower_le_actual
    pre_bp avec row k hk0 htrace.
have [_ hlocalpos] :=
  zero_seed_accepted_trace_headrooms_positive row k hnumeric hrow hk.
have hmpos :
    0%r < zero_seed_accepted_trace_imag_headroom row k ^ 8 by
  exact (expr_gt0 8 _ hlocalpos).
have hrange :
    0%r <= zero_seed_accepted_trace_imag_headroom row k <=
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k by
  smt().
have hpowmono := ler_pexp 8
  (zero_seed_accepted_trace_imag_headroom row k)
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k)
  _ hrange.
+ trivial.
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentUniformLimitationPostFreeze
    .ideal_final_s2_uniform_div_bound
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k 256)
      (interval_abs_upper (zero_seed_accepted_im_profile8_interval row k))
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 8)
      (zero_seed_accepted_trace_imag_headroom row k ^ 8)
      hmpos hpowmono hc hac).
qed.

lemma ideal_mode2_accumulator_s2_slot_headroom_bad_mu_le_zero_seed_trace_sum
    pre_bp avec :
  zero_seed_accepted_trace_headroom_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < 2 =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    ideal_mode2_accumulator_s2_slot_headroom_bad <=
  zero_seed_accepted_trace_headroom_markov8_sum.
proof.
move=> hnumeric hctx htrace.
have -> :
    ideal_mode2_accumulator_s2_slot_headroom_bad =
    (fun sample =>
      exists row,
        0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i /\
        exists k,
          0 <= k < KeygenM23SingularSpec.singular_words_i /\
          ideal_mode2_accumulator_s2_slot_headroom_bad_at sample row k).
+ apply fun_ext => sample.
  exact (ideal_mode2_accumulator_s2_slot_headroom_badE sample).
rewrite /zero_seed_accepted_trace_headroom_markov8_sum.
apply
  (ideal_mode2_accumulator_rowk_range_bad_mu_le
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun row k sample =>
      ideal_mode2_accumulator_s2_slot_headroom_bad_at sample row k)
    zero_seed_accepted_trace_headroom_markov8_rhs
    KeygenM23SingularFFTSpec.mode2_s2_count_i
    KeygenM23SingularSpec.singular_words_i).
+ rewrite /KeygenM23SingularFFTSpec.mode2_s2_count_i.
  trivial.
+ rewrite /KeygenM23SingularSpec.singular_words_i.
  trivial.
move=> row k hrow hk.
rewrite /ideal_mode2_accumulator_s2_slot_headroom_bad_at
        /zero_seed_accepted_trace_headroom_markov8_rhs.
apply
  (mode2_accumulator_coordinate_headroom_bad_at_mu_le_split
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k
    (zero_seed_accepted_trace_real_markov8_rhs row k)
    (zero_seed_accepted_trace_imag_markov8_rhs row k)).
+ exact
    (ideal_mode2_accumulator_s2_slot_real_bad_mu_le_zero_seed_trace_headroom
      pre_bp avec row k hnumeric hctx hrow hk (htrace row hrow)).
exact
  (ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_zero_seed_trace_headroom
    pre_bp avec row k hnumeric hctx hrow hk (htrace row hrow)).
qed.

lemma zero_seed_accepted_trace_headroom_markov8_sum_lt_target :
  zero_seed_accepted_trace_headroom_p8_numeric_certificate =>
  zero_seed_accepted_trace_headroom_markov8_sum <
    zero_seed_accepted_trace_headroom_p8_target.
proof.
rewrite /zero_seed_accepted_trace_headroom_p8_numeric_certificate.
move=> [_ [_ hsum]].
exact hsum.
qed.

lemma ideal_mode2_accumulator_s2_slot_headroom_bad_mu_lt_one_over_1024
    pre_bp avec :
  zero_seed_accepted_trace_headroom_p8_numeric_certificate =>
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  (forall row,
    0 <= row < 2 =>
    ideal_final_s2_row_class_trace pre_bp avec row =
      zero_seed_accepted_trace row) =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    ideal_mode2_accumulator_s2_slot_headroom_bad <
  1%r / 1024%r.
proof.
move=> hnumeric hctx htrace.
have hbound :=
  ideal_mode2_accumulator_s2_slot_headroom_bad_mu_le_zero_seed_trace_sum
    pre_bp avec hnumeric hctx htrace.
have hsum :=
  zero_seed_accepted_trace_headroom_markov8_sum_lt_target hnumeric.
rewrite /zero_seed_accepted_trace_headroom_p8_target in hsum.
exact (ler_lt_trans _ _ _ hbound hsum).
qed.

end Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze.
