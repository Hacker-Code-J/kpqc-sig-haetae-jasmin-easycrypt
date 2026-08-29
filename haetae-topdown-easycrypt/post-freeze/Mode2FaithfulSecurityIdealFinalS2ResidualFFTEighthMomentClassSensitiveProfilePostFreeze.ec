require import AllCore DList Distr Finite IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.

(* This file exposes the exact fixed-context finalized-[s2] centered moment
   table as a class-coded oracle, then reindexes the residual coordinate
   moments through the row-local class trace and rewrites every exact FFT
   moment profile into a class-trace normal form. It keeps odd moments signed
   and does not claim a context distribution, tail bound, or security level. *)

op ideal_final_s2_class_moment2_oracle (cls : int) : real =
  if cls = 0 then 2%r / 9%r
  else if cls = 1 then 2%r / 9%r
  else if cls = 2 then 0%r
  else if cls = 3 then 8%r / 9%r
  else if cls = 4 then 8%r / 3%r
  else if cls = 5 then 8%r / 9%r
  else 0%r.

op ideal_final_s2_class_moment3_oracle (cls : int) : real =
  if cls = 0 then -2%r / 27%r
  else if cls = 1 then 2%r / 27%r
  else if cls = 2 then 0%r
  else if cls = 3 then 16%r / 27%r
  else if cls = 4 then 0%r
  else if cls = 5 then -16%r / 27%r
  else 0%r.

op ideal_final_s2_class_moment4_oracle (cls : int) : real =
  if cls = 0 then 2%r / 27%r
  else if cls = 1 then 2%r / 27%r
  else if cls = 2 then 0%r
  else if cls = 3 then 32%r / 27%r
  else if cls = 4 then 32%r / 3%r
  else if cls = 5 then 32%r / 27%r
  else 0%r.

op ideal_final_s2_class_moment5_oracle (cls : int) : real =
  if cls = 0 then -10%r / 243%r
  else if cls = 1 then 10%r / 243%r
  else if cls = 2 then 0%r
  else if cls = 3 then 320%r / 243%r
  else if cls = 4 then 0%r
  else if cls = 5 then -320%r / 243%r
  else 0%r.

op ideal_final_s2_class_moment6_oracle (cls : int) : real =
  if cls = 0 then 22%r / 729%r
  else if cls = 1 then 22%r / 729%r
  else if cls = 2 then 0%r
  else if cls = 3 then 1408%r / 729%r
  else if cls = 4 then 128%r / 3%r
  else if cls = 5 then 1408%r / 729%r
  else 0%r.

op ideal_final_s2_class_moment8_oracle (cls : int) : real =
  if cls = 0 then 86%r / 6561%r
  else if cls = 1 then 86%r / 6561%r
  else if cls = 2 then 0%r
  else if cls = 3 then 22016%r / 6561%r
  else if cls = 4 then 512%r / 3%r
  else if cls = 5 then 22016%r / 6561%r
  else 0%r.

lemma ideal_final_s2_centered_moment_class_oracleE b a :
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_centered_moment2 b a =
    ideal_final_s2_class_moment2_oracle
      (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
        .ideal_final_s2_class_index b a) /\
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_centered_moment3 b a =
    ideal_final_s2_class_moment3_oracle
      (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
        .ideal_final_s2_class_index b a) /\
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_centered_moment4 b a =
    ideal_final_s2_class_moment4_oracle
      (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
        .ideal_final_s2_class_index b a) /\
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_centered_moment5 b a =
    ideal_final_s2_class_moment5_oracle
      (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
        .ideal_final_s2_class_index b a) /\
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_centered_moment6 b a =
    ideal_final_s2_class_moment6_oracle
      (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
        .ideal_final_s2_class_index b a) /\
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_centered_moment8 b a =
    ideal_final_s2_class_moment8_oracle
      (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
        .ideal_final_s2_class_index b a).
proof.
have hexh :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_exhaustive b a.
move: hexh => [h0 | [h1 | [h2 | [h3 | [h4 | h5]]]]].
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_rho0 b a h0.
  have hm56 :=
    Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .moments56_rho0 b a h0.
  move: hm hm56 => [_ [_ [_ [h2 [h3 [h4 h8]]]]]] [h5m h6].
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_rho0 in h0.
  rewrite h2 h3 h4 h5m h6 h8 /ideal_final_s2_class_moment2_oracle
          /ideal_final_s2_class_moment3_oracle
          /ideal_final_s2_class_moment4_oracle
          /ideal_final_s2_class_moment5_oracle
          /ideal_final_s2_class_moment6_oracle
          /ideal_final_s2_class_moment8_oracle h0.
  smt().
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_rhoq1 b a h1.
  have hm56 :=
    Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .moments56_rhoq1 b a h1.
  move: hm hm56 => [_ [_ [_ [h2 [h3 [h4 h8]]]]]] [h5m h6].
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_rhoq1 in h1.
  rewrite h2 h3 h4 h5m h6 h8 /ideal_final_s2_class_moment2_oracle
          /ideal_final_s2_class_moment3_oracle
          /ideal_final_s2_class_moment4_oracle
          /ideal_final_s2_class_moment5_oracle
          /ideal_final_s2_class_moment6_oracle
          /ideal_final_s2_class_moment8_oracle h1.
  smt().
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_mod0 b a h2.
  have hm56 :=
    Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .moments56_mod0 b a h2.
  move: hm hm56 => [_ [_ [_ [h2m [h3 [h4 h8]]]]]] [h5m h6].
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_mod0 in h2.
  rewrite h2m h3 h4 h5m h6 h8 /ideal_final_s2_class_moment2_oracle
          /ideal_final_s2_class_moment3_oracle
          /ideal_final_s2_class_moment4_oracle
          /ideal_final_s2_class_moment5_oracle
          /ideal_final_s2_class_moment6_oracle
          /ideal_final_s2_class_moment8_oracle h2.
  smt().
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_mod1 b a h3.
  have hm56 :=
    Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .moments56_mod1 b a h3.
  move: hm hm56 => [_ [_ [_ [h2 [h3m [h4 h8]]]]]] [h5m h6].
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_mod1 in h3.
  rewrite h2 h3m h4 h5m h6 h8 /ideal_final_s2_class_moment2_oracle
          /ideal_final_s2_class_moment3_oracle
          /ideal_final_s2_class_moment4_oracle
          /ideal_final_s2_class_moment5_oracle
          /ideal_final_s2_class_moment6_oracle
          /ideal_final_s2_class_moment8_oracle h3.
  smt().
+ have hm :=
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .moments_mod2 b a h4.
  have hm56 :=
    Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
      .moments56_mod2 b a h4.
  move: hm hm56 => [_ [_ [_ [h2 [h3 [h4m h8]]]]]] [h5m h6].
  rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
            .ideal_final_s2_class_mod2 in h4.
  rewrite h2 h3 h4m h5m h6 h8 /ideal_final_s2_class_moment2_oracle
          /ideal_final_s2_class_moment3_oracle
          /ideal_final_s2_class_moment4_oracle
          /ideal_final_s2_class_moment5_oracle
          /ideal_final_s2_class_moment6_oracle
          /ideal_final_s2_class_moment8_oracle h4.
  smt().
have hm :=
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .moments_mod3 b a h5.
have hm56 :=
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .moments56_mod3 b a h5.
move: hm hm56 => [_ [_ [_ [h2 [h3 [h4 h8]]]]]] [h5m h6].
rewrite /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
          .ideal_final_s2_class_mod3 in h5.
rewrite h2 h3 h4 h5m h6 h8 /ideal_final_s2_class_moment2_oracle
        /ideal_final_s2_class_moment3_oracle
        /ideal_final_s2_class_moment4_oracle
        /ideal_final_s2_class_moment5_oracle
        /ideal_final_s2_class_moment6_oracle
        /ideal_final_s2_class_moment8_oracle h5.
smt().
qed.

op ideal_final_s2_row_class_trace
    (pre_bp avec : BArray8192.t) (row j : int) : int =
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_class_at pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j).

lemma ideal_final_s2_residual_moment_class_traceE
    pre_bp avec row j :
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment2_at pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j) =
    ideal_final_s2_class_moment2_oracle
      (ideal_final_s2_row_class_trace pre_bp avec row j) /\
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_residual_moment3_at pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j) =
    ideal_final_s2_class_moment3_oracle
      (ideal_final_s2_row_class_trace pre_bp avec row j) /\
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment4_at pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j) =
    ideal_final_s2_class_moment4_oracle
      (ideal_final_s2_row_class_trace pre_bp avec row j) /\
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment5_at pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j) =
    ideal_final_s2_class_moment5_oracle
      (ideal_final_s2_row_class_trace pre_bp avec row j) /\
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment6_at pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j) =
    ideal_final_s2_class_moment6_oracle
      (ideal_final_s2_row_class_trace pre_bp avec row j) /\
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment8_at pre_bp avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j) =
    ideal_final_s2_class_moment8_oracle
      (ideal_final_s2_row_class_trace pre_bp avec row j).
proof.
rewrite
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment2_bridge
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_residual_moment3_bridge
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment4_bridge
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment5_bridge
  Mode2FaithfulSecurityIdealFinalS2CenteredMoment56PostFreeze
    .ideal_final_s2_residual_moment6_bridge
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_residual_moment8_bridge.
rewrite /ideal_final_s2_row_class_trace
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_class_at.
rewrite /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_moment2_at
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_moment3_at
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_moment4_at
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_moment8_at.
have :=
  ideal_final_s2_centered_moment_class_oracleE
    (BArray8192.get32 pre_bp
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j))
    (BArray8192.get32 avec
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_index row j)).
move=> h.
move: h => [h2 [h3 [h4 [h5 [h6 h8]]]]].
split; first exact h2.
split; first exact h3.
split; first exact h4.
split; first exact h5.
split; first exact h6.
exact h8.
qed.

lemma ideal_final_s2_row_class_trace_range pre_bp avec row j :
  0 <= ideal_final_s2_row_class_trace pre_bp avec row j <= 5.
proof.
rewrite /ideal_final_s2_row_class_trace
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_class_at.
exact
  (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_range
      (BArray8192.get32 pre_bp
        (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_index row j))
      (BArray8192.get32 avec
        (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_index row j))).
qed.

op ideal_final_s2_class_re_moment2_term
    (trace : int -> int) (k j : int) : real =
  creal (cpow (odd_root k) j) ^ 2 *
  ideal_final_s2_class_moment2_oracle (trace j).

op ideal_final_s2_class_im_moment2_term
    (trace : int -> int) (k j : int) : real =
  cimag (cpow (odd_root k) j) ^ 2 *
  ideal_final_s2_class_moment2_oracle (trace j).

op ideal_final_s2_class_re_moment3_term
    (trace : int -> int) (k j : int) : real =
  creal (cpow (odd_root k) j) ^ 3 *
  ideal_final_s2_class_moment3_oracle (trace j).

op ideal_final_s2_class_im_moment3_term
    (trace : int -> int) (k j : int) : real =
  cimag (cpow (odd_root k) j) ^ 3 *
  ideal_final_s2_class_moment3_oracle (trace j).

op ideal_final_s2_class_re_moment4_term
    (trace : int -> int) (k j : int) : real =
  creal (cpow (odd_root k) j) ^ 4 *
  ideal_final_s2_class_moment4_oracle (trace j).

op ideal_final_s2_class_im_moment4_term
    (trace : int -> int) (k j : int) : real =
  cimag (cpow (odd_root k) j) ^ 4 *
  ideal_final_s2_class_moment4_oracle (trace j).

op ideal_final_s2_class_re_moment5_term
    (trace : int -> int) (k j : int) : real =
  creal (cpow (odd_root k) j) ^ 5 *
  ideal_final_s2_class_moment5_oracle (trace j).

op ideal_final_s2_class_im_moment5_term
    (trace : int -> int) (k j : int) : real =
  cimag (cpow (odd_root k) j) ^ 5 *
  ideal_final_s2_class_moment5_oracle (trace j).

op ideal_final_s2_class_re_moment6_term
    (trace : int -> int) (k j : int) : real =
  creal (cpow (odd_root k) j) ^ 6 *
  ideal_final_s2_class_moment6_oracle (trace j).

op ideal_final_s2_class_im_moment6_term
    (trace : int -> int) (k j : int) : real =
  cimag (cpow (odd_root k) j) ^ 6 *
  ideal_final_s2_class_moment6_oracle (trace j).

op ideal_final_s2_class_re_moment8_term
    (trace : int -> int) (k j : int) : real =
  creal (cpow (odd_root k) j) ^ 8 *
  ideal_final_s2_class_moment8_oracle (trace j).

op ideal_final_s2_class_im_moment8_term
    (trace : int -> int) (k j : int) : real =
  cimag (cpow (odd_root k) j) ^ 8 *
  ideal_final_s2_class_moment8_oracle (trace j).

lemma ideal_final_s2_class_re_moment_termsE pre_bp avec row k j :
  ideal_final_s2_class_re_moment2_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j /\
  ideal_final_s2_class_re_moment3_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
      .ideal_final_s2_row_residual_re_moment3_term pre_bp avec row k j /\
  ideal_final_s2_class_re_moment4_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j /\
  ideal_final_s2_class_re_moment5_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
      .ideal_final_s2_row_residual_re_moment5_term pre_bp avec row k j /\
  ideal_final_s2_class_re_moment6_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
      .ideal_final_s2_row_residual_re_moment6_term pre_bp avec row k j /\
  ideal_final_s2_class_re_moment8_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_moment8_term pre_bp avec row k j.
proof.
have hm := ideal_final_s2_residual_moment_class_traceE pre_bp avec row j.
move: hm => [h2 [h3 [h4 [h5 [h6 h8]]]]].
rewrite /ideal_final_s2_class_re_moment2_term
        /ideal_final_s2_class_re_moment3_term
        /ideal_final_s2_class_re_moment4_term
        /ideal_final_s2_class_re_moment5_term
        /ideal_final_s2_class_re_moment6_term
        /ideal_final_s2_class_re_moment8_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_re_moment2_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_re_moment3_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_re_moment4_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_re_moment5_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_re_moment6_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_re_moment8_term.
rewrite -h2 -h3 -h4 -h5 -h6 -h8.
trivial.
qed.

lemma ideal_final_s2_class_im_moment_termsE pre_bp avec row k j :
  ideal_final_s2_class_im_moment2_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j /\
  ideal_final_s2_class_im_moment3_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
      .ideal_final_s2_row_residual_im_moment3_term pre_bp avec row k j /\
  ideal_final_s2_class_im_moment4_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
      .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j /\
  ideal_final_s2_class_im_moment5_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
      .ideal_final_s2_row_residual_im_moment5_term pre_bp avec row k j /\
  ideal_final_s2_class_im_moment6_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
      .ideal_final_s2_row_residual_im_moment6_term pre_bp avec row k j /\
  ideal_final_s2_class_im_moment8_term
    (ideal_final_s2_row_class_trace pre_bp avec row) k j =
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_moment8_term pre_bp avec row k j.
proof.
have hm := ideal_final_s2_residual_moment_class_traceE pre_bp avec row j.
move: hm => [h2 [h3 [h4 [h5 [h6 h8]]]]].
rewrite /ideal_final_s2_class_im_moment2_term
        /ideal_final_s2_class_im_moment3_term
        /ideal_final_s2_class_im_moment4_term
        /ideal_final_s2_class_im_moment5_term
        /ideal_final_s2_class_im_moment6_term
        /ideal_final_s2_class_im_moment8_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_im_moment2_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_im_moment3_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_im_moment4_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_im_moment5_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_im_moment6_term
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_im_moment8_term.
rewrite -h2 -h3 -h4 -h5 -h6 -h8.
trivial.
qed.

op ideal_final_s2_class_re_profile2
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j => ideal_final_s2_class_re_moment2_term trace k j) 0 n.

op ideal_final_s2_class_im_profile2
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j => ideal_final_s2_class_im_moment2_term trace k j) 0 n.

op ideal_final_s2_class_re_profile3
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j => ideal_final_s2_class_re_moment3_term trace k j) 0 n.

op ideal_final_s2_class_im_profile3
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j => ideal_final_s2_class_im_moment3_term trace k j) 0 n.

op ideal_final_s2_class_re_profile4
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      6%r * ideal_final_s2_class_re_profile2 trace k j *
        ideal_final_s2_class_re_moment2_term trace k j +
      ideal_final_s2_class_re_moment4_term trace k j)
    0 n.

op ideal_final_s2_class_im_profile4
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      6%r * ideal_final_s2_class_im_profile2 trace k j *
        ideal_final_s2_class_im_moment2_term trace k j +
      ideal_final_s2_class_im_moment4_term trace k j)
    0 n.

op ideal_final_s2_class_re_profile5
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      10%r * ideal_final_s2_class_re_profile3 trace k j *
        ideal_final_s2_class_re_moment2_term trace k j +
      10%r * ideal_final_s2_class_re_profile2 trace k j *
        ideal_final_s2_class_re_moment3_term trace k j +
      ideal_final_s2_class_re_moment5_term trace k j)
    0 n.

op ideal_final_s2_class_im_profile5
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      10%r * ideal_final_s2_class_im_profile3 trace k j *
        ideal_final_s2_class_im_moment2_term trace k j +
      10%r * ideal_final_s2_class_im_profile2 trace k j *
        ideal_final_s2_class_im_moment3_term trace k j +
      ideal_final_s2_class_im_moment5_term trace k j)
    0 n.

op ideal_final_s2_class_re_profile6
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      15%r * ideal_final_s2_class_re_profile4 trace k j *
        ideal_final_s2_class_re_moment2_term trace k j +
      20%r * ideal_final_s2_class_re_profile3 trace k j *
        ideal_final_s2_class_re_moment3_term trace k j +
      15%r * ideal_final_s2_class_re_profile2 trace k j *
        ideal_final_s2_class_re_moment4_term trace k j +
      ideal_final_s2_class_re_moment6_term trace k j)
    0 n.

op ideal_final_s2_class_im_profile6
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      15%r * ideal_final_s2_class_im_profile4 trace k j *
        ideal_final_s2_class_im_moment2_term trace k j +
      20%r * ideal_final_s2_class_im_profile3 trace k j *
        ideal_final_s2_class_im_moment3_term trace k j +
      15%r * ideal_final_s2_class_im_profile2 trace k j *
        ideal_final_s2_class_im_moment4_term trace k j +
      ideal_final_s2_class_im_moment6_term trace k j)
    0 n.

op ideal_final_s2_class_re_profile8
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      28%r * ideal_final_s2_class_re_profile6 trace k j *
        ideal_final_s2_class_re_moment2_term trace k j +
      56%r * ideal_final_s2_class_re_profile5 trace k j *
        ideal_final_s2_class_re_moment3_term trace k j +
      70%r * ideal_final_s2_class_re_profile4 trace k j *
        ideal_final_s2_class_re_moment4_term trace k j +
      56%r * ideal_final_s2_class_re_profile3 trace k j *
        ideal_final_s2_class_re_moment5_term trace k j +
      28%r * ideal_final_s2_class_re_profile2 trace k j *
        ideal_final_s2_class_re_moment6_term trace k j +
      ideal_final_s2_class_re_moment8_term trace k j)
    0 n.

op ideal_final_s2_class_im_profile8
    (trace : int -> int) (k n : int) : real =
  BRA.bigi predT
    (fun j =>
      28%r * ideal_final_s2_class_im_profile6 trace k j *
        ideal_final_s2_class_im_moment2_term trace k j +
      56%r * ideal_final_s2_class_im_profile5 trace k j *
        ideal_final_s2_class_im_moment3_term trace k j +
      70%r * ideal_final_s2_class_im_profile4 trace k j *
        ideal_final_s2_class_im_moment4_term trace k j +
      56%r * ideal_final_s2_class_im_profile3 trace k j *
        ideal_final_s2_class_im_moment5_term trace k j +
      28%r * ideal_final_s2_class_im_profile2 trace k j *
        ideal_final_s2_class_im_moment6_term trace k j +
      ideal_final_s2_class_im_moment8_term trace k j)
    0 n.

lemma class_profile4_step_congr
    (p2 p2' t2 t2' t4 t4' : real) :
  p2 = p2' => t2 = t2' => t4 = t4' =>
  6%r * p2 * t2 + t4 = 6%r * p2' * t2' + t4'.
proof.
move=> -> -> ->.
trivial.
qed.

lemma class_profile5_step_congr
    (p3 p3' p2 p2' t2 t2' t3 t3' t5 t5' : real) :
  p3 = p3' => p2 = p2' => t2 = t2' => t3 = t3' => t5 = t5' =>
  10%r * p3 * t2 + 10%r * p2 * t3 + t5 =
  10%r * p3' * t2' + 10%r * p2' * t3' + t5'.
proof.
move=> -> -> -> -> ->.
trivial.
qed.

lemma class_profile6_step_congr
    (p4 p4' p3 p3' p2 p2'
     t2 t2' t3 t3' t4 t4' t6 t6' : real) :
  p4 = p4' => p3 = p3' => p2 = p2' =>
  t2 = t2' => t3 = t3' => t4 = t4' => t6 = t6' =>
  15%r * p4 * t2 + 20%r * p3 * t3 + 15%r * p2 * t4 + t6 =
  15%r * p4' * t2' + 20%r * p3' * t3' + 15%r * p2' * t4' + t6'.
proof.
move=> -> -> -> -> -> -> ->.
trivial.
qed.

lemma class_profile8_step_congr
    (p6 p6' p5 p5' p4 p4' p3 p3' p2 p2'
     t2 t2' t3 t3' t4 t4' t5 t5' t6 t6' t8 t8' : real) :
  p6 = p6' => p5 = p5' => p4 = p4' => p3 = p3' => p2 = p2' =>
  t2 = t2' => t3 = t3' => t4 = t4' =>
  t5 = t5' => t6 = t6' => t8 = t8' =>
  28%r * p6 * t2 + 56%r * p5 * t3 + 70%r * p4 * t4 +
  56%r * p3 * t5 + 28%r * p2 * t6 + t8 =
  28%r * p6' * t2' + 56%r * p5' * t3' + 70%r * p4' * t4' +
  56%r * p3' * t5' + 28%r * p2' * t6' + t8'.
proof.
move=> -> -> -> -> -> -> -> -> -> -> ->.
trivial.
qed.

lemma ideal_final_s2_class_re_profile2E pre_bp avec row k n :
  ideal_final_s2_class_re_profile2
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_re_profile pre_bp avec row k n.
proof.
change
  (BRA.bigi predT
    (fun j => ideal_final_s2_class_re_moment2_term
      (ideal_final_s2_row_class_trace pre_bp avec row) k j) 0 n =
   BRA.bigi predT
    (fun j =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j) 0 n).
apply BRA.eq_big_seq => j hj.
have [h2 _] := ideal_final_s2_class_re_moment_termsE pre_bp avec row k j.
exact h2.
qed.

lemma ideal_final_s2_class_re_profile3E pre_bp avec row k n :
  ideal_final_s2_class_re_profile3
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_profile3 pre_bp avec row k n.
proof.
rewrite /ideal_final_s2_class_re_profile3
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_re_profile3.
apply BRA.eq_big_seq => j hj.
have [_ [h3 _]] := ideal_final_s2_class_re_moment_termsE pre_bp avec row k j.
exact h3.
qed.

lemma ideal_final_s2_class_re_profile4E pre_bp avec row k n :
  ideal_final_s2_class_re_profile4
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile4 pre_bp avec row k n.
proof.
change
  (BRA.bigi predT
    (fun j =>
      6%r * ideal_final_s2_class_re_profile2
        (ideal_final_s2_row_class_trace pre_bp avec row) k j *
        ideal_final_s2_class_re_moment2_term
          (ideal_final_s2_row_class_trace pre_bp avec row) k j +
      ideal_final_s2_class_re_moment4_term
        (ideal_final_s2_row_class_trace pre_bp avec row) k j) 0 n =
   BRA.bigi predT
    (fun j =>
      6%r *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_re_profile pre_bp avec row k j *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_re_moment2_term pre_bp avec row k j +
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_re_moment4_term pre_bp avec row k j) 0 n).
apply BRA.eq_big_seq => j hj.
have hp2 := ideal_final_s2_class_re_profile2E pre_bp avec row k j.
have [h2 [_ [h4 _]]] :=
  ideal_final_s2_class_re_moment_termsE pre_bp avec row k j.
exact (class_profile4_step_congr _ _ _ _ _ _ hp2 h2 h4).
qed.

lemma ideal_final_s2_class_re_profile5E pre_bp avec row k n :
  ideal_final_s2_class_re_profile5
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_profile5 pre_bp avec row k n.
proof.
rewrite /ideal_final_s2_class_re_profile5
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_re_profile5.
apply BRA.eq_big_seq => j hj.
have hp3 := ideal_final_s2_class_re_profile3E pre_bp avec row k j.
have hp2 := ideal_final_s2_class_re_profile2E pre_bp avec row k j.
have [h2 [h3 [_ [h5 _]]]] :=
  ideal_final_s2_class_re_moment_termsE pre_bp avec row k j.
exact
  (class_profile5_step_congr _ _ _ _ _ _ _ _ _ _
    hp3 hp2 h2 h3 h5).
qed.

lemma ideal_final_s2_class_re_profile6E pre_bp avec row k n :
  ideal_final_s2_class_re_profile6
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_re_profile6 pre_bp avec row k n.
proof.
rewrite /ideal_final_s2_class_re_profile6
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_re_profile6.
apply BRA.eq_big_seq => j hj.
have hp4 := ideal_final_s2_class_re_profile4E pre_bp avec row k j.
have hp3 := ideal_final_s2_class_re_profile3E pre_bp avec row k j.
have hp2 := ideal_final_s2_class_re_profile2E pre_bp avec row k j.
have [h2 [h3 [h4 [_ [h6 _]]]]] :=
  ideal_final_s2_class_re_moment_termsE pre_bp avec row k j.
exact
  (class_profile6_step_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hp4 hp3 hp2 h2 h3 h4 h6).
qed.

lemma ideal_final_s2_class_re_profile8E pre_bp avec row k n :
  ideal_final_s2_class_re_profile8
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n.
proof.
rewrite /ideal_final_s2_class_re_profile8
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_re_profile8.
apply BRA.eq_big_seq => j hj.
have hp6 := ideal_final_s2_class_re_profile6E pre_bp avec row k j.
have hp5 := ideal_final_s2_class_re_profile5E pre_bp avec row k j.
have hp4 := ideal_final_s2_class_re_profile4E pre_bp avec row k j.
have hp3 := ideal_final_s2_class_re_profile3E pre_bp avec row k j.
have hp2 := ideal_final_s2_class_re_profile2E pre_bp avec row k j.
have [h2 [h3 [h4 [h5 [h6 h8]]]]] :=
  ideal_final_s2_class_re_moment_termsE pre_bp avec row k j.
exact
  (class_profile8_step_congr
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hp6 hp5 hp4 hp3 hp2 h2 h3 h4 h5 h6 h8).
qed.

lemma ideal_final_s2_class_im_profile2E pre_bp avec row k n :
  ideal_final_s2_class_im_profile2
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_im_profile pre_bp avec row k n.
proof.
change
  (BRA.bigi predT
    (fun j => ideal_final_s2_class_im_moment2_term
      (ideal_final_s2_row_class_trace pre_bp avec row) k j) 0 n =
   BRA.bigi predT
    (fun j =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j) 0 n).
apply BRA.eq_big_seq => j hj.
have [h2 _] := ideal_final_s2_class_im_moment_termsE pre_bp avec row k j.
exact h2.
qed.

lemma ideal_final_s2_class_im_profile3E pre_bp avec row k n :
  ideal_final_s2_class_im_profile3
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_profile3 pre_bp avec row k n.
proof.
rewrite /ideal_final_s2_class_im_profile3
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_im_profile3.
apply BRA.eq_big_seq => j hj.
have [_ [h3 _]] := ideal_final_s2_class_im_moment_termsE pre_bp avec row k j.
exact h3.
qed.

lemma ideal_final_s2_class_im_profile4E pre_bp avec row k n :
  ideal_final_s2_class_im_profile4
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile4 pre_bp avec row k n.
proof.
change
  (BRA.bigi predT
    (fun j =>
      6%r * ideal_final_s2_class_im_profile2
        (ideal_final_s2_row_class_trace pre_bp avec row) k j *
        ideal_final_s2_class_im_moment2_term
          (ideal_final_s2_row_class_trace pre_bp avec row) k j +
      ideal_final_s2_class_im_moment4_term
        (ideal_final_s2_row_class_trace pre_bp avec row) k j) 0 n =
   BRA.bigi predT
    (fun j =>
      6%r *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_im_profile pre_bp avec row k j *
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
          .ideal_final_s2_row_residual_im_moment2_term pre_bp avec row k j +
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
        .ideal_final_s2_row_residual_im_moment4_term pre_bp avec row k j) 0 n).
apply BRA.eq_big_seq => j hj.
have hp2 := ideal_final_s2_class_im_profile2E pre_bp avec row k j.
have [h2 [_ [h4 _]]] :=
  ideal_final_s2_class_im_moment_termsE pre_bp avec row k j.
exact (class_profile4_step_congr _ _ _ _ _ _ hp2 h2 h4).
qed.

lemma ideal_final_s2_class_im_profile5E pre_bp avec row k n :
  ideal_final_s2_class_im_profile5
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_profile5 pre_bp avec row k n.
proof.
rewrite /ideal_final_s2_class_im_profile5
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_im_profile5.
apply BRA.eq_big_seq => j hj.
have hp3 := ideal_final_s2_class_im_profile3E pre_bp avec row k j.
have hp2 := ideal_final_s2_class_im_profile2E pre_bp avec row k j.
have [h2 [h3 [_ [h5 _]]]] :=
  ideal_final_s2_class_im_moment_termsE pre_bp avec row k j.
exact
  (class_profile5_step_congr _ _ _ _ _ _ _ _ _ _
    hp3 hp2 h2 h3 h5).
qed.

lemma ideal_final_s2_class_im_profile6E pre_bp avec row k n :
  ideal_final_s2_class_im_profile6
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
    .ideal_final_s2_row_residual_im_profile6 pre_bp avec row k n.
proof.
rewrite /ideal_final_s2_class_im_profile6
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMoment356PostFreeze
          .ideal_final_s2_row_residual_im_profile6.
apply BRA.eq_big_seq => j hj.
have hp4 := ideal_final_s2_class_im_profile4E pre_bp avec row k j.
have hp3 := ideal_final_s2_class_im_profile3E pre_bp avec row k j.
have hp2 := ideal_final_s2_class_im_profile2E pre_bp avec row k j.
have [h2 [h3 [h4 [_ [h6 _]]]]] :=
  ideal_final_s2_class_im_moment_termsE pre_bp avec row k j.
exact
  (class_profile6_step_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hp4 hp3 hp2 h2 h3 h4 h6).
qed.

lemma ideal_final_s2_class_im_profile8E pre_bp avec row k n :
  ideal_final_s2_class_im_profile8
    (ideal_final_s2_row_class_trace pre_bp avec row) k n =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n.
proof.
rewrite /ideal_final_s2_class_im_profile8
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
          .ideal_final_s2_row_residual_im_profile8.
apply BRA.eq_big_seq => j hj.
have hp6 := ideal_final_s2_class_im_profile6E pre_bp avec row k j.
have hp5 := ideal_final_s2_class_im_profile5E pre_bp avec row k j.
have hp4 := ideal_final_s2_class_im_profile4E pre_bp avec row k j.
have hp3 := ideal_final_s2_class_im_profile3E pre_bp avec row k j.
have hp2 := ideal_final_s2_class_im_profile2E pre_bp avec row k j.
have [h2 [h3 [h4 [h5 [h6 h8]]]]] :=
  ideal_final_s2_class_im_moment_termsE pre_bp avec row k j.
exact
  (class_profile8_step_congr
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hp6 hp5 hp4 hp3 hp2 h2 h3 h4 h5 h6 h8).
qed.

lemma ideal_final_s2_row_residual_profile8_class_traceE
    pre_bp avec row k n :
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n =
    ideal_final_s2_class_re_profile8
      (ideal_final_s2_row_class_trace pre_bp avec row) k n /\
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n =
    ideal_final_s2_class_im_profile8
      (ideal_final_s2_row_class_trace pre_bp avec row) k n.
proof.
have hre := ideal_final_s2_class_re_profile8E pre_bp avec row k n.
have him := ideal_final_s2_class_im_profile8E pre_bp avec row k n.
split.
+ apply eq_sym.
  exact hre.
apply eq_sym.
exact him.
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
