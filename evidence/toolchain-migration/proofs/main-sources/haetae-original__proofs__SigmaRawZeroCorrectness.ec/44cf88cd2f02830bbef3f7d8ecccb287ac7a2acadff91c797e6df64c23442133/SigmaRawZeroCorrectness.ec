require import AllCore IntDiv Real StdOrder.
from Jasmin require import JModel_x86.
require import SigmaRawSpec SigmaRawNoiseSpec SigmaSpec SigmaCorrectness
  SigmaRoundingCorrectness SigmaRejection48Bridge Rejection48Spec.
import IntOrder RealOrder RField.

lemma sr_decoded_bounds (p : BArray26.t) :
  0 <= sr_noise p < sr_noise_modulus /\ 0 <= sr_cdt p <= 166.
proof.
have [hlo [hhi hcdt]] := sigma76_decoded_bounds p.
rewrite /sr_noise /sr_noise_modulus /sr_scale /sr_cdt; smt().
qed.

lemma sr_rounding_zero_int lo hi x :
  0 <= lo < 281474976710656 => 0 <= hi < 16777216 => 0 <= x <= 166 =>
  (sigma_round_int lo hi x = 0) =
    (x = 0 /\ 0 <= lo + 281474976710656 * hi < 32768).
proof.
move=> hlo hhi hx.
have hd := divz_eq lo 32768.
have hr := modz_cmp lo 32768.
have hq := divz_eq (lo %/ 32768 + 1) 2.
have hs := modz_cmp (lo %/ 32768 + 1) 2.
rewrite /sigma_round_int; smt().
qed.

lemma sr_rounded_zero (p : BArray26.t) :
  (sigma_rejection48_rounded p = W64.zero) =
    (sr_cdt p = 0 /\ 0 <= sr_noise p < 32768).
proof.
have [hlo [hhi hcdt]] := sigma76_decoded_bounds p.
rewrite W64.to_uint_eq W64.to_uint0 /sigma_rejection48_rounded sigma76_spec_rounding
  /sigma76_rounding_int /sr_noise /sr_scale /sr_cdt.
exact (sr_rounding_zero_int _ _ _ hlo hhi hcdt).
qed.

lemma sr_candidate_zero (p : BArray26.t) :
  (sr_candidate p = 0) = (sr_cdt p = 0 /\ sr_noise p = 0).
proof.
have [hy hx] := sr_decoded_bounds p.
rewrite /sr_candidate /sr_noise_modulus.
rewrite /sr_noise_modulus in hy.
exact (sr_noise_raw_zero (sr_cdt p) (sr_noise p) hy).
qed.

lemma sr_zero_tests_differ (p : BArray26.t) :
  ((sigma_rejection48_rounded p = W64.zero) <> (sr_candidate p = 0)) =
    sr_zero_mismatch p.
proof.
have [hy hx] := sr_decoded_bounds p.
rewrite sr_rounded_zero sr_candidate_zero /sr_zero_mismatch; smt().
qed.

lemma sr_zero_factor_difference (p : BArray26.t) :
  sr_raw_factor p - rejection48_factor (sigma_rejection48_rounded p) =
    if sr_zero_mismatch p then 1%r / 2%r else 0%r.
proof.
have [hy hx] := sr_decoded_bounds p.
rewrite /sr_raw_factor /rejection48_factor sr_candidate_zero sr_rounded_zero
  /sr_zero_mismatch; smt().
qed.

lemma sr_zero_factor_absolute_difference (p : BArray26.t) :
  `|rejection48_factor (sigma_rejection48_rounded p) - sr_raw_factor p| =
    if sr_zero_mismatch p then 1%r / 2%r else 0%r.
proof.
rewrite distrC sr_zero_factor_difference.
case (sr_zero_mismatch p); smt().
qed.

lemma sr_raw_factor_bounds (p : BArray26.t) : 0%r <= sr_raw_factor p <= 1%r.
proof. rewrite /sr_raw_factor; case (sr_candidate p = 0); smt(). qed.

lemma sr_rounded_factor_bounds (p : BArray26.t) :
  0%r <= rejection48_factor (sigma_rejection48_rounded p) <= 1%r.
proof.
rewrite /rejection48_factor; case (sigma_rejection48_rounded p = W64.zero); smt().
qed.

lemma sr_zero_factor_noise_link (p : BArray26.t) :
  sr_raw_factor p = sr_noise_raw_factor (sr_cdt p) (sr_noise p) /\
  rejection48_factor (sigma_rejection48_rounded p) =
    sr_noise_rounded_factor (sr_cdt p) (sr_noise p) /\
  sr_zero_mismatch p = sr_noise_mismatch (sr_cdt p) (sr_noise p).
proof.
by rewrite /sr_raw_factor /sr_candidate /sr_noise_modulus /sr_noise_raw_factor
  /rejection48_factor sr_rounded_zero /sr_noise_rounded_factor
  /sr_zero_mismatch /sr_noise_mismatch.
qed.
