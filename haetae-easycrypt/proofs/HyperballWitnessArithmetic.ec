require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HyperballWitnessSpec HyperballFixedPointSpec
  HyperballReferenceConstants HyperballScaleSpec.
import HyperballScaleSpec.

lemma hbw_polynomial_bounds mode : hbw_mode mode =>
  2 <= hb_ref_l mode + hb_ref_k mode <= 11.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hb_ref_l /hb_ref_k.
qed.

lemma hbw_storage_bounds mode : hbw_mode mode =>
  hb_scale_bounds (hbw_left mode) (hbw_count mode).
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hb_scale_bounds /hbw_left /hbw_count /hb_ref_l /hb_ref_k.
qed.

lemma hbw_event_budget mode : hbw_mode mode =>
  0 <= hbw_count mode /\ hbw_events mode <= 2818.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_events /hbw_count /hb_ref_l /hb_ref_k.
qed.

lemma hbw_square_value_upper mode : hbw_mode mode =>
  0 <= hb_value (hbw_square mode) <= 19342813113834066795298815.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hb_value /hbw_square /= ?W64.of_uintK /=.
qed.

lemma hbw_sum_exact mode : hbw_mode mode =>
  W64.to_uint (hbw_sum mode).`1 < 281474976710656 /\
  hb_value (hbw_sum mode) = hbw_events mode * hb_value (hbw_square mode).
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hb_value /hbw_sum /hbw_square /hbw_events /hbw_count
      /hb_ref_l /hb_ref_k /= ?W64.of_uintK /=.
qed.

lemma hbw_coefficient_sint mode : hbw_mode mode =>
  W32.to_sint (W32.of_int (hbw_coefficient mode)) = hbw_coefficient mode.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_coefficient /= ?W32.of_sintK /=.
qed.

lemma hbw_fixture_norm mode : hbw_mode mode =>
  hbw_count mode * (hbw_coefficient mode * hbw_coefficient mode) = hbw_total mode /\
  hbw_total mode %% W64.modulus = hbw_residue mode /\
  0 <= hbw_residue mode /\
  hbw_residue mode <= W64.to_uint (hb_ref_bound mode) /\
  W64.to_uint (hb_ref_bound mode) < W64.modulus /\
  W64.modulus <= hbw_total mode.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_count /hb_ref_l /hb_ref_k /hbw_coefficient
      /hbw_total /hbw_residue /hb_ref_bound /= ?W64.of_uintK /=.
qed.
