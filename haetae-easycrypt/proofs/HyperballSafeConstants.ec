require import AllCore IntDiv StdOrder.
from Jasmin require import JModel_x86.
require import HyperballSafeSpec HyperballFixedPointSpec HyperballReferenceConstants.

lemma hbs_format_constants :
  hbs_q=2^76 /\ hbs_radix=2^48 /\ hbs_operand_cap=2^88 /\
  hbs_scale_cap=2^85 /\ hbs_coefficient_cap=2^26.
proof. by rewrite /hbs_q /hbs_radix /hbs_operand_cap /hbs_scale_cap /hbs_coefficient_cap. qed.

lemma hbs_mode_certificate mode : hbs_mode mode =>
  2^70 <= hbs_inverse_cap mode <= 2^71 /\
  0 < hbs_half_min mode <= hbs_half_max mode /\
  hbs_half_max mode <= hbs_operand_cap /\
  17*hbs_q^3 <= 16*2*hbs_half_min mode*(hbs_inverse_cap mode)^2 /\
  8*hbs_half_max mode*(hbs_inverse_cap mode)^2 <= 9*hbs_q^3 /\
  hbs_canonical (hb_ref_cube mode) /\ hbs_canonical (hb_ref_three mode) /\
  0 < hb_value (hb_ref_cube mode) <= hbs_operand_cap /\
  0 < hb_value (hb_ref_three mode) <= hbs_operand_cap /\
  W64.to_uint (hb_ref_scale mode) < 2^43 /\
  (hbs_inverse_cap mode*W64.to_uint (hb_ref_scale mode)) %/ 268435456+1 <= hbs_scale_cap.
proof.
  rewrite /hbs_mode; move=> [-> | [-> | ->]];
    by rewrite /hbs_inverse_cap /hbs_half_min /hbs_half_max
      /hbs_sum_min /hbs_sum_max /hbs_events /hb_ref_l /hb_ref_k
      /hbs_operand_cap /hbs_q /hbs_radix /hbs_scale_cap /hbs_canonical
      /hb_ref_cube /hb_ref_three /hb_ref_scale /hb_value /= ?W64.of_uintK /=.
qed.

lemma hbs_half_certificate mode h : hbs_mode mode =>
  hbs_half_min mode <= h <= hbs_half_max mode =>
  0 <= h <= hbs_operand_cap /\
  17*hbs_q^3 <= 16*2*h*(hbs_inverse_cap mode)^2 /\
  8*h*(hbs_inverse_cap mode)^2 <= 9*hbs_q^3.
proof.
  rewrite /hbs_mode; move=> [-> | [-> | ->]];
    rewrite /hbs_half_min /hbs_half_max /hbs_sum_min /hbs_sum_max
      /hbs_events /hb_ref_l /hb_ref_k /hbs_inverse_cap /hbs_q /hbs_operand_cap /=;
    smt().
qed.

lemma hbs_initial_numeric_bound mode h p : hbs_mode mode =>
  hbs_half_min mode <= h <= hbs_half_max mode =>
  `|hbs_q*p-h*hb_value (hb_ref_cube mode)| <= hbs_q =>
  hbs_radix <= hb_value (hb_ref_three mode)-p <= hbs_inverse_cap mode /\
  0 <= p <= hbs_operand_cap.
proof.
  rewrite /hbs_mode; move=> [-> | [-> | ->]];
    rewrite /hbs_half_min /hbs_half_max /hbs_sum_min /hbs_sum_max
      /hbs_events /hb_ref_l /hb_ref_k /hbs_inverse_cap /hbs_q /hbs_radix
      /hbs_operand_cap /hb_value /hb_ref_cube /hb_ref_three /= ?W64.of_uintK /=;
    smt(IntOrder.ler_norml).
qed.

lemma hbs_center_good mode : hbs_mode mode =>
  hbs_good mode (W64.zero,W64.of_int (hbs_events mode*268435456)).
proof.
  rewrite /hbs_mode; move=> [-> | [-> | ->]];
    by rewrite /hbs_good /hbs_mode /hbs_canonical /hbs_radix
      /hbs_sum_min /hbs_sum_max /hbs_events /hb_ref_l /hb_ref_k /hb_value /=
      ?W64.of_uintK /=.
qed.
