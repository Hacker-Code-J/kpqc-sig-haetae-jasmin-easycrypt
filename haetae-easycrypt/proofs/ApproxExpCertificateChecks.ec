require import AllCore IntDiv List Real StdRing StdOrder.
require import ApproxExpSpec ReferenceConstants ApproxExpCertificate
  Bernstein10Spec Bernstein10Correctness.
import RField RealOrder.

op aec_cell (j : int) (t : real) : real = (2*j)%r / 9%r + (2%r/9%r)*t.
op aec_error : real = aec_error_units%r / ae_scale%r.
op aec_upper_residual (z : real) : real =
  (ae_scale+1)%r * (ae_polynomial (z+1%r/ae_scale%r)+aec_error) -
    ae_scale%r * (ae_polynomial z+aec_error).
op aec_lower_residual (z : real) : real =
  (ae_scale-1)%r * (ae_polynomial z-aec_error) -
    ae_scale%r * (ae_polynomial (z+1%r/ae_scale%r)-aec_error).

lemma aec_positive_constants :
  1 < ae_scale /\ aec_scale = ae_scale /\
  0 < aec_denominator /\ aec_error_units = 24 /\
  0 <= aec_domain_limit /\ 3*aec_domain_limit <= 2*ae_scale /\
  2*ae_scale < 3*(aec_domain_limit+1).
proof.
  by rewrite /ae_scale /aec_scale /aec_denominator /aec_error_units /aec_domain_limit /=.
qed.

lemma aec_coefficient_provenance : aec_coefficients = ae_coefficients.
proof. by rewrite /aec_coefficients /ae_coefficients /reference_exp_coefficients /=. qed.

lemma aec_polynomial_power z :
  ae_polynomial z = power_eval (rev aec_coefficients) z / aec_scale%r.
proof.
  rewrite /ae_polynomial /ae_real_fold /ae_leading /ae_tail /ae_coefficients
    /reference_exp_coefficients /aec_coefficients /ae_scale /aec_scale /power_eval /rev /=.
  ring.
qed.

lemma aec_upper_0_checked :
  bernstein10_check aec_upper_0_power aec_upper_0_bernstein.
proof.
  by rewrite /bernstein10_check /bernstein10_power_coefficients
    /aec_upper_0_power /aec_upper_0_bernstein /=.
qed.

lemma aec_upper_0_identity t :
  power_eval aec_upper_0_power t =
    aec_denominator%r * ae_scale%r * aec_upper_residual (aec_cell 0 t).
proof.
  rewrite /aec_upper_residual !aec_polynomial_power /aec_cell /aec_error
    /aec_upper_0_power /aec_denominator /ae_scale /aec_scale /aec_error_units
    /aec_coefficients /power_eval /rev /=.
  field; trivial.
qed.

lemma aec_upper_1_checked :
  bernstein10_check aec_upper_1_power aec_upper_1_bernstein.
proof.
  by rewrite /bernstein10_check /bernstein10_power_coefficients
    /aec_upper_1_power /aec_upper_1_bernstein /=.
qed.

lemma aec_upper_1_identity t :
  power_eval aec_upper_1_power t =
    aec_denominator%r * ae_scale%r * aec_upper_residual (aec_cell 1 t).
proof.
  rewrite /aec_upper_residual !aec_polynomial_power /aec_cell /aec_error
    /aec_upper_1_power /aec_denominator /ae_scale /aec_scale /aec_error_units
    /aec_coefficients /power_eval /rev /=.
  field; trivial.
qed.

lemma aec_upper_2_checked :
  bernstein10_check aec_upper_2_power aec_upper_2_bernstein.
proof.
  by rewrite /bernstein10_check /bernstein10_power_coefficients
    /aec_upper_2_power /aec_upper_2_bernstein /=.
qed.

lemma aec_upper_2_identity t :
  power_eval aec_upper_2_power t =
    aec_denominator%r * ae_scale%r * aec_upper_residual (aec_cell 2 t).
proof.
  rewrite /aec_upper_residual !aec_polynomial_power /aec_cell /aec_error
    /aec_upper_2_power /aec_denominator /ae_scale /aec_scale /aec_error_units
    /aec_coefficients /power_eval /rev /=.
  field; trivial.
qed.

lemma aec_lower_0_checked :
  bernstein10_check aec_lower_0_power aec_lower_0_bernstein.
proof.
  by rewrite /bernstein10_check /bernstein10_power_coefficients
    /aec_lower_0_power /aec_lower_0_bernstein /=.
qed.

lemma aec_lower_0_identity t :
  power_eval aec_lower_0_power t =
    aec_denominator%r * ae_scale%r * aec_lower_residual (aec_cell 0 t).
proof.
  rewrite /aec_lower_residual !aec_polynomial_power /aec_cell /aec_error
    /aec_lower_0_power /aec_denominator /ae_scale /aec_scale /aec_error_units
    /aec_coefficients /power_eval /rev /=.
  field; trivial.
qed.

lemma aec_lower_1_checked :
  bernstein10_check aec_lower_1_power aec_lower_1_bernstein.
proof.
  by rewrite /bernstein10_check /bernstein10_power_coefficients
    /aec_lower_1_power /aec_lower_1_bernstein /=.
qed.

lemma aec_lower_1_identity t :
  power_eval aec_lower_1_power t =
    aec_denominator%r * ae_scale%r * aec_lower_residual (aec_cell 1 t).
proof.
  rewrite /aec_lower_residual !aec_polynomial_power /aec_cell /aec_error
    /aec_lower_1_power /aec_denominator /ae_scale /aec_scale /aec_error_units
    /aec_coefficients /power_eval /rev /=.
  field; trivial.
qed.

lemma aec_lower_2_checked :
  bernstein10_check aec_lower_2_power aec_lower_2_bernstein.
proof.
  by rewrite /bernstein10_check /bernstein10_power_coefficients
    /aec_lower_2_power /aec_lower_2_bernstein /=.
qed.

lemma aec_lower_2_identity t :
  power_eval aec_lower_2_power t =
    aec_denominator%r * ae_scale%r * aec_lower_residual (aec_cell 2 t).
proof.
  rewrite /aec_lower_residual !aec_polynomial_power /aec_cell /aec_error
    /aec_lower_2_power /aec_denominator /ae_scale /aec_scale /aec_error_units
    /aec_coefficients /power_eval /rev /=.
  field; trivial.
qed.
