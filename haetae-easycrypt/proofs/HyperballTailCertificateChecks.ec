require import AllCore IntDiv List.
require import ExpIntervalSpec HyperballTailCertificate.

(* Every concrete claim below reduces to finite integer arithmetic.
   The exponential/power meaning is proved separately, never assumed. *)
lemma htc_scale_positive : 0 < htc_scale.
proof. by rewrite /htc_scale. qed.

lemma htc_exp_plus_checked :
  htc_seed_ok htc_scale 19 687194767360 (head witness htc_exp_plus_chain) /\
  ei_square_check htc_scale htc_exp_plus_chain /\
  size htc_exp_plus_chain = 33 /\
  last witness htc_exp_plus_chain = htc_exp_plus_bound.
proof.
  by rewrite /htc_seed_ok /htc_scale /htc_exp_plus_chain
    /htc_exp_plus_bound /ei_square_check /ei_square_steps_check /ei_mul /=.
qed.

lemma htc_exp_minus_checked :
  htc_seed_ok htc_scale 45 1683627180032 (head witness htc_exp_minus_chain) /\
  ei_square_check htc_scale htc_exp_minus_chain /\
  size htc_exp_minus_chain = 33 /\
  last witness htc_exp_minus_chain = htc_exp_minus_bound.
proof.
  by rewrite /htc_seed_ok /htc_scale /htc_exp_minus_chain
    /htc_exp_minus_bound /ei_square_check /ei_square_steps_check /ei_mul /=.
qed.

lemma htc_rational_bases_checked :
  htc_rational_ok htc_scale 3947 4000 htc_rplus_bound /\
  htc_rational_ok htc_scale 1963 2000 htc_rminus_bound.
proof.
  by rewrite /htc_rational_ok /htc_scale /htc_rplus_bound /htc_rminus_bound /=.
qed.

lemma htc_factor_plus_checked :
  0 <= htc_exp_plus_bound.`2 /\
  htc_exp_plus_bound.`2 * 2621449 * 4000 <= htc_scale * 2359296 * 3947.
proof. by rewrite /htc_exp_plus_bound /htc_scale /=. qed.

lemma htc_factor_minus_checked :
  0 < htc_exp_minus_bound.`1 /\
  htc_scale * 229377 * 2000 <= htc_exp_minus_bound.`1 * 262144 * 1963.
proof. by rewrite /htc_exp_minus_bound /htc_scale /=. qed.

lemma htc_power_plus_1538_checked :
  htc_power_check htc_scale htc_rplus_bound htc_power_plus_1538 /\
  last witness htc_power_plus_1538 = (1538, htc_power_plus_bound_1538).
proof.
  by rewrite /htc_scale /htc_rplus_bound /htc_power_plus_1538
    /htc_power_plus_bound_1538 /htc_power_check /htc_power_steps_check
    /htc_power_step_ok /ei_mul /=.
qed.

lemma htc_power_plus_2306_checked :
  htc_power_check htc_scale htc_rplus_bound htc_power_plus_2306 /\
  last witness htc_power_plus_2306 = (2306, htc_power_plus_bound_2306).
proof.
  by rewrite /htc_scale /htc_rplus_bound /htc_power_plus_2306
    /htc_power_plus_bound_2306 /htc_power_check /htc_power_steps_check
    /htc_power_step_ok /ei_mul /=.
qed.

lemma htc_power_plus_2818_checked :
  htc_power_check htc_scale htc_rplus_bound htc_power_plus_2818 /\
  last witness htc_power_plus_2818 = (2818, htc_power_plus_bound_2818).
proof.
  by rewrite /htc_scale /htc_rplus_bound /htc_power_plus_2818
    /htc_power_plus_bound_2818 /htc_power_check /htc_power_steps_check
    /htc_power_step_ok /ei_mul /=.
qed.

lemma htc_power_minus_1538_checked :
  htc_power_check htc_scale htc_rminus_bound htc_power_minus_1538 /\
  last witness htc_power_minus_1538 = (1538, htc_power_minus_bound_1538).
proof.
  by rewrite /htc_scale /htc_rminus_bound /htc_power_minus_1538
    /htc_power_minus_bound_1538 /htc_power_check /htc_power_steps_check
    /htc_power_step_ok /ei_mul /=.
qed.

lemma htc_power_minus_2306_checked :
  htc_power_check htc_scale htc_rminus_bound htc_power_minus_2306 /\
  last witness htc_power_minus_2306 = (2306, htc_power_minus_bound_2306).
proof.
  by rewrite /htc_scale /htc_rminus_bound /htc_power_minus_2306
    /htc_power_minus_bound_2306 /htc_power_check /htc_power_steps_check
    /htc_power_step_ok /ei_mul /=.
qed.

lemma htc_power_minus_2818_checked :
  htc_power_check htc_scale htc_rminus_bound htc_power_minus_2818 /\
  last witness htc_power_minus_2818 = (2818, htc_power_minus_bound_2818).
proof.
  by rewrite /htc_scale /htc_rminus_bound /htc_power_minus_2818
    /htc_power_minus_bound_2818 /htc_power_check /htc_power_steps_check
    /htc_power_step_ok /ei_mul /=.
qed.

lemma htc_power_sum_1538_checked :
  (htc_power_plus_bound_1538.`2 + htc_power_minus_bound_1538.`2) * 536870912 < htc_scale.
proof.
  by rewrite /htc_power_plus_bound_1538 /htc_power_minus_bound_1538 /htc_scale /=.
qed.

lemma htc_power_sum_2306_checked :
  (htc_power_plus_bound_2306.`2 + htc_power_minus_bound_2306.`2) * 17592186044416 < htc_scale.
proof.
  by rewrite /htc_power_plus_bound_2306 /htc_power_minus_bound_2306 /htc_scale /=.
qed.

lemma htc_power_sum_2818_checked :
  (htc_power_plus_bound_2818.`2 + htc_power_minus_bound_2818.`2) * 18014398509481984 < htc_scale.
proof.
  by rewrite /htc_power_plus_bound_2818 /htc_power_minus_bound_2818 /htc_scale /=.
qed.
