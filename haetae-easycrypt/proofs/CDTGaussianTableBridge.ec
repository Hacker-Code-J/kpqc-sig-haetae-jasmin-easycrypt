require import AllCore IntDiv List Distr StdOrder StdRing StdBigop.
require import ExpIntervalSpec CDTDistributionSpec CDTDistribution CDTDistributionBridge
  CDTGaussianCertificate CDTGaussianCertificateChecks DistributionIntervalBounds.
import RField RealOrder.

(* The mathematical Gaussian target never reads the implementation table.
   This separate bridge identifies the actual table being compared to it. *)
lemma gi_actual_thresholds : gi_thresholds = cdt83_thresholds.
proof.
  by rewrite /gi_thresholds /cdt83_thresholds /cdt83_reference_high
    /ReferenceConstants.reference_cdt83_hi_words /ReferenceConstants.reference_cdt83_lo_words
    /ReferenceConstants.reference_cdt83_tail_hi /mapi /=.
qed.

lemma gi_actual_modulus : gi_input_size = cdt83_modulus.
proof. by rewrite /gi_input_size /cdt83_modulus /=. qed.

lemma gi_actual_counts k : 0 <= k < 256 =>
  mu1 (cdt_distribution cdt83_modulus cdt83_thresholds) k =
    (nth 0 gi_probability_counts k)%r / gi_input_size%r.
proof.
  move=> hk.
  have hcheck := gi_probability_counts_checked.
  rewrite allP in hcheck.
  have hc := hcheck k _; first by rewrite mem_iota /=; smt().
  rewrite (cdt_distribution_mass cdt83_modulus cdt83_thresholds k cdt83_table_valid)
    /cdt_bin_mass cdt83_thresholds_length -gi_actual_thresholds -gi_actual_modulus.
  rewrite hc; smt().
qed.

op gi_error (k : int) : real =
  (nth 0 gi_point_error_bounds k)%r / gi_probability_scale%r.

lemma gi_scaled_point_error (R M lift count lo hi error : int) (p : real) :
  0 < R => 0 < M => R = M * lift =>
  ei_contains R (lo, hi) p =>
  count * lift - lo <= error => hi - count * lift <= error =>
  `|count%r / M%r - p| <= error%r / R%r.
proof.
  move=> hR hM hscale hp hlo hhi.
  have hRr : 0%r < R%r by rewrite lt_fromint.
  have hMr : 0%r < M%r by rewrite lt_fromint.
  have hscale_real : R%r = M%r * lift%r by rewrite hscale fromintM.
  have hmass : R%r * (count%r / M%r) = (count * lift)%r.
  + rewrite fromintM hscale_real; field; smt().
  have he : R%r * (error%r / R%r) = error%r by field; smt().
  have hlow : (count * lift)%r - lo%r <= error%r
    by rewrite -fromintB le_fromint.
  have hhigh : hi%r - (count * lift)%r <= error%r
    by rewrite -fromintB le_fromint.
  rewrite ler_norml; move: hp; rewrite /ei_contains /=; smt().
qed.

lemma gi_point_error_transport k (p : real) :
  0 <= k < 256 =>
  ei_contains gi_probability_scale (nth witness gi_pmf_bounds k) p =>
  `|mu1 (cdt_distribution cdt83_modulus cdt83_thresholds) k - p| <= gi_error k.
proof.
  move=> hk hp.
  have hchecked := gi_point_errors_checked.
  rewrite allP in hchecked.
  have [he0 [hlo hhi]] := hchecked k _; first by rewrite mem_iota /=; smt().
  clear hchecked he0.
  rewrite (gi_actual_counts k hk) /gi_error.
  apply (gi_scaled_point_error gi_probability_scale gi_input_size 35184372088832
    (nth 0 gi_probability_counts k) (nth witness gi_pmf_bounds k).`1
    (nth witness gi_pmf_bounds k).`2 (nth 0 gi_point_error_bounds k) p).
  + by rewrite /gi_probability_scale.
  + by rewrite /gi_input_size.
  + by rewrite /gi_probability_scale /gi_input_size.
  + exact hp.
  + exact hlo.
  exact hhi.
qed.

lemma gi_error_sum_exact :
  interval_error_sum 256 gi_error =
    (Bigint.BIA.big predT (fun x => x) gi_point_error_bounds)%r / gi_probability_scale%r.
proof.
  have hsize : size gi_point_error_bounds = 256 by have := gi_dimensions; smt().
  have hlist := mkseq_nth 0 gi_point_error_bounds.
  rewrite /mkseq in hlist.
  have hsum := Bigreal.BRA.big_mapT (nth 0 gi_point_error_bounds)
    (fun (x : int) => x%r / gi_probability_scale%r) (iota_ 0 (size gi_point_error_bounds)).
  rewrite hlist /= in hsum.
  rewrite /interval_error_sum /gi_error -hsize -hsum.
  by rewrite Bigreal.sumr_ofint Bigreal.BRA.divr_suml.
qed.

lemma gi_budget_transfer (M R E T : int) :
  0 < M => 0 < R => M * (E + T) < 64 * R =>
  (E%r / R%r + T%r / R%r) / 2%r < 32%r / M%r.
proof.
  move=> hM hR hbudget.
  have hm : 0%r < M%r by rewrite lt_fromint.
  have hr : 0%r < R%r by rewrite lt_fromint.
  have hb : M%r * (E%r + T%r) < 64%r * R%r.
  + by rewrite -fromintD -!fromintM lt_fromint.
  rewrite ltr_pdivl_mulr 1:hm.
  have he : (E%r / R%r + T%r / R%r) / 2%r * M%r =
      (M%r * (E%r + T%r)) / (2%r * R%r).
  + by rewrite invrM; smt().
  rewrite he ltr_pdivr_mulr 1:(mulr_gt0 _ _ _ hr) 1://.
  smt().
qed.

lemma gi_error_budget :
  (interval_error_sum 256 gi_error +
    gi_tail_probability_upper%r / gi_probability_scale%r) / 2%r <
      32%r / gi_input_size%r.
proof.
  rewrite gi_error_sum_exact.
  apply (gi_budget_transfer gi_input_size gi_probability_scale
    (Bigint.BIA.big predT (fun x => x) gi_point_error_bounds) gi_tail_probability_upper).
  + by rewrite /gi_input_size.
  + by rewrite /gi_probability_scale.
  exact gi_statistical_distance_budget_checked.
qed.
