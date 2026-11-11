require import AllCore IntDiv List StdBigop StdRing.
require import ExpIntervalSpec CDTDistributionSpec CDTGaussianCertificate.

(* These are checked finite integer identities.  No numerical result from
   Python is assumed: changing a certificate entry must preserve the checks. *)
lemma gi_dimensions :
  size gi_squaring_chain = 129 /\ size gi_weight_chain = 257 /\
  size gi_thresholds = 166 /\ size gi_probability_counts = 256 /\
  size gi_pmf_bounds = 256 /\ size gi_point_error_bounds = 256.
proof.
  by rewrite /gi_squaring_chain /gi_weight_chain /gi_thresholds
    /gi_probability_counts /gi_pmf_bounds /gi_point_error_bounds /=.
qed.

lemma gi_indices256 :
  iota_ 0 256 = mapi (fun i (_ : int) => i) gi_probability_counts.
proof.
  have hsize : size gi_probability_counts = 256 by have := gi_dimensions; smt().
  apply (eq_from_nth 0).
  + by rewrite size_iota size_mapi hsize.
  move=> i; rewrite size_iota /= => hi.
  by rewrite nth_iota 1:hi (nth_mapi 0 _ 0 _ i) 1:/# /=.
qed.

lemma gi_positive_constants :
  0 < gi_scale /\ gi_seed_denominator = 2^137 /\ gi_cutoff = 256 /\
  gi_input_size = 2^83 /\ 0 < gi_probability_scale /\
  gi_probability_scale = gi_input_size * 35184372088832 /\
  0 < gi_normalizer_bounds.`1 <= gi_normalizer_bounds.`2 /\
  0 <= gi_tail_weight_upper /\ 0 <= gi_tail_probability_upper.
proof.
  rewrite /gi_scale /gi_seed_denominator /gi_cutoff /gi_input_size
    /gi_probability_scale /gi_normalizer_bounds
    /gi_tail_weight_upper /gi_tail_probability_upper /=.
  split; ring.
qed.

lemma gi_exp_seed_checked :
  ei_seed_ok gi_scale gi_seed_denominator (head witness gi_squaring_chain).
proof. by rewrite /ei_seed_ok /gi_scale /gi_seed_denominator /gi_squaring_chain /=. qed.

lemma gi_exp_squarings_checked : ei_square_check gi_scale gi_squaring_chain.
proof.
  by rewrite /gi_scale /gi_squaring_chain /ei_square_check /ei_square_steps_check /ei_mul /=.
qed.

lemma gi_gaussian_weights_checked :
  ei_weights_check gi_scale (last witness gi_squaring_chain) gi_weight_chain.
proof.
  by rewrite /gi_scale /gi_squaring_chain /gi_weight_chain /ei_weights_check
    /ei_weight_steps_check /ei_weight_step /ei_mul /=.
qed.

lemma gi_normalizer_checked :
  gi_normalizer_bounds.`1 =
    Bigint.BIA.big predT (fun (s : ei_weight_state) => s.`1.`1) (take 256 gi_weight_chain) /\
  gi_normalizer_bounds.`2 =
    Bigint.BIA.big predT (fun (s : ei_weight_state) => s.`1.`2) (take 256 gi_weight_chain)
      + gi_tail_weight_upper /\
  (nth witness gi_weight_chain 256).`2.`2 < gi_scale /\
  (nth witness gi_weight_chain 256).`1.`2 * gi_scale <=
    gi_tail_weight_upper * (gi_scale - (nth witness gi_weight_chain 256).`2.`2) /\
  gi_probability_scale * gi_tail_weight_upper <=
    gi_tail_probability_upper * gi_normalizer_bounds.`1.
proof.
  by rewrite /gi_normalizer_bounds /gi_weight_chain /gi_tail_weight_upper
    /gi_tail_probability_upper /gi_probability_scale /gi_scale /=.
qed.

lemma gi_pmf_intervals_checked :
  all (fun i =>
    0 <= (nth witness gi_pmf_bounds i).`1 /\
    0 <= (nth witness gi_pmf_bounds i).`2 /\
    (nth witness gi_pmf_bounds i).`1 * gi_normalizer_bounds.`2 <=
      gi_probability_scale * (nth witness gi_weight_chain i).`1.`1 /\
    gi_probability_scale * (nth witness gi_weight_chain i).`1.`2 <=
      (nth witness gi_pmf_bounds i).`2 * gi_normalizer_bounds.`1)
    (iota_ 0 256).
proof.
  by rewrite gi_indices256 /gi_probability_counts /mapi
    /gi_pmf_bounds /gi_normalizer_bounds /gi_probability_scale /gi_weight_chain /=.
qed.

lemma gi_probability_counts_checked :
  all (fun k => nth 0 gi_probability_counts k =
    if k <= 166 then cdt_bin_upper gi_input_size gi_thresholds k - cdt_bin_lower gi_thresholds k
    else 0) (iota_ 0 256).
proof.
  by rewrite gi_indices256 /gi_probability_counts /mapi /gi_thresholds /gi_input_size
    /cdt_bin_upper /cdt_bin_lower /=.
qed.

lemma gi_point_errors_checked :
  all (fun i =>
    0 <= nth 0 gi_point_error_bounds i /\
    nth 0 gi_probability_counts i * 35184372088832 - (nth witness gi_pmf_bounds i).`1 <=
      nth 0 gi_point_error_bounds i /\
    (nth witness gi_pmf_bounds i).`2 - nth 0 gi_probability_counts i * 35184372088832 <=
      nth 0 gi_point_error_bounds i)
    (iota_ 0 256).
proof.
  by rewrite gi_indices256 /gi_point_error_bounds /gi_probability_counts /mapi /gi_pmf_bounds /=.
qed.

lemma gi_statistical_distance_budget_checked :
  gi_input_size * (Bigint.BIA.big predT (fun x => x) gi_point_error_bounds
    + gi_tail_probability_upper) < 64 * gi_probability_scale.
proof.
  by rewrite /gi_input_size /gi_point_error_bounds /gi_tail_probability_upper
    /gi_probability_scale /=.
qed.
