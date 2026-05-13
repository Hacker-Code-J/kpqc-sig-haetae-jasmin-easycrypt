require import AllCore Real RealExp StdOrder.
require import HAETAE_Events.

theory HAETAE_Reductions.

import HAETAE_Events.
import RealOrder.

op mlwe_hardness_term : real.
op module_sis_hardness_term : real.
op bimodal_to_msis_reduction_loss_term : real = 0%r.

op bimodal_selftarget_msis_hardness_term =
  module_sis_hardness_term + bimodal_to_msis_reduction_loss_term.

op signature_query_count : real = 2%r.
op hash_query_count : real = 2%r.
op signature_query_budget_count : int = 2.
op hash_query_budget_count : int = 2.
op abort_probability : real = 0%r.
op min_entropy_loss_factor : real = 2%r.
op challenge_support_bits_lower_bound : int = 58.
op challenge_support_cardinality_lower_bound : real =
  288230376151711744%r.

op rom_hash_query_budget : real = hash_query_count.
op rom_signature_query_budget : real = signature_query_count.
op rom_total_query_budget =
  rom_hash_query_budget + rom_signature_query_budget + 1%r.

op counted_rom_collision_term =
  (rom_total_query_budget * rom_total_query_budget) /
    challenge_support_cardinality_lower_bound.

op counted_rom_prequery_term =
  (rom_signature_query_budget * (rom_hash_query_budget + 1%r)) /
    challenge_support_cardinality_lower_bound.

op counted_rom_min_entropy_term =
  (rom_signature_query_budget * (rom_hash_query_budget + 1%r)) /
    challenge_support_cardinality_lower_bound.

op counted_rom_prequery_reprogramming_term =
  counted_rom_collision_term + counted_rom_prequery_term.

op counted_rom_programming_loss_term =
  counted_rom_collision_term +
  counted_rom_prequery_term +
  counted_rom_min_entropy_term.

op signing_query_scale =
  signature_query_count / (1%r - abort_probability).

op fs_with_aborts_reprogramming_term =
  sqrt signing_query_scale *
    (hash_query_count + 1%r + sqrt signing_query_scale).

op fs_with_aborts_min_entropy_term =
  min_entropy_loss_factor *
    (signing_query_scale * (hash_query_count + 1%r)).

op rejection_sampling_loss_term =
  fs_with_aborts_reprogramming_term + fs_with_aborts_min_entropy_term.

op haetae_euf_bound =
  mlwe_hardness_term +
  bimodal_selftarget_msis_hardness_term +
  rejection_sampling_loss_term.

op haetae_euf_counted_rom_bound =
  mlwe_hardness_term +
  bimodal_selftarget_msis_hardness_term +
  counted_rom_programming_loss_term.

lemma haetae_euf_boundE :
  haetae_euf_bound =
    mlwe_hardness_term +
    module_sis_hardness_term +
    bimodal_to_msis_reduction_loss_term +
    fs_with_aborts_reprogramming_term +
    fs_with_aborts_min_entropy_term.
proof.
by rewrite /haetae_euf_bound /bimodal_selftarget_msis_hardness_term
           /rejection_sampling_loss_term; ring.
qed.

lemma haetae_euf_bound_groupedE :
  haetae_euf_bound =
    (mlwe_hardness_term +
      (module_sis_hardness_term + bimodal_to_msis_reduction_loss_term)) +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term).
proof.
by rewrite /haetae_euf_bound /bimodal_selftarget_msis_hardness_term
           /rejection_sampling_loss_term; ring.
qed.

lemma haetae_euf_bound_rejection_groupedE :
  haetae_euf_bound =
    (mlwe_hardness_term +
      (module_sis_hardness_term + bimodal_to_msis_reduction_loss_term)) +
    rejection_sampling_loss_term.
proof.
by rewrite /haetae_euf_bound /bimodal_selftarget_msis_hardness_term; ring.
qed.

lemma haetae_euf_counted_rom_bound_groupedE :
  haetae_euf_counted_rom_bound =
    (mlwe_hardness_term +
      (module_sis_hardness_term + bimodal_to_msis_reduction_loss_term)) +
    counted_rom_programming_loss_term.
proof.
by rewrite /haetae_euf_counted_rom_bound
           /bimodal_selftarget_msis_hardness_term; ring.
qed.

lemma signing_query_scaleE :
  signing_query_scale = signature_query_count.
proof.
by rewrite /signing_query_scale /signature_query_count /abort_probability; ring.
qed.

lemma signing_query_scale_nonnegative :
  0%r <= signing_query_scale.
proof.
by rewrite signing_query_scaleE /signature_query_count.
qed.

lemma fs_with_aborts_reprogramming_term_nonnegative :
  0%r <= fs_with_aborts_reprogramming_term.
proof.
rewrite /fs_with_aborts_reprogramming_term.
apply mulr_ge0.
+ by apply ge0_sqrt.
rewrite addr_ge0.
+ by rewrite addr_ge0 /hash_query_count.
+ by apply ge0_sqrt.
qed.

lemma fs_with_aborts_min_entropy_term_nonnegative :
  0%r <= fs_with_aborts_min_entropy_term.
proof.
rewrite /fs_with_aborts_min_entropy_term.
apply mulr_ge0.
+ by rewrite /min_entropy_loss_factor.
apply mulr_ge0.
+ by apply signing_query_scale_nonnegative.
by rewrite addr_ge0 /hash_query_count.
qed.

lemma rom_hash_query_budget_nonnegative :
  0%r <= rom_hash_query_budget.
proof. by rewrite /rom_hash_query_budget /hash_query_count. qed.

lemma rom_signature_query_budget_nonnegative :
  0%r <= rom_signature_query_budget.
proof. by rewrite /rom_signature_query_budget /signature_query_count. qed.

lemma hash_query_budget_countE :
  hash_query_count = (hash_query_budget_count)%r.
proof. by rewrite /hash_query_count /hash_query_budget_count. qed.

lemma signature_query_budget_countE :
  signature_query_count = (signature_query_budget_count)%r.
proof. by rewrite /signature_query_count /signature_query_budget_count. qed.

lemma hash_query_budget_count_nonnegative :
  0 <= hash_query_budget_count.
proof. by rewrite /hash_query_budget_count. qed.

lemma signature_query_budget_count_nonnegative :
  0 <= signature_query_budget_count.
proof. by rewrite /signature_query_budget_count. qed.

lemma min_entropy_loss_factor_nonnegative :
  0%r <= min_entropy_loss_factor.
proof. by rewrite /min_entropy_loss_factor. qed.

lemma challenge_support_cardinality_lower_bound_positive :
  0%r < challenge_support_cardinality_lower_bound.
proof. by rewrite /challenge_support_cardinality_lower_bound. qed.

lemma challenge_support_cardinality_lower_bound_nonnegative :
  0%r <= challenge_support_cardinality_lower_bound.
proof.
by apply ltrW; apply challenge_support_cardinality_lower_bound_positive.
qed.

lemma rom_total_query_budget_nonnegative :
  0%r <= rom_total_query_budget.
proof.
rewrite /rom_total_query_budget.
apply addr_ge0.
+ by apply addr_ge0;
     [apply rom_hash_query_budget_nonnegative
     | apply rom_signature_query_budget_nonnegative].
+ by [].
qed.

lemma counted_rom_collision_term_nonnegative :
  0%r <= counted_rom_collision_term.
proof.
rewrite /counted_rom_collision_term.
apply divr_ge0.
+ by apply mulr_ge0; apply rom_total_query_budget_nonnegative.
by apply challenge_support_cardinality_lower_bound_nonnegative.
qed.

lemma counted_rom_prequery_term_nonnegative :
  0%r <= counted_rom_prequery_term.
proof.
rewrite /counted_rom_prequery_term.
apply divr_ge0.
+ apply mulr_ge0.
  + by apply rom_signature_query_budget_nonnegative.
  by apply addr_ge0; [apply rom_hash_query_budget_nonnegative |].
by apply challenge_support_cardinality_lower_bound_nonnegative.
qed.

lemma counted_rom_min_entropy_term_nonnegative :
  0%r <= counted_rom_min_entropy_term.
proof.
rewrite /counted_rom_min_entropy_term.
apply divr_ge0.
+ apply mulr_ge0.
  + by apply rom_signature_query_budget_nonnegative.
  by apply addr_ge0; [apply rom_hash_query_budget_nonnegative |].
by apply challenge_support_cardinality_lower_bound_nonnegative.
qed.

lemma counted_rom_prequery_reprogramming_term_nonnegative :
  0%r <= counted_rom_prequery_reprogramming_term.
proof.
rewrite /counted_rom_prequery_reprogramming_term.
by apply addr_ge0;
   [apply counted_rom_collision_term_nonnegative
   | apply counted_rom_prequery_term_nonnegative].
qed.

lemma counted_rom_programming_loss_term_nonnegative :
  0%r <= counted_rom_programming_loss_term.
proof.
rewrite /counted_rom_programming_loss_term.
apply addr_ge0.
+ by apply addr_ge0;
     [apply counted_rom_collision_term_nonnegative
     | apply counted_rom_prequery_term_nonnegative].
+ by apply counted_rom_min_entropy_term_nonnegative.
qed.

lemma counted_rom_collision_termE :
  counted_rom_collision_term =
    25%r / challenge_support_cardinality_lower_bound.
proof.
by rewrite /counted_rom_collision_term
           /rom_total_query_budget
           /rom_hash_query_budget
           /rom_signature_query_budget
           /hash_query_count
           /signature_query_count; ring.
qed.

lemma counted_rom_prequery_termE :
  counted_rom_prequery_term =
    6%r / challenge_support_cardinality_lower_bound.
proof.
by rewrite /counted_rom_prequery_term
           /rom_signature_query_budget
           /rom_hash_query_budget
           /hash_query_count
           /signature_query_count; ring.
qed.

lemma counted_rom_min_entropy_termE :
  counted_rom_min_entropy_term =
    6%r / challenge_support_cardinality_lower_bound.
proof.
by rewrite /counted_rom_min_entropy_term
           /rom_signature_query_budget
           /rom_hash_query_budget
           /hash_query_count
           /signature_query_count; ring.
qed.

lemma counted_rom_prequery_reprogramming_termE :
  counted_rom_prequery_reprogramming_term =
    31%r / challenge_support_cardinality_lower_bound.
proof.
by rewrite /counted_rom_prequery_reprogramming_term
           counted_rom_collision_termE
           counted_rom_prequery_termE; ring.
qed.

lemma counted_rom_programming_loss_termE :
  counted_rom_programming_loss_term =
    37%r / challenge_support_cardinality_lower_bound.
proof.
by rewrite /counted_rom_programming_loss_term
           counted_rom_collision_termE
           counted_rom_prequery_termE
           counted_rom_min_entropy_termE; ring.
qed.

lemma counted_rom_programming_loss_term_subunit :
  counted_rom_programming_loss_term < 1%r.
proof.
rewrite counted_rom_programming_loss_termE.
rewrite ltr_pdivr_mulr.
+ by apply challenge_support_cardinality_lower_bound_positive.
by rewrite /challenge_support_cardinality_lower_bound.
qed.

lemma counted_rom_programming_loss_term_positive :
  0%r < counted_rom_programming_loss_term.
proof.
rewrite counted_rom_programming_loss_termE.
apply divr_gt0.
+ by [].
by apply challenge_support_cardinality_lower_bound_positive.
qed.

lemma counted_rom_programming_loss_term_le1 :
  1%r >= counted_rom_programming_loss_term.
proof.
by apply ltrW; apply counted_rom_programming_loss_term_subunit.
qed.

lemma counted_rom_prequery_reprogramming_budget_numeratorE :
  (rom_total_query_budget * rom_total_query_budget) +
  (rom_signature_query_budget * (rom_hash_query_budget + 1%r)) =
  31%r.
proof.
by rewrite /rom_total_query_budget
           /rom_hash_query_budget
           /rom_signature_query_budget
           /hash_query_count
           /signature_query_count; ring.
qed.

lemma counted_rom_budget_numeratorE :
  (rom_total_query_budget * rom_total_query_budget) +
  (rom_signature_query_budget * (rom_hash_query_budget + 1%r)) +
  (rom_signature_query_budget * (rom_hash_query_budget + 1%r)) =
  37%r.
proof.
by rewrite /rom_total_query_budget
           /rom_hash_query_budget
           /rom_signature_query_budget
           /hash_query_count
           /signature_query_count; ring.
qed.

lemma counted_rom_programming_loss_term_cardinalityE :
  counted_rom_programming_loss_term =
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r)) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound.
proof.
by rewrite counted_rom_programming_loss_termE
           counted_rom_budget_numeratorE.
qed.

lemma counted_rom_prequery_reprogramming_term_cardinalityE :
  counted_rom_prequery_reprogramming_term =
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound.
proof.
by rewrite counted_rom_prequery_reprogramming_termE
           counted_rom_prequery_reprogramming_budget_numeratorE.
qed.

lemma counted_rom_programming_loss_term_concreteE :
  counted_rom_programming_loss_term =
    37%r / 288230376151711744%r.
proof.
by rewrite counted_rom_programming_loss_termE
           /challenge_support_cardinality_lower_bound.
qed.

lemma counted_rom_prequery_reprogramming_term_concreteE :
  counted_rom_prequery_reprogramming_term =
    31%r / 288230376151711744%r.
proof.
by rewrite counted_rom_prequery_reprogramming_termE
           /challenge_support_cardinality_lower_bound.
qed.

lemma counted_rom_programming_loss_term_checked_subunit :
  0%r < counted_rom_programming_loss_term /\
  counted_rom_programming_loss_term < 1%r /\
  counted_rom_programming_loss_term =
    37%r / 288230376151711744%r.
proof.
split.
+ by apply counted_rom_programming_loss_term_positive.
split.
+ by apply counted_rom_programming_loss_term_subunit.
by apply counted_rom_programming_loss_term_concreteE.
qed.

lemma counted_rom_support_lower_bound_summary :
  challenge_support_bits_lower_bound = 58 /\
  challenge_support_cardinality_lower_bound =
    288230376151711744%r.
proof.
split.
+ by rewrite /challenge_support_bits_lower_bound.
by rewrite /challenge_support_cardinality_lower_bound.
qed.

lemma counted_rom_support_dominates_budget :
  37%r < challenge_support_cardinality_lower_bound.
proof. by rewrite /challenge_support_cardinality_lower_bound. qed.

lemma counted_rom_prequery_reprogramming_support_dominates_budget :
  31%r < challenge_support_cardinality_lower_bound.
proof. by rewrite /challenge_support_cardinality_lower_bound. qed.

lemma counted_rom_prequery_reprogramming_term_subunit :
  counted_rom_prequery_reprogramming_term < 1%r.
proof.
rewrite counted_rom_prequery_reprogramming_termE.
rewrite ltr_pdivr_mulr.
+ by apply challenge_support_cardinality_lower_bound_positive.
by apply counted_rom_prequery_reprogramming_support_dominates_budget.
qed.

lemma counted_rom_prequery_reprogramming_from_query_budgets_and_support :
  counted_rom_prequery_reprogramming_term =
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound /\
  ((rom_total_query_budget * rom_total_query_budget) +
   (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) <
  challenge_support_cardinality_lower_bound.
proof.
split.
+ by apply counted_rom_prequery_reprogramming_term_cardinalityE.
rewrite counted_rom_prequery_reprogramming_budget_numeratorE.
by apply counted_rom_prequery_reprogramming_support_dominates_budget.
qed.

lemma counted_rom_programming_loss_splitE :
  counted_rom_programming_loss_term =
    counted_rom_prequery_reprogramming_term +
    counted_rom_min_entropy_term.
proof.
by rewrite /counted_rom_programming_loss_term
           /counted_rom_prequery_reprogramming_term; ring.
qed.

lemma counted_rom_loss_from_query_budgets_and_support :
  counted_rom_programming_loss_term =
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r)) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound /\
  ((rom_total_query_budget * rom_total_query_budget) +
   (rom_signature_query_budget * (rom_hash_query_budget + 1%r)) +
   (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) <
  challenge_support_cardinality_lower_bound.
proof.
split.
+ by apply counted_rom_programming_loss_term_cardinalityE.
rewrite counted_rom_budget_numeratorE.
by apply counted_rom_support_dominates_budget.
qed.

lemma rejection_sampling_loss_term_nonnegative :
  0%r <= rejection_sampling_loss_term.
proof.
rewrite /rejection_sampling_loss_term.
by apply addr_ge0; [apply fs_with_aborts_reprogramming_term_nonnegative
                  | apply fs_with_aborts_min_entropy_term_nonnegative].
qed.

lemma fs_with_aborts_min_entropy_termE :
  fs_with_aborts_min_entropy_term = 12%r.
proof.
by rewrite /fs_with_aborts_min_entropy_term /min_entropy_loss_factor
           signing_query_scaleE /signature_query_count /hash_query_count; ring.
qed.

lemma fs_with_aborts_min_entropy_term_ge1 :
  1%r <= fs_with_aborts_min_entropy_term.
proof.
by rewrite fs_with_aborts_min_entropy_termE.
qed.

lemma rejection_sampling_loss_term_ge1 :
  1%r <= rejection_sampling_loss_term.
proof.
rewrite /rejection_sampling_loss_term.
smt(fs_with_aborts_min_entropy_term_ge1
    fs_with_aborts_reprogramming_term_nonnegative).
qed.

lemma bimodal_to_msis_reduction_loss_termE :
  bimodal_to_msis_reduction_loss_term = 0%r.
proof. by rewrite /bimodal_to_msis_reduction_loss_term. qed.

end HAETAE_Reductions.
