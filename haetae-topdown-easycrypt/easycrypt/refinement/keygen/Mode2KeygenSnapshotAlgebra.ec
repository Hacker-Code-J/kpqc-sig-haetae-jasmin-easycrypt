require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import KeygenM23FinalizeSemantics KeygenM23FinalizeArraySemantics.

theory Mode2KeygenSnapshotAlgebra.

op q : int = KeygenM23FinalizeSemantics.q.
op q2 : int = 2 * q.

op congruent_mod_2q (x y : int) : bool =
  (x - y) %% q2 = 0.

op raw_sum_from_product (mul e a : int) : int =
  mul + e + a.

op raw_residue_from_product (mul e a : int) : int =
  raw_sum_from_product mul e a %% q.

op snapshot_low (r : int) : int =
  KeygenM23FinalizeSemantics.vk_low_int r.

op snapshot_high (r : int) : int =
  KeygenM23FinalizeSemantics.vk_high_int r.

op residue_low_from_product (mul e a : int) : int =
  snapshot_low (raw_residue_from_product mul e a).

op residue_high_from_product (mul e a : int) : int =
  snapshot_high (raw_residue_from_product mul e a).

op adjusted_from_product (mul e a : int) : int =
  e - residue_low_from_product mul e a.

op snapshot_expression_from_product (mul e a j : int) : int =
  2 * (a - 2 * residue_high_from_product mul e a) +
  q * j + 2 * mul + 2 * adjusted_from_product mul e a.

lemma array_raw_sum_matches_from_product (b s2 a : W32.t) :
  raw_sum_from_product (W32.to_sint b) (W32.to_sint s2) (W32.to_uint a) =
  KeygenM23FinalizeArraySemantics.raw_sum_int b s2 a.
proof.
by rewrite /raw_sum_from_product
           /KeygenM23FinalizeArraySemantics.raw_sum_int.
qed.

lemma array_raw_residue_matches_from_product (b s2 a : W32.t) :
  raw_residue_from_product (W32.to_sint b) (W32.to_sint s2) (W32.to_uint a) =
  KeygenM23FinalizeArraySemantics.raw_residue b s2 a.
proof.
rewrite /raw_residue_from_product /KeygenM23FinalizeArraySemantics.raw_residue.
by rewrite array_raw_sum_matches_from_product /q.
qed.

lemma raw_residue_from_product_range (mul e a : int) :
  0 <= raw_residue_from_product mul e a < q.
proof.
rewrite /raw_residue_from_product /q.
apply modz_cmp.
by rewrite /KeygenM23FinalizeSemantics.q.
qed.

lemma snapshot_low_sub_even (r : int) :
  (r - snapshot_low r) %% 2 = 0.
proof.
rewrite /snapshot_low KeygenM23FinalizeSemantics.vk_low_int_formula.
have hr : 0 <= r %% 2 < 2 by smt(@IntDiv).
have hh : 0 <= (r %/ 2) %% 2 < 2 by smt(@IntDiv).
have hdiv := divz_eq r 2.
by smt(@IntDiv).
qed.

lemma snapshot_residue_decompose (r : int) :
  0 <= r < q =>
  r = 2 * snapshot_high r + snapshot_low r.
proof.
move=> hr.
rewrite /snapshot_high /KeygenM23FinalizeSemantics.vk_high_int.
have heven := snapshot_low_sub_even r.
by smt(@IntDiv).
qed.

lemma snapshot_residue_exact_low_high (r : int) :
  0 <= r < q =>
  r = 2 * snapshot_high r + snapshot_low r /\
  -1 <= snapshot_low r <= 1 /\
  0 <= snapshot_high r < 32768.
proof.
move=> hr.
split.
+ exact (snapshot_residue_decompose r hr).
split.
+ exact (KeygenM23FinalizeSemantics.vk_low_int_range r).
exact (KeygenM23FinalizeSemantics.vk_high_int_range r hr).
qed.

lemma raw_residue_from_product_decompose (mul e a : int) :
  raw_residue_from_product mul e a =
    2 * residue_high_from_product mul e a +
    residue_low_from_product mul e a.
proof.
apply (snapshot_residue_decompose (raw_residue_from_product mul e a)).
exact (raw_residue_from_product_range mul e a).
qed.

lemma raw_sum_double_minus_residue_double (mul e a : int) :
  2 * raw_sum_from_product mul e a -
  2 * raw_residue_from_product mul e a =
    q2 * (raw_sum_from_product mul e a %/ q).
proof.
rewrite /raw_residue_from_product /raw_sum_from_product /q2 /q.
have hdiv := divz_eq (mul + e + a) KeygenM23FinalizeSemantics.q.
by smt().
qed.

lemma raw_sum_raw_residue_congruent_mod_2q (mul e a : int) :
  congruent_mod_2q
    (2 * raw_sum_from_product mul e a)
    (2 * raw_residue_from_product mul e a).
proof.
rewrite /congruent_mod_2q raw_sum_double_minus_residue_double.
by smt(divz_eq).
qed.

lemma snapshot_expression_from_product_diff (mul e a j : int) :
  snapshot_expression_from_product mul e a j - q * j =
    2 * raw_sum_from_product mul e a -
    2 * raw_residue_from_product mul e a.
proof.
rewrite /snapshot_expression_from_product
        /adjusted_from_product
        /residue_low_from_product
        /residue_high_from_product.
have hdecomp := raw_residue_from_product_decompose mul e a.
by smt().
qed.

lemma snapshot_expression_from_product_congruent_mod_2q
    (mul e a j : int) :
  congruent_mod_2q
    (snapshot_expression_from_product mul e a j)
    (q * j).
proof.
rewrite /congruent_mod_2q snapshot_expression_from_product_diff.
rewrite raw_sum_double_minus_residue_double.
by smt(divz_eq).
qed.

end Mode2KeygenSnapshotAlgebra.
