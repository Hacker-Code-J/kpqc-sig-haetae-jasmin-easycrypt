require import AllCore IntDiv List Distr DInterval StdOrder.
from Jasmin require import JModel_x86.
require import Rejection48Spec FixedPointCorrectness SigmaSpec.
import IntOrder RealOrder RField.

lemma rejection48_low_bit (w : W64.t) :
  w `&` W64.one = W64.of_int (b2i (odd (W64.to_uint w))).
proof.
have -> : W64.one = W64.of_int (2^1 - 1) by trivial.
by rewrite W64.and_mod 1:// /= modz2.
qed.

lemma rejection48_clear_low_bit (w : W64.t) :
  w `^` (w `&` W64.one) = W64.of_int (2 * (W64.to_uint w %/ 2)).
proof.
rewrite -W64.subw_xorw.
+ by rewrite W64.andwA (W64.andwC (W64.invw w)) W64.andw_invw W64.and0w.
have hmask : w `&` W64.one = W64.of_int (W64.to_uint w %% 2).
+ have -> : W64.one = W64.of_int (2^1 - 1) by trivial.
  by rewrite W64.and_mod 1://.
rewrite hmask -{1}(W64.to_uintK w) -W64.of_intS.
congr; have h := divz_eq (W64.to_uint w) 2; smt().
qed.

lemma rejection48_compare_mask (v threshold : int) :
  0 <= v < 281474976710656 => 0 <= threshold < 9223372036854775808 =>
  ((W64.of_int v - W64.of_int threshold) `|>>>` 63) =
    if v < threshold then W64.onew else W64.zero.
proof.
move=> hv he.
rewrite -W64.of_intS w64_sign_mask W64.of_uintK /=.
case (v < threshold) => hc.
+ have hm : (v - threshold) %% 18446744073709551616 =
      v - threshold + 18446744073709551616.
  - have -> : v - threshold = (-1) * 18446744073709551616 +
        (v - threshold + 18446744073709551616) by ring.
    rewrite modzMDl modz_small 1:/#; ring.
  rewrite hm.
  have -> : 9223372036854775808 <= v - threshold + 18446744073709551616 by smt().
  trivial.
rewrite modz_small 1:/#.
have -> : !(9223372036854775808 <= v - threshold) by smt().
trivial.
qed.

lemma rejection48_word_correct (u threshold : int) (rounded : W64.t) :
  0 <= u < 281474976710656 => 0 <= threshold < 9223372036854775808 =>
  rejection48_word (W64.of_int u) (W64.of_int threshold) rounded =
    W64.of_int (b2i (rejection48_accept u threshold rounded)).
proof.
move=> hu he.
have huword : W64.to_uint (W64.of_int u) = u by rewrite W64.to_uint_small 1:/#.
have hd := divz_eq u 2.
have hr := modz_cmp u 2.
have hv : 0 <= 2 * (u %/ 2) < 281474976710656 by smt().
have hnz : (W64.to_uint rounded <> 0) = (rounded <> W64.zero) by
  rewrite W64.to_uint_eq W64.to_uint0.
rewrite /rejection48_word rejection48_clear_low_bit huword
  rejection48_compare_mask 1:hv 1:he w64_nonzero_carry hnz.
case (2 * (u %/ 2) < threshold) => hc.
+ rewrite /rejection48_accept hc /b2i /=.
  case (rounded = W64.zero) => hz.
  - by rewrite ?hz /= ?W64.or0w rejection48_low_bit ?huword /b2i.
  rewrite ?hz /= W64.andw_orwDl W64.andwK rejection48_low_bit ?huword.
  case (odd u); by rewrite /b2i /= ?W64.orwK ?W64.orw0.
by rewrite /rejection48_accept hc /b2i /= ?W64.and0w.
qed.

lemma rejection48_word_event (u threshold : int) (rounded : W64.t) :
  0 <= u < 281474976710656 => 0 <= threshold < 9223372036854775808 =>
  (rejection48_word (W64.of_int u) (W64.of_int threshold) rounded = W64.one) =
    rejection48_accept u threshold rounded.
proof.
move=> hu he; rewrite rejection48_word_correct 1:hu 1:he.
rewrite W64.to_uint_eq.
case (rejection48_accept u threshold rounded); by rewrite /b2i !W64.of_uintK /=.
qed.

lemma rejection48_count_odd_pairs c : 0 <= c =>
  count odd (range 0 (2 * c)) = c.
proof.
move: c; apply intind.
+ by rewrite /= range_geq.
move=> c hc ih; rewrite /= in ih; rewrite /=.
rewrite (range_cat (2 * c)) 1:/# 1:/# count_cat ih.
have ht : range (2 * c) (2 * (c + 1)) = [2 * c; 2 * c + 1].
+ rewrite /range.
  have -> : 2 * (c + 1) - 2 * c = 2 by ring.
  by rewrite (iotaS _ 1) 1:// iota1.
by rewrite ht /= oddD !oddM odd2 odd1 /b2i /=.
qed.

lemma rejection48_guard_count c (rounded : W64.t) : 0 <= c =>
  count (fun u => rounded <> W64.zero \/ odd u) (range 0 (2 * c)) =
    if rounded = W64.zero then c else 2 * c.
proof.
move=> hc; case (rounded = W64.zero) => hz.
+ by rewrite /= rejection48_count_odd_pairs.
rewrite count_predT_eq 1:/# size_range; smt().
qed.

lemma rejection48_prefix_count c (rounded : W64.t) :
  0 <= c <= 140737488355328 =>
  count (fun u => u < 2 * c /\ (rounded <> W64.zero \/ odd u))
    (range 0 281474976710656) =
    if rounded = W64.zero then c else 2 * c.
proof.
move=> hc; rewrite (range_cat (2 * c)) 1:/# 1:/# count_cat.
have hhead :
    count (fun u => u < 2 * c /\ (rounded <> W64.zero \/ odd u)) (range 0 (2 * c)) =
    count (fun u => rounded <> W64.zero \/ odd u) (range 0 (2 * c)).
+ apply eq_in_count => u; rewrite mem_range; smt().
have htail :
    count (fun u => u < 2 * c /\ (rounded <> W64.zero \/ odd u))
      (range (2 * c) 281474976710656) = 0.
+ apply count_pred0_eq_in => u; rewrite mem_range; smt().
by rewrite hhead htail /= rejection48_guard_count 1:/#.
qed.

lemma rejection48_uniform_probability threshold rounded :
  mu rejection48_uniform (fun u => rejection48_accept u threshold rounded) =
    rejection48_probability threshold rounded.
proof.
rewrite /rejection48_uniform DInterval.dinterE /= size_filter.
have hcount :
    count (fun u => rejection48_accept u threshold rounded) (range 0 281474976710656) =
    count (fun u => u < 2 * rejection48_cutoff threshold /\
      (rounded <> W64.zero \/ odd u)) (range 0 281474976710656).
+ apply eq_in_count => u; rewrite mem_range => hu.
  by rewrite /= rejection48_accept_cutoff 1:/#.
rewrite hcount rejection48_prefix_count 1:rejection48_cutoff_bounds
  /rejection48_probability /rejection48_factor /rejection48_base_probability.
case (rounded = W64.zero) => hz; rewrite ?hz /max /= ?fromintM /=; try field; trivial.
qed.

lemma rejection48_word_probability threshold rounded :
  0 <= threshold < 9223372036854775808 =>
  mu rejection48_uniform
    (fun u => rejection48_word (W64.of_int u) (W64.of_int threshold) rounded = W64.one) =
    rejection48_probability threshold rounded.
proof.
move=> he; rewrite -rejection48_uniform_probability.
apply mu_eq_support => u.
rewrite /rejection48_uniform DInterval.supp_dinter => hu.
by rewrite /= rejection48_word_event 1:/# 1:he.
qed.

lemma rejection48_word_probability_error threshold rounded (p epsilon : real) :
  0 <= threshold < 9223372036854775808 => 0%r <= p <= 1%r =>
  `|threshold%r / 281474976710656%r - p| <= epsilon =>
  `|mu rejection48_uniform
      (fun u => rejection48_word (W64.of_int u) (W64.of_int threshold) rounded = W64.one)
    - rejection48_factor rounded * p| <=
    rejection48_factor rounded * (epsilon + 1%r / 281474976710656%r).
proof.
move=> he hp herr.
rewrite rejection48_word_probability 1:he.
exact (rejection48_probability_error threshold rounded p epsilon hp herr).
qed.

(* Definition-level binding to the actual SigmaSpec acceptance expression;
   the fixed threshold and rounded word depend on the candidate bytes. *)
lemma sigma_from_cdt_rejection48 (p : BArray26.t) (x : W64.t) :
  let y0 = le6_word p 17 in
  let y1 = le3_word p 23 `|` (x `<<<` 24) in
  let rounded = (((y0 `>>>` 15) + W64.one) `>>>` 1) + (y1 `<<<` 32) in
  let sq = square_word y0 y1 in
  let ei = ((((sq.`2 - ((x * x) `<<<` 20)) `<<<` 20) `|`
       (sq.`1 `>>>` 28)) + W64.one) `>>>` 1 in
  (sigma_from_cdt p x).`4 =
    rejection48_word (le6_word p 11) (FixedPointSpec.approx_exp_word ei) rounded.
proof. by rewrite /sigma_from_cdt /rejection48_word /=. qed.
