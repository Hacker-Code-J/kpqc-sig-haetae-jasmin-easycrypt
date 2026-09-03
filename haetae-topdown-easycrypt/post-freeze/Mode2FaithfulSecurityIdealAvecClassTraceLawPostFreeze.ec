require import
  AllCore DList Distr DInterval IntDiv List Real Ring StdBigop StdOrder.

require import KeygenM23FinalizeSemantics.

import RealOrder.

theory Mode2FaithfulSecurityIdealAvecClassTraceLawPostFreeze.

(* Exact class counts and masses are proved below and independently checked by
   [check-mode2-ideal-avec-class-counts.py].  This theory keeps the formal
   carrier, the modular-shift uniformity bridge, the 512-coordinate ordered
   product law, and the independent-carrier marginals.  It does not identify
   actual SHAKE/ExpandVecA output with the ideal coefficient law, condition on
   acceptance, or assert independence inside the retained pre_bp/secret
   carrier. *)

op ideal_avec_q : int = 64513.

op ideal_avec_trace_rows : int = 2.
op ideal_avec_trace_words : int = 256.
op ideal_avec_trace_size : int =
  ideal_avec_trace_rows * ideal_avec_trace_words.

lemma ideal_avec_parameter_certificate :
  ideal_avec_q = KeygenM23FinalizeSemantics.q /\
  ideal_avec_trace_rows = 2 /\
  ideal_avec_trace_words = 256 /\
  ideal_avec_trace_size = 512.
proof.
by rewrite /ideal_avec_q /KeygenM23FinalizeSemantics.q
           /ideal_avec_trace_rows /ideal_avec_trace_words
           /ideal_avec_trace_size.
qed.

op ideal_avec_class2_count : int = 16127.
op ideal_avec_nonedge_class_count : int = 16128.

op ideal_avec_coefficient_distribution : int distr =
  dinter 0 (ideal_avec_q - 1).

op ideal_avec_shift (pre_bp avec : int) : int =
  (pre_bp + avec) %% ideal_avec_q.

op ideal_avec_class_index (rho : int) : int =
  if rho = 0 then 0
  else if rho = ideal_avec_q - 1 then 1
  else 2 + rho %% 4.

op ideal_avec_shifted_class_index (pre_bp avec : int) : int =
  ideal_avec_class_index (ideal_avec_shift pre_bp avec).

op ideal_avec_class_distribution : int distr =
  dmap ideal_avec_coefficient_distribution ideal_avec_class_index.

op ideal_avec_class_count (cls : int) : int =
  if cls = 0 then 1
  else if cls = 1 then 1
  else if cls = 2 then ideal_avec_class2_count
  else if cls = 3 then ideal_avec_nonedge_class_count
  else if cls = 4 then ideal_avec_nonedge_class_count
  else if cls = 5 then ideal_avec_nonedge_class_count
  else 0.

op ideal_avec_class_point_mass (cls : int) : real =
  (ideal_avec_class_count cls)%r / ideal_avec_q%r.

op ideal_avec_class0_values : int list = [0].
op ideal_avec_class1_values : int list = [ideal_avec_q - 1].
op ideal_avec_class2_values : int list =
  map (fun k => 4 * k) (range 1 ideal_avec_nonedge_class_count).
op ideal_avec_class3_values : int list =
  map (fun k => 4 * k + 1) (range 0 ideal_avec_nonedge_class_count).
op ideal_avec_class4_values : int list =
  map (fun k => 4 * k + 2) (range 0 ideal_avec_nonedge_class_count).
op ideal_avec_class5_values : int list =
  map (fun k => 4 * k + 3) (range 0 ideal_avec_nonedge_class_count).

op ideal_avec_shift_distribution (pre_bp : int) : int distr =
  dmap ideal_avec_coefficient_distribution (ideal_avec_shift pre_bp).

op ideal_avec_flat_class_distribution : int list distr =
  dlist ideal_avec_class_distribution ideal_avec_trace_size.

op ideal_avec_flat_to_rows (xs : int list) : int list list = [
  take ideal_avec_trace_words xs;
  take ideal_avec_trace_words (drop ideal_avec_trace_words xs)
].

op ideal_avec_flat_class_trace (xs : int list) : int list list =
  ideal_avec_flat_to_rows (map ideal_avec_class_index xs).

op ideal_avec_ordered_class_trace_distribution : int list list distr =
  dmap ideal_avec_flat_class_distribution ideal_avec_flat_to_rows.

op ideal_avec_flat_index (row j : int) : int =
  row * ideal_avec_trace_words + j.

op ideal_avec_ordered_class_trace_coordinate
    (row j : int) (rows : int list list) : int =
  nth 0 (nth [] rows row) j.

type ideal_mode2_prebp_secret_sample.

type ideal_mode2_independent_avec_carrier_sample =
  ideal_mode2_prebp_secret_sample * int list list.

op ideal_mode2_independent_avec_carrier_distribution
    (dpresec : ideal_mode2_prebp_secret_sample distr) :
    ideal_mode2_independent_avec_carrier_sample distr =
  dpresec `*` ideal_avec_ordered_class_trace_distribution.

op ideal_mode2_independent_avec_carrier_prebp_secret_marginal
    (djoint : ideal_mode2_independent_avec_carrier_sample distr) :
    ideal_mode2_prebp_secret_sample distr =
  dmap djoint
    (fun (sample : ideal_mode2_independent_avec_carrier_sample) =>
      sample.`1).

op ideal_mode2_independent_avec_carrier_trace_marginal
    (djoint : ideal_mode2_independent_avec_carrier_sample distr) :
    int list list distr =
  dmap djoint
    (fun (sample : ideal_mode2_independent_avec_carrier_sample) =>
      sample.`2).

op ideal_mode2_independent_avec_carrier_boundary
    (dpresec : ideal_mode2_prebp_secret_sample distr) : bool =
  is_lossless dpresec.

lemma ideal_avec_coefficient_lossless :
  is_lossless ideal_avec_coefficient_distribution.
proof. by rewrite /ideal_avec_coefficient_distribution; apply dinter_ll. qed.

lemma ideal_avec_coefficient_uniform :
  is_uniform ideal_avec_coefficient_distribution.
proof. by rewrite /ideal_avec_coefficient_distribution; apply dinter_uni. qed.

lemma ideal_avec_coefficient_support x :
  x \in ideal_avec_coefficient_distribution <=>
  0 <= x <= ideal_avec_q - 1.
proof.
by rewrite /ideal_avec_coefficient_distribution supp_dinter.
qed.

lemma ideal_avec_shift_cancel pre_bp avec :
  0 <= avec <= ideal_avec_q - 1 =>
  ((ideal_avec_shift pre_bp avec) - pre_bp) %% ideal_avec_q = avec.
proof.
move=> havec.
rewrite /ideal_avec_shift.
have -> :
    (((pre_bp + avec) %% ideal_avec_q) - pre_bp) %% ideal_avec_q =
    avec %% ideal_avec_q by smt(@IntDiv).
rewrite modz_small; smt().
qed.

lemma ideal_avec_shift_inverse pre_bp rho :
  0 <= rho <= ideal_avec_q - 1 =>
  ideal_avec_shift pre_bp ((rho - pre_bp) %% ideal_avec_q) = rho.
proof.
move=> hrho.
rewrite /ideal_avec_shift.
have -> :
    (pre_bp + ((rho - pre_bp) %% ideal_avec_q)) %% ideal_avec_q =
    rho %% ideal_avec_q by smt(@IntDiv).
rewrite modz_small; smt().
qed.

lemma ideal_avec_shift_support pre_bp rho :
  rho \in ideal_avec_shift_distribution pre_bp <=>
  0 <= rho <= ideal_avec_q - 1.
proof.
rewrite /ideal_avec_shift_distribution supp_dmap.
split.
+ move=> [avec [havec ->]].
   rewrite ideal_avec_coefficient_support in havec.
   rewrite /ideal_avec_shift.
   smt(@IntDiv).
move=> hrho.
exists ((rho - pre_bp) %% ideal_avec_q).
split.
+ rewrite ideal_avec_coefficient_support.
   smt(@IntDiv).
rewrite ideal_avec_shift_inverse //.
qed.

lemma ideal_avec_shift_uniform pre_bp :
  ideal_avec_shift_distribution pre_bp =
  ideal_avec_coefficient_distribution.
proof.
have hll1 : is_lossless (ideal_avec_shift_distribution pre_bp).
+ rewrite /ideal_avec_shift_distribution.
   by apply dmap_ll; exact ideal_avec_coefficient_lossless.
have hll2 := ideal_avec_coefficient_lossless.
have huni1 : is_uniform (ideal_avec_shift_distribution pre_bp).
+ rewrite /ideal_avec_shift_distribution.
   apply dmap_uni_in_inj.
   move=> avec1 avec2 h1 h2 heq.
   rewrite ideal_avec_coefficient_support in h1.
   rewrite ideal_avec_coefficient_support in h2.
   have hc1 := ideal_avec_shift_cancel pre_bp avec1 h1.
   have hc2 := ideal_avec_shift_cancel pre_bp avec2 h2.
   by rewrite -hc1 -hc2 heq.
   exact ideal_avec_coefficient_uniform.
have huni2 := ideal_avec_coefficient_uniform.
have hsupp :
    support (ideal_avec_shift_distribution pre_bp) =
    support ideal_avec_coefficient_distribution.
+ apply fun_ext => rho.
   rewrite ideal_avec_shift_support ideal_avec_coefficient_support.
   trivial.
apply/eq_distr => rho.
rewrite (mu1_uni (ideal_avec_shift_distribution pre_bp) rho huni1)
        (mu1_uni ideal_avec_coefficient_distribution rho huni2).
rewrite hll1 hll2 hsupp.
trivial.
qed.

lemma ideal_avec_shifted_class_distribution pre_bp :
  dmap ideal_avec_coefficient_distribution
    (ideal_avec_shifted_class_index pre_bp) =
  ideal_avec_class_distribution.
proof.
rewrite /ideal_avec_shifted_class_index /ideal_avec_class_distribution.
have -> :
    (fun avec => ideal_avec_class_index (ideal_avec_shift pre_bp avec)) =
    (ideal_avec_class_index \o ideal_avec_shift pre_bp).
+ by apply fun_ext => avec; rewrite /(\o).
rewrite -dmap_comp.
change
  (dmap (ideal_avec_shift_distribution pre_bp) ideal_avec_class_index =
   dmap ideal_avec_coefficient_distribution ideal_avec_class_index).
rewrite (ideal_avec_shift_uniform pre_bp).
trivial.
qed.

lemma ideal_avec_class_range rho :
  0 <= rho <= ideal_avec_q - 1 =>
  0 <= ideal_avec_class_index rho <= 5.
proof.
move=> hrho.
rewrite /ideal_avec_class_index.
case (rho = 0) => hrho0; first smt().
case (rho = ideal_avec_q - 1) => hrhoq1; first smt().
have hmod : 0 <= rho %% 4 < 4 by smt(@IntDiv).
smt().
qed.

lemma ideal_avec_class_distribution_support cls :
  cls \in ideal_avec_class_distribution => 0 <= cls <= 5.
proof.
rewrite /ideal_avec_class_distribution supp_dmap.
move=> [rho [hrho ->]].
rewrite ideal_avec_coefficient_support in hrho.
exact (ideal_avec_class_range rho hrho).
qed.

lemma ideal_avec_class_distribution_point_outside cls :
  !(0 <= cls <= 5) =>
  mu1 ideal_avec_class_distribution cls = 0%r.
proof.
move=> hcls.
rewrite -supportPn.
smt(ideal_avec_class_distribution_support).
qed.

lemma ideal_avec_class0_values_uniq :
  uniq ideal_avec_class0_values.
proof. by rewrite /ideal_avec_class0_values. qed.

lemma ideal_avec_class1_values_uniq :
  uniq ideal_avec_class1_values.
proof. by rewrite /ideal_avec_class1_values. qed.

lemma ideal_avec_class2_values_uniq :
  uniq ideal_avec_class2_values.
proof.
rewrite /ideal_avec_class2_values.
apply map_inj_in_uniq.
+ move=> x y _ _ /=; smt().
exact (range_uniq 1 ideal_avec_nonedge_class_count).
qed.

lemma ideal_avec_class3_values_uniq :
  uniq ideal_avec_class3_values.
proof.
rewrite /ideal_avec_class3_values.
apply map_inj_in_uniq.
+ move=> x y _ _ /=; smt().
exact (range_uniq 0 ideal_avec_nonedge_class_count).
qed.

lemma ideal_avec_class4_values_uniq :
  uniq ideal_avec_class4_values.
proof.
rewrite /ideal_avec_class4_values.
apply map_inj_in_uniq.
+ move=> x y _ _ /=; smt().
exact (range_uniq 0 ideal_avec_nonedge_class_count).
qed.

lemma ideal_avec_class5_values_uniq :
  uniq ideal_avec_class5_values.
proof.
rewrite /ideal_avec_class5_values.
apply map_inj_in_uniq.
+ move=> x y _ _ /=; smt().
exact (range_uniq 0 ideal_avec_nonedge_class_count).
qed.

lemma ideal_avec_class0_values_support rho :
  rho \in ideal_avec_class0_values =>
  0 <= rho <= ideal_avec_q - 1.
proof.
by rewrite /ideal_avec_class0_values /ideal_avec_q /=; smt().
qed.

lemma ideal_avec_class1_values_support rho :
  rho \in ideal_avec_class1_values =>
  0 <= rho <= ideal_avec_q - 1.
proof.
by rewrite /ideal_avec_class1_values /ideal_avec_q /=; smt().
qed.

lemma ideal_avec_class2_values_support rho :
  rho \in ideal_avec_class2_values =>
  0 <= rho <= ideal_avec_q - 1.
proof.
rewrite /ideal_avec_class2_values.
case/mapP => k [/mem_range hk ->].
rewrite /ideal_avec_nonedge_class_count /ideal_avec_q in hk.
rewrite /ideal_avec_q.
smt().
qed.

lemma ideal_avec_class3_values_support rho :
  rho \in ideal_avec_class3_values =>
  0 <= rho <= ideal_avec_q - 1.
proof.
rewrite /ideal_avec_class3_values.
case/mapP => k [/mem_range hk ->].
rewrite /ideal_avec_nonedge_class_count /ideal_avec_q in hk.
rewrite /ideal_avec_q.
smt().
qed.

lemma ideal_avec_class4_values_support rho :
  rho \in ideal_avec_class4_values =>
  0 <= rho <= ideal_avec_q - 1.
proof.
rewrite /ideal_avec_class4_values.
case/mapP => k [/mem_range hk ->].
rewrite /ideal_avec_nonedge_class_count /ideal_avec_q in hk.
rewrite /ideal_avec_q.
smt().
qed.

lemma ideal_avec_class5_values_support rho :
  rho \in ideal_avec_class5_values =>
  0 <= rho <= ideal_avec_q - 1.
proof.
rewrite /ideal_avec_class5_values.
case/mapP => k [/mem_range hk ->].
rewrite /ideal_avec_nonedge_class_count /ideal_avec_q in hk.
rewrite /ideal_avec_q.
smt().
qed.

lemma ideal_avec_class0_valuesP rho :
  0 <= rho <= ideal_avec_q - 1 =>
  (rho \in ideal_avec_class0_values <=> ideal_avec_class_index rho = 0).
proof.
move=> hrho.
rewrite /ideal_avec_class0_values /= /ideal_avec_class_index.
apply/eq_iff; smt().
qed.

lemma ideal_avec_class1_valuesP rho :
  0 <= rho <= ideal_avec_q - 1 =>
  (rho \in ideal_avec_class1_values <=> ideal_avec_class_index rho = 1).
proof.
move=> hrho.
rewrite /ideal_avec_class1_values /= /ideal_avec_class_index.
apply/eq_iff; smt().
qed.

lemma ideal_avec_class2_valuesP rho :
  0 <= rho <= ideal_avec_q - 1 =>
  (rho \in ideal_avec_class2_values <=> ideal_avec_class_index rho = 2).
proof.
move=> hrho.
rewrite /ideal_avec_class2_values /ideal_avec_class_index.
split.
+ case/mapP => k [/mem_range hk ->].
   have hk0 : 4 * k <> 0 by smt().
   have hkq1 : 4 * k <> ideal_avec_q - 1 by smt().
   rewrite hk0 hkq1.
   have -> : (4 * k) %% 4 = 0 by smt().
   trivial.
move=> hcls.
have hrho0 : rho <> 0 by smt().
have hrhoq1 : rho <> ideal_avec_q - 1 by smt().
have hmod : rho %% 4 = 0 by smt().
apply/mapP.
exists (rho %/ 4).
split.
+ rewrite mem_range.
   have hdiv := divz_eq rho 4.
   smt().
have hdiv := divz_eq rho 4.
smt().
qed.

lemma ideal_avec_class3_valuesP rho :
  0 <= rho <= ideal_avec_q - 1 =>
  (rho \in ideal_avec_class3_values <=> ideal_avec_class_index rho = 3).
proof.
move=> hrho.
rewrite /ideal_avec_class3_values /ideal_avec_class_index.
split.
+ case/mapP => k [/mem_range hk ->].
   have hk0 : 4 * k + 1 <> 0 by smt().
   have hkq1 : 4 * k + 1 <> ideal_avec_q - 1 by smt().
   rewrite hk0 hkq1.
   have -> : (4 * k + 1) %% 4 = 1 by smt().
   trivial.
move=> hcls.
have hrho0 : rho <> 0 by smt().
have hrhoq1 : rho <> ideal_avec_q - 1 by smt().
have hmod : rho %% 4 = 1 by smt().
apply/mapP.
exists (rho %/ 4).
split.
+ rewrite mem_range.
   have hdiv := divz_eq rho 4.
   smt().
have hdiv := divz_eq rho 4.
smt().
qed.

lemma ideal_avec_class4_valuesP rho :
  0 <= rho <= ideal_avec_q - 1 =>
  (rho \in ideal_avec_class4_values <=> ideal_avec_class_index rho = 4).
proof.
move=> hrho.
rewrite /ideal_avec_class4_values /ideal_avec_class_index.
split.
+ case/mapP => k [/mem_range hk ->].
   have hk0 : 4 * k + 2 <> 0 by smt().
   have hkq1 : 4 * k + 2 <> ideal_avec_q - 1 by smt().
   rewrite hk0 hkq1.
   have -> : (4 * k + 2) %% 4 = 2 by smt().
   trivial.
move=> hcls.
have hrho0 : rho <> 0 by smt().
have hrhoq1 : rho <> ideal_avec_q - 1 by smt().
have hmod : rho %% 4 = 2 by smt().
apply/mapP.
exists (rho %/ 4).
split.
+ rewrite mem_range.
   have hdiv := divz_eq rho 4.
   smt().
have hdiv := divz_eq rho 4.
smt().
qed.

lemma ideal_avec_class5_valuesP rho :
  0 <= rho <= ideal_avec_q - 1 =>
  (rho \in ideal_avec_class5_values <=> ideal_avec_class_index rho = 5).
proof.
move=> hrho.
rewrite /ideal_avec_class5_values /ideal_avec_class_index.
split.
+ case/mapP => k [/mem_range hk ->].
   have hk0 : 4 * k + 3 <> 0 by smt().
   have hkq1 : 4 * k + 3 <> ideal_avec_q - 1 by smt().
   rewrite hk0 hkq1.
   have -> : (4 * k + 3) %% 4 = 3 by smt().
   trivial.
move=> hcls.
have hrho0 : rho <> 0 by smt().
have hrhoq1 : rho <> ideal_avec_q - 1 by smt().
have hmod : rho %% 4 = 3 by smt().
apply/mapP.
exists (rho %/ 4).
split.
+ rewrite mem_range.
   have hdiv := divz_eq rho 4.
   smt().
have hdiv := divz_eq rho 4.
smt().
qed.

lemma ideal_avec_class0_size :
  size ideal_avec_class0_values = 1.
proof. by rewrite /ideal_avec_class0_values. qed.

lemma ideal_avec_class1_size :
  size ideal_avec_class1_values = 1.
proof. by rewrite /ideal_avec_class1_values. qed.

lemma ideal_avec_class2_size :
  size ideal_avec_class2_values = ideal_avec_class2_count.
proof.
rewrite /ideal_avec_class2_values size_map size_range.
by rewrite /ideal_avec_nonedge_class_count /ideal_avec_class2_count.
qed.

lemma ideal_avec_class3_size :
  size ideal_avec_class3_values = ideal_avec_nonedge_class_count.
proof. by rewrite /ideal_avec_class3_values size_map size_range. qed.

lemma ideal_avec_class4_size :
  size ideal_avec_class4_values = ideal_avec_nonedge_class_count.
proof. by rewrite /ideal_avec_class4_values size_map size_range. qed.

lemma ideal_avec_class5_size :
  size ideal_avec_class5_values = ideal_avec_nonedge_class_count.
proof. by rewrite /ideal_avec_class5_values size_map size_range. qed.

lemma ideal_avec_coefficient_sum_values values :
  (forall rho,
    rho \in values => 0 <= rho <= ideal_avec_q - 1) =>
  Bigreal.BRA.big predT (mu1 ideal_avec_coefficient_distribution) values =
  (size values)%r * (1%r / ideal_avec_q%r).
proof.
elim: values.
+ by move=> _; rewrite Bigreal.BRA.big_nil /=.
move=> x xs ih hsupport.
rewrite Bigreal.BRA.big_cons /predT /=.
have hx : 0 <= x <= ideal_avec_q - 1 by
  apply hsupport; rewrite /=; smt().
have hxs : forall rho,
    rho \in xs => 0 <= rho <= ideal_avec_q - 1 by
  move=> rho hrho; apply hsupport; rewrite /=; smt().
rewrite /ideal_avec_coefficient_distribution dinter1E hx /=.
rewrite (ih hxs) /=.
ring.
qed.

lemma ideal_avec_class_values_point values count cls :
  uniq values =>
  (forall rho,
    rho \in values => 0 <= rho <= ideal_avec_q - 1) =>
  (forall rho,
    0 <= rho <= ideal_avec_q - 1 =>
    (rho \in values <=> ideal_avec_class_index rho = cls)) =>
  size values = count =>
  mu1 ideal_avec_class_distribution cls = count%r / ideal_avec_q%r.
proof.
move=> huniq hsupport hvalues hcount.
rewrite /ideal_avec_class_distribution dmap1E.
have heq :
    mu ideal_avec_coefficient_distribution
      (fun rho => ideal_avec_class_index rho = cls) =
    mu ideal_avec_coefficient_distribution (mem values).
+ apply mu_eq_support => rho hrho.
   rewrite ideal_avec_coefficient_support in hrho.
   apply/eq_iff.
   by rewrite (hvalues rho hrho).
rewrite heq (mu_mem_uniq ideal_avec_coefficient_distribution values) 1:huniq.
rewrite (ideal_avec_coefficient_sum_values values hsupport) hcount.
ring.
qed.

lemma ideal_avec_class_distribution_point0 :
  mu1 ideal_avec_class_distribution 0 = 1%r / ideal_avec_q%r.
proof.
apply (ideal_avec_class_values_point ideal_avec_class0_values 1 0).
+ exact ideal_avec_class0_values_uniq.
+ exact ideal_avec_class0_values_support.
+ exact ideal_avec_class0_valuesP.
exact ideal_avec_class0_size.
qed.

lemma ideal_avec_class_distribution_point1 :
  mu1 ideal_avec_class_distribution 1 = 1%r / ideal_avec_q%r.
proof.
apply (ideal_avec_class_values_point ideal_avec_class1_values 1 1).
+ exact ideal_avec_class1_values_uniq.
+ exact ideal_avec_class1_values_support.
+ exact ideal_avec_class1_valuesP.
exact ideal_avec_class1_size.
qed.

lemma ideal_avec_class_distribution_point2 :
  mu1 ideal_avec_class_distribution 2 =
    ideal_avec_class2_count%r / ideal_avec_q%r.
proof.
apply
  (ideal_avec_class_values_point
    ideal_avec_class2_values ideal_avec_class2_count 2).
+ exact ideal_avec_class2_values_uniq.
+ exact ideal_avec_class2_values_support.
+ exact ideal_avec_class2_valuesP.
exact ideal_avec_class2_size.
qed.

lemma ideal_avec_class_distribution_point3 :
  mu1 ideal_avec_class_distribution 3 =
    ideal_avec_nonedge_class_count%r / ideal_avec_q%r.
proof.
apply
  (ideal_avec_class_values_point
    ideal_avec_class3_values ideal_avec_nonedge_class_count 3).
+ exact ideal_avec_class3_values_uniq.
+ exact ideal_avec_class3_values_support.
+ exact ideal_avec_class3_valuesP.
exact ideal_avec_class3_size.
qed.

lemma ideal_avec_class_distribution_point4 :
  mu1 ideal_avec_class_distribution 4 =
    ideal_avec_nonedge_class_count%r / ideal_avec_q%r.
proof.
apply
  (ideal_avec_class_values_point
    ideal_avec_class4_values ideal_avec_nonedge_class_count 4).
+ exact ideal_avec_class4_values_uniq.
+ exact ideal_avec_class4_values_support.
+ exact ideal_avec_class4_valuesP.
exact ideal_avec_class4_size.
qed.

lemma ideal_avec_class_distribution_point5 :
  mu1 ideal_avec_class_distribution 5 =
    ideal_avec_nonedge_class_count%r / ideal_avec_q%r.
proof.
apply
  (ideal_avec_class_values_point
    ideal_avec_class5_values ideal_avec_nonedge_class_count 5).
+ exact ideal_avec_class5_values_uniq.
+ exact ideal_avec_class5_values_support.
+ exact ideal_avec_class5_valuesP.
exact ideal_avec_class5_size.
qed.

lemma ideal_avec_class_count_certificate :
  ideal_avec_class_count 0 = 1 /\
  ideal_avec_class_count 1 = 1 /\
  ideal_avec_class_count 2 = 16127 /\
  ideal_avec_class_count 3 = 16128 /\
  ideal_avec_class_count 4 = 16128 /\
  ideal_avec_class_count 5 = 16128.
proof.
by rewrite /ideal_avec_class_count /ideal_avec_class2_count
           /ideal_avec_nonedge_class_count.
qed.

lemma ideal_avec_class_distribution_point cls :
  0 <= cls < 6 =>
  mu1 ideal_avec_class_distribution cls = ideal_avec_class_point_mass cls.
proof.
move=> hcls.
rewrite /ideal_avec_class_point_mass.
case (cls = 0) => [-> | hneq0].
+ exact ideal_avec_class_distribution_point0.
case (cls = 1) => [-> | hneq1].
+ exact ideal_avec_class_distribution_point1.
case (cls = 2) => [-> | hneq2].
+ exact ideal_avec_class_distribution_point2.
case (cls = 3) => [-> | hneq3].
+ exact ideal_avec_class_distribution_point3.
case (cls = 4) => [-> | hneq4].
+ exact ideal_avec_class_distribution_point4.
case (cls = 5) => [-> | hneq5].
+ exact ideal_avec_class_distribution_point5.
smt().
qed.

lemma ideal_avec_shifted_class_distribution_point pre_bp cls :
  0 <= cls < 6 =>
  mu1
    (dmap ideal_avec_coefficient_distribution
      (ideal_avec_shifted_class_index pre_bp)) cls =
  ideal_avec_class_point_mass cls.
proof.
move=> hcls.
rewrite (ideal_avec_shifted_class_distribution pre_bp).
exact (ideal_avec_class_distribution_point cls hcls).
qed.

lemma ideal_avec_class_point_mass_sum1 :
  ideal_avec_class_point_mass 0 +
  ideal_avec_class_point_mass 1 +
  ideal_avec_class_point_mass 2 +
  ideal_avec_class_point_mass 3 +
  ideal_avec_class_point_mass 4 +
  ideal_avec_class_point_mass 5 = 1%r.
proof.
rewrite /ideal_avec_class_point_mass /ideal_avec_class_count
        /ideal_avec_class2_count /ideal_avec_nonedge_class_count
        /ideal_avec_q.
ring.
smt().
qed.

lemma ideal_avec_class_distribution_lossless :
  is_lossless ideal_avec_class_distribution.
proof.
rewrite /ideal_avec_class_distribution.
by apply dmap_ll; exact ideal_avec_coefficient_lossless.
qed.

lemma ideal_avec_flat_class_distribution_lossless :
  is_lossless ideal_avec_flat_class_distribution.
proof.
rewrite /ideal_avec_flat_class_distribution.
by apply dlist_ll; exact ideal_avec_class_distribution_lossless.
qed.

lemma ideal_avec_dmap_dlist_nth ['a]
    (d : 'a distr) (x0 : 'a) n i :
  is_lossless d =>
  0 <= i < n =>
  dmap (dlist d n) (fun xs => nth x0 xs i) = d.
proof.
move=> hll hi.
have hn : 0 <= n - 1 by smt().
have hi' : 0 <= i <= n - 1 by smt().
rewrite (_ : n = (n - 1) + 1) 1:/#.
rewrite (dlist_insert x0 i (n - 1) d hn hi') dmap_comp.
have -> :
    dmap (d `*` dlist d (n - 1))
      ((fun xs => nth x0 xs i) \o
       (fun x_xs : 'a * 'a list => insert x_xs.`1 x_xs.`2 i)) =
    dmap (d `*` dlist d (n - 1))
      (fun (x_xs : 'a * 'a list) => x_xs.`1).
+ apply eq_dmap_in => x_xs hx_x_xs.
   rewrite supp_dprod in hx_x_xs.
   move: hx_x_xs => [_ hxs].
   have hsize := supp_dlist_size d (n - 1) x_xs.`2 hn hxs.
   rewrite /(\o) /=.
   apply nth_insert.
   rewrite hsize.
   exact hi'.
rewrite (dprod_marginalL d (dlist d (n - 1)) idfun).
have htail : is_lossless (dlist d (n - 1)) by apply dlist_ll; exact hll.
rewrite /is_lossless in htail.
rewrite htail dmap_id dscalar1.
trivial.
qed.

lemma ideal_avec_flat_to_rows_nth xs row j :
  0 <= row < ideal_avec_trace_rows =>
  0 <= j < ideal_avec_trace_words =>
  nth 0 (nth [] (ideal_avec_flat_to_rows xs) row) j =
  nth 0 xs (ideal_avec_flat_index row j).
proof.
move=> hrow hj.
rewrite /ideal_avec_flat_to_rows /ideal_avec_flat_index.
have hrow01 : row = 0 \/ row = 1 by
  rewrite /ideal_avec_trace_rows in hrow; smt().
case hrow01.
+ move=> ->.
   rewrite /= nth_take; smt().
move=> ->.
rewrite /= nth_take; smt().
qed.

lemma ideal_avec_ordered_class_trace_distributionE :
  ideal_avec_ordered_class_trace_distribution =
  dmap
    (dlist ideal_avec_coefficient_distribution ideal_avec_trace_size)
    ideal_avec_flat_class_trace.
proof.
rewrite /ideal_avec_ordered_class_trace_distribution
        /ideal_avec_flat_class_trace.
rewrite /ideal_avec_flat_class_distribution /ideal_avec_class_distribution.
rewrite dlist_dmap dmap_comp.
trivial.
qed.

lemma ideal_avec_ordered_class_trace_coordinate_marginal row j :
  0 <= row < ideal_avec_trace_rows =>
  0 <= j < ideal_avec_trace_words =>
  dmap
    ideal_avec_ordered_class_trace_distribution
    (ideal_avec_ordered_class_trace_coordinate row j) =
  ideal_avec_class_distribution.
proof.
move=> hrow hj.
rewrite /ideal_avec_ordered_class_trace_distribution dmap_comp.
have -> :
    dmap ideal_avec_flat_class_distribution
      (ideal_avec_ordered_class_trace_coordinate row j \o
       ideal_avec_flat_to_rows) =
    dmap ideal_avec_flat_class_distribution
      (fun xs => nth 0 xs (ideal_avec_flat_index row j)).
+ apply eq_dmap_in => xs hxs.
   rewrite /(\o) /ideal_avec_ordered_class_trace_coordinate.
   exact (ideal_avec_flat_to_rows_nth xs row j hrow hj).
have hidx : 0 <= ideal_avec_flat_index row j < ideal_avec_trace_size.
+ rewrite /ideal_avec_flat_index /ideal_avec_trace_words /ideal_avec_trace_rows.
   smt().
exact
  (ideal_avec_dmap_dlist_nth
    ideal_avec_class_distribution
    0
    ideal_avec_trace_size
    (ideal_avec_flat_index row j)
    ideal_avec_class_distribution_lossless
    hidx).
qed.

lemma ideal_avec_ordered_class_trace_coordinate_point_mass row j cls :
  0 <= row < ideal_avec_trace_rows =>
  0 <= j < ideal_avec_trace_words =>
  0 <= cls < 6 =>
  mu1
    (dmap
      ideal_avec_ordered_class_trace_distribution
      (ideal_avec_ordered_class_trace_coordinate row j)) cls =
  ideal_avec_class_point_mass cls.
proof.
move=> hrow hj hcls.
rewrite (ideal_avec_ordered_class_trace_coordinate_marginal row j hrow hj).
exact (ideal_avec_class_distribution_point cls hcls).
qed.

lemma ideal_mode2_independent_avec_carrier_trace_lossless :
  is_lossless ideal_avec_ordered_class_trace_distribution.
proof.
rewrite /ideal_avec_ordered_class_trace_distribution.
by apply dmap_ll; exact ideal_avec_flat_class_distribution_lossless.
qed.

lemma ideal_mode2_independent_avec_carrier_prebp_secret_marginalE dpresec :
  ideal_mode2_independent_avec_carrier_boundary dpresec =>
  ideal_mode2_independent_avec_carrier_prebp_secret_marginal
    (ideal_mode2_independent_avec_carrier_distribution dpresec) =
  dpresec.
proof.
move=> hll.
rewrite /ideal_mode2_independent_avec_carrier_boundary in hll.
rewrite /ideal_mode2_independent_avec_carrier_prebp_secret_marginal
        /ideal_mode2_independent_avec_carrier_distribution.
rewrite (dprod_marginalL dpresec ideal_avec_ordered_class_trace_distribution idfun).
rewrite /is_lossless ideal_mode2_independent_avec_carrier_trace_lossless.
rewrite dmap_id dscalar1.
trivial.
qed.

lemma ideal_mode2_independent_avec_carrier_trace_marginalE dpresec :
  ideal_mode2_independent_avec_carrier_boundary dpresec =>
  ideal_mode2_independent_avec_carrier_trace_marginal
    (ideal_mode2_independent_avec_carrier_distribution dpresec) =
  ideal_avec_ordered_class_trace_distribution.
proof.
move=> hll.
rewrite /ideal_mode2_independent_avec_carrier_boundary in hll.
rewrite /ideal_mode2_independent_avec_carrier_trace_marginal
        /ideal_mode2_independent_avec_carrier_distribution.
rewrite (dprod_marginalR dpresec ideal_avec_ordered_class_trace_distribution idfun).
rewrite /is_lossless hll dmap_id dscalar1.
trivial.
qed.

end Mode2FaithfulSecurityIdealAvecClassTraceLawPostFreeze.
