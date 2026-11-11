require import AllCore IntDiv List Distr DInterval.
require import CDTDistributionSpec.

lemma cdt_rank_bounds thresholds u : 0 <= cdt_rank thresholds u <= size thresholds.
proof. rewrite /cdt_rank; smt(count_ge0 count_size). qed.

lemma cdt_path_lower (x : int) (thresholds : int list) :
  path (<=) x thresholds => all (fun t => x <= t) thresholds.
proof.
  elim: thresholds x => [|y thresholds ih] x //=.
  move=> [hxy hp]; split; first exact hxy.
  have ht := ih y hp.
  move: ht; rewrite List.allP => ht.
  apply List.allP => t hin; have := ht t hin; smt().
qed.

lemma cdt_sorted_tail (x : int) thresholds :
  sorted (<=) (x :: thresholds) => sorted (<=) thresholds.
proof. move=> hs; apply (path_sorted Int.(<=) x thresholds); exact hs. qed.

lemma cdt_rank_zero thresholds u :
  all (fun t => u <= t) thresholds => cdt_rank thresholds u = 0.
proof.
  move=> hall; rewrite /cdt_rank; apply count_pred0_eq_in => t ht.
  move: hall; rewrite List.allP => hall; have := hall t ht; smt().
qed.

(* For a sorted table, precisely the initial rank positions lie below u. *)
lemma cdt_rank_prefix thresholds u i :
  sorted (<=) thresholds => 0 <= i < size thresholds =>
  (nth 0 thresholds i < u) = (i < cdt_rank thresholds u).
proof.
  elim: thresholds i => [|x thresholds ih] i hs hi.
  + by rewrite /= in hi; smt().
  have htail := cdt_sorted_tail x thresholds hs.
  have hhead := cdt_path_lower x thresholds hs.
  case (x < u) => hx.
  + case (i = 0) => hi0.
    - rewrite hi0 /cdt_rank /= hx.
      have := count_ge0 (fun t => t < u) thresholds; smt().
    have hitail : 0 <= i - 1 < size thresholds by move: hi; rewrite /=; smt().
    have hp := ih (i - 1) htail hitail.
    rewrite /cdt_rank in hp.
    rewrite /cdt_rank /=; smt().
  have hall : all (fun t => u <= t) (x :: thresholds).
  + rewrite /=; split; first smt().
    move: hhead; rewrite List.allP => hhead.
    apply List.allP => t ht; have := hhead t ht; smt().
  have hz := cdt_rank_zero (x :: thresholds) u hall.
  move: hall; rewrite -(all_nthP _ _ 0) => hall.
  have hv := hall i hi.
  rewrite hz; smt().
qed.

lemma cdt_sorted_nth thresholds i j :
  sorted (<=) thresholds => 0 <= i <= j => j < size thresholds =>
  nth 0 thresholds i <= nth 0 thresholds j.
proof.
  move=> hs hi hj.
  have hip : 0 <= i < size thresholds by smt().
  have hjp : 0 <= j < size thresholds by smt().
  have h1 := cdt_rank_prefix thresholds (nth 0 thresholds j + 1) i hs hip.
  have h2 := cdt_rank_prefix thresholds (nth 0 thresholds j + 1) j hs hjp.
  smt().
qed.

lemma cdt_threshold_range modulus thresholds i :
  cdt_valid modulus thresholds => 0 <= i < size thresholds =>
  0 <= nth 0 thresholds i < modulus.
proof.
  move=> [hm [hs hall]] hi.
  move: hall; rewrite -(all_nthP _ _ 0) => hall.
  exact (hall i hi).
qed.

lemma cdt_bin_bounds modulus thresholds k :
  cdt_valid modulus thresholds => 0 <= k <= size thresholds =>
  0 <= cdt_bin_lower thresholds k <= cdt_bin_upper modulus thresholds k /\
  cdt_bin_upper modulus thresholds k <= modulus.
proof.
  move=> hv hk.
  have [hm [hs hall]] := hv.
  have hlo : k <> 0 => 0 <= nth 0 thresholds (k - 1) < modulus.
  + move=> h; apply (cdt_threshold_range modulus thresholds (k - 1) hv); smt().
  have hhi : k <> size thresholds => 0 <= nth 0 thresholds k < modulus.
  + move=> h; apply (cdt_threshold_range modulus thresholds k hv); smt().
  have horder : k <> 0 => k <> size thresholds =>
    nth 0 thresholds (k - 1) <= nth 0 thresholds k.
  + move=> h0 hn; apply cdt_sorted_nth; smt().
  rewrite /cdt_bin_lower /cdt_bin_upper; smt().
qed.

lemma cdt_rank_bin modulus thresholds k u :
  cdt_valid modulus thresholds => 0 <= u < modulus => 0 <= k <= size thresholds =>
  (cdt_rank thresholds u = k) =
    (cdt_bin_lower thresholds k <= u < cdt_bin_upper modulus thresholds k).
proof.
  move=> [hm [hs hall]] hu hk.
  have hc := cdt_rank_bounds thresholds u.
  rewrite /cdt_bin_lower /cdt_bin_upper.
  case (k = 0) => h0.
  + case (k = size thresholds) => hn; first smt().
    have hfirst := cdt_rank_prefix thresholds u 0 hs _; first smt().
    smt().
  case (k = size thresholds) => hn.
  + have hlast := cdt_rank_prefix thresholds u (k - 1) hs _; first smt().
    smt().
  have hprev := cdt_rank_prefix thresholds u (k - 1) hs _; first smt().
  have hnext := cdt_rank_prefix thresholds u k hs _; first smt().
  smt().
qed.

lemma cdt_filter_interval modulus lower upper :
  0 <= lower <= upper => upper <= modulus =>
  filter (fun u => lower <= u < upper) (range 0 modulus) = range lower upper.
proof.
  move=> hlo hhi.
  have hsplit0 : range 0 modulus = range 0 lower ++ range lower modulus
    by apply range_cat; smt().
  have hsplit1 : range lower modulus = range lower upper ++ range upper modulus
    by apply range_cat; smt().
  have hzero : filter (fun u => lower <= u < upper) (range 0 lower) = [].
  + apply eq_in_filter_pred0 => u; rewrite mem_range; smt().
  have hmid : filter (fun u => lower <= u < upper) (range lower upper) = range lower upper.
  + apply eq_in_filter_predT => u; rewrite mem_range; smt().
  have hlast : filter (fun u => lower <= u < upper) (range upper modulus) = [].
  + apply eq_in_filter_pred0 => u; rewrite mem_range; smt().
  by rewrite hsplit0 hsplit1 !filter_cat hzero hmid hlast /= ?cats0.
qed.

lemma cdt_uniform_interval modulus lower upper :
  0 < modulus => 0 <= lower <= upper => upper <= modulus =>
  mu (dinter 0 (modulus - 1)) (fun u => lower <= u < upper) =
    (upper - lower)%r / modulus%r.
proof.
  move=> hm hlo hhi.
  rewrite dinterE /= (cdt_filter_interval modulus lower upper hlo hhi) size_range.
  have hnum : max 0 (upper - lower) = upper - lower by smt().
  have hden : max 0 modulus = modulus by smt().
  by rewrite hnum hden.
qed.

lemma cdt_uniform_rank_mass modulus thresholds k :
  cdt_valid modulus thresholds =>
  mu (dinter 0 (modulus - 1)) (fun u => cdt_rank thresholds u = k) =
    cdt_bin_mass modulus thresholds k.
proof.
  move=> hv; have [hm _] := hv.
  rewrite /cdt_bin_mass.
  case (0 <= k <= size thresholds) => hk.
  + have hb := cdt_bin_bounds modulus thresholds k hv hk.
    have he : mu (dinter 0 (modulus - 1)) (fun u => cdt_rank thresholds u = k) =
      mu (dinter 0 (modulus - 1))
        (fun u => cdt_bin_lower thresholds k <= u < cdt_bin_upper modulus thresholds k).
    + apply mu_eq_support => u hu.
      apply (cdt_rank_bin modulus thresholds k u hv _ hk).
      move: hu; rewrite supp_dinter; smt().
    rewrite he; apply cdt_uniform_interval; smt().
  apply mu0_false => u hu.
  have hc := cdt_rank_bounds thresholds u; smt().
qed.

lemma cdt_distribution_mass modulus thresholds k :
  cdt_valid modulus thresholds =>
  mu1 (cdt_distribution modulus thresholds) k = cdt_bin_mass modulus thresholds k.
proof.
  move=> hv; rewrite /cdt_distribution dmap1E /pred1 /(\o).
  exact (cdt_uniform_rank_mass modulus thresholds k hv).
qed.

lemma cdt_distribution_lossless modulus thresholds :
  0 < modulus => is_lossless (cdt_distribution modulus thresholds).
proof. move=> hm; rewrite /cdt_distribution; apply dmap_ll; apply dinter_ll; smt(). qed.

lemma cdt_distribution_support_bounds modulus thresholds k :
  k \in cdt_distribution modulus thresholds => 0 <= k <= size thresholds.
proof.
  rewrite /cdt_distribution supp_dmap.
  move=> [u [hu ->]]; exact (cdt_rank_bounds thresholds u).
qed.

lemma cdt_distribution_support modulus thresholds k :
  cdt_valid modulus thresholds =>
  (k \in cdt_distribution modulus thresholds) =
    (0 <= k <= size thresholds /\ cdt_bin_lower thresholds k < cdt_bin_upper modulus thresholds k).
proof.
  move=> hv; apply/eq_iff; split.
  + move=> hsupport.
    have hk := cdt_distribution_support_bounds modulus thresholds k hsupport.
    move: hsupport; rewrite /cdt_distribution supp_dmap.
    move=> [u [hu he]].
    have hu' : 0 <= u < modulus by move: hu; rewrite supp_dinter; smt().
    have hbin := cdt_rank_bin modulus thresholds k u hv hu' hk; smt().
  move=> [hk hnonempty].
  have hb := cdt_bin_bounds modulus thresholds k hv hk.
  rewrite /cdt_distribution supp_dmap.
  exists (cdt_bin_lower thresholds k); split.
  + rewrite supp_dinter; smt().
  have hu : 0 <= cdt_bin_lower thresholds k < modulus by smt().
  have he := cdt_rank_bin modulus thresholds k (cdt_bin_lower thresholds k) hv hu hk.
  smt().
qed.

lemma uniform_cdt_lossless modulus0 thresholds0 : 0 < modulus0 =>
  phoare [UniformCDT.sample : modulus = modulus0 /\ thresholds = thresholds0 ==> true] = 1%r.
proof.
  move=> hm; proc; rnd; skip; auto => />.
  apply dinter_ll; smt().
qed.


lemma uniform_cdt_mass modulus0 thresholds0 k : cdt_valid modulus0 thresholds0 =>
  phoare [UniformCDT.sample : modulus = modulus0 /\ thresholds = thresholds0 ==> res = k] =
    (cdt_bin_mass modulus0 thresholds0 k).
proof.
  move=> hv; proc; rnd; skip; auto => />.
  exact (cdt_uniform_rank_mass modulus0 thresholds0 k hv).
qed.

lemma uniform_cdt_probability modulus0 thresholds0 k &m :
  cdt_valid modulus0 thresholds0 =>
  Pr[UniformCDT.sample(modulus0, thresholds0) @ &m : res = k] =
    cdt_bin_mass modulus0 thresholds0 k.
proof.
  move=> hv.
  byphoare (uniform_cdt_mass modulus0 thresholds0 k hv) => //.
qed.

lemma uniform_cdt_law modulus0 thresholds0 (event : int -> bool) &m :
  Pr[UniformCDT.sample(modulus0, thresholds0) @ &m : event res] =
    mu (cdt_distribution modulus0 thresholds0) event.
proof.
  byphoare (_ : modulus = modulus0 /\ thresholds = thresholds0 ==> event res) => //.
  proc; rnd; skip; auto => />.
  by rewrite /cdt_distribution dmapE /(\o).
qed.


lemma cdt_strict_adjacent (thresholds : int list) i :
  sorted (<) thresholds => 0 <= i => i + 1 < size thresholds =>
  nth 0 thresholds i < nth 0 thresholds (i + 1).
proof.
  elim: thresholds i => [|x thresholds ih] i hs hi hlen.
  + by rewrite /= in hlen; smt().
  have htail : sorted (<) thresholds by apply (path_sorted Int.(<) x thresholds); exact hs.
  case (i = 0) => hi0.
  + rewrite hi0 /=.
    clear htail ih.
    move: hs hlen; case: thresholds => [|y ys] /=; smt().
  have hi' : 0 <= i - 1 by smt().
  have hlen' : i - 1 + 1 < size thresholds by move: hlen; rewrite /=; smt().
  have hp := ih (i - 1) htail hi' hlen'.
  have he0 : nth 0 (x :: thresholds) i = nth 0 thresholds (i - 1) by rewrite /=; smt().
  have he1 : nth 0 (x :: thresholds) (i + 1) = nth 0 thresholds i by rewrite /=; smt().
  smt().
qed.

lemma cdt_bin_positive modulus thresholds k :
  cdt_valid modulus thresholds => sorted (<) thresholds =>
  (0 < size thresholds => nth 0 thresholds (size thresholds - 1) < modulus - 1) =>
  0 <= k <= size thresholds =>
  cdt_bin_lower thresholds k < cdt_bin_upper modulus thresholds k.
proof.
  move=> hv hstrict hlast hk.
  have [hm _] := hv.
  rewrite /cdt_bin_lower /cdt_bin_upper.
  case (k = 0) => h0.
  + case (k = size thresholds) => hn; first smt().
    have ht := cdt_threshold_range modulus thresholds 0 hv _; first smt().
    smt().
  case (k = size thresholds) => hn; first smt().
  have ht := cdt_strict_adjacent thresholds (k - 1) hstrict _ _; first 2 smt().
  smt().
qed.

lemma cdt_distribution_full_support modulus thresholds k :
  cdt_valid modulus thresholds => sorted (<) thresholds =>
  (0 < size thresholds => nth 0 thresholds (size thresholds - 1) < modulus - 1) =>
  (k \in cdt_distribution modulus thresholds) = (0 <= k <= size thresholds).
proof.
  move=> hv hstrict hlast; rewrite (cdt_distribution_support modulus thresholds k hv).
  apply/eq_iff; split; first smt().
  move=> hk; split; first exact hk.
  exact (cdt_bin_positive modulus thresholds k hv hstrict hlast hk).
qed.
