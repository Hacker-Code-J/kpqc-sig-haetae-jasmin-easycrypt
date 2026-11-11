require import AllCore IntDiv List Distr DList StdRing StdOrder.
from Jasmin require import JModel_x86.
require import GaussianPayloadSpec GaussianTraceSpec GaussianTraceProperties
  GaussianAccumulatorCorrectness GaussianStreamAccumulator HyperballGaussianBounds
  SigmaCorrectness GaussianUniformBytes GaussianRetryInputs GaussianRetryCore
  GaussianIidKernel GaussianIidProgress GaussianBlockSampling.

lemma gpd_pack_magnitude (event : gauss_event) :
  gpd_magnitude (gpd_pack event) = W64.to_uint event.`1.
proof.
  have /= hm := W64.to_uint_cmp event.`1.
  rewrite /gpd_magnitude /gpd_pack /gpd_base
    (mulzC 18446744073709551616 (gauss_limb_value event.`2 event.`3)) modzMDr.
  by rewrite modz_small.
qed.

lemma gpd_pack_square (event : gauss_event) :
  gpd_square (gpd_pack event) = gauss_limb_value event.`2 event.`3.
proof.
  have /= hm := W64.to_uint_cmp event.`1.
  rewrite /gpd_square /gpd_pack /gpd_base
    (mulzC 18446744073709551616 (gauss_limb_value event.`2 event.`3)) divzMDr 1://.
  by rewrite divz_small.
qed.

lemma gpd_pack_record (event : gauss_event) :
  gpd_record (gpd_pack event) =
    (W64.to_uint event.`1,gauss_limb_value event.`2 event.`3).
proof. by rewrite /gpd_record gpd_pack_magnitude gpd_pack_square. qed.

lemma gpd_pack_nonnegative (event : gauss_event) : 0 <= gpd_pack event.
proof.
  have h0 := W64.to_uint_cmp event.`1.
  have h1 := W64.to_uint_cmp event.`2.
  have h2 := W64.to_uint_cmp event.`3.
  rewrite /gpd_pack /gpd_base /gauss_limb_value; smt().
qed.

lemma gpd_pack_square_limbs (event : gauss_event) :
  W64.to_uint event.`2 < 281474976710656 =>
  gpd_square (gpd_pack event) %% 281474976710656 = W64.to_uint event.`2 /\
  gpd_square (gpd_pack event) %/ 281474976710656 = W64.to_uint event.`3.
proof.
  move=> hl; have hlo := W64.to_uint_cmp event.`2.
  rewrite gpd_pack_square /gauss_limb_value (mulzC 281474976710656 (W64.to_uint event.`3)).
  rewrite modzMDr divzMDr 1:// modz_small 1:/# divz_small 1:/#.
  trivial.
qed.

lemma gpd_event_max : hb_event_max = 2^84-1.
proof. rewrite /hb_event_max; ring. qed.

lemma gpd_sigma_square_bound p :
  0 <= gpd_square (gpd_pack (sigma76_spec p)) <= hb_event_max.
proof.
  have h := hb_sigma76_event_bounded p.
  rewrite /hb_event_bounded in h.
  rewrite gpd_pack_square /gauss_limb_value /hb_event_max; smt().
qed.

lemma gpd_sigma_valid p : gpd_valid (gpd_pack (sigma76_spec p)).
proof.
  have h0 := gpd_pack_nonnegative (sigma76_spec p).
  have h1 := gpd_sigma_square_bound p.
  by rewrite /gpd_valid.
qed.

lemma gpd_valid_bounds code : gpd_valid code =>
  0 <= gpd_magnitude code < gpd_base /\ code < gpd_base*(hb_event_max+1).
proof.
  rewrite /gpd_valid /gpd_square => hv.
  have hd := divz_eq code gpd_base.
  have hm := modz_cmp code gpd_base _; first by rewrite /gpd_base.
  rewrite /gpd_base /hb_event_max in hv.
  rewrite /gpd_base in hd.
  rewrite /gpd_base in hm.
  rewrite /gpd_magnitude /gpd_base /hb_event_max; smt().
qed.

lemma gpd_trial_ll : is_lossless gpd_trial.
proof. rewrite /gpd_trial; apply dmap_ll; exact gbc_candidate_ll. qed.

lemma gpd_trial_acceptance : mu gpd_trial gr_accept = mu gik_pairs gr_accept.
proof.
  rewrite /gpd_trial /gik_pairs !dmapE.
  apply mu_eq => candidate.
  by rewrite /(\o) /gr_accept /gpd_observer /= gr_candidate_event_accept.
qed.

lemma gpd_trial_acceptance_lower : 1%r/7%r <= mu gpd_trial gr_accept.
proof. by rewrite gpd_trial_acceptance; exact gik_acceptance_lower. qed.

lemma gpd_trial_acceptance_positive : 0%r < mu gpd_trial gr_accept.
proof. have h := gpd_trial_acceptance_lower; smt(). qed.

lemma gpd_accepted_ll : is_lossless gpd_accepted.
proof. rewrite /gpd_accepted; exact (gr_output_ll gpd_trial gpd_trial_acceptance_positive). qed.

lemma gpd_trial_valid (outcome : int * bool) : outcome \in gpd_trial => gpd_valid outcome.`1.
proof.
  rewrite /gpd_trial supp_dmap => -[candidate [hc ->]].
  rewrite /gpd_observer /=; exact (gpd_sigma_valid candidate).
qed.

lemma gpd_accepted_valid code : code \in gpd_accepted => gpd_valid code.
proof.
  rewrite /gpd_accepted /gr_output supp_dmap => -[outcome [ho ->]].
  move: ho; rewrite dcond_supp => -[ht ha].
  exact (gpd_trial_valid outcome ht).
qed.

lemma gpd_dlist_valid n codes : 0 <= n => codes \in dlist gpd_accepted n => all gpd_valid codes.
proof.
  move=> hn; rewrite supp_dlist 1:hn => -[hs ha].
  move/List.allP: ha => ha; apply/List.allP => code hc.
  exact (gpd_accepted_valid code (ha code hc)).
qed.

lemma gpd_sum_pack events :
  gpd_sum (map gpd_pack events) = gauss_event_value_sum events.
proof.
  elim: events => [|event events ih].
  + by rewrite /gpd_sum /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /=.
  rewrite /gpd_sum /= gpd_pack_square -/(gpd_sum (map gpd_pack events)) ih.
  rewrite /gauss_event_value_sum /gauss_limb_value /gauss_low_sum /gauss_high_sum /=.
  ring.
qed.

lemma gpd_sum_bounds codes : all gpd_valid codes =>
  0 <= gpd_sum codes <= size codes * hb_event_max.
proof.
  elim: codes => [|code codes ih] /=.
  + by rewrite /gpd_sum.
  move=> [hc ht]; have hs := ih ht.
  rewrite /gpd_valid in hc.
  rewrite /gpd_sum /= -/(gpd_sum codes); smt().
qed.

lemma gpd_filtered_observers candidates :
  map fst (filter snd (map gpd_observer candidates)) =
    map gpd_pack (filter gauss_event_accepted (map sigma76_spec candidates)).
proof.
  elim: candidates => [|candidate candidates ih] //=.
  rewrite /gpd_observer /=.
  case (gauss_event_accepted (sigma76_spec candidate)); by rewrite /= ih.
qed.

lemma gpd_events_chunks pending : size pending <= 8192 =>
  gpd_events pending = map sigma76_spec (gbc_chunks (size pending %/ 26) pending).
proof. rewrite /gpd_events; exact (gip_events_chunks pending). qed.

lemma gpd_scan_selected n history pending :
  0 <= size history <= n => size pending <= 8192 =>
  gpd_scan n history pending = history ++ gpd_selected pending (n-size history).
proof.
  move=> hn hp.
  rewrite /gpd_scan gbs_scan_filter 1:/# gpd_filtered_observers take_catr 1:/#.
  by rewrite /gpd_selected /gauss_selected_events (gpd_events_chunks pending hp) map_take.
qed.

lemma gpd_selected_count pending requested : 0 <= requested =>
  size (gpd_selected pending requested) =
    min requested (count gauss_event_accepted (gpd_events pending)).
proof.
  move=> hr; rewrite /gpd_selected /gauss_selected_events size_map size_take 1:hr size_filter.
  trivial.
qed.

lemma gpd_scan_count n history pending :
  0 <= size history <= n => size pending <= 8192 =>
  size (gpd_scan n history pending) = size history +
    min (n-size history) (count gauss_event_accepted (gpd_events pending)).
proof.
  move=> hn hp; by rewrite (gpd_scan_selected n history pending hn hp)
    size_cat gpd_selected_count 1:/#.
qed.

lemma gpd_scan_increment n history pending :
  0 <= size history <= n => size pending <= 8192 =>
  size (gpd_scan n history pending)-size history =
    min (n-size history) (count gauss_event_accepted (gpd_events pending)).
proof. by move=> hn hp; rewrite (gpd_scan_count n history pending hn hp); ring. qed.
