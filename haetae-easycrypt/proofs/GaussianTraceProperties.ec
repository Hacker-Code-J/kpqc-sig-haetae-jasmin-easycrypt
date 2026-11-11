require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianTraceSpec GaussianConsumerCorrectness.

op gauss_event_accepted (event : gauss_event) : bool =
  W64.to_uint event.`4 = 1.

op gauss_selected_events (requested : int) (events : gauss_event list) =
  take requested (filter gauss_event_accepted events).

op gauss_accepted_values (events : gauss_event list) : W64.t list =
  map (fun (event : gauss_event) => event.`1) (filter gauss_event_accepted events).

op gauss_events_are_bits (events : gauss_event list) : bool =
  all (fun (event : gauss_event) => 0 <= W64.to_uint event.`4 <= 1) events.

lemma gauss_event_accept_bit buf k :
  0 <= W64.to_uint (gauss_event_at buf k).`4 <= 1.
proof.
  rewrite /gauss_event_at /sigma76_spec /sigma_from_cdt /=.
  exact: gauss_mask_bit.
qed.

lemma gauss_event_accept_cases buf k :
  W64.to_uint (gauss_event_at buf k).`4 = 0 \/
  W64.to_uint (gauss_event_at buf k).`4 = 1.
proof. have := gauss_event_accept_bit buf k; smt(). qed.

lemma gauss_events_bits buf k : gauss_events_are_bits (gauss_events buf k).
proof.
  rewrite /gauss_events_are_bits /gauss_events all_map.
  apply/List.allP => i _; exact (gauss_event_accept_bit buf i).
qed.

lemma gauss_trace_step_count n d state event :
  (gauss_trace_step n d state event).`4 =
  if n <= state.`4 then state.`4 else state.`4 + W64.to_uint event.`4.
proof. by rewrite /gauss_trace_step; case (n <= state.`4). qed.

lemma gauss_trace_step_count_bounds n d (state : gauss_trace_state) (event : gauss_event) :
  0 <= state.`4 <= n => 0 <= W64.to_uint event.`4 <= 1 =>
  0 <= (gauss_trace_step n d state event).`4 <= n /\
  state.`4 <= (gauss_trace_step n d state event).`4 <= state.`4 + 1.
proof. move=> hs he; rewrite gauss_trace_step_count; smt(). qed.

lemma gauss_trace_fold_full n d (state : gauss_trace_state) events : n <= state.`4 =>
  foldl (gauss_trace_step n d) state events = state.
proof.
  move=> hs; elim: events => [|event events ih] //=.
  by rewrite /gauss_trace_step hs /= ih.
qed.

lemma gauss_trace_prefix_count_bounds buf n d values squares k :
  0 <= n => 0 <= k =>
  0 <= (gauss_trace_prefix buf n d values squares k).`4 <= n /\
  (gauss_trace_prefix buf n d values squares k).`4 <= k.
proof.
  move=> hn hk; elim: k hk => [|k hk ih].
  + rewrite gauss_trace_prefix0 /gauss_trace_initial /=; smt().
  rewrite gauss_trace_prefixS 1:hk.
  have [ihn ihk] := ih.
  have := gauss_trace_step_count_bounds n d
    (gauss_trace_prefix buf n d values squares k) (gauss_event_at buf k)
    ihn (gauss_event_accept_bit buf k).
  smt().
qed.

lemma gauss_trace_prefix_extend buf n d values squares k K :
  0 <= k <= K =>
  gauss_trace_prefix buf n d values squares K =
  foldl (gauss_trace_step n d) (gauss_trace_prefix buf n d values squares k)
    (map (gauss_event_at buf) (iota_ k (K - k))).
proof.
  move=> hk.
  have hnonneg : 0 <= K - k by smt().
  have hsum : k + (K - k) = K by ring.
  have hsplit := iota_add 0 k (K - k) _ hnonneg; first smt().
  rewrite hsum /= in hsplit.
  by rewrite /gauss_trace_prefix /gauss_events hsplit map_cat foldl_cat.
qed.

lemma gauss_trace_prefix_full_stable buf n d values squares k K :
  0 <= k <= K =>
  (gauss_trace_prefix buf n d values squares k).`4 = n =>
  gauss_trace_prefix buf n d values squares K =
  gauss_trace_prefix buf n d values squares k.
proof.
  move=> hk hfull.
  rewrite (gauss_trace_prefix_extend buf n d values squares k K hk).
  apply gauss_trace_fold_full; smt().
qed.

lemma gauss_bit_as_indicator (event : gauss_event) :
  0 <= W64.to_uint event.`4 <= 1 =>
  W64.to_uint event.`4 = b2i (gauss_event_accepted event).
proof. rewrite /gauss_event_accepted /b2i; smt(). qed.

lemma gauss_trace_fold_count n d (state : gauss_trace_state) events :
  0 <= state.`4 <= n => gauss_events_are_bits events =>
  (foldl (gauss_trace_step n d) state events).`4 =
  min n (state.`4 + count gauss_event_accepted events).
proof.
  elim: events state => [|event events ih] state hs he.
  + rewrite /= /min; smt().
  have [hbit hbits] : 0 <= W64.to_uint event.`4 <= 1 /\ gauss_events_are_bits events.
  + by move: he; rewrite /gauss_events_are_bits /=.
  have [hstep hinc] := gauss_trace_step_count_bounds n d state event hs hbit.
  rewrite /= (ih (gauss_trace_step n d state event) hstep hbits).
  rewrite gauss_trace_step_count.
  have hc := count_ge0 gauss_event_accepted events.
  have heq := gauss_bit_as_indicator event hbit.
  rewrite /min; smt().
qed.

lemma gauss_trace_prefix_count_exact buf n d values squares k :
  0 <= n =>
  (gauss_trace_prefix buf n d values squares k).`4 =
  size (gauss_selected_events n (gauss_events buf k)).
proof.
  move=> hn; rewrite /gauss_trace_prefix gauss_trace_fold_count.
  + by rewrite /gauss_trace_initial /=.
  + exact: gauss_events_bits.
  rewrite /gauss_trace_initial /gauss_selected_events /= size_take 1:hn size_filter.
  rewrite /min; smt().
qed.


lemma gauss_take_append ['a] (n : int) (xs : 'a list) (x : 'a) : 0 <= n =>
  take n (xs ++ [x]) =
  if size (take n xs) < n then take n xs ++ [x] else take n xs.
proof.
  move=> hn; case (n <= size xs) => hs.
  + rewrite take_catl 1:hs size_takel 1:/# /=; smt().
  have hsn : size xs < n by smt().
  have hxs : size xs <= n by smt().
  have hall : size (xs ++ [x]) <= n by rewrite size_cat /=; smt().
  by rewrite (take_oversize n (xs ++ [x]) hall) (take_oversize n xs hxs) hsn.
qed.

(* Only committed output positions are described here: the slot at the
   current count can contain the most recently rejected speculative value. *)
op gauss_trace_stores (n : int) (d : bool) (state : gauss_trace_state)
    (xs : W64.t list) : bool =
  state.`4 = size xs /\
  forall j, 0 <= j < size xs => !d \/ j < n - 1 =>
    BArray4096.get64 state.`1 j = nth W64.zero xs j.

lemma gauss_trace_stores_step n d (state : gauss_trace_state)
    (event : gauss_event) xs :
  0 <= n <= 512 => size xs <= n =>
  gauss_trace_stores n d state xs =>
  0 <= W64.to_uint event.`4 <= 1 =>
  gauss_trace_stores n d (gauss_trace_step n d state event)
    (if size xs < n /\ gauss_event_accepted event then xs ++ [event.`1] else xs).
proof.
  move=> hn hsize [hcount hstored] hbit.
  case (n <= size xs) => hfull.
  + have hf : n <= state.`4 by smt().
    have hf' : !(size xs < n /\ gauss_event_accepted event) by smt().
    rewrite /gauss_trace_step hf /= hf' /gauss_trace_stores.
    smt().
  have hf : !(n <= state.`4) by smt().
  have hless : size xs < n by smt().
  rewrite /gauss_trace_step hf /= hcount hless /=.
  case (gauss_event_accepted event) => he.
  + have hae : W64.to_uint event.`4 = 1.
    + by move: he; rewrite /gauss_event_accepted.
    rewrite hae /gauss_trace_stores /= size_cat /=.
    move=> j hj hv; rewrite nth_cat.
    case (d /\ size xs = n - 1) => hd /=.
    - have hjlt : j < size xs by smt().
      rewrite hjlt /=; apply hstored; smt().
    rewrite BArray4096.get_set64E 1:(size_ge0 xs) 1:/#.
    case (size xs = j) => hjx.
    - by rewrite -hjx ltzz subzz /=.
    have hjlt : j < size xs by smt().
    rewrite hjlt /=; apply hstored; smt().
  have hae : W64.to_uint event.`4 = 0.
  + move: he; rewrite /gauss_event_accepted; smt().
  rewrite hae /gauss_trace_stores /=.
  move=> j hj hv.
  case (d /\ size xs = n - 1) => hd /=.
  + apply hstored; smt().
  rewrite BArray4096.get_set64E_neq 1:/#.
  apply hstored; smt().
qed.

lemma gauss_accepted_values_cat events tail :
  gauss_accepted_values (events ++ tail) =
  gauss_accepted_values events ++ gauss_accepted_values tail.
proof. by rewrite /gauss_accepted_values filter_cat map_cat. qed.

lemma gauss_selected_values_step n events (event : gauss_event) : 0 <= n =>
  take n (gauss_accepted_values (events ++ [event])) =
  if size (take n (gauss_accepted_values events)) < n /\ gauss_event_accepted event
  then take n (gauss_accepted_values events) ++ [event.`1]
  else take n (gauss_accepted_values events).
proof.
  move=> hn; rewrite gauss_accepted_values_cat.
  have hs : gauss_accepted_values [event] =
    if gauss_event_accepted event then [event.`1] else [].
  + by rewrite /gauss_accepted_values /=; case (gauss_event_accepted event).
  rewrite hs; case (gauss_event_accepted event) => he /=.
  + by rewrite gauss_take_append.
  by rewrite cats0.
qed.

lemma gauss_trace_prefix_stores buf n d values squares k :
  0 <= n <= 512 => 0 <= k =>
  gauss_trace_stores n d (gauss_trace_prefix buf n d values squares k)
    (take n (gauss_accepted_values (gauss_events buf k))).
proof.
  move=> hn hk; elim: k hk => [|k hk ih].
  + rewrite gauss_trace_prefix0 gauss_events0 /gauss_accepted_values /=
      /gauss_trace_stores /gauss_trace_initial /=; smt().
  rewrite gauss_trace_prefixS 1:hk gauss_eventsS 1:hk
    gauss_selected_values_step 1:/#.
  apply gauss_trace_stores_step.
  + exact hn.
  + apply size_take_le; smt().
  + exact ih.
  exact (gauss_event_accept_bit buf k).
qed.

lemma gauss_trace_prefix_value_at buf n d values squares k j :
  0 <= n <= 512 => 0 <= k =>
  0 <= j < (gauss_trace_prefix buf n d values squares k).`4 =>
  !d \/ j < n - 1 =>
  BArray4096.get64 (gauss_trace_prefix buf n d values squares k).`1 j =
    nth W64.zero (take n (gauss_accepted_values (gauss_events buf k))) j.
proof.
  move=> hn hk hj hv.
  have [hc hs] := gauss_trace_prefix_stores buf n d values squares k hn hk.
  apply hs; smt().
qed.

op gauss_visible_limit (n : int) (d : bool) : int =
  if d then max 0 (n - 1) else n.

lemma gauss_visible_limit_bounds n d : 0 <= n =>
  0 <= gauss_visible_limit n d <= n.
proof. rewrite /gauss_visible_limit; smt(). qed.

lemma gauss_trace_stores_observed n d (state : gauss_trace_state) xs :
  0 <= n => size xs <= n => gauss_trace_stores n d state xs =>
  map (fun j => BArray4096.get64 state.`1 j)
    (iota_ 0 (min state.`4 (gauss_visible_limit n d))) =
  take (gauss_visible_limit n d) xs.
proof.
  move=> hn hlen [hc hs].
  have hlimit := gauss_visible_limit_bounds n d hn.
  have hsize := size_ge0 xs.
  apply (List.eq_from_nth W64.zero).
  + rewrite size_map size_iota size_take 1:/#; smt().
  move=> j; rewrite size_map size_iota; move=> hj.
  rewrite (nth_map 0) 1:size_iota 1:/# nth_iota 1:/# /= nth_take 1:/# 1:/#.
  apply hs; first smt().
  move: hj; rewrite /gauss_visible_limit; smt().
qed.

(* Read only the accepted prefix. With dont=true the requested final slot
   is deliberately omitted; rejected speculative writes are outside it. *)
lemma gauss_trace_prefix_accepted_sequence buf n d values squares k :
  0 <= n <= 512 => 0 <= k =>
  let state = gauss_trace_prefix buf n d values squares k in
  map (fun j => BArray4096.get64 state.`1 j)
    (iota_ 0 (min state.`4 (gauss_visible_limit n d))) =
  take (gauss_visible_limit n d) (gauss_accepted_values (gauss_events buf k)).
proof.
  move=> hn hk /=.
  have hn0 : 0 <= n by smt().
  have hs := gauss_trace_prefix_stores buf n d values squares k hn hk.
  rewrite (gauss_trace_stores_observed n d
    (gauss_trace_prefix buf n d values squares k)
    (take n (gauss_accepted_values (gauss_events buf k))) hn0 _ hs).
  + exact (size_take_le n (gauss_accepted_values (gauss_events buf k)) hn0).
  have hv := gauss_visible_limit_bounds n d hn0.
  have hle : gauss_visible_limit n d <= n by smt().
  by rewrite take_take hle.
qed.

lemma gauss_trace_prefix_accepted_sequence_plain buf n values squares k :
  0 <= n <= 512 => 0 <= k =>
  let state = gauss_trace_prefix buf n false values squares k in
  map (fun j => BArray4096.get64 state.`1 j) (iota_ 0 state.`4) =
  take n (gauss_accepted_values (gauss_events buf k)).
proof.
  move=> hn hk /=.
  have hn0 : 0 <= n by smt().
  have hc := gauss_trace_prefix_count_bounds buf n false values squares k hn0 hk.
  have hs := gauss_trace_prefix_accepted_sequence buf n false values squares k hn hk.
  rewrite /gauss_visible_limit /= in hs.
  have hmin : min (gauss_trace_prefix buf n false values squares k).`4 n =
    (gauss_trace_prefix buf n false values squares k).`4 by smt().
  by move: hs; rewrite hmin.
qed.

lemma gauss_trace_step_dummy_last n (state : gauss_trace_state) event :
  BArray4096.get64 (gauss_trace_step n true state event).`1 (n - 1) =
  BArray4096.get64 state.`1 (n - 1).
proof.
  rewrite /gauss_trace_step.
  case (n <= state.`4) => hfull //=.
  case (state.`4 = n - 1) => hd //=.
  by rewrite BArray4096.get_set64E_neq.
qed.

lemma gauss_trace_fold_dummy_last n (state : gauss_trace_state) events :
  BArray4096.get64 (foldl (gauss_trace_step n true) state events).`1 (n - 1) =
  BArray4096.get64 state.`1 (n - 1).
proof.
  elim: events state => [|event events ih] state //=.
  by rewrite ih gauss_trace_step_dummy_last.
qed.

lemma gauss_trace_prefix_dummy_last buf n values squares k :
  BArray4096.get64 (gauss_trace_prefix buf n true values squares k).`1 (n - 1) =
  BArray4096.get64 values (n - 1).
proof.
  by rewrite /gauss_trace_prefix gauss_trace_fold_dummy_last /gauss_trace_initial /=.
qed.
