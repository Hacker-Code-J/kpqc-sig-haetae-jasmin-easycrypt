require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianAccumulatorCorrectness GaussianTraceSpec GaussianTraceProperties
  GaussianSequenceCorrectness GaussianOffsetBridge GaussianWindowSpec GaussianConsumerSpec.

op gauss_stream_value (squares : BArray16.t) : int =
  gauss_limb_value (BArray16.get64 squares 0) (BArray16.get64 squares 1).

op gauss_event_value_sum (events : gauss_event list) : int =
  gauss_low_sum events + 281474976710656 * gauss_high_sum events.

op gauss_stream_events_valid (events : gauss_event list) : bool =
  all (fun (e : gauss_event) =>
    0 <= W64.to_uint e.`2 < 281474976710656 /\
    0 <= W64.to_uint e.`3 < 274877906944) events.

(* The high limb is deliberately not constrained to 48 bits after a refill.
   A total integer budget, with at most 512 accepted events, supplies headroom. *)
op gauss_stream_acc_ok (initial_value accepted : int) (squares : BArray16.t) : bool =
  0 <= initial_value < 158456325028528675187087900672 /\
  0 <= accepted <= 512 /\
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
  gauss_stream_value squares <= initial_value + accepted * 77371252455336267181195263.

op gauss_stream_add_events (squares : BArray16.t) (events : gauss_event list) : BArray16.t =
  let lo = BArray16.get64 squares 0 + W64.of_int (gauss_low_sum events) in
  let hi = BArray16.get64 squares 1 + W64.of_int (gauss_high_sum events) in
  let nr = gauss_normalize lo hi in
  BArray16.set64 (BArray16.set64 squares 0 nr.`1) 1 nr.`2.

lemma gauss_stream_value_nonnegative squares : 0 <= gauss_stream_value squares.
proof.
  have h0 := W64.to_uint_cmp (BArray16.get64 squares 0).
  have h1 := W64.to_uint_cmp (BArray16.get64 squares 1).
  rewrite /gauss_stream_value /gauss_limb_value; smt().
qed.

lemma gauss_stream_acc_initial squares :
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  W64.to_uint (BArray16.get64 squares 1) <= 281474976710656 =>
  gauss_stream_acc_ok (gauss_stream_value squares) 0 squares.
proof.
  move=> h0 h1.
  have hnonneg := gauss_stream_value_nonnegative squares.
  rewrite /gauss_stream_acc_ok /gauss_stream_value /gauss_limb_value; smt().
qed.

lemma gauss_event_limb_value_bound (event : gauss_event) :
  0 <= W64.to_uint event.`2 < 281474976710656 =>
  0 <= W64.to_uint event.`3 < 274877906944 =>
  0 <= gauss_limb_value event.`2 event.`3 < 77371252455336267181195264.
proof. move=> hlo hhi; rewrite /gauss_limb_value; smt(). qed.

lemma gauss_stream_event_sum_bounds events :
  gauss_stream_events_valid events =>
  0 <= gauss_low_sum events <= size events * 281474976710655 /\
  0 <= gauss_high_sum events <= size events * 274877906943 /\
  0 <= gauss_event_value_sum events <= size events * 77371252455336267181195263.
proof.
  move=> hv.
  have hlo : all (fun (e : gauss_event) =>
      0 <= W64.to_uint e.`2 < 281474976710656) events.
  + apply List.allP => e he.
    move: hv; rewrite /gauss_stream_events_valid List.allP => hv.
    have := hv e he; smt().
  have hhi : all (fun (e : gauss_event) =>
      0 <= W64.to_uint e.`3 < 274877906944) events.
  + apply List.allP => e he.
    move: hv; rewrite /gauss_stream_events_valid List.allP => hv.
    have := hv e he; smt().
  have hl := gauss_low_sum_bound events hlo.
  have hh := gauss_high_sum_bound events hhi.
  rewrite /gauss_event_value_sum; smt().
qed.

lemma gauss_event_value_sum_cat events tail :
  gauss_event_value_sum (events ++ tail) =
    gauss_event_value_sum events + gauss_event_value_sum tail.
proof.
  elim: events => [|event events ih].
  + by rewrite /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /=.
  rewrite /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /= in ih.
  rewrite /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /=.
  smt().
qed.

lemma gauss_stream_add_normalized squares events :
  W64.to_uint (BArray16.get64 (gauss_stream_add_events squares events) 0) < 281474976710656.
proof.
  rewrite /gauss_stream_add_events /= gauss_normalize_low_uint.
  have := modz_cmp (W64.to_uint (BArray16.get64 squares 0 +
    W64.of_int (gauss_low_sum events))) 281474976710656; smt().
qed.

lemma gauss_stream_add_headroom initial_value accepted squares events :
  gauss_stream_acc_ok initial_value accepted squares =>
  gauss_stream_events_valid events => accepted + size events <= 512 =>
  W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events < 18446744073709551616 /\
  W64.to_uint (BArray16.get64 squares 1) + gauss_high_sum events +
    (W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events) %/ 281474976710656
      < 18446744073709551616.
proof.
  move=> hok hevents hbudget.
  have [hl [hh hv]] := gauss_stream_event_sum_bounds events hevents.
  have hsize := size_ge0 events.
  have hd := divz_eq (W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events)
    281474976710656.
  have /= hr := modz_cmp (W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events)
    281474976710656.
  rewrite /gauss_stream_acc_ok /gauss_stream_value /gauss_limb_value in hok.
  rewrite /gauss_event_value_sum in hv.
  smt().
qed.

lemma gauss_stream_add_exact squares events :
  0 <= gauss_low_sum events => 0 <= gauss_high_sum events =>
  W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events < 18446744073709551616 =>
  W64.to_uint (BArray16.get64 squares 1) + gauss_high_sum events +
    (W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events) %/ 281474976710656
      < 18446744073709551616 =>
  gauss_stream_value (gauss_stream_add_events squares events) =
    gauss_stream_value squares + gauss_event_value_sum events.
proof.
  move=> hl hh hlow hhigh.
  have hw0 := W64.to_uint_cmp (BArray16.get64 squares 0).
  have hw1 := W64.to_uint_cmp (BArray16.get64 squares 1).
  have hd := divz_eq (W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events)
    281474976710656.
  have /= hr := modz_cmp (W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events)
    281474976710656.
  have hlo : W64.to_uint (BArray16.get64 squares 0 + W64.of_int (gauss_low_sum events)) =
      W64.to_uint (BArray16.get64 squares 0) + gauss_low_sum events.
  + rewrite W64.to_uintD W64.of_uintK modzDmr modz_small; smt().
  have hhi : W64.to_uint (BArray16.get64 squares 1 + W64.of_int (gauss_high_sum events)) =
      W64.to_uint (BArray16.get64 squares 1) + gauss_high_sum events.
  + rewrite W64.to_uintD W64.of_uintK modzDmr modz_small; smt().
  rewrite /gauss_stream_value /gauss_stream_add_events /= gauss_normalize_value_exact.
  + rewrite hlo hhi; exact hhigh.
  rewrite /gauss_limb_value hlo hhi /gauss_event_value_sum /=; ring.
qed.

lemma gauss_stream_add_preserves initial_value accepted squares events :
  gauss_stream_acc_ok initial_value accepted squares =>
  gauss_stream_events_valid events => accepted + size events <= 512 =>
  gauss_stream_acc_ok initial_value (accepted + size events) (gauss_stream_add_events squares events) /\
  gauss_stream_value (gauss_stream_add_events squares events) =
    gauss_stream_value squares + gauss_event_value_sum events.
proof.
  move=> hok hevents hbudget.
  have [hl [hh hv]] := gauss_stream_event_sum_bounds events hevents.
  have [hlo hhi] := gauss_stream_add_headroom initial_value accepted squares events hok hevents hbudget.
  have hln : 0 <= gauss_low_sum events by smt().
  have hhn : 0 <= gauss_high_sum events by smt().
  have he := gauss_stream_add_exact squares events hln hhn hlo hhi.
  have hc := gauss_stream_add_normalized squares events.
  have hs := size_ge0 events.
  rewrite /gauss_stream_acc_ok in hok.
  rewrite /gauss_stream_acc_ok; smt().
qed.

lemma gauss_stream_selected_valid buf n k :
  gauss_stream_events_valid (gauss_selected_events n (gauss_events buf k)).
proof.
  have hall : gauss_stream_events_valid (gauss_events buf k).
  + rewrite /gauss_stream_events_valid /gauss_events all_map.
    apply List.allP => i _.
    have hl := gauss_event_low_bound buf i.
    have hh := gauss_event_high_bound buf i; smt().
  rewrite /gauss_stream_events_valid; apply List.allP => e he.
  have hf := mem_take n (filter gauss_event_accepted (gauss_events buf k)) e he.
  rewrite mem_filter in hf; have [_ hevents] := hf.
  move: hall; rewrite /gauss_stream_events_valid List.allP => hall.
  exact (hall e hevents).
qed.

lemma gauss_stream_selected_size buf n k :
  0 <= n => 0 <= size (gauss_selected_events n (gauss_events buf k)) <= n.
proof.
  move=> hn.
  have hs := size_ge0 (gauss_selected_events n (gauss_events buf k)).
  have ht := size_take_le n (filter gauss_event_accepted (gauss_events buf k)) hn.
  rewrite /gauss_selected_events in hs.
  rewrite /gauss_selected_events; smt().
qed.

lemma gauss_trace_result_add_events buf n b d values squares count0 :
  0 <= n =>
  (gauss_trace_result buf n b d values squares count0).`2 =
    gauss_stream_add_events squares (gauss_selected_events n (gauss_events buf (b %/ 26))).
proof.
  move=> hn.
  have [hl hh] := gauss_trace_prefix_word_sums buf n d values squares (b %/ 26) hn.
  by rewrite /gauss_trace_result /gauss_stream_add_events /= hl hh
    /gauss_selected_low_sum /gauss_selected_high_sum.
qed.

lemma gauss_trace_result_stream_accumulator initial_value accepted buf n b d values squares count0 :
  gauss_stream_acc_ok initial_value accepted squares =>
  0 <= n <= 512 - accepted => 0 <= b =>
  let result = gauss_trace_result buf n b d values squares count0 in
  let events = gauss_selected_events n (gauss_events buf (b %/ 26)) in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  q = size events /\
  gauss_stream_acc_ok initial_value (accepted + q) result.`2 /\
  gauss_stream_value result.`2 = gauss_stream_value squares + gauss_event_value_sum events.
proof.
  move=> hok hn hb /=.
  have hn0 : 0 <= n by smt().
  have hn512 : 0 <= n <= 512 by move: hok; rewrite /gauss_stream_acc_ok; smt().
  have hv := gauss_stream_selected_valid buf n (b %/ 26).
  have hsize := gauss_stream_selected_size buf n (b %/ 26) hn0.
  have hbudget : accepted + size (gauss_selected_events n (gauss_events buf (b %/ 26))) <= 512
    by smt().
  have [hacc heq] := gauss_stream_add_preserves initial_value accepted squares
    (gauss_selected_events n (gauss_events buf (b %/ 26))) hok hv hbudget.
  have hcount := gauss_trace_result_count_exact buf n b d values squares count0 hn512 hb.
  have hsq := gauss_trace_result_add_events buf n b d values squares count0 hn0.
  rewrite -/(gauss_selected_events n (gauss_events buf (b %/ 26))) in hcount.
  rewrite !hcount !hsq; smt().
qed.

lemma sample_gauss_at_stream_accumulator_correct
    (initial_value accepted : int) (initial : BArray32768.t) (buf : BArray8192.t)
    (n b bo oo : int) (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 - accepted /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo /\
    gauss_stream_acc_ok initial_value accepted squares
    ==>
    let events = gauss_selected_events n
      (gauss_events (gauss_input_window buf bo) (b %/ 26)) in
    let q = W64.to_uint (BArray8.get64 res.`3 0) in
    q = size events /\
    gauss_stream_acc_ok initial_value (accepted + q) res.`2 /\
    gauss_stream_value res.`2 = gauss_stream_value squares + gauss_event_value_sum events /\
    gauss_big_output_frame initial res.`1 oo n].
proof.
  conseq (GaussianOffsetBridge.sample_gauss_at_trace_correct
    initial buf n b bo oo d squares count0) => //.
  + move=> &m; rewrite /gauss_stream_acc_ok; smt().
  move=> &m hpre result [htrace hframe].
  have hok : gauss_stream_acc_ok initial_value accepted squares by smt().
  have hn : 0 <= n <= 512 - accepted by smt().
  have hb : 0 <= b by smt().
  have hs : result.`2 =
      (gauss_trace_result (gauss_input_window buf bo) n b (d <> W64.zero)
        (gauss_output_window initial oo) squares count0).`2 by smt().
  have hc : result.`3 =
      (gauss_trace_result (gauss_input_window buf bo) n b (d <> W64.zero)
        (gauss_output_window initial oo) squares count0).`3 by smt().
  have hpost := gauss_trace_result_stream_accumulator initial_value accepted
    (gauss_input_window buf bo) n b (d <> W64.zero)
    (gauss_output_window initial oo) squares count0 hok hn hb.
  rewrite /= -hs -hc in hpost.
  smt().
qed.

(* No termination assumption for an unbounded refill loop is made. This
   finite-partition theorem composes any number of already accepted batches. *)
lemma gauss_stream_finite_partitions initial_value (batches : gauss_event list list) :
  forall accepted squares,
  gauss_stream_acc_ok initial_value accepted squares =>
  all gauss_stream_events_valid batches => accepted + size (flatten batches) <= 512 =>
  let result = foldl gauss_stream_add_events squares batches in
  gauss_stream_acc_ok initial_value (accepted + size (flatten batches)) result /\
  gauss_stream_value result = gauss_stream_value squares + gauss_event_value_sum (flatten batches).
proof.
  elim: batches => [|events batches ih] accepted squares hok hv hb.
  + by rewrite /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /=.
  have [he htail] : gauss_stream_events_valid events /\ all gauss_stream_events_valid batches
    by move: hv; rewrite /=.
  have hs := size_ge0 (flatten batches).
  have hfirst : accepted + size events <= 512 by move: hb; rewrite flatten_cons size_cat; smt().
  have [hnext heq] := gauss_stream_add_preserves initial_value accepted squares events hok he hfirst.
  have hrest : accepted + size events + size (flatten batches) <= 512
    by move: hb; rewrite flatten_cons size_cat; smt().
  have [hfinal hvalue] := ih (accepted + size events) (gauss_stream_add_events squares events)
    hnext htail hrest.
  rewrite !flatten_cons !size_cat /= gauss_event_value_sum_cat.
  rewrite heq in hvalue.
  smt().
qed.
