require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import SigmaCorrectness GaussianPayloadSpec GaussianPayloadEncoding
  GaussianTraceSpec GaussianTraceProperties GaussianSequenceCorrectness
  GaussianAccumulatorCorrectness GaussianStreamAccumulator HyperballGaussianBounds
  GaussianIidBufferSpec GaussianIidBufferPath GaussianIidVisible GaussianWindowSpec.

(* History contains every accepted payload, including an unstored dummy.
   The square budget is cumulative across earlier polynomial samplers. *)
op [opaque] gpt_state (previous : int) (initial_values : BArray32768.t)
    (initial_squares : BArray16.t) (n offset : int) (history : int list)
    (values : BArray32768.t) (squares : BArray16.t) : bool =
  size history <= n /\
  gib_visible values offset (size history) = map gpd_magnitude (take 256 history) /\
  gauss_big_output_frame initial_values values offset 256 /\
  hb_cumulative_square_bound (previous + size history) squares /\
  gauss_stream_value squares = gauss_stream_value initial_squares + gpd_sum history.

lemma gpt_sum_cat history tail :
  gpd_sum (history++tail) = gpd_sum history + gpd_sum tail.
proof.
  elim: history => [|code history ih].
  + by rewrite /gpd_sum /=.
  rewrite /gpd_sum /= in ih.
  rewrite /gpd_sum /=; smt().
qed.

lemma gpt_pack_magnitudes (events : gauss_event list) :
  map gpd_magnitude (map gpd_pack events) =
    map (fun (event : gauss_event) => W64.to_uint event.`1) events.
proof.
  rewrite -map_comp; apply eq_in_map => event he.
  by rewrite /(\o) gpd_pack_magnitude.
qed.

lemma gpt_selected_magnitudes pending requested :
  map gpd_magnitude (gpd_selected pending requested) = take requested (gib_accepted pending).
proof.
  by rewrite /gpd_selected gpt_pack_magnitudes /gauss_selected_events map_take
    /gib_accepted /gauss_accepted_values /gpd_events -map_comp.
qed.

lemma gpt_selected_count pending requested : 0 <= requested =>
  size (gpd_selected pending requested) = min requested (size (gib_accepted pending)).
proof.
  move=> hn; by rewrite (gpd_selected_count pending requested hn)
    /gib_accepted /gauss_accepted_values !size_map size_filter /gpd_events.
qed.

lemma gpt_events_bounded pending : hb_events_bounded (gpd_events pending).
proof.
  rewrite /hb_events_bounded /gpd_events /gauss_events all_map.
  apply List.allP => i hi; rewrite /gauss_event_at.
  exact (hb_sigma76_event_bounded (gauss_chunk (BArray8192.of_list pending) (26*i))).
qed.

lemma gpt_selected_bounded pending requested :
  hb_events_bounded (gauss_selected_events requested (gpd_events pending)).
proof.
  have hall := gpt_events_bounded pending.
  rewrite /hb_events_bounded; apply List.allP => event he.
  have hf := mem_take requested (filter gauss_event_accepted (gpd_events pending)) event he.
  rewrite mem_filter in hf.
  move: hall; rewrite /hb_events_bounded List.allP => hall.
  apply hall; smt().
qed.

lemma gpt_consume_frame values squares count pending n accepted offset :
  (n=256 \/ n=257) => 0 <= accepted < n =>
  0 <= offset => offset+n <= 4096 =>
  gauss_big_output_frame values
    (gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted)).`1
    offset 256.
proof.
  move=> hn ha ho hcap; rewrite /gauss_big_output_frame => j hj hout.
  rewrite /gib_consume /= gib_commit_get 1:/# 1:/# 1:/# 1:hj.
  have hend : offset+accepted+(n-accepted) = offset+n by ring.
  rewrite hend.
  case (offset+accepted <= j < offset+n) => hin //=.
  have hn257 : n=257 by smt().
  have hidx : j-(offset+accepted) = (n-accepted)-1 by smt().
  rewrite hidx hn257 /gauss_trace_result /= gauss_trace_prefix_dummy_last
    gauss_output_window_get 1:/#.
  smt().
qed.

lemma gpt_frame_transitive initial before after offset :
  gauss_big_output_frame initial before offset 256 =>
  gauss_big_output_frame before after offset 256 =>
  gauss_big_output_frame initial after offset 256.
proof.
  rewrite /gauss_big_output_frame; move=> h1 h2 j hj hout.
  by rewrite (h2 j hj hout) (h1 j hj hout).
qed.

lemma gpt_initial previous initial_values initial_squares n offset :
  0 <= n => hb_cumulative_square_bound previous initial_squares =>
  gpt_state previous initial_values initial_squares n offset [] initial_values initial_squares.
proof.
  move=> hn hp.
  by rewrite /gpt_state /gpd_sum /= giv_empty gauss_big_output_frame_refl.
qed.

lemma gpt_visible_append n history pending : size history <= 256 => 256 <= n =>
  map gpd_magnitude (take 256 (history ++ gpd_selected pending (n-size history))) =
    take 256 (map gpd_magnitude (take 256 history) ++ gib_accepted pending).
proof.
  move=> hh hn.
  have htake : take 256 history = history by apply take_oversize; exact hh.
  have hlen : size (map gpd_magnitude history) = size history by rewrite size_map.
  have hlen256 : size (map gpd_magnitude history) <= 256 by rewrite hlen.
  rewrite htake map_take map_cat gpt_selected_magnitudes
    (take_catr (map gpd_magnitude history) (take (n-size history) (gib_accepted pending)) 256 hlen256)
    (take_catr (map gpd_magnitude history) (gib_accepted pending) 256 hlen256)
    hlen take_take.
  have -> : 256-size history <= n-size history by smt().
  trivial.
qed.

lemma gpt_consume_accumulator previous values squares count pending requested dummy offset :
  hb_cumulative_square_bound previous squares =>
  0 <= requested <= 512 => previous+requested <= 2818 =>
  let result = gib_consume values squares count pending requested dummy offset in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  q = size (gpd_selected pending requested) /\
  hb_cumulative_square_bound (previous+q) result.`2 /\
  gauss_stream_value result.`2 = gauss_stream_value squares + gpd_sum (gpd_selected pending requested).
proof.
  move=> hp hn hbudget /=.
  have [hlo hhi] := hb_cumulative_canonical previous squares hp.
  have hhi_le : W64.to_uint (BArray16.get64 squares 1) <= 281474976710656 by smt().
  have hlocal := gauss_stream_acc_initial squares hlo hhi_le.
  pose trace := gauss_trace_result (BArray8192.of_list pending) requested (size pending)
    dummy (gauss_output_window values offset) squares count.
  pose events := gauss_selected_events requested (gpd_events pending).
  have hav := size_ge0 pending.
  have [hq [hacc hvalue]] := gauss_trace_result_stream_accumulator
    (gauss_stream_value squares) 0 (BArray8192.of_list pending) requested (size pending)
    dummy (gauss_output_window values offset) squares count hlocal hn hav.
  have hsize := gauss_stream_selected_size (BArray8192.of_list pending) requested
    (size pending %/ 26) _; first smt().
  have hevents := gpt_selected_bounded pending requested.
  have hsum := hb_event_value_sum_bound events hevents.
  have hc : hb_cumulative_square_bound (previous + size events) trace.`2.
  + have hlow : W64.to_uint (BArray16.get64 trace.`2 0) < 281474976710656 by
      move: hacc; rewrite /gauss_stream_acc_ok; smt().
    rewrite /hb_cumulative_square_bound /hb_event_max in hp.
    rewrite /hb_event_max in hsum.
    rewrite /hb_cumulative_square_bound /hb_event_max.
    smt().
  have hdecode : gpd_sum (gpd_selected pending requested) = gauss_event_value_sum events.
  + by rewrite /gpd_selected gpd_sum_pack /events.
  rewrite /gib_consume /= -/trace /gpd_selected size_map -/events hdecode.
  smt().
qed.

lemma gpt_consume previous initial_values initial_squares values squares count pending
    n offset history :
  (n=256 \/ n=257) => 0 <= offset => offset+n <= 4096 =>
  size pending <= 8192 => previous+n <= 2818 => size history < n =>
  gpt_state previous initial_values initial_squares n offset history values squares =>
  let result = gib_consume values squares count pending (n-size history) (n=257)
    (offset+size history) in
  let following = gpd_scan n history pending in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  q = size (gpd_selected pending (n-size history)) /\
  size following = size history+q /\
  gpt_state previous initial_values initial_squares n offset following result.`1 result.`2.
proof.
  move=> hn ho hcap hbytes hbudget hactive hstate /=.
  have [hsize [hvisible [hframe [hcumulative hvalue]]]] :
    size history <= n /\
    gib_visible values offset (size history) = map gpd_magnitude (take 256 history) /\
    gauss_big_output_frame initial_values values offset 256 /\
    hb_cumulative_square_bound (previous+size history) squares /\
    gauss_stream_value squares = gauss_stream_value initial_squares+gpd_sum history
    by move: hstate; rewrite /gpt_state.
  have hrequested : 0 <= n-size history <= 512 by smt(size_ge0).
  have hremaining : (previous+size history)+(n-size history) <= 2818 by smt().
  have hhistory : 0 <= size history <= n by smt(size_ge0).
  have hbefore : 0 <= size history < n by smt(size_ge0).
  pose result := gib_consume values squares count pending (n-size history) (n=257)
    (offset+size history).
  pose following := gpd_scan n history pending.
  pose selected := gpd_selected pending (n-size history).
  pose q := W64.to_uint (BArray8.get64 result.`3 0).
  have [hq [hbound hsum]] := gpt_consume_accumulator (previous+size history)
    values squares count pending (n-size history) (n=257) (offset+size history)
    hcumulative hrequested hremaining.
  have hfollowing : following = history++selected by
    exact (gpd_scan_selected n history pending hhistory hbytes).
  have hqbound : 0 <= q <= n-size history.
  + have h := gauss_stream_selected_size (BArray8192.of_list pending) (n-size history)
      (size pending %/ 26) _; first smt().
    move: hq; rewrite /gpd_selected size_map /gpd_events; smt().
  have hcount : size following = size history+q by rewrite hfollowing size_cat; smt().
  have [_ hnewvisible] := giv_consume values squares count pending n (size history)
    offset hn hbefore ho hcap.
  have hprojection : map gpd_magnitude (take 256 following) =
      take 256 (map gpd_magnitude (take 256 history) ++ gib_accepted pending).
  + rewrite hfollowing /selected.
    apply gpt_visible_append; smt().
  have hvisible' : gib_visible result.`1 offset (size following) =
      map gpd_magnitude (take 256 following) by smt().
  have hstepframe := gpt_consume_frame values squares count pending n (size history)
    offset hn hbefore ho hcap.
  have hframe' := gpt_frame_transitive initial_values values result.`1 offset hframe hstepframe.
  have hsum' : gpd_sum following = gpd_sum history+gpd_sum selected by
    rewrite hfollowing gpt_sum_cat.
  have hbound' : hb_cumulative_square_bound (previous+size following) result.`2 by smt().
  rewrite /gpt_state -/result -/following -/q.
  smt().
qed.
