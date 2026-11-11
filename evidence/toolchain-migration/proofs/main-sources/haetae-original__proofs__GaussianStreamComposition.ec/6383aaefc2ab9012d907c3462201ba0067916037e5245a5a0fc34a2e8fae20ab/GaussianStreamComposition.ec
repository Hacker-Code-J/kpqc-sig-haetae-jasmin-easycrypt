require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianStreamSpec GaussianStreamBuffer GaussianStreamSequence GaussianStreamAccumulator
  GaussianOffsetBridge GaussianTraceSpec GaussianTraceProperties
  GaussianSequenceCorrectness GaussianConsumerSpec GaussianWindowSpec.

lemma gs_visible_requested n : n = 256 \/ n = 257 =>
  gauss_visible_limit n (n = 257) = 256.
proof. rewrite /gauss_visible_limit; smt(). qed.

lemma gs_dummy_word n : n = 256 \/ n = 257 =>
  (W64.of_int (n - 256) <> W64.zero) = (n = 257).
proof. move=> [-> | ->]; by rewrite W64.to_uint_eq W64.to_uint0 W64.of_uintK /=. qed.

lemma gs_progress_initial f initial initial_squares n oo :
  n = 256 \/ n = 257 =>
  W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 =>
  W64.to_uint (BArray16.get64 initial_squares 1) <= 281474976710656 =>
  gs_progress f initial initial initial_squares initial_squares n oo 0 0.
proof.
  move=> hn hlo hhi.
  have ha := gauss_stream_acc_initial initial_squares hlo hhi.
  rewrite /gs_progress /gauss_selected_events /gauss_stream_events iota0 1://
    /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /=.
  smt(gauss_big_output_frame_refl).
qed.

lemma gs_selected_values n events :
  map (fun (event : gauss_event) => event.`1) (gauss_selected_events n events) =
    take n (gauss_accepted_values events).
proof. by rewrite /gauss_selected_events map_take /gauss_accepted_values. qed.

lemma gs_frame_extend initial before after oo n accepted :
  0 <= accepted <= n =>
  gauss_big_output_frame initial before oo n =>
  gauss_big_output_frame before after (oo + accepted) (n - accepted) =>
  gauss_big_output_frame initial after oo n.
proof. rewrite /gauss_big_output_frame; smt(). qed.

lemma gs_frame_prefix before after oo n accepted j :
  0 <= oo => oo + n <= 4096 => 0 <= accepted <= n => 0 <= j < accepted =>
  gauss_big_output_frame before after (oo + accepted) (n - accepted) =>
  BArray32768.get64 after (oo + j) = BArray32768.get64 before (oo + j).
proof. rewrite /gauss_big_output_frame; smt(). qed.

lemma gs_visible_index n dummy count j :
  0 <= j < min count (gauss_visible_limit n dummy) =>
  0 <= j < count /\ (!dummy \/ j < n - 1).
proof. rewrite /gauss_visible_limit; smt(). qed.

lemma gs_trace_value_at buf requested available dummy values squares count0 j :
  0 <= requested <= 512 => 0 <= available =>
  let result = gauss_trace_result buf requested available dummy values squares count0 in
  0 <= j < min (W64.to_uint (BArray8.get64 result.`3 0))
    (gauss_visible_limit requested dummy) =>
  BArray4096.get64 result.`1 j =
    nth W64.zero (take requested (gauss_accepted_values
      (gauss_events buf (available %/ 26)))) j.
proof.
  move=> hn hb /= hj.
  have hk : 0 <= available %/ 26 by rewrite divz_ge0.
  have hc := gauss_trace_result_count buf requested available dummy values squares count0 hn hb.
  move: hj; rewrite hc => hj.
  have [hjcount hjvisible] := gs_visible_index requested dummy
    (gauss_trace_prefix buf requested dummy values squares (available %/ 26)).`4 j hj.
  rewrite /gauss_trace_result /=.
  exact (gauss_trace_prefix_value_at buf requested dummy values squares
    (available %/ 26) j hn hk hjcount hjvisible).
qed.

lemma gs_trace_dummy_at buf requested available values squares count0 :
  BArray4096.get64 (gauss_trace_result buf requested available true values squares count0).`1
    (requested - 1) = BArray4096.get64 values (requested - 1).
proof. by rewrite /gauss_trace_result /= gauss_trace_prefix_dummy_last. qed.

lemma gs_buffer_events_append f buf bo available attempts :
  0 <= attempts => 0 <= available <= 8192 =>
  gs_buffer_segment f buf bo (26 * attempts) available =>
  gauss_stream_events f (attempts + available %/ 26) =
    gauss_stream_events f attempts ++
    gauss_events (gauss_input_window buf bo) (available %/ 26).
proof.
  move=> ha hb hbuf.
  have hm : 0 <= available %/ 26 by rewrite divz_ge0; smt().
  have hd := divz_eq available 26.
  have hr := modz_cmp available 26.
  apply gauss_stream_events_append_buffer; first 2 smt().
  move=> j hj.
  rewrite gauss_input_window_get 1:/#.
  apply (hbuf j); smt().
qed.

lemma gs_progress_consume f initial current initial_squares squares
    n oo attempts accepted buf available bo count0
    (result : BArray32768.t * BArray16.t * BArray8.t) :
  gs_progress f initial current initial_squares squares n oo attempts accepted =>
  accepted < n => 0 <= oo => oo + n <= 4096 =>
  0 <= available => 0 <= bo => bo + available <= 8192 =>
  gs_buffer_segment f buf bo (26 * attempts) available =>
  (gauss_output_window result.`1 (oo + accepted), result.`2, result.`3) =
    gauss_trace_result (gauss_input_window buf bo) (n - accepted) available (n = 257)
      (gauss_output_window current (oo + accepted)) squares count0 =>
  gauss_big_output_frame current result.`1 (oo + accepted) (n - accepted) =>
  gs_progress f initial result.`1 initial_squares result.`2 n oo
    (attempts + available %/ 26) (accepted + W64.to_uint (BArray8.get64 result.`3 0)).
proof.
  move=> hp hlt hoo hend hb hbo hcap hbuf htrace hframe.
  have [hn [ha [hc [hcount [hvalues [holdframe [hdummy [hacc hsum]]]]]]]] := hp.
  have hn0 : 0 <= n by smt().
  have hminaccepted : min accepted 256 = accepted by smt().
  have hremaining : 0 <= n - accepted <= 512 - accepted by smt().
  have hremaining512 : 1 <= n - accepted <= 512 by smt().
  have hbytes : 0 <= available <= 8192 by smt().
  have hchunks : 0 <= available %/ 26 by rewrite divz_ge0.
  have hprefix := gs_buffer_events_append f buf bo available attempts ha hbytes hbuf.
  pose next_events := gauss_events (gauss_input_window buf bo) (available %/ 26).
  pose q := W64.to_uint (BArray8.get64 result.`3 0).
  have [hq [hnewacc hnewsum]] := gauss_trace_result_stream_accumulator
    (gauss_stream_value initial_squares) accepted (gauss_input_window buf bo)
    (n - accepted) available (n = 257) (gauss_output_window current (oo + accepted))
    squares count0 hacc hremaining hb.
  rewrite -htrace /= -/next_events -/q in hq.
  rewrite -htrace /= -/next_events -/q in hnewacc.
  rewrite -htrace /= -/next_events -/q in hnewsum.
  have hselected := gauss_selected_events_concat_partial n
    (gauss_stream_events f attempts) next_events accepted hn0 hcount hlt.
  have hcountnew := gauss_selected_events_count_concat n
    (gauss_stream_events f attempts) next_events accepted hn0 hcount.
  have hqbounds := gauss_selected_events_bounds (n - accepted) next_events _;
    first smt().
  have hvlocal : forall j, 0 <= j < min q (gauss_visible_limit (n - accepted) (n = 257)) =>
      BArray32768.get64 result.`1 (oo + accepted + j) =
        nth W64.zero (take (n - accepted) (gauss_accepted_values next_events)) j.
  + move=> j hj.
    have h := gs_trace_value_at (gauss_input_window buf bo) (n - accepted) available
      (n = 257) (gauss_output_window current (oo + accepted)) squares count0 j _ hb;
      first smt().
    rewrite -htrace /= -/next_events -/q in h.
    rewrite gauss_output_window_get 1:/# in h.
    exact (h hj).
  have hvglobal : forall j, 0 <= j < min (accepted + q) 256 =>
      BArray32768.get64 result.`1 (oo + j) =
        nth W64.zero (take n (gauss_accepted_values
          (gauss_stream_events f attempts ++ next_events))) j.
  + have hvn := gs_visible_requested n hn.
    rewrite -hvn.
    apply (gauss_visible_output_concat n (n = 257)
      (gauss_stream_events f attempts) next_events accepted q
      (fun j => BArray32768.get64 current (oo + j))
      (fun j => BArray32768.get64 result.`1 (oo + j))) => //.
    + move=> j hj.
      have hjold : 0 <= j < min accepted 256 by rewrite hminaccepted; exact hj.
      have h := hvalues j hjold.
      by rewrite gs_selected_values in h.
    + move=> j hj.
      exact (gs_frame_prefix current result.`1 oo n accepted j hoo hend hc hj hframe).
    move=> j hj.
    have h := hvlocal j hj.
    smt().
  have hnewframe := gs_frame_extend initial current result.`1 oo n accepted
    hc holdframe hframe.
  have hnewdummy : n = 257 =>
      BArray32768.get64 result.`1 (oo + 256) = BArray32768.get64 initial (oo + 256).
  + move=> hn257.
    have hbool : (n = 257) = true by smt().
    have hindex : oo + accepted + (n - accepted - 1) = oo + 256 by smt().
    have hidx : 0 <= n - accepted - 1 < 512 by smt().
    have h := gs_trace_dummy_at (gauss_input_window buf bo) (n - accepted) available
      (gauss_output_window current (oo + accepted)) squares count0.
    move: h; rewrite -hbool -htrace /=
      (gauss_output_window_get result.`1 (oo + accepted) (n - accepted - 1) hidx)
      (gauss_output_window_get current (oo + accepted) (n - accepted - 1) hidx)
      hindex => h.
    have hprev := hdummy hn257; smt().
  have hnewvalues : forall j, 0 <= j < min (accepted + q) 256 =>
      BArray32768.get64 result.`1 (oo + j) =
      nth W64.zero (map (fun (event : gauss_event) => event.`1)
        (gauss_selected_events n (gauss_stream_events f attempts) ++
         gauss_selected_events (n - accepted) next_events)) j.
  + move=> j hj.
    have h := hvglobal j hj.
    rewrite -gs_selected_values hselected in h.
    exact h.
  have hnewsumall : gauss_stream_value result.`2 = gauss_stream_value initial_squares +
      gauss_event_value_sum
        (gauss_selected_events n (gauss_stream_events f attempts) ++
         gauss_selected_events (n - accepted) next_events).
  + rewrite gauss_event_value_sum_cat; smt().
  rewrite /gs_progress /= hprefix -/next_events hselected size_cat -hcount -hq -/q.
  smt().
qed.

(* One bounded call of the actual signing helper extends the continuous-stream
   invariant. The invariant describes the old prefix, never the desired result. *)
lemma gs_progress_consume_correct (f : int -> W8.t)
    (initial current : BArray32768.t) (initial_squares squares : BArray16.t)
    (n oo attempts accepted : int) (buf : BArray8192.t)
    (available bo : int) (count0 : BArray8.t) :
  hoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = current /\ sqsump = squares /\ coefcntp = count0 /\ bufp = buf /\
    gauss_requested counts = n - accepted /\ gauss_available counts = available /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo + accepted /\
    dont_write_last = W64.of_int (n - 256) /\
    gs_progress f initial current initial_squares squares n oo attempts accepted /\
    accepted < n /\ 0 <= oo /\ oo + n <= 4096 /\
    0 <= available /\ 0 <= bo /\ bo + available <= 8192 /\
    gs_buffer_segment f buf bo (26 * attempts) available
    ==>
    gs_progress f initial res.`1 initial_squares res.`2 n oo
      (attempts + available %/ 26)
      (accepted + W64.to_uint (BArray8.get64 res.`3 0))].
proof.
  conseq (GaussianOffsetBridge.sample_gauss_at_trace_correct
    current buf (n - accepted) available bo (oo + accepted)
    (W64.of_int (n - 256)) squares count0) => //.
  + move=> &m hpre.
    have hp : gs_progress f initial current initial_squares squares n oo attempts accepted by smt().
    have [hn [ha [hc hrest]]] := hp.
    smt().
  move=> &m hpre result [htrace hframe].
  have hp : gs_progress f initial current initial_squares squares n oo attempts accepted by smt().
  have [hn [ha [hc hrest]]] := hp.
  move: htrace; rewrite gs_dummy_word 1:hn => htrace.
  apply (gs_progress_consume f initial current initial_squares squares
    n oo attempts accepted buf available bo count0 result); smt().
qed.
