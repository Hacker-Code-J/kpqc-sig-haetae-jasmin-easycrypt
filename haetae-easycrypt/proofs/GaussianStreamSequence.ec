require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianTraceSpec GaussianTraceProperties GaussianConsumerCorrectness
  GaussianBufferLemmas SigmaCorrectness SigmaSpec GaussianOffsetBridge GaussianWindowSpec
  GaussianConsumerSpec.

op gauss_stream_event (f : int -> W8.t) (i : int) : gauss_event =
  sigma76_spec (BArray26.init (fun j => f (26 * i + j))).

op gauss_stream_events (f : int -> W8.t) (k : int) : gauss_event list =
  map (gauss_stream_event f) (iota_ 0 k).

op gauss_stream_shift (f : int -> W8.t) (k : int) : int -> W8.t =
  fun j => f (26 * k + j).

lemma gauss_take_concat ['a] n (xs ys : 'a list) : 0 <= n =>
  take n (xs ++ ys) = take n xs ++ take (n - size (take n xs)) ys.
proof.
  move=> hn; rewrite take_cat_le.
  case (n <= size xs) => hs /=.
  + by rewrite size_takel 1:/# subzz take0 cats0.
  by rewrite (take_oversize n xs) 1:/#.
qed.

lemma gauss_selected_events_bounds n es : 0 <= n =>
  0 <= size (gauss_selected_events n es) <= n.
proof.
  move=> hn; rewrite /gauss_selected_events.
  have := size_take_le n (filter gauss_event_accepted es) hn.
  have := size_ge0 (take n (filter gauss_event_accepted es)); smt().
qed.

lemma gauss_selected_events_concat n es tail : 0 <= n =>
  gauss_selected_events n (es ++ tail) =
  gauss_selected_events n es ++
    gauss_selected_events (n - size (gauss_selected_events n es)) tail.
proof. by move=> hn; rewrite /gauss_selected_events filter_cat gauss_take_concat. qed.

lemma gauss_selected_events_concat_partial n es tail c :
  0 <= n => c = size (gauss_selected_events n es) => c < n =>
  gauss_selected_events n (es ++ tail) =
    gauss_selected_events n es ++ gauss_selected_events (n - c) tail.
proof. by move=> hn hc _; rewrite gauss_selected_events_concat 1:hn -hc. qed.

lemma gauss_selected_events_count_concat n es tail c :
  0 <= n => c = size (gauss_selected_events n es) =>
  size (gauss_selected_events n (es ++ tail)) =
    c + size (gauss_selected_events (n - c) tail).
proof.
  by move=> hn hc; rewrite gauss_selected_events_concat 1:hn size_cat -hc.
qed.

lemma gauss_selected_values_size n es :
  size (take n (gauss_accepted_values es)) = size (gauss_selected_events n es).
proof. by rewrite /gauss_accepted_values /gauss_selected_events -map_take size_map. qed.

lemma gauss_selected_values_concat n es tail c :
  0 <= n => c = size (gauss_selected_events n es) =>
  take n (gauss_accepted_values (es ++ tail)) =
    take n (gauss_accepted_values es) ++ take (n - c) (gauss_accepted_values tail).
proof.
  move=> hn hc.
  by rewrite gauss_accepted_values_cat gauss_take_concat 1:hn
    gauss_selected_values_size -hc.
qed.

lemma gauss_selected_values_prefix_at n es tail c j :
  0 <= n => c = size (gauss_selected_events n es) => 0 <= j < c =>
  nth W64.zero (take n (gauss_accepted_values (es ++ tail))) j =
    nth W64.zero (take n (gauss_accepted_values es)) j.
proof.
  move=> hn hc hj.
  rewrite (gauss_selected_values_concat n es tail c hn hc) nth_cat
    gauss_selected_values_size -hc; smt().
qed.

lemma gauss_selected_values_suffix_at n es tail c j :
  0 <= n => c = size (gauss_selected_events n es) => c <= j =>
  nth W64.zero (take n (gauss_accepted_values (es ++ tail))) j =
    nth W64.zero (take (n - c) (gauss_accepted_values tail)) (j - c).
proof.
  move=> hn hc hj.
  rewrite (gauss_selected_values_concat n es tail c hn hc) nth_cat
    gauss_selected_values_size -hc; smt().
qed.

lemma gauss_selected_partial_size n es c :
  0 <= n => c = size (gauss_selected_events n es) => c < n =>
  size (gauss_accepted_values es) = c.
proof.
  move=> hn hc hcn.
  move: hc; rewrite /gauss_selected_events size_take 1:hn
    /gauss_accepted_values size_map; smt().
qed.

lemma gauss_visible_limit_split n d c : 0 <= c < n =>
  gauss_visible_limit n d = c + gauss_visible_limit (n - c) d.
proof. rewrite /gauss_visible_limit; smt(). qed.

lemma gauss_visible_count_concat n d c t :
  0 <= c < n => 0 <= t <= n - c =>
  min (c + t) (gauss_visible_limit n d) =
    c + min t (gauss_visible_limit (n - c) d).
proof. move=> hc ht; rewrite (gauss_visible_limit_split n d c hc); smt(). qed.

lemma gauss_visible_values_concat n d es tail c :
  0 <= n => c = size (gauss_selected_events n es) => c < n =>
  take (gauss_visible_limit n d) (gauss_accepted_values (es ++ tail)) =
    take n (gauss_accepted_values es) ++
      take (gauss_visible_limit (n - c) d) (gauss_accepted_values tail).
proof.
  move=> hn hc hcn.
  have hraw := gauss_selected_partial_size n es c hn hc hcn.
  have hcb := gauss_selected_events_bounds n es hn.
  have hnonneg : 0 <= n - c by smt().
  have hv := gauss_visible_limit_bounds (n - c) d hnonneg.
  have hsplit := gauss_visible_limit_split n d c _; first smt().
  have hpref : size (gauss_accepted_values es) <= gauss_visible_limit n d by smt().
  rewrite gauss_accepted_values_cat take_catr 1:hpref hraw.
  have -> : gauss_visible_limit n d - c = gauss_visible_limit (n - c) d by smt().
  by rewrite (take_oversize n (gauss_accepted_values es)) 1:/#.
qed.

lemma gauss_visible_shift n d c j : 0 <= c < n => c <= j =>
  (j < gauss_visible_limit n d) = (j - c < gauss_visible_limit (n - c) d).
proof. move=> hc hj; rewrite (gauss_visible_limit_split n d c hc); smt(). qed.

lemma gauss_dummy_last_shift n c : c + ((n - c) - 1) = n - 1.
proof. ring. qed.

(* A later call only needs to preserve positions strictly below c.  No
   preservation premise is made for the speculative slot at c. *)
lemma gauss_visible_output_concat n d es tail c t
    (before after : int -> W64.t) :
  0 <= n => c = size (gauss_selected_events n es) => c < n =>
  t = size (gauss_selected_events (n - c) tail) =>
  (forall j, 0 <= j < c => before j =
    nth W64.zero (take n (gauss_accepted_values es)) j) =>
  (forall j, 0 <= j < c => after j = before j) =>
  (forall j, 0 <= j < min t (gauss_visible_limit (n - c) d) => after (c + j) =
    nth W64.zero (take (n - c) (gauss_accepted_values tail)) j) =>
  forall j, 0 <= j < min (c + t) (gauss_visible_limit n d) =>
    after j = nth W64.zero (take n (gauss_accepted_values (es ++ tail))) j.
proof.
  move=> hn hc hcn ht hp hf hs j hj.
  case (j < c) => hjc.
  + rewrite (gauss_selected_values_prefix_at n es tail c j hn hc _) 1:/#.
    rewrite hf 1:/#; apply hp; smt().
  rewrite (gauss_selected_values_suffix_at n es tail c j hn hc _) 1:/#.
  have hcb := gauss_selected_events_bounds n es hn.
  have hnonneg : 0 <= n - c by smt().
  have htb := gauss_selected_events_bounds (n - c) tail hnonneg.
  have hsplit := gauss_visible_count_concat n d c t _ _; first 2 smt().
  have hlocal : 0 <= j - c < min t (gauss_visible_limit (n - c) d) by smt().
  have he := hs (j - c) hlocal.
  have hindex : c + (j - c) = j by ring.
  by move: he; rewrite hindex.
qed.

lemma gauss_stream_event_accept_bit f i :
  0 <= W64.to_uint (gauss_stream_event f i).`4 <= 1.
proof.
  rewrite /gauss_stream_event /sigma76_spec /sigma_from_cdt /=.
  exact: gauss_mask_bit.
qed.

lemma gauss_stream_events_bits f k : gauss_events_are_bits (gauss_stream_events f k).
proof.
  rewrite /gauss_events_are_bits /gauss_stream_events all_map.
  apply List.allP => i _; exact (gauss_stream_event_accept_bit f i).
qed.

lemma gauss_stream_events_size f k : 0 <= k => size (gauss_stream_events f k) = k.
proof. move=> hk; rewrite /gauss_stream_events size_map size_iota; smt(). qed.

lemma gauss_selected_events_count n es : 0 <= n =>
  size (gauss_selected_events n es) = min n (count gauss_event_accepted es).
proof.
  move=> hn; rewrite /gauss_selected_events size_take 1:hn size_filter /min; smt().
qed.

lemma gauss_stream_selected_count_bounds n f k : 0 <= n => 0 <= k =>
  0 <= size (gauss_selected_events n (gauss_stream_events f k)) <= min n k.
proof.
  move=> hn hk.
  have hc0 := count_ge0 gauss_event_accepted (gauss_stream_events f k).
  have hc := count_size gauss_event_accepted (gauss_stream_events f k).
  rewrite gauss_stream_events_size 1:hk in hc.
  rewrite gauss_selected_events_count 1:hn /min; smt().
qed.

lemma gauss_stream_event_shift f k i :
  gauss_stream_event (gauss_stream_shift f k) i = gauss_stream_event f (k + i).
proof.
  rewrite /gauss_stream_event /gauss_stream_shift.
  congr; apply BArray26.init_ext => j hj /=; congr; ring.
qed.

lemma gauss_stream_events_segment f k m :
  map (gauss_stream_event f) (iota_ k m) =
  gauss_stream_events (gauss_stream_shift f k) m.
proof.
  have hindices := iota_addl k 0 m.
  rewrite /= in hindices.
  rewrite /gauss_stream_events hindices -map_comp.
  apply List.eq_in_map => i _.
  by rewrite /= gauss_stream_event_shift.
qed.

lemma gauss_stream_events_split f k m : 0 <= k => 0 <= m =>
  gauss_stream_events f (k + m) = gauss_stream_events f k ++
    gauss_stream_events (gauss_stream_shift f k) m.
proof.
  move=> hk hm; rewrite /gauss_stream_events iota_add 1:hk 1:hm map_cat /=.
  by rewrite (gauss_stream_events_segment f k m) /gauss_stream_events.
qed.

lemma gauss_stream_events_take f k m : 0 <= k => 0 <= m =>
  take k (gauss_stream_events f (k + m)) = gauss_stream_events f k.
proof.
  move=> hk hm; rewrite gauss_stream_events_split 1:hk 1:hm.
  by apply take_size_cat; rewrite gauss_stream_events_size.
qed.

lemma gauss_stream_events_drop f k m : 0 <= k => 0 <= m =>
  drop k (gauss_stream_events f (k + m)) = gauss_stream_events (gauss_stream_shift f k) m.
proof.
  move=> hk hm; rewrite gauss_stream_events_split 1:hk 1:hm.
  by apply drop_size_cat; rewrite gauss_stream_events_size.
qed.

lemma gauss_stream_buffer_event (f : int -> W8.t) buf k m i :
  0 <= i < m =>
  (forall j, 0 <= j < 26 * m => BArray8192.get8 buf j = f (26 * k + j)) =>
  gauss_event_at buf i = gauss_stream_event f (k + i).
proof.
  move=> hi hb; rewrite /gauss_event_at /gauss_stream_event.
  congr; apply BArray26.ext_eq => j hj.
  rewrite gauss_chunk_get 1:hj BArray26.initiE 1:hj.
  rewrite hb 1:/# /=; congr; ring.
qed.

lemma gauss_stream_events_from_buffer (f : int -> W8.t) buf k m :
  0 <= m =>
  (forall j, 0 <= j < 26 * m => BArray8192.get8 buf j = f (26 * k + j)) =>
  gauss_events buf m = gauss_stream_events (gauss_stream_shift f k) m.
proof.
  move=> hm hb; rewrite /gauss_events /gauss_stream_events.
  apply List.eq_in_map => i; rewrite mem_iota /=; move=> hi.
  rewrite gauss_stream_event_shift.
  apply (gauss_stream_buffer_event f buf k m i); first smt().
  exact hb.
qed.

lemma gauss_stream_events_append_buffer (f : int -> W8.t) buf k m :
  0 <= k => 0 <= m =>
  (forall j, 0 <= j < 26 * m => BArray8192.get8 buf j = f (26 * k + j)) =>
  gauss_stream_events f (k + m) = gauss_stream_events f k ++ gauss_events buf m.
proof.
  move=> hk hm hb; rewrite gauss_stream_events_split 1:hk 1:hm.
  by rewrite -(gauss_stream_events_from_buffer f buf k m hm hb).
qed.

lemma gauss_stream_events_drop_buffer (f : int -> W8.t) buf k m :
  0 <= k => 0 <= m =>
  (forall j, 0 <= j < 26 * m => BArray8192.get8 buf j = f (26 * k + j)) =>
  drop k (gauss_stream_events f (k + m)) = gauss_events buf m.
proof.
  move=> hk hm hb; rewrite gauss_stream_events_drop 1:hk 1:hm.
  by rewrite -(gauss_stream_events_from_buffer f buf k m hm hb).
qed.

lemma gauss_stream_events_append_available (f : int -> W8.t) buf k available :
  0 <= k => 0 <= available =>
  (forall j, 0 <= j < available => BArray8192.get8 buf j = f (26 * k + j)) =>
  gauss_stream_events f (k + available %/ 26) =
    gauss_stream_events f k ++ gauss_events buf (available %/ 26).
proof.
  move=> hk hb hbytes.
  have hm : 0 <= available %/ 26 by rewrite divz_ge0.
  have hd := divz_eq available 26.
  have hr := modz_cmp available 26.
  apply (gauss_stream_events_append_buffer f buf k (available %/ 26) hk hm).
  move=> j hj; apply hbytes; smt().
qed.

lemma gauss_visible_limit_signer d :
  gauss_visible_limit (256 + b2i d) d = 256.
proof. by rewrite /gauss_visible_limit /b2i; case d. qed.

lemma gauss_visible_remaining_signer d c : 0 <= c < 256 + b2i d =>
  gauss_visible_limit (256 + b2i d - c) d = 256 - c.
proof.
  move=> hc.
  have hs := gauss_visible_limit_split (256 + b2i d) d c hc.
  move: hs; rewrite gauss_visible_limit_signer; smt().
qed.

lemma sample_gauss_at_dummy_last_correct
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int)
    (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 < n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo /\ d <> W64.zero
    ==>
    BArray32768.get64 res.`1 (oo + n - 1) =
      BArray32768.get64 initial (oo + n - 1) /\
    gauss_big_output_frame initial res.`1 oo n].
proof.
  conseq (GaussianOffsetBridge.sample_gauss_at_trace_correct
    initial buf n b bo oo d squares count0) => //.
  + smt().
  move=> &m hpre result [htrace hframe].
  split; last exact hframe.
  have hj : 0 <= n - 1 < 512 by smt().
  have hd : d <> W64.zero by smt().
  have hw : gauss_output_window result.`1 oo =
    (gauss_trace_result (gauss_input_window buf bo) n b (d <> W64.zero)
      (gauss_output_window initial oo) squares count0).`1 by smt().
  have -> : oo + n - 1 = oo + (n - 1) by ring.
  rewrite -(gauss_output_window_get result.`1 oo (n - 1) hj)
    -(gauss_output_window_get initial oo (n - 1) hj) hw hd.
  by rewrite /gauss_trace_result /= gauss_trace_prefix_dummy_last.
qed.

lemma sample_gauss_at_dummy_last_total
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int)
    (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 < n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo /\ d <> W64.zero
    ==>
    BArray32768.get64 res.`1 (oo + n - 1) =
      BArray32768.get64 initial (oo + n - 1) /\
    gauss_big_output_frame initial res.`1 oo n] = 1%r.
proof.
  conseq (GaussianOffsetBridge.sample_gauss_at_total_frame initial buf n b bo oo)
    (sample_gauss_at_dummy_last_correct initial buf n b bo oo d squares count0) => />.
  smt().
qed.
