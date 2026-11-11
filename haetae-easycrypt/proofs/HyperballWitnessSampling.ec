require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import HyperballWitnessSpec HyperballWitnessCandidate HyperballWitnessArithmetic
  HyperballSpec HyperballReferenceConstants HyperballBatchCorrectness HyperballGaussianBounds
  HyperballFixedPointSpec HyperballFixedPointCorrectness
  GaussianTraceSpec GaussianTraceProperties GaussianSequenceCorrectness
  GaussianAccumulatorCorrectness GaussianStreamAccumulator GaussianStreamSpec
  GaussianStreamComposition GaussianWindowSpec GaussianOffsetBridge
  GaussianConsumerSpec GaussianIidBufferSpec GaussianIidBufferPath GaussianRetryConsumerTotal.

op hbws_event (mode : int) : gauss_event =
  (hbw_sample mode, (hbw_square mode).`1, (hbw_square mode).`2, W64.one).

op hbws_buffer (mode : int) : BArray8192.t =
  BArray8192.init (fun j => BArray26.get8 (hbw_candidate mode) (j %% 26)).

op hbws_zero_samples : BArray32768.t = BArray32768.init (fun _ => W8.zero).
op hbws_zero_squares : BArray16.t = hb_pack (W64.zero, W64.zero).

op [opaque] hbws_progress (mode polys : int)
    (samples : BArray32768.t) (squares : BArray16.t) : bool =
  (forall j, 0 <= j < 256 * polys => BArray32768.get64 samples j = hbw_sample mode) /\
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
  gauss_stream_value squares = hb_draw_count polys * hb_value (hbw_square mode).

(* Prescribed candidate bytes, not a claimed SHAKE seed or SHAKE output.
   Each call receives enough bytes for every requested event, including
   the first two calls' accepted but unstored final candidates. *)
module HyperballWitnessSampling = {
  proc sample(mode : int) : gib_result = {
    var samples : BArray32768.t;
    var signs : BArray512.t;
    var squares : BArray16.t;
    var count : BArray8.t;
    var buf : BArray8192.t;
    var i, polys, requested : int;
    samples <- hbws_zero_samples;
    signs <- hbw_signs;
    squares <- hbws_zero_squares;
    count <- witness;
    buf <- hbws_buffer mode;
    polys <- hb_ref_l mode + hb_ref_k mode;
    i <- 0;
    while (i < polys) {
      requested <- hb_request i;
      (samples, squares, count) <@ GaussianOffsetBridge.Signer.__sample_gauss_at
        (samples, squares, count, buf, gib_counts requested (26 * requested),
         W64.of_int (requested - 256), W64.zero, W64.of_int (256 * i));
      i <- i + 1;
    }
    return (samples, signs, squares);
  }
}.

lemma hbws_progress_parts mode i samples squares :
  hbws_progress mode i samples squares =>
  (forall j, 0 <= j < 256 * i => BArray32768.get64 samples j = hbw_sample mode) /\
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
  gauss_stream_value squares = hb_draw_count i * hb_value (hbw_square mode).
proof. by rewrite /hbws_progress. qed.

lemma hbws_chunk mode i : 0 <= i => 26 * (i + 1) <= 8192 =>
  gauss_chunk (hbws_buffer mode) (26 * i) = hbw_candidate mode.
proof.
  move=> hi hcap; apply BArray26.ext_eq => j hj.
  rewrite /gauss_chunk BArray26.initiE 1:hj /= /hbws_buffer BArray8192.initiE 1:/# /=.
  by rewrite (mulzC 26 i) modzMDl modz_small 1:hj.
qed.

lemma hbws_events mode n : hbw_mode mode => 0 <= n <= 257 =>
  gauss_events (hbws_buffer mode) n = nseq n (hbws_event mode).
proof.
  move=> hm hn; apply (eq_from_nth (witness<:gauss_event>)).
  + rewrite /gauss_events size_map size_iota size_nseq; smt().
  move=> i hi.
  have hi' : 0 <= i < n by move: hi; rewrite /gauss_events size_map size_iota; smt().
  rewrite /gauss_events (nth_map 0) 1:size_iota 1:/# nth_iota 1:hi' /=
    nth_nseq 1:hi' /gauss_event_at hbws_chunk 1:/# 1:/#.
  exact (hbw_candidate_spec mode hm).
qed.

lemma hbws_filter mode n :
  filter gauss_event_accepted (nseq n (hbws_event mode)) = nseq n (hbws_event mode).
proof.
  apply/all_filterP.
  by rewrite all_nseq /gauss_event_accepted /hbws_event /=.
qed.

lemma hbws_selected mode n : hbw_mode mode => 0 <= n <= 257 =>
  gauss_selected_events n (gauss_events (hbws_buffer mode) n) = nseq n (hbws_event mode).
proof.
  move=> hm hn; rewrite /gauss_selected_events (hbws_events mode n hm hn) hbws_filter.
  apply take_oversize; rewrite size_nseq; smt().
qed.

lemma hbws_limb_sums mode n : 0 <= n =>
  gauss_low_sum (nseq n (hbws_event mode)) = n * W64.to_uint (hbw_square mode).`1 /\
  gauss_high_sum (nseq n (hbws_event mode)) = n * W64.to_uint (hbw_square mode).`2.
proof.
  elim: n => [|n hn ih].
  + by rewrite nseq0 /gauss_low_sum /gauss_high_sum /=.
  have [hl hh] := ih.
  rewrite /gauss_low_sum in hl.
  rewrite /gauss_high_sum in hh.
  rewrite nseqS 1:hn /gauss_low_sum /gauss_high_sum /= hl hh /hbws_event /=.
  split; ring.
qed.

lemma hbws_event_sum mode n : 0 <= n =>
  gauss_event_value_sum (nseq n (hbws_event mode)) = n * hb_value (hbw_square mode).
proof.
  move=> hn; have [hl hh] := hbws_limb_sums mode n hn.
  rewrite /gauss_event_value_sum hl hh /hb_value; ring.
qed.

lemma hbws_window0 buf : gauss_input_window buf 0 = buf.
proof.
  apply BArray8192.ext_eq => j hj.
  by rewrite gauss_input_window_get 1:hj /=.
qed.

lemma hbws_progress_canonical mode i samples squares :
  hbw_mode mode => 0 <= i <= hb_ref_l mode + hb_ref_k mode =>
  hbws_progress mode i samples squares =>
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
  W64.to_uint (BArray16.get64 squares 1) < 281474976710656.
proof.
  move=> hm hi hp.
  have hl : W64.to_uint (BArray16.get64 squares 0) < 281474976710656 by
    move: hp; rewrite /hbws_progress; smt().
  have hs : gauss_stream_value squares = hb_draw_count i * hb_value (hbw_square mode) by
    move: hp; rewrite /hbws_progress; smt().
  have hb := hbw_polynomial_bounds mode hm.
  have hc := hb_draw_count_bounds i _; first smt().
  have he := hbw_square_value_upper mode hm.
  have hc0 : 0 <= hb_draw_count i by smt().
  have he0 : 0 <= hb_value (hbw_square mode) by smt().
  have hemax : hb_value (hbw_square mode) <= 19342813113834066795298815 by smt().
  have hpos := IntOrder.mulr_ge0 (hb_draw_count i) (hb_value (hbw_square mode)) hc0 he0.
  have hupper := IntOrder.ler_wpmul2l (hb_draw_count i) hc0 (hb_value (hbw_square mode))
    19342813113834066795298815 hemax.
  have hcum : hb_cumulative_square_bound (hb_draw_count i) squares.
  + rewrite /hb_cumulative_square_bound hs.
    split; first exact hc.
    split; first exact hl.
    split; first exact hpos.
    by rewrite /hb_event_max.
  exact (hb_cumulative_canonical (hb_draw_count i) squares hcum).
qed.

lemma hbws_trace_properties mode n dummy values squares count :
  hbw_mode mode => (n = 256 \/ n = 257) => dummy = (n = 257) =>
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  W64.to_uint (BArray16.get64 squares 1) <= 281474976710656 =>
  let result = gauss_trace_result (hbws_buffer mode) n (26 * n) dummy values squares count in
  W64.to_uint (BArray8.get64 result.`3 0) = n /\
  (forall j, 0 <= j < 256 => BArray4096.get64 result.`1 j = hbw_sample mode) /\
  W64.to_uint (BArray16.get64 result.`2 0) < 281474976710656 /\
  gauss_stream_value result.`2 = gauss_stream_value squares + n * hb_value (hbw_square mode).
proof.
  move=> hm hn hd hl hh /=.
  have hn512 : 0 <= n <= 512 by smt().
  have hn257 : 0 <= n <= 257 by smt().
  have hb : 0 <= 26 * n by smt().
  have hdiv : (26 * n) %/ 26 = n by rewrite mulzC mulzK.
  have he := hbws_selected mode n hm hn257.
  have hsum := hbws_event_sum mode n _; first smt().
  have hacc := gauss_stream_acc_initial squares hl hh.
  have hstat := gauss_trace_result_stream_accumulator (gauss_stream_value squares) 0
    (hbws_buffer mode) n (26 * n) dummy values squares count hacc hn512 hb.
  rewrite /= hdiv he hsum size_nseq in hstat.
  have [hc [ha hs]] := hstat.
  have hc' : W64.to_uint (BArray8.get64
    (gauss_trace_result (hbws_buffer mode) n (26 * n) dummy values squares count).`3 0) = n by smt().
  have hl' : W64.to_uint (BArray16.get64
    (gauss_trace_result (hbws_buffer mode) n (26 * n) dummy values squares count).`2 0) <
      281474976710656 by move: ha; rewrite /gauss_stream_acc_ok; smt().
  split; first exact hc'.
  split.
  + move=> j hj.
    have hvlim : gauss_visible_limit n dummy = 256 by rewrite hd; exact (gs_visible_requested n hn).
    have hj' : 0 <= j < min n 256 by smt().
    have hv := gs_trace_value_at (hbws_buffer mode) n (26 * n) dummy values squares count j
      hn512 hb _; first by rewrite hc' hvlim.
    move: hv; rewrite hdiv /gauss_accepted_values (hbws_events mode n hm hn257)
      hbws_filter nth_take 1:/# 1:/# (nth_map (witness<:gauss_event>))
      1:size_nseq 1:/# nth_nseq 1:/# /hbws_event /=.
    trivial.
  smt().
qed.

lemma hbws_consume_correct mode i values squares count :
  hoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    hbw_mode mode /\ 0 <= i < hb_ref_l mode + hb_ref_k mode /\
    rp = values /\ sqsump = squares /\ coefcntp = count /\ bufp = hbws_buffer mode /\
    counts = gib_counts (hb_request i) (26 * hb_request i) /\
    dont_write_last = W64.of_int (hb_request i - 256) /\
    bufoff = W64.zero /\ outoff = W64.of_int (256 * i) /\
    W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 squares 1) <= 281474976710656 ==>
    W64.to_uint (BArray8.get64 res.`3 0) = hb_request i /\
    (forall j, 0 <= j < 256 => BArray32768.get64 res.`1 (256 * i + j) = hbw_sample mode) /\
    W64.to_uint (BArray16.get64 res.`2 0) < 281474976710656 /\
    gauss_stream_value res.`2 = gauss_stream_value squares +
      hb_request i * hb_value (hbw_square mode) /\
    gauss_big_output_frame values res.`1 (256 * i) (hb_request i)].
proof.
  conseq (GaussianOffsetBridge.sample_gauss_at_trace_correct values (hbws_buffer mode)
    (hb_request i) (26 * hb_request i) 0 (256 * i)
    (W64.of_int (hb_request i - 256)) squares count) => //.
  + move=> &m hpre.
    have hm : hbw_mode mode by smt().
    have hshape := hbw_polynomial_bounds mode hm.
    have hn := hb_request_shape i.
    have hi : 0 <= i < 11 by smt().
    have hoff := hb_batch_call_offsets i hi.
    have hn512 : 0 <= hb_request i <= 512 by smt().
    have hb : 0 <= 26 * hb_request i <= 8192 by smt().
    have hcounts := gib_counts_decode (hb_request i) (26 * hb_request i) hn512 hb.
    have hu : W64.to_uint (W64.of_int (256 * i)) = 256 * i by
      rewrite W64.of_uintK /= modz_small; smt().
    smt(W64.to_uint0).
  move=> &m hpre result [htrace hframe].
  have hm : hbw_mode mode by smt().
  have hn := hb_request_shape i.
  have hd := gs_dummy_word (hb_request i) hn.
  have hl : W64.to_uint (BArray16.get64 squares 0) < 281474976710656 by smt().
  have hh : W64.to_uint (BArray16.get64 squares 1) <= 281474976710656 by smt().
  rewrite hbws_window0 in htrace.
  have hp := hbws_trace_properties mode (hb_request i)
    (W64.of_int (hb_request i - 256) <> W64.zero)
    (gauss_output_window values (256 * i)) squares count hm hn hd hl hh.
  rewrite -htrace /= in hp.
  have [hc [hv [hlo hs]]] := hp.
  split; first exact hc.
  split.
  + move=> j hj.
    have h := hv j hj.
    by move: h; rewrite gauss_output_window_get 1:/#.
  smt().
qed.

lemma hbws_step_correct mode i :
  hoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    hbw_mode mode /\ 0 <= i < hb_ref_l mode + hb_ref_k mode /\
    bufp = hbws_buffer mode /\ counts = gib_counts (hb_request i) (26 * hb_request i) /\
    dont_write_last = W64.of_int (hb_request i - 256) /\
    bufoff = W64.zero /\ outoff = W64.of_int (256 * i) /\
    hbws_progress mode i rp sqsump ==>
    hbws_progress mode (i + 1) res.`1 res.`2 /\
    W64.to_uint (BArray8.get64 res.`3 0) = hb_request i].
proof.
  exists* rp, sqsump, coefcntp; elim* => values squares count.
  conseq (hbws_consume_correct mode i values squares count) => //.
  + move=> &m hpre.
    have hm : hbw_mode mode by smt().
    have hi : 0 <= i <= hb_ref_l mode + hb_ref_k mode by smt().
    have hp : hbws_progress mode i values squares by smt().
    have hcan := hbws_progress_canonical mode i values squares hm hi hp.
    smt().
  move=> &m hpre result [hc [hv [hl [hs hf]]]].
  have hm : hbw_mode mode by smt().
  have hi : 0 <= i < hb_ref_l mode + hb_ref_k mode by smt().
  have hshape := hbw_polynomial_bounds mode hm.
  have hp : hbws_progress mode i values squares by smt().
  have [hold [hlo hsum]] := hbws_progress_parts mode i values squares hp.
  split; last exact hc.
  rewrite /hbws_progress; split.
  + move=> j hj; case (j < 256 * i) => hpart.
    - have hprev := hold j _; first smt().
      have hkeep := hf j _ _; first 2 smt().
      smt().
    have hnew := hv (j - 256 * i) _; first smt().
    have he : 256 * i + (j - 256 * i) = j by ring.
    by move: hnew; rewrite he.
  split; first exact hl.
  rewrite hs hsum (hb_draw_count_step i _) 1:/#; ring.
qed.

lemma hbws_step_total mode i :
  phoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    hbw_mode mode /\ 0 <= i < hb_ref_l mode + hb_ref_k mode /\
    bufp = hbws_buffer mode /\ counts = gib_counts (hb_request i) (26 * hb_request i) /\
    dont_write_last = W64.of_int (hb_request i - 256) /\
    bufoff = W64.zero /\ outoff = W64.of_int (256 * i) /\
    hbws_progress mode i rp sqsump ==>
    hbws_progress mode (i + 1) res.`1 res.`2 /\
    W64.to_uint (BArray8.get64 res.`3 0) = hb_request i] = 1%r.
proof.
  exists* rp; elim* => values.
  conseq (gr_consumer_lossless values (hbws_buffer mode) (hb_request i)
    (26 * hb_request i) 0 (256 * i)) (hbws_step_correct mode i) => //.
  move=> &m hpre.
  have hm : hbw_mode mode by smt().
  have hshape := hbw_polynomial_bounds mode hm.
  have hn := hb_request_shape i.
  have hi : 0 <= i < 11 by smt().
  have hoff := hb_batch_call_offsets i hi.
  have hn512 : 0 <= hb_request i <= 512 by smt().
  have hb : 0 <= 26 * hb_request i <= 8192 by smt().
  have hcounts := gib_counts_decode (hb_request i) (26 * hb_request i) hn512 hb.
  have hu : W64.to_uint (W64.of_int (256 * i)) = 256 * i by
    rewrite W64.of_uintK /= modz_small; smt().
  smt(W64.to_uint0).
qed.

lemma hbws_initial mode : hbws_progress mode 0 hbws_zero_samples hbws_zero_squares.
proof.
  rewrite /hbws_progress /hbws_zero_squares hb_draw_count_zero
    /gauss_stream_value /gauss_limb_value /hb_pack /hb_store /=.
  smt().
qed.

lemma hbws_pack_value x : gauss_stream_value (hb_pack x) = hb_value x.
proof. by case: x => lo hi; rewrite /gauss_stream_value /gauss_limb_value /hb_pack /hb_store /hb_value /=. qed.

lemma hbws_final_count mode : hbw_mode mode =>
  hb_draw_count (hb_ref_l mode + hb_ref_k mode) = hbw_events mode.
proof.
  move=> hm; have h := hbw_polynomial_bounds mode hm.
  rewrite /hb_draw_count /hbw_events /hbw_count /min; smt().
qed.

lemma hbws_final_square mode squares : hbw_mode mode =>
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  gauss_stream_value squares = hbw_events mode * hb_value (hbw_square mode) =>
  squares = hb_pack (hbw_sum mode).
proof.
  move=> hm hl hs; have [hl0 hs0] := hbw_sum_exact mode hm.
  apply gs_canonical_square_unique; first exact hl.
  + by rewrite /hb_pack /hb_store /=.
  by rewrite hbws_pack_value hs hs0.
qed.

lemma hbw_sampling_total (mode0 : int) :
  phoare [HyperballWitnessSampling.sample : mode = mode0 /\ hbw_mode mode0 ==>
    res.`2 = hbw_signs /\
    (forall j, 0 <= j < hbw_count mode0 => BArray32768.get64 res.`1 j = hbw_sample mode0) /\
    res.`3 = hb_pack (hbw_sum mode0) /\
    gauss_stream_value res.`3 = hbw_events mode0 * hb_value (hbw_square mode0)] = 1%r.
proof.
  proc.
  while (mode = mode0 /\ hbw_mode mode0 /\
    polys = hb_ref_l mode0 + hb_ref_k mode0 /\ buf = hbws_buffer mode0 /\
    signs = hbw_signs /\ 0 <= i <= polys /\ hbws_progress mode0 i samples squares)
    (polys - i).
  + move=> z; exists* i; elim* => i0.
    wp; call (hbws_step_total mode0 i0).
    auto => />; smt().
  auto => />.
  move=> hm.
  have hshape := hbw_polynomial_bounds mode0 hm.
  split; first smt(hbws_initial).
  move=> i0 samples0 squares0.
  split.
  + move=> hi0 him hp hzero; smt().
  move=> hdone hi0 him hp.
  have he : i0 = hb_ref_l mode0 + hb_ref_k mode0 by smt().
  have [hv [hl hs]] := hbws_progress_parts mode0 i0 samples0 squares0 hp.
  move: hv; rewrite he -/(hbw_count mode0) => hv.
  move: hs; rewrite he (hbws_final_count mode0 hm) => hs.
  have hsq := hbws_final_square mode0 squares0 hm hl hs.
  smt().
qed.

lemma hbw_sampling_correct (mode0 : int) :
  hoare [HyperballWitnessSampling.sample : mode = mode0 /\ hbw_mode mode0 ==>
    res.`2 = hbw_signs /\
    (forall j, 0 <= j < hbw_count mode0 => BArray32768.get64 res.`1 j = hbw_sample mode0) /\
    res.`3 = hb_pack (hbw_sum mode0) /\
    gauss_stream_value res.`3 = hbw_events mode0 * hb_value (hbw_square mode0)].
proof. by conseq (hbw_sampling_total mode0). qed.
