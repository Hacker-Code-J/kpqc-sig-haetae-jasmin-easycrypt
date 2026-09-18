require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import SamplerTarget GaussianTraceSpec GaussianTraceProperties
  GaussianTraceCorrectness GaussianConsumerCorrectness GaussianConsumerSpec
  GaussianAccumulatorCorrectness GaussianOffsetBridge GaussianWindowSpec.

lemma gauss_visible_limit_word n (d : W64.t) : 0 <= n =>
  gauss_visible_limit n (d <> W64.zero) = max 0 (n - b2i (d <> W64.zero)).
proof. rewrite /gauss_visible_limit /b2i; smt(). qed.

lemma gauss_trace_result_count buf n b dont values squares count0 :
  0 <= n <= 512 => 0 <= b =>
  W64.to_uint (BArray8.get64
    (gauss_trace_result buf n b dont values squares count0).`3 0) =
  (gauss_trace_prefix buf n dont values squares (b %/ 26)).`4.
proof.
  move=> hn hb.
  have hn0 : 0 <= n by smt().
  have hk : 0 <= b %/ 26 by rewrite divz_ge0.
  have [hc _] := gauss_trace_prefix_count_bounds buf n dont values squares
    (b %/ 26) hn0 hk.
  rewrite /gauss_trace_result /= W64.to_uint_small 1:/#.
  trivial.
qed.

lemma gauss_trace_result_count_exact buf n b dont values squares count0 :
  0 <= n <= 512 => 0 <= b =>
  W64.to_uint (BArray8.get64
    (gauss_trace_result buf n b dont values squares count0).`3 0) =
  size (take n (filter gauss_event_accepted (gauss_events buf (b %/ 26)))).
proof.
  move=> hn hb; rewrite gauss_trace_result_count 1:hn 1:hb.
  rewrite gauss_trace_prefix_count_exact 1:/# /gauss_selected_events.
  trivial.
qed.

lemma gauss_trace_result_sequence buf n b (d : W64.t) values squares count0 :
  0 <= n <= 512 => 0 <= b =>
  let result = gauss_trace_result buf n b (d <> W64.zero) values squares count0 in
  map (fun j => BArray4096.get64 result.`1 j)
    (iota_ 0 (min (W64.to_uint (BArray8.get64 result.`3 0))
      (max 0 (n - b2i (d <> W64.zero))))) =
  take (max 0 (n - b2i (d <> W64.zero)))
    (gauss_accepted_values (gauss_events buf (b %/ 26))).
proof.
  move=> hn hb /=.
  have hn0 : 0 <= n by smt().
  have hk : 0 <= b %/ 26 by rewrite divz_ge0.
  rewrite gauss_trace_result_count 1:hn 1:hb.
  rewrite -(gauss_visible_limit_word n d hn0) /gauss_trace_result /=.
  exact (gauss_trace_prefix_accepted_sequence buf n (d <> W64.zero)
    values squares (b %/ 26) hn hk).
qed.

(* The returned count includes a possible dummy final coefficient. The visible
   list excludes that slot and every unaccepted speculative candidate. *)
lemma sample_gauss_jazz_sequence_correct (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    W64.to_uint (BArray8.get64 res.`3 0) =
      size (take n (filter gauss_event_accepted (gauss_events buf (b %/ 26)))) /\
    map (fun j => BArray4096.get64 res.`1 j)
      (iota_ 0 (min (W64.to_uint (BArray8.get64 res.`3 0))
        (max 0 (n - b2i (d <> W64.zero))))) =
    take (max 0 (n - b2i (d <> W64.zero)))
      (map (fun (event : gauss_event) => event.`1)
        (filter gauss_event_accepted (gauss_events buf (b %/ 26))))].
proof.
  conseq (sample_gauss_jazz_trace_correct buf n b d values squares count0) => //.
  move=> &m hpre result ->.
  have hn : 0 <= n <= 512 by smt().
  have hb : 0 <= b by smt().
  split.
  + exact (gauss_trace_result_count_exact buf n b (d <> W64.zero)
      values squares count0 hn hb).
  exact (gauss_trace_result_sequence buf n b d values squares count0 hn hb).
qed.

lemma sample_gauss_jazz_sequence_total (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    W64.to_uint (BArray8.get64 res.`3 0) =
      size (take n (filter gauss_event_accepted (gauss_events buf (b %/ 26)))) /\
    map (fun j => BArray4096.get64 res.`1 j)
      (iota_ 0 (min (W64.to_uint (BArray8.get64 res.`3 0))
        (max 0 (n - b2i (d <> W64.zero))))) =
    take (max 0 (n - b2i (d <> W64.zero)))
      (map (fun (event : gauss_event) => event.`1)
        (filter gauss_event_accepted (gauss_events buf (b %/ 26))))] = 1%r.
proof.
  by conseq sample_gauss_jazz_lossless
    (sample_gauss_jazz_sequence_correct buf n b d values squares count0).
qed.

lemma sample_gauss_jazz_accepted_count_correct
    (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    W64.to_uint (BArray8.get64 res.`3 0) =
      size (take n (filter gauss_event_accepted (gauss_events buf (b %/ 26))))].
proof.
  conseq (sample_gauss_jazz_sequence_correct buf n b d values squares count0) => />; smt().
qed.

lemma sample_gauss_jazz_accepted_count_total
    (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    W64.to_uint (BArray8.get64 res.`3 0) =
      size (take n (filter gauss_event_accepted (gauss_events buf (b %/ 26))))] = 1%r.
proof.
  by conseq sample_gauss_jazz_lossless
    (sample_gauss_jazz_accepted_count_correct buf n b d values squares count0).
qed.

lemma sample_gauss_jazz_dummy_last_correct
    (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 < n <= 512 /\ 0 <= b <= 8192 /\ d <> W64.zero
    ==>
    BArray4096.get64 res.`1 (n - 1) = BArray4096.get64 values (n - 1)].
proof.
  conseq (sample_gauss_jazz_trace_correct buf n b d values squares count0) => //.
  + smt().
  move=> &m hpre result ->.
  have hd : d <> W64.zero by smt().
  by rewrite hd /gauss_trace_result /= gauss_trace_prefix_dummy_last.
qed.

lemma sample_gauss_jazz_dummy_last_total
    (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 < n <= 512 /\ 0 <= b <= 8192 /\ d <> W64.zero
    ==>
    BArray4096.get64 res.`1 (n - 1) = BArray4096.get64 values (n - 1)] = 1%r.
proof.
  by conseq sample_gauss_jazz_lossless
    (sample_gauss_jazz_dummy_last_correct buf n b d values squares count0).
qed.

(* With canonical initial 48-bit limbs the concrete accumulator represents
   the exact integer sum of the selected square limbs, without wrapping. *)
lemma sample_gauss_jazz_accumulator_exact_correct
    (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192 /\
    W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 squares 1) < 281474976710656
    ==>
    gauss_limb_value (BArray16.get64 res.`2 0) (BArray16.get64 res.`2 1) =
      gauss_accumulator_integer_total buf n (b %/ 26) squares].
proof.
  conseq (sample_gauss_jazz_trace_correct buf n b d values squares count0) => //.
  move=> &m hpre result ->.
  apply (gauss_trace_result_canonical_both_exact buf n b (d <> W64.zero)
    values squares count0); smt().
qed.

lemma sample_gauss_jazz_accumulator_exact_total
    (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192 /\
    W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 squares 1) < 281474976710656
    ==>
    gauss_limb_value (BArray16.get64 res.`2 0) (BArray16.get64 res.`2 1) =
      gauss_accumulator_integer_total buf n (b %/ 26) squares] = 1%r.
proof.
  by conseq sample_gauss_jazz_lossless
    (sample_gauss_jazz_accumulator_exact_correct buf n b d values squares count0).
qed.

lemma gauss_output_window_sequence (big : BArray32768.t) oo k :
  0 <= k <= 512 =>
  map (fun j => BArray4096.get64 (gauss_output_window big oo) j) (iota_ 0 k) =
  map (fun j => BArray32768.get64 big (oo + j)) (iota_ 0 k).
proof.
  move=> hk; apply List.eq_in_map => j; rewrite mem_iota /=; move=> hj.
  apply gauss_output_window_get; smt().
qed.

lemma gauss_offset_result_sequence
    (initial : BArray32768.t) (buf : BArray8192.t) n b bo oo (d : W64.t)
    (squares : BArray16.t) (count0 : BArray8.t)
    (result : BArray32768.t * BArray16.t * BArray8.t) :
  0 <= n <= 512 => 0 <= b =>
  (gauss_output_window result.`1 oo, result.`2, result.`3) =
    gauss_trace_result (gauss_input_window buf bo) n b (d <> W64.zero)
      (gauss_output_window initial oo) squares count0 =>
  W64.to_uint (BArray8.get64 result.`3 0) =
    size (take n (filter gauss_event_accepted
      (gauss_events (gauss_input_window buf bo) (b %/ 26)))) /\
  map (fun j => BArray32768.get64 result.`1 (oo + j))
    (iota_ 0 (min (W64.to_uint (BArray8.get64 result.`3 0))
      (max 0 (n - b2i (d <> W64.zero))))) =
  take (max 0 (n - b2i (d <> W64.zero)))
    (gauss_accepted_values (gauss_events (gauss_input_window buf bo) (b %/ 26))).
proof.
  move=> hn hb hresult.
  have hn0 : 0 <= n by smt().
  have hc := gauss_trace_result_count_exact (gauss_input_window buf bo) n b
    (d <> W64.zero) (gauss_output_window initial oo) squares count0 hn hb.
  have hs := gauss_trace_result_sequence (gauss_input_window buf bo) n b d
    (gauss_output_window initial oo) squares count0 hn hb.
  move: hc hs; rewrite -hresult /= => hc hs.
  split; first exact hc.
  have hv := gauss_visible_limit_bounds n (d <> W64.zero) hn0.
  rewrite gauss_visible_limit_word 1:hn0 in hv.
  have huint := W64.to_uint_cmp (BArray8.get64 result.`3 0).
  have hk : 0 <= min (W64.to_uint (BArray8.get64 result.`3 0))
    (max 0 (n - b2i (d <> W64.zero))) <= 512 by smt().
  rewrite -(gauss_output_window_sequence result.`1 oo _ hk).
  exact hs.
qed.

lemma sample_gauss_at_sequence_correct
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int)
    (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo
    ==>
    W64.to_uint (BArray8.get64 res.`3 0) =
      size (take n (filter gauss_event_accepted
        (gauss_events (gauss_input_window buf bo) (b %/ 26)))) /\
    map (fun j => BArray32768.get64 res.`1 (oo + j))
      (iota_ 0 (min (W64.to_uint (BArray8.get64 res.`3 0))
        (max 0 (n - b2i (d <> W64.zero))))) =
    take (max 0 (n - b2i (d <> W64.zero)))
      (map (fun (event : gauss_event) => event.`1)
        (filter gauss_event_accepted
          (gauss_events (gauss_input_window buf bo) (b %/ 26)))) /\
    gauss_big_output_frame initial res.`1 oo n].
proof.
  conseq (GaussianOffsetBridge.sample_gauss_at_trace_correct
    initial buf n b bo oo d squares count0) => //.
  move=> &m hpre result [htrace hframe].
  have hn : 0 <= n <= 512 by smt().
  have hb : 0 <= b by smt().
  have [hc hs] := gauss_offset_result_sequence initial buf n b bo oo d
    squares count0 result hn hb htrace.
  rewrite /gauss_accepted_values in hs.
  smt().
qed.

lemma sample_gauss_at_sequence_total
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int)
    (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo
    ==>
    W64.to_uint (BArray8.get64 res.`3 0) =
      size (take n (filter gauss_event_accepted
        (gauss_events (gauss_input_window buf bo) (b %/ 26)))) /\
    map (fun j => BArray32768.get64 res.`1 (oo + j))
      (iota_ 0 (min (W64.to_uint (BArray8.get64 res.`3 0))
        (max 0 (n - b2i (d <> W64.zero))))) =
    take (max 0 (n - b2i (d <> W64.zero)))
      (map (fun (event : gauss_event) => event.`1)
        (filter gauss_event_accepted
          (gauss_events (gauss_input_window buf bo) (b %/ 26)))) /\
    gauss_big_output_frame initial res.`1 oo n] = 1%r.
proof.
  by conseq (GaussianOffsetBridge.sample_gauss_at_total_frame initial buf n b bo oo)
    (sample_gauss_at_sequence_correct initial buf n b bo oo d squares count0) => />.
qed.
