require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianTraceSpec GaussianTraceProperties SigmaCorrectness SigmaSpec SigmaSquareBounds.

(* A 48-bit low limb and a 64-bit high limb represent a 112-bit integer. *)
op gauss_limb_value (lo hi : W64.t) : int =
  W64.to_uint lo + 281474976710656 * W64.to_uint hi.

op gauss_low_sum (es : gauss_event list) : int =
  foldr (fun (e : gauss_event) z => W64.to_uint e.`2 + z) 0 es.

op gauss_high_sum (es : gauss_event list) : int =
  foldr (fun (e : gauss_event) z => W64.to_uint e.`3 + z) 0 es.

lemma gauss_normalize_low_uint (lo hi : W64.t) :
  W64.to_uint (gauss_normalize lo hi).`1 = W64.to_uint lo %% 281474976710656.
proof.
  rewrite /gauss_normalize /=.
  have -> : 281474976710655 = 2^48 - 1 by trivial.
  by rewrite W64.to_uint_and_mod.
qed.

lemma gauss_normalize_high_uint (lo hi : W64.t) :
  W64.to_uint (gauss_normalize lo hi).`2 =
    (W64.to_uint hi + W64.to_uint lo %/ 281474976710656) %% 18446744073709551616.
proof.
  by rewrite /gauss_normalize /= W64.to_uintD W64.to_uint_shr.
qed.

lemma gauss_normalize_value_mod (lo hi : W64.t) :
  gauss_limb_value (gauss_normalize lo hi).`1 (gauss_normalize lo hi).`2 =
    gauss_limb_value lo hi %% 5192296858534827628530496329220096.
proof.
  rewrite /gauss_limb_value gauss_normalize_low_uint gauss_normalize_high_uint.
  pose s := W64.to_uint hi + W64.to_uint lo %/ 281474976710656.
  have hlo := divz_eq (W64.to_uint lo) 281474976710656.
  have hs := divz_eq s 18446744073709551616.
  have /= hrl := modz_cmp (W64.to_uint lo) 281474976710656.
  have /= hrh := modz_cmp s 18446744073709551616.
  have he : W64.to_uint lo + 281474976710656 * W64.to_uint hi =
    (s %/ 18446744073709551616) * 5192296858534827628530496329220096 +
    (W64.to_uint lo %% 281474976710656 +
      281474976710656 * (s %% 18446744073709551616)) by smt().
  rewrite he modzMDl.
  rewrite (modz_small (W64.to_uint lo %% 281474976710656 +
    281474976710656 * (s %% 18446744073709551616))
    5192296858534827628530496329220096); smt().
qed.

lemma gauss_normalize_value_exact (lo hi : W64.t) :
  W64.to_uint hi + W64.to_uint lo %/ 281474976710656 < 18446744073709551616 =>
  gauss_limb_value (gauss_normalize lo hi).`1 (gauss_normalize lo hi).`2 =
    gauss_limb_value lo hi.
proof.
  move=> hroom.
  have /= hlo := W64.to_uint_cmp lo.
  have /= hhi := W64.to_uint_cmp hi.
  have hd := divz_eq (W64.to_uint lo) 281474976710656.
  have /= hr := modz_cmp (W64.to_uint lo) 281474976710656.
  rewrite /gauss_limb_value gauss_normalize_low_uint gauss_normalize_high_uint.
  rewrite (modz_small (W64.to_uint hi + W64.to_uint lo %/ 281474976710656)
    18446744073709551616); smt().
qed.

lemma gauss_square_low_bound (x0 x1 : W64.t) :
  0 <= W64.to_uint (square_word x0 x1).`1 < 281474976710656.
proof.
  rewrite /square_word /=.
  have -> : 281474976710655 = 2^48 - 1 by trivial.
  rewrite W64.to_uint_and_mod //=.
  apply modz_cmp; trivial.
qed.

lemma gauss_event_low_bound (buf : BArray8192.t) (i : int) :
  0 <= W64.to_uint (gauss_event_at buf i).`2 < 281474976710656.
proof.
  rewrite /gauss_event_at /sigma76_spec /sigma_from_cdt /=.
  apply gauss_square_low_bound.
qed.

lemma gauss_trace_fold_word_sums n d es :
  forall (values : BArray4096.t) (lo hi : W64.t) (c : int),
  0 <= c <= n => gauss_events_are_bits es =>
  let state = foldl (gauss_trace_step n d) (values, lo, hi, c) es in
  state.`2 = lo + W64.of_int (gauss_low_sum (gauss_selected_events (n - c) es)) /\
  state.`3 = hi + W64.of_int (gauss_high_sum (gauss_selected_events (n - c) es)).
proof.
  elim: es => [|event es ih] values lo hi c hc hb.
  + by rewrite /gauss_selected_events /gauss_low_sum /gauss_high_sum /=.
  have [he hes] : (0 <= W64.to_uint event.`4 <= 1) /\ gauss_events_are_bits es.
  + by move: hb; rewrite /gauss_events_are_bits /=.
  case (n <= c) => hn.
  + have hstep : gauss_trace_step n d (values, lo, hi, c) event =
        (values, lo, hi, c) by rewrite /gauss_trace_step /= hn.
    rewrite /= hstep gauss_trace_fold_full 1://=.
    have -> : n - c = 0 by smt().
    by rewrite /gauss_selected_events take0 /gauss_low_sum /gauss_high_sum /=.
  case (W64.to_uint event.`4 = 0) => hz.
  + have hw : event.`4 = W64.zero by rewrite W64.to_uint_eq W64.to_uint0.
    have hstep : gauss_trace_step n d (values, lo, hi, c) event =
      ((if d /\ c = n - 1 then values else BArray4096.set64 values c event.`1),
       lo, hi, c).
    + by rewrite /gauss_trace_step /= hn hw W64.WRingA.oppr0 !W64.andw0
        W64.to_uint0 /=.
    rewrite /= hstep.
    have hs : gauss_selected_events (n - c) (event :: es) =
      gauss_selected_events (n - c) es.
    + by rewrite /gauss_selected_events /= /gauss_event_accepted hz /=.
    rewrite hs.
    exact (ih (if d /\ c = n - 1 then values else BArray4096.set64 values c event.`1)
      lo hi c hc hes).
  have ho : W64.to_uint event.`4 = 1 by smt().
  have hw : event.`4 = W64.one by rewrite W64.to_uint_eq W64.to_uint1.
  have hstep : gauss_trace_step n d (values, lo, hi, c) event =
    ((if d /\ c = n - 1 then values else BArray4096.set64 values c event.`1),
     lo + event.`2, hi + event.`3, c + 1).
  + by rewrite /gauss_trace_step /= hn hw W64.minus_one
      !W64.andw1 W64.to_uint1 /=.
  have hs : gauss_selected_events (n - c) (event :: es) =
    event :: gauss_selected_events (n - (c + 1)) es.
  + rewrite /gauss_selected_events /= /gauss_event_accepted ho /=.
    smt().
  rewrite /= hstep hs /gauss_low_sum /gauss_high_sum /=.
  have hc1 : 0 <= c + 1 <= n by smt().
  have [hl hh] := ih
    (if d /\ c = n - 1 then values else BArray4096.set64 values c event.`1)
    (lo + event.`2) (hi + event.`3) (c + 1) hc1 hes.
  rewrite hl hh /gauss_low_sum /gauss_high_sum !W64.of_intD !W64.to_uintK.
  split; ring.
qed.

op gauss_selected_low_sum (buf : BArray8192.t) (n k : int) : int =
  gauss_low_sum (gauss_selected_events n (gauss_events buf k)).

op gauss_selected_high_sum (buf : BArray8192.t) (n k : int) : int =
  gauss_high_sum (gauss_selected_events n (gauss_events buf k)).

lemma gauss_trace_prefix_word_sums buf n d values squares k :
  0 <= n =>
  (gauss_trace_prefix buf n d values squares k).`2 =
    BArray16.get64 squares 0 + W64.of_int (gauss_selected_low_sum buf n k) /\
  (gauss_trace_prefix buf n d values squares k).`3 =
    BArray16.get64 squares 1 + W64.of_int (gauss_selected_high_sum buf n k).
proof.
  move=> hn.
  have h := gauss_trace_fold_word_sums n d (gauss_events buf k) values
    (BArray16.get64 squares 0) (BArray16.get64 squares 1) 0 _
    (gauss_events_bits buf k); first smt().
  by move: h; rewrite /gauss_trace_prefix /gauss_trace_initial
    /gauss_selected_low_sum /gauss_selected_high_sum /=.
qed.

(* Each raw limb is an independent sum modulo 2^64. No canonical-initial-limb
   assumption is needed for these exact word-level identities. *)
lemma gauss_trace_prefix_uint_sums buf n d values squares k :
  0 <= n =>
  W64.to_uint (gauss_trace_prefix buf n d values squares k).`2 =
    (W64.to_uint (BArray16.get64 squares 0) + gauss_selected_low_sum buf n k)
      %% 18446744073709551616 /\
  W64.to_uint (gauss_trace_prefix buf n d values squares k).`3 =
    (W64.to_uint (BArray16.get64 squares 1) + gauss_selected_high_sum buf n k)
      %% 18446744073709551616.
proof.
  move=> hn.
  have [hl hh] := gauss_trace_prefix_word_sums buf n d values squares k hn.
  by rewrite hl hh !W64.to_uintD !W64.of_uintK !modzDmr.
qed.

lemma gauss_low_sum_bound es :
  all (fun (e : gauss_event) => 0 <= W64.to_uint e.`2 < 281474976710656) es =>
  0 <= gauss_low_sum es <= size es * 281474976710655.
proof.
  elim: es => [|event es ih].
  + by rewrite /gauss_low_sum /=.
  rewrite /gauss_low_sum /= -/(gauss_low_sum es).
  move=> [he hes]; have ht := ih hes; smt().
qed.

lemma gauss_high_sum_nonnegative es : 0 <= gauss_high_sum es.
proof.
  elim: es => [|event es ih].
  + by rewrite /gauss_high_sum /=.
  rewrite /gauss_high_sum /= -/(gauss_high_sum es).
  have := W64.to_uint_cmp event.`3; smt().
qed.

lemma gauss_selected_low_bounds buf n k :
  0 <= n => 0 <= gauss_selected_low_sum buf n k <= n * 281474976710655.
proof.
  move=> hn.
  have hall : all (fun (e : gauss_event) =>
      0 <= W64.to_uint e.`2 < 281474976710656) (gauss_events buf k).
  + rewrite /gauss_events all_map.
    apply List.allP => i _; exact (gauss_event_low_bound buf i).
  have hselected : all (fun (e : gauss_event) =>
      0 <= W64.to_uint e.`2 < 281474976710656)
      (gauss_selected_events n (gauss_events buf k)).
  + apply List.allP => e he.
    have hf := mem_take n (filter gauss_event_accepted (gauss_events buf k)) e he.
    rewrite mem_filter in hf.
    have [_ hevents] := hf.
    move: hall; rewrite List.allP => hall; exact (hall e hevents).
  have hs := gauss_low_sum_bound _ hselected.
  have hsize := size_take_le n (filter gauss_event_accepted (gauss_events buf k)) hn.
  rewrite /gauss_selected_events in hs.
  rewrite /gauss_selected_low_sum /gauss_selected_events.
  smt().
qed.

lemma gauss_canonical_low_headroom buf n k squares :
  0 <= n <= 512 => W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  0 <= W64.to_uint (BArray16.get64 squares 0) + gauss_selected_low_sum buf n k
    < 18446744073709551616.
proof.
  move=> hn hlo.
  have hs := gauss_selected_low_bounds buf n k _; first smt().
  have := W64.to_uint_cmp (BArray16.get64 squares 0); smt().
qed.

op gauss_accumulator_low_total (buf : BArray8192.t) (n k : int)
    (squares : BArray16.t) : int =
  W64.to_uint (BArray16.get64 squares 0) + gauss_selected_low_sum buf n k.

op gauss_accumulator_high_total (buf : BArray8192.t) (n k : int)
    (squares : BArray16.t) : int =
  W64.to_uint (BArray16.get64 squares 1) + gauss_selected_high_sum buf n k.

op gauss_accumulator_integer_total (buf : BArray8192.t) (n k : int)
    (squares : BArray16.t) : int =
  gauss_accumulator_low_total buf n k squares +
    281474976710656 * gauss_accumulator_high_total buf n k squares.

op gauss_normalized_trace_value (buf : BArray8192.t) (n : int) (d : bool)
    (values : BArray4096.t) (squares : BArray16.t) (k : int) : int =
  let state = gauss_trace_prefix buf n d values squares k in
  let nr = gauss_normalize state.`2 state.`3 in
  gauss_limb_value nr.`1 nr.`2.

lemma gauss_accumulator_totals_nonnegative buf n k squares :
  0 <= n =>
  0 <= gauss_accumulator_low_total buf n k squares /\
  0 <= gauss_accumulator_high_total buf n k squares.
proof.
  move=> hn.
  have hl := gauss_selected_low_bounds buf n k hn.
  have hh := gauss_high_sum_nonnegative (gauss_selected_events n (gauss_events buf k)).
  have hw0 := W64.to_uint_cmp (BArray16.get64 squares 0).
  have hw1 := W64.to_uint_cmp (BArray16.get64 squares 1).
  rewrite /gauss_accumulator_low_total /gauss_accumulator_high_total
    /gauss_selected_high_sum; smt().
qed.

lemma gauss_joint_mod_high (a b : int) :
  (a + 281474976710656 * (b %% 18446744073709551616))
      %% 5192296858534827628530496329220096 =
  (a + 281474976710656 * b) %% 5192296858534827628530496329220096.
proof.
  have hb := divz_eq b 18446744073709551616.
  have -> : a + 281474976710656 * b =
    (b %/ 18446744073709551616) * 5192296858534827628530496329220096 +
    (a + 281474976710656 * (b %% 18446744073709551616)) by smt().
  by rewrite modzMDl.
qed.

(* Raw low-word overflow would discard a carry of 2^64. The following joint
   conservation statement therefore requires low headroom explicitly. High
   word overflow is allowed here because it is exactly reduction modulo 2^112. *)
lemma gauss_trace_accumulator_mod buf n d values squares k :
  0 <= n =>
  gauss_accumulator_low_total buf n k squares < 18446744073709551616 =>
  gauss_normalized_trace_value buf n d values squares k =
    gauss_accumulator_integer_total buf n k squares
      %% 5192296858534827628530496329220096.
proof.
  move=> hn hroom.
  have [ha hb] := gauss_accumulator_totals_nonnegative buf n k squares hn.
  have [hl hh] := gauss_trace_prefix_uint_sums buf n d values squares k hn.
  rewrite /gauss_normalized_trace_value /= gauss_normalize_value_mod
    /gauss_limb_value hl hh.
  rewrite -/(gauss_accumulator_low_total buf n k squares)
    -/(gauss_accumulator_high_total buf n k squares).
  rewrite (modz_small (gauss_accumulator_low_total buf n k squares)
    18446744073709551616) 1:/#.
  by rewrite gauss_joint_mod_high /gauss_accumulator_integer_total.
qed.

lemma gauss_trace_accumulator_exact buf n d values squares k :
  0 <= n =>
  gauss_accumulator_low_total buf n k squares < 18446744073709551616 =>
  gauss_accumulator_high_total buf n k squares +
    gauss_accumulator_low_total buf n k squares %/ 281474976710656
      < 18446744073709551616 =>
  gauss_normalized_trace_value buf n d values squares k =
    gauss_accumulator_integer_total buf n k squares.
proof.
  move=> hn hlow hhigh.
  have [ha hb] := gauss_accumulator_totals_nonnegative buf n k squares hn.
  have hd := divz_eq (gauss_accumulator_low_total buf n k squares) 281474976710656.
  have /= hr := modz_cmp (gauss_accumulator_low_total buf n k squares) 281474976710656.
  rewrite gauss_trace_accumulator_mod 1:hn 1:hlow.
  rewrite modz_small // /gauss_accumulator_integer_total; smt().
qed.

lemma gauss_trace_accumulator_canonical_mod buf n d values squares k :
  0 <= n <= 512 => W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  gauss_normalized_trace_value buf n d values squares k =
    gauss_accumulator_integer_total buf n k squares
      %% 5192296858534827628530496329220096.
proof.
  move=> hn hc.
  apply gauss_trace_accumulator_mod; first smt().
  have := gauss_canonical_low_headroom buf n k squares hn hc.
  by rewrite /gauss_accumulator_low_total; smt().
qed.

lemma gauss_trace_accumulator_canonical_exact buf n d values squares k :
  0 <= n <= 512 => W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  gauss_accumulator_high_total buf n k squares +
    gauss_accumulator_low_total buf n k squares %/ 281474976710656
      < 18446744073709551616 =>
  gauss_normalized_trace_value buf n d values squares k =
    gauss_accumulator_integer_total buf n k squares.
proof.
  move=> hn hc hhigh.
  apply gauss_trace_accumulator_exact; first smt().
  + have := gauss_canonical_low_headroom buf n k squares hn hc.
    by rewrite /gauss_accumulator_low_total; smt().
  exact hhigh.
qed.

lemma gauss_event_high_bound (buf : BArray8192.t) (i : int) :
  0 <= W64.to_uint (gauss_event_at buf i).`3 < 274877906944.
proof. rewrite /gauss_event_at; exact: sigma76_square_high_bound. qed.

lemma gauss_high_sum_bound es :
  all (fun (e : gauss_event) => 0 <= W64.to_uint e.`3 < 274877906944) es =>
  0 <= gauss_high_sum es <= size es * 274877906943.
proof.
  elim: es => [|event es ih].
  + by rewrite /gauss_high_sum /=.
  rewrite /gauss_high_sum /= -/(gauss_high_sum es).
  move=> [he hes]; have ht := ih hes; smt().
qed.

lemma gauss_selected_high_bounds buf n k :
  0 <= n => 0 <= gauss_selected_high_sum buf n k <= n * 274877906943.
proof.
  move=> hn.
  have hall : all (fun (e : gauss_event) =>
      0 <= W64.to_uint e.`3 < 274877906944) (gauss_events buf k).
  + rewrite /gauss_events all_map.
    apply List.allP => i _; exact (gauss_event_high_bound buf i).
  have hselected : all (fun (e : gauss_event) =>
      0 <= W64.to_uint e.`3 < 274877906944)
      (gauss_selected_events n (gauss_events buf k)).
  + apply List.allP => e he.
    have hf := mem_take n (filter gauss_event_accepted (gauss_events buf k)) e he.
    rewrite mem_filter in hf.
    have [_ hevents] := hf.
    move: hall; rewrite List.allP => hall; exact (hall e hevents).
  have hs := gauss_high_sum_bound _ hselected.
  have hsize := size_take_le n (filter gauss_event_accepted (gauss_events buf k)) hn.
  rewrite /gauss_selected_events in hs.
  rewrite /gauss_selected_high_sum /gauss_selected_events.
  smt().
qed.

lemma gauss_canonical_both_headroom buf n k squares :
  0 <= n <= 512 =>
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  W64.to_uint (BArray16.get64 squares 1) < 281474976710656 =>
  gauss_accumulator_high_total buf n k squares +
    gauss_accumulator_low_total buf n k squares %/ 281474976710656
      < 18446744073709551616.
proof.
  move=> hn hlo hhi.
  have hs := gauss_selected_high_bounds buf n k _; first smt().
  have ha := gauss_canonical_low_headroom buf n k squares hn hlo.
  have hd := divz_eq (gauss_accumulator_low_total buf n k squares) 281474976710656.
  have /= hr := modz_cmp (gauss_accumulator_low_total buf n k squares) 281474976710656.
  rewrite -/(gauss_accumulator_low_total buf n k squares) in ha.
  rewrite /gauss_accumulator_high_total; smt().
qed.

(* With both initial limbs canonical in 48 bits and at most 512 accepted
   outputs, the actual square-high bound discharges all arithmetic headroom. *)
lemma gauss_trace_accumulator_canonical_both_exact buf n d values squares k :
  0 <= n <= 512 =>
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  W64.to_uint (BArray16.get64 squares 1) < 281474976710656 =>
  gauss_normalized_trace_value buf n d values squares k =
    gauss_accumulator_integer_total buf n k squares.
proof.
  move=> hn hlo hhi.
  apply (gauss_trace_accumulator_canonical_exact buf n d values squares k hn hlo).
  exact (gauss_canonical_both_headroom buf n k squares hn hlo hhi).
qed.

lemma gauss_trace_result_accumulator_value buf n available d values squares count :
  gauss_limb_value
    (BArray16.get64 (gauss_trace_result buf n available d values squares count).`2 0)
    (BArray16.get64 (gauss_trace_result buf n available d values squares count).`2 1) =
  gauss_normalized_trace_value buf n d values squares (available %/ 26).
proof.
  by rewrite /gauss_trace_result /gauss_normalized_trace_value /=.
qed.

lemma gauss_trace_result_canonical_both_exact buf n available d values squares count :
  0 <= n <= 512 =>
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  W64.to_uint (BArray16.get64 squares 1) < 281474976710656 =>
  gauss_limb_value
    (BArray16.get64 (gauss_trace_result buf n available d values squares count).`2 0)
    (BArray16.get64 (gauss_trace_result buf n available d values squares count).`2 1) =
  gauss_accumulator_integer_total buf n (available %/ 26) squares.
proof.
  move=> hn hlo hhi; rewrite gauss_trace_result_accumulator_value.
  exact (gauss_trace_accumulator_canonical_both_exact buf n d values squares
    (available %/ 26) hn hlo hhi).
qed.
