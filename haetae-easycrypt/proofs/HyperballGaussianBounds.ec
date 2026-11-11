require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import SigmaSpec SigmaCorrectness SigmaRoundingCorrectness SigmaSquareBounds
  CDTCorrectness GaussianTraceSpec GaussianTraceProperties GaussianStreamSequence
  GaussianAccumulatorCorrectness GaussianStreamAccumulator GaussianStreamSpec
  GaussianStreamCorrectness SHAKEStreamSpec SHAKESeedInitCorrectness GaussianStreamBuffer.

lemma hb_xor32_bound (a b : W64.t) :
  W64.to_uint a < 4294967296 => W64.to_uint b < 4294967296 =>
  W64.to_uint (a `^` b) < 4294967296.
proof.
  move=> ha hb.
  have hm : (a `^` b) `&` W64.of_int (2^32 - 1) = a `^` b.
  + by rewrite W64.andwDl !sigma_mask_id.
  have he := W64.to_uint_and_mod 32 (a `^` b) _; first trivial.
  rewrite hm /= in he.
  have /= hr := modz_cmp (W64.to_uint (a `^` b)) 4294967296.
  smt().
qed.

lemma hb_mul48_high_bound (x0 x1 : W64.t) :
  W64.to_uint x0 < 281474976710656 => W64.to_uint x1 < 4294967296 =>
  0 <= W64.to_uint (mul48_word x0 x1).`2 < 4294967296.
proof.
  move=> hx0 hx1.
  have /= h0 := W64.to_uint_cmp x0.
  have /= h1 := W64.to_uint_cmp x1.
  have hp : W64.to_uint x0 * W64.to_uint x1 < 1208925819614629174706176 by smt().
  have /= hm := W64.mulhiP x0 x1.
  have /= hl := W64.to_uint_cmp (x0 * x1).
  have /= hh := W64.to_uint_cmp (W64.mulhi x0 x1).
  have hhigh : W64.to_uint (W64.mulhi x0 x1) < 65536 by smt().
  have hshift : W64.to_uint (W64.mulhi x0 x1 `<<<` 16) < 4294967296.
  + rewrite W64.to_uint_shl //= modz_small; smt().
  have hlow := sigma_shr48_bound (x0 * x1).
  have hxor := hb_xor32_bound (W64.mulhi x0 x1 `<<<` 16)
    ((x0 * x1) `>>>` 48) hshift _; first smt().
  have hz := W64.to_uint_cmp (mul48_word x0 x1).`2.
  rewrite /mul48_word W64.muluE /=; smt().
qed.

lemma hb_square_high_sum (cross product carry : W64.t) :
  W64.to_uint cross < 8589934592 =>
  W64.to_uint product < 9223372036854775808 =>
  0 <= W64.to_uint (((cross `>>>` 28) + (product `>>>` 28)) + (carry `>>>` 48))
    < 68719476736.
proof.
  move=> hc hp.
  have /= hcw := W64.to_uint_cmp cross.
  have /= hpw := W64.to_uint_cmp product.
  have hc28 : 0 <= W64.to_uint (cross `>>>` 28) < 32.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have hp28 : 0 <= W64.to_uint (product `>>>` 28) < 34359738368.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have hcarry := sigma_shr48_bound carry.
  have hadd : W64.to_uint ((cross `>>>` 28) + (product `>>>` 28)) =
    W64.to_uint (cross `>>>` 28) + W64.to_uint (product `>>>` 28).
  + rewrite W64.to_uintD modz_small; smt().
  rewrite W64.to_uintD hadd modz_small; smt().
qed.

(* This is a bound on the exact truncated word computation. It does not
   replace square_word with an ideal integer or real square. *)
lemma hb_square_word_high_bound (x0 x1 : W64.t) :
  W64.to_uint x0 < 281474976710656 => W64.to_uint x1 < 2801795072 =>
  0 <= W64.to_uint (square_word x0 x1).`2 < 68719476736.
proof.
  move=> hx0 hx1.
  have /= hr := W64.to_uint_cmp x1.
  have hp : W64.to_uint x1 * W64.to_uint x1 < 9223372036854775808 by smt().
  have hprod : W64.to_uint (x1 * x1) < 9223372036854775808.
  + rewrite W64.to_uintM_small; smt().
  have hhi : W64.mulhi x1 x1 = W64.zero.
  + rewrite W64.to_uint_eq W64.to_uint0 W64.mulhi0; smt().
  have hcross := hb_mul48_high_bound x0 x1 hx0 _; first smt().
  have hcross2 : W64.to_uint ((mul48_word x0 x1).`2 `<<<` 1) < 8589934592.
  + rewrite W64.to_uint_shl //= modz_small; smt().
  rewrite /square_word W64.muluE /= hhi (W64.shlMP 0 36) //=.
  exact (hb_square_high_sum _ _ _ hcross2 hprod).
qed.

lemma hb_sigma76_square_high_bound (p : BArray26.t) :
  0 <= W64.to_uint (sigma76_spec p).`3 < 68719476736.
proof.
  have [h0 [h1 h2]] := sigma76_decoded_bounds p.
  pose count := cdt_count (cdt_lo_input p) (cdt_hi_input p) 166.
  have hx : W64.to_uint (W64.of_int count) = count.
  + rewrite W64.of_uintK modz_small; smt().
  have hy : W64.to_uint (le3_word p 23 `|` (W64.of_int count `<<<` 24)) < 2801795072.
  + rewrite sigma_high_uint 1:/# 1:/# hx; smt().
  rewrite /sigma76_spec /sigma_from_cdt /= -/count.
  apply hb_square_word_high_bound; smt().
qed.

op hb_event_max : int = 19342813113834066795298815.

op hb_event_bounded (event : gauss_event) : bool =
  0 <= W64.to_uint event.`2 < 281474976710656 /\
  0 <= W64.to_uint event.`3 < 68719476736.

op hb_events_bounded (events : gauss_event list) : bool = all hb_event_bounded events.

(* The budget includes accepted dummy coefficients.  The value is the exact
   radix-2^48 combination of the two current machine limbs. *)
op hb_cumulative_square_bound (accepted : int) (squares : BArray16.t) : bool =
  0 <= accepted <= 2818 /\
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
  0 <= gauss_stream_value squares <= accepted * hb_event_max.

lemma hb_sigma76_event_bounded p : hb_event_bounded (sigma76_spec p).
proof.
  have hh := hb_sigma76_square_high_bound p.
  have hl : 0 <= W64.to_uint (sigma76_spec p).`2 < 281474976710656.
  + rewrite /sigma76_spec /sigma_from_cdt /=; exact: gauss_square_low_bound.
  by rewrite /hb_event_bounded.
qed.

lemma hb_stream_events_bounded f k : hb_events_bounded (gauss_stream_events f k).
proof.
  rewrite /hb_events_bounded /gauss_stream_events all_map.
  apply List.allP => i _; rewrite /gauss_stream_event.
  exact: hb_sigma76_event_bounded.
qed.

lemma hb_selected_stream_events_bounded f n k :
  hb_events_bounded (gauss_selected_events n (gauss_stream_events f k)).
proof.
  have hall := hb_stream_events_bounded f k.
  rewrite /hb_events_bounded; apply List.allP => event he.
  have hf := mem_take n (filter gauss_event_accepted (gauss_stream_events f k)) event he.
  rewrite mem_filter in hf; have [_ hm] := hf.
  move: hall; rewrite /hb_events_bounded List.allP => hall.
  exact (hall event hm).
qed.

lemma hb_event_value_sum_bound events : hb_events_bounded events =>
  0 <= gauss_event_value_sum events <= size events * hb_event_max.
proof.
  elim: events => [|event events ih].
  + by rewrite /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /=.
  move=> [he hes]; have hs := ih hes.
  rewrite /hb_event_bounded in he.
  rewrite /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /hb_event_max /= in hs.
  rewrite /gauss_event_value_sum /gauss_low_sum /gauss_high_sum /hb_event_max /=.
  smt().
qed.

lemma hb_events_bounded_cat es1 es2 :
  hb_events_bounded es1 => hb_events_bounded es2 => hb_events_bounded (es1 ++ es2).
proof. by rewrite /hb_events_bounded all_cat. qed.

lemma hb_events_bounded_flatten batches :
  all hb_events_bounded batches => hb_events_bounded (flatten batches).
proof.
  elim: batches => [|events batches ih] //=.
  move=> [he hs]; rewrite flatten_cons.
  apply hb_events_bounded_cat; first exact he.
  exact (ih hs).
qed.

lemma hb_selected_event_value_sum_bound f n k : 0 <= n =>
  0 <= gauss_event_value_sum (gauss_selected_events n (gauss_stream_events f k)) <=
    n * hb_event_max.
proof.
  move=> hn.
  have hs := hb_event_value_sum_bound _ (hb_selected_stream_events_bounded f n k).
  have hc := gauss_selected_events_bounds n (gauss_stream_events f k) hn.
  rewrite /hb_event_max in hs.
  rewrite /hb_event_max; smt().
qed.

lemma hb_cumulative_canonical accepted squares :
  hb_cumulative_square_bound accepted squares =>
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
  W64.to_uint (BArray16.get64 squares 1) < 281474976710656.
proof.
  rewrite /hb_cumulative_square_bound /hb_event_max /gauss_stream_value /gauss_limb_value.
  have hl := W64.to_uint_cmp (BArray16.get64 squares 0); smt().
qed.

lemma hb_cumulative_zero squares :
  BArray16.get64 squares 0 = W64.zero => BArray16.get64 squares 1 = W64.zero =>
  hb_cumulative_square_bound 0 squares.
proof.
  move=> h0 h1.
  by rewrite /hb_cumulative_square_bound /gauss_stream_value /gauss_limb_value h0 h1 /=.
qed.

lemma hb_partition_canonical batches squares :
  all hb_events_bounded batches => size (flatten batches) <= 2818 =>
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 =>
  gauss_stream_value squares = gauss_event_value_sum (flatten batches) =>
  hb_cumulative_square_bound (size (flatten batches)) squares /\
  W64.to_uint (BArray16.get64 squares 1) < 281474976710656.
proof.
  move=> hb hbudget hlo hvalue.
  have hs := hb_event_value_sum_bound _ (hb_events_bounded_flatten batches hb).
  have hsize := size_ge0 (flatten batches).
  have hc : hb_cumulative_square_bound (size (flatten batches)) squares.
  + rewrite /hb_cumulative_square_bound; smt().
  have hcan := hb_cumulative_canonical _ _ hc; smt().
qed.

lemma hb_gs_progress_bound f initial current initial_squares squares n oo attempts accepted previous :
  hb_cumulative_square_bound previous initial_squares => previous + accepted <= 2818 =>
  gs_progress f initial current initial_squares squares n oo attempts accepted =>
  hb_cumulative_square_bound (previous + accepted) squares.
proof.
  move=> hprevious hbudget hp.
  have [_ [ha [hc [hcount [hvalues [hframe [hdummy [hacc hsum]]]]]]]] := hp.
  have hs := hb_event_value_sum_bound _ (hb_selected_stream_events_bounded f n attempts).
  have hlo : W64.to_uint (BArray16.get64 squares 0) < 281474976710656.
  + move: hacc; rewrite /gauss_stream_acc_ok; smt().
  rewrite /hb_cumulative_square_bound /hb_event_max in hprevious.
  rewrite /hb_event_max in hs.
  rewrite /hb_cumulative_square_bound /hb_event_max.
  smt().
qed.

lemma hb_gs_stream_result_bound stream initial current initial_signs signs
    initial_squares squares n oo so previous :
  hb_cumulative_square_bound previous initial_squares => previous + n <= 2818 =>
  gs_stream_result stream initial current initial_signs signs initial_squares squares n oo so =>
  hb_cumulative_square_bound (previous + n) squares /\
  W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
  W64.to_uint (BArray16.get64 squares 1) < 281474976710656.
proof.
  move=> hprevious hbudget [hsigns [blocks [hblocks hp]]].
  have hc := hb_gs_progress_bound (fun j => stream (32 + j)) initial current
    initial_squares squares n oo (gs_stream_attempts blocks) n previous
    hprevious hbudget hp.
  have hcan := hb_cumulative_canonical _ _ hc; smt().
qed.

(* The source theorem is Hoare partial correctness: this strengthening does
   not add a termination claim for the unbounded rejection/refill loop. *)
lemma hb_sample_gauss_N_full_at_correct
    (previous : int) (seed0 : BArray64.t) (nonce0 : W64.t)
    (n sample_offset sign_offset : int) (initial : BArray32768.t)
    (initial_signs : BArray512.t) (initial_squares : BArray16.t) :
  hoare [GaussianStreamCorrectness.StreamSigner._sf_sample_gauss_N_full_at :
    seedp = seed0 /\ nonce = nonce0 /\ len = W64.of_int n /\
    W64.to_uint sampleoff = sample_offset /\ W64.to_uint signoff = sign_offset /\
    rp = initial /\ signsp = initial_signs /\ sqsump = initial_squares /\
    (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
    0 <= sign_offset /\ sign_offset + 32 <= 512 /\
    hb_cumulative_square_bound previous initial_squares /\ previous + n <= 2818
    ==>
    gs_stream_result
      (SHAKEStreamSpec.shake_stream_byte (SHAKEStreamSpec.shake_initial_words seed0 nonce0))
      initial res.`1 initial_signs res.`2 initial_squares res.`3 n sample_offset sign_offset /\
    hb_cumulative_square_bound (previous + n) res.`3 /\
    W64.to_uint (BArray16.get64 res.`3 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 res.`3 1) < 281474976710656].
proof.
  conseq (sample_gauss_N_full_at_correct seed0 nonce0 n sample_offset sign_offset
    initial initial_signs initial_squares) => //.
  + move=> &m hpre.
    have hb : hb_cumulative_square_bound previous initial_squares by smt().
    have hc := hb_cumulative_canonical _ _ hb; smt().
  move=> &m hpre result hresult.
  have hb : hb_cumulative_square_bound previous initial_squares by smt().
  have hbudget : previous + n <= 2818 by smt().
  have hpost := hb_gs_stream_result_bound
    (SHAKEStreamSpec.shake_stream_byte (SHAKEStreamSpec.shake_initial_words seed0 nonce0))
    initial result.`1 initial_signs result.`2 initial_squares result.`3
    n sample_offset sign_offset previous hb hbudget hresult.
  smt().
qed.
