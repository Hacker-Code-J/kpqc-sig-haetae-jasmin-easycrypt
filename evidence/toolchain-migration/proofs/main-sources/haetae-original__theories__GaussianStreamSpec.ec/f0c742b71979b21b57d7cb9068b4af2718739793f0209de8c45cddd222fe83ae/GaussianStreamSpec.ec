require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianStreamBuffer GaussianStreamSequence GaussianStreamAccumulator
  GaussianTraceSpec GaussianTraceProperties GaussianWindowSpec.

(* Only the production requests 256 and 257 are used here. Both store 256
   visible coefficients; request257 includes one accepted, unwritten dummy. *)
op gs_progress (candidate_bytes : int -> W8.t)
    (initial current : BArray32768.t) (initial_squares squares : BArray16.t)
    (requested sample_offset attempts accepted : int) : bool =
  let selected = gauss_selected_events requested (gauss_stream_events candidate_bytes attempts) in
  (requested = 256 \/ requested = 257) /\
  0 <= attempts /\ 0 <= accepted <= requested /\
  accepted = size selected /\
  (forall j, 0 <= j < min accepted 256 =>
    BArray32768.get64 current (sample_offset + j) =
      nth W64.zero (map (fun (event : gauss_event) => event.`1) selected) j) /\
  gauss_big_output_frame initial current sample_offset requested /\
  (requested = 257 =>
    BArray32768.get64 current (sample_offset + 256) =
      BArray32768.get64 initial (sample_offset + 256)) /\
  gauss_stream_acc_ok (gauss_stream_value initial_squares) accepted squares /\
  gauss_stream_value squares = gauss_stream_value initial_squares +
    gauss_event_value_sum selected.

(* This is a partial-correctness result: some finite SHAKE prefix supplies the
   requested accepted samples. It does not assert existence of that prefix
   for every seed, termination of rejection sampling, or a distribution law. *)
op gs_stream_result (stream : int -> W8.t)
    (initial current : BArray32768.t) (initial_signs signs : BArray512.t)
    (initial_squares squares : BArray16.t)
    (requested sample_offset sign_offset : int) : bool =
  gs_signs_result stream initial_signs signs sign_offset /\
  exists blocks, 49 <= blocks /\
    gs_progress (fun j => stream (32 + j)) initial current initial_squares squares
      requested sample_offset (gs_stream_attempts blocks) requested.

lemma gs_stream_result_finish stream initial current initial_signs signs
    initial_squares squares n oo so blocks accepted :
  49 <= blocks =>
  gs_signs_result stream initial_signs signs so =>
  gs_progress (fun j => stream (32 + j)) initial current initial_squares squares
    n oo (gs_stream_attempts blocks) accepted =>
  n <= accepted =>
  gs_stream_result stream initial current initial_signs signs initial_squares squares n oo so.
proof.
  move=> hb hs hp hend.
  have he : accepted = n by move: hp; rewrite /gs_progress /=; smt().
  rewrite /gs_stream_result.
  split; first exact hs.
  exists blocks; split; first exact hb.
  by move: hp; rewrite he.
qed.

lemma gs_selected_complete_stable f n attempts later :
  0 <= n => 0 <= attempts <= later =>
  size (gauss_selected_events n (gauss_stream_events f attempts)) = n =>
  gauss_selected_events n (gauss_stream_events f later) =
    gauss_selected_events n (gauss_stream_events f attempts).
proof.
  move=> hn ha hsize.
  have he : later = attempts + (later - attempts) by ring.
  rewrite he gauss_stream_events_split 1:/# 1:/#
    gauss_selected_events_concat 1:hn hsize subzz /gauss_selected_events take0 cats0.
  trivial.
qed.

lemma gs_selected_complete_unique f n a b :
  0 <= n => 0 <= a => 0 <= b =>
  size (gauss_selected_events n (gauss_stream_events f a)) = n =>
  size (gauss_selected_events n (gauss_stream_events f b)) = n =>
  gauss_selected_events n (gauss_stream_events f a) =
    gauss_selected_events n (gauss_stream_events f b).
proof.
  move=> hn ha hb hca hcb.
  case (a <= b) => hab.
  + have h := gs_selected_complete_stable f n a b hn _ hca; first smt().
    smt().
  apply gs_selected_complete_stable; smt().
qed.

lemma gs_progress_terminal_frame f initial current initial_squares squares n oo attempts :
  gs_progress f initial current initial_squares squares n oo attempts n =>
  gauss_big_output_frame initial current oo 256.
proof.
  rewrite /gs_progress /gauss_big_output_frame /=.
  smt().
qed.

lemma gs_canonical_square_unique (squares_left squares_right : BArray16.t) :
  W64.to_uint (BArray16.get64 squares_left 0) < 281474976710656 =>
  W64.to_uint (BArray16.get64 squares_right 0) < 281474976710656 =>
  gauss_stream_value squares_left = gauss_stream_value squares_right => squares_left = squares_right.
proof.
  move=> hl hr heq.
  have hln := W64.to_uint_cmp (BArray16.get64 squares_left 0).
  have hrn := W64.to_uint_cmp (BArray16.get64 squares_right 0).
  rewrite /gauss_stream_value /GaussianAccumulatorCorrectness.gauss_limb_value in heq.
  have hlow : W64.to_uint (BArray16.get64 squares_left 0) =
      W64.to_uint (BArray16.get64 squares_right 0) by smt().
  have hhigh : W64.to_uint (BArray16.get64 squares_left 1) =
      W64.to_uint (BArray16.get64 squares_right 1) by smt().
  apply BArray16.ext_eq64 => i hi.
  have hi01 : i = 0 \/ i = 1 by smt().
  move: hi01 => [-> | ->]; apply W64.to_uint_eq; assumption.
qed.

(* The existential prefix in the result does not make the return value
   ambiguous: every sufficiently long prefix selects the same first n events. *)
lemma gs_stream_result_unique stream initial initial_signs initial_squares n oo so
    current1 signs1 squares1 current2 signs2 squares2 :
  gs_stream_result stream initial current1 initial_signs signs1
    initial_squares squares1 n oo so =>
  gs_stream_result stream initial current2 initial_signs signs2
    initial_squares squares2 n oo so =>
  current1 = current2 /\ signs1 = signs2 /\ squares1 = squares2.
proof.
  move=> [hs1 [b1 [hb1 hp1]]] [hs2 [b2 [hb2 hp2]]].
  have [hn [ha1 [hc1 [hcount1 [hvalues1 [hf1 [hd1 [hacc1 hsum1]]]]]]]] := hp1.
  have [_ [ha2 [_ [hcount2 [hvalues2 [hf2 [hd2 [hacc2 hsum2]]]]]]]] := hp2.
  have hselected := gs_selected_complete_unique (fun j => stream (32 + j)) n
    (gs_stream_attempts b1) (gs_stream_attempts b2) _ ha1 ha2 _ _; first 3 smt().
  have hframe1 := gs_progress_terminal_frame _ _ _ _ _ _ _ _ hp1.
  have hframe2 := gs_progress_terminal_frame _ _ _ _ _ _ _ _ hp2.
  split.
  + apply BArray32768.ext_eq64 => j hj.
    have hword : 0 <= j < 4096 by smt().
    case (oo <= j < oo + 256) => hin.
    + have hv1 := hvalues1 (j - oo) _; first smt().
      have hv2 := hvalues2 (j - oo) _; first smt().
      rewrite hselected in hv1.
      smt().
    have hf1j := hframe1 j hword hin.
    have hf2j := hframe2 j hword hin.
    smt().
  split.
  + apply BArray512.ext_eq => j hj.
    have h1 := hs1 j hj; have h2 := hs2 j hj; smt().
  apply gs_canonical_square_unique.
  + move: hacc1; rewrite /gauss_stream_acc_ok; smt().
  + move: hacc2; rewrite /gauss_stream_acc_ok; smt().
  rewrite hsum1 hsum2 hselected; trivial.
qed.
