require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianTraceSpec GaussianTraceProperties GaussianStreamSequence
  GaussianStreamSpec GaussianStreamBuffer GaussianStreamAccumulator GaussianStreamCorrectness
  GaussianWindowSpec SHAKEStreamSpec.
import SHAKEStreamSpec.

(* A property of a particular finite candidate-byte prefix, with no
   randomness or termination assumption about concrete SHAKE seeds. *)
op [opaque] gr_adequate (candidate_bytes : int -> W8.t) (requested attempts : int) : bool =
  0 <= requested /\ 0 <= attempts /\
  requested <= count gauss_event_accepted (gauss_stream_events candidate_bytes attempts).

(* Includes the 32 sign bytes and rounds up to a complete 136-byte block. *)
op [opaque] gr_block_cap (attempts : int) : int =
  max 49 ((26 * attempts + 167) %/ 136).

op [opaque] gr_prefix_result (stream : int -> W8.t)
    (initial current : BArray32768.t) (initial_signs signs : BArray512.t)
    (initial_squares squares : BArray16.t) (n oo so attempts : int) : bool =
  gs_signs_result stream initial_signs signs so /\
  gs_progress (fun j => stream (32 + j)) initial current initial_squares squares n oo attempts n.

lemma gr_block_cap_bounds attempts : 0 <= attempts =>
  49 <= gr_block_cap attempts /\ attempts <= gs_stream_attempts (gr_block_cap attempts).
proof.
  move=> ha.
  have hd := divz_eq (26 * attempts + 167) 136.
  have hr := modz_cmp (26 * attempts + 167) 136.
  rewrite /gr_block_cap /gs_stream_attempts lez_divRL 1:// /max; smt().
qed.

lemma gr_attempts_monotone a b : a <= b => gs_stream_attempts a <= gs_stream_attempts b.
proof.
  move=> hab; rewrite /gs_stream_attempts; apply leq_div2r; smt().
qed.

lemma gr_refill_candidate_count blocks : 49 <= blocks =>
  5 <= gs_stream_attempts (blocks + 1) - gs_stream_attempts blocks <= 6.
proof.
  move=> hb; have [_ ht] := gs_stream_bounds blocks hb.
  have [ha _] := gs_stream_advance blocks.
  have hd := divz_eq (136 + gs_stream_tail blocks) 26.
  have hr := modz_cmp (136 + gs_stream_tail blocks) 26.
  rewrite ha; smt().
qed.

lemma gr_adequate_selected f n attempts : gr_adequate f n attempts =>
  size (gauss_selected_events n (gauss_stream_events f attempts)) = n.
proof.
  rewrite /gr_adequate; move=> [hn [ha hc]].
  rewrite gauss_selected_events_count 1:hn /min; smt().
qed.

lemma gr_adequate_attempts f n attempts : gr_adequate f n attempts => n <= attempts.
proof.
  rewrite /gr_adequate; move=> [hn [ha hc]].
  have hsize := count_size gauss_event_accepted (gauss_stream_events f attempts).
  rewrite gauss_stream_events_size 1:ha in hsize; smt().
qed.

lemma gr_adequate_bounds f n attempts : gr_adequate f n attempts =>
  0 <= n /\ 0 <= attempts.
proof. rewrite /gr_adequate; smt(). qed.

lemma gr_selected_stable f n attempts later :
  gr_adequate f n attempts => attempts <= later =>
  gauss_selected_events n (gauss_stream_events f later) =
    gauss_selected_events n (gauss_stream_events f attempts).
proof.
  move=> had hle; have [hn ha] := gr_adequate_bounds f n attempts had.
  apply gs_selected_complete_stable; first 2 smt().
  exact (gr_adequate_selected f n attempts had).
qed.

lemma gr_block_selection f n attempts blocks :
  gr_adequate f n attempts => gr_block_cap attempts <= blocks =>
  gauss_selected_events n (gauss_stream_events f (gs_stream_attempts blocks)) =
    gauss_selected_events n (gauss_stream_events f attempts) /\
  size (gauss_selected_events n (gauss_stream_events f (gs_stream_attempts blocks))) = n.
proof.
  move=> had hb; have [hn ha] := gr_adequate_bounds f n attempts had.
  have [_ hcap] := gr_block_cap_bounds attempts ha.
  have hmono := gr_attempts_monotone (gr_block_cap attempts) blocks hb.
  have hstable := gr_selected_stable f n attempts (gs_stream_attempts blocks) had _;
    first smt().
  have hsize := gr_adequate_selected f n attempts had.
  by rewrite hstable hsize.
qed.

lemma gr_progress_complete f initial current initial_squares squares n oo attempts blocks accepted :
  gr_adequate f n attempts => gr_block_cap attempts <= blocks =>
  gs_progress f initial current initial_squares squares n oo (gs_stream_attempts blocks) accepted =>
  accepted = n.
proof.
  move=> had hb hp.
  have [_ hselected] := gr_block_selection f n attempts blocks had hb.
  have [_ [_ [_ [hcount _]]]] := hp.
  smt().
qed.

lemma gr_progress_below_cap f initial current initial_squares squares n oo attempts blocks accepted :
  gr_adequate f n attempts =>
  gs_progress f initial current initial_squares squares n oo (gs_stream_attempts blocks) accepted =>
  accepted < n => blocks < gr_block_cap attempts.
proof.
  move=> had hp haccept.
  case (gr_block_cap attempts <= blocks) => hb; last smt().
  have := gr_progress_complete f initial current initial_squares squares n oo attempts blocks accepted
    had hb hp; smt().
qed.

lemma gr_progress_rebase f initial current initial_squares squares n oo a b :
  0 <= b =>
  gauss_selected_events n (gauss_stream_events f a) = gauss_selected_events n (gauss_stream_events f b) =>
  gs_progress f initial current initial_squares squares n oo a n =>
  gs_progress f initial current initial_squares squares n oo b n.
proof. move=> hb he hp; move: hp; rewrite /gs_progress he; smt(). qed.

lemma gr_stream_result_prefix stream initial current initial_signs signs
    initial_squares squares n oo so attempts :
  gr_adequate (fun j => stream (32 + j)) n attempts =>
  gs_stream_result stream initial current initial_signs signs initial_squares squares n oo so =>
  gr_prefix_result stream initial current initial_signs signs initial_squares squares n oo so attempts.
proof.
  move=> had [hsigns [blocks [hb hp]]].
  have [hn ha] := gr_adequate_bounds _ _ _ had.
  have [_ [haold [_ [hcount _]]]] := hp.
  have hcountold : size (gauss_selected_events n
      (gauss_stream_events (fun j => stream (32 + j)) (gs_stream_attempts blocks))) = n by
    apply/eq_sym; exact hcount.
  have hselected := gr_adequate_selected _ _ _ had.
  have heq := gs_selected_complete_unique (fun j => stream (32 + j)) n
    (gs_stream_attempts blocks) attempts hn haold ha hcountold hselected.
  rewrite /gr_prefix_result; split; first exact hsigns.
  exact (gr_progress_rebase _ _ _ _ _ _ _ _ _ ha heq hp).
qed.

lemma gr_prefix_result_values stream initial current initial_signs signs
    initial_squares squares n oo so attempts j :
  gr_prefix_result stream initial current initial_signs signs initial_squares squares n oo so attempts =>
  0 <= j < 256 =>
  BArray32768.get64 current (oo + j) = nth W64.zero
    (map (fun (event : gauss_event) => event.`1)
      (gauss_selected_events n (gauss_stream_events (fun i => stream (32 + i)) attempts))) j.
proof.
  rewrite /gr_prefix_result; move=> [_ hp] hj.
  have [hn [_ [_ [_ [hvalues _]]]]] := hp.
  apply hvalues; smt().
qed.

lemma gr_prefix_result_frame stream initial current initial_signs signs
    initial_squares squares n oo so attempts :
  gr_prefix_result stream initial current initial_signs signs initial_squares squares n oo so attempts =>
  gauss_big_output_frame initial current oo 256.
proof.
  rewrite /gr_prefix_result; move=> [_ hp]; exact (gs_progress_terminal_frame _ _ _ _ _ _ _ _ hp).
qed.

lemma gr_prefix_result_squares stream initial current initial_signs signs
    initial_squares squares n oo so attempts :
  gr_prefix_result stream initial current initial_signs signs initial_squares squares n oo so attempts =>
  gauss_stream_value squares = gauss_stream_value initial_squares +
    gauss_event_value_sum
      (gauss_selected_events n (gauss_stream_events (fun i => stream (32 + i)) attempts)).
proof. rewrite /gr_prefix_result; move=> [_ hp]; move: hp; rewrite /gs_progress; smt(). qed.

lemma gr_prefix_result_dummy stream initial current initial_signs signs
    initial_squares squares n oo so attempts :
  gr_prefix_result stream initial current initial_signs signs initial_squares squares n oo so attempts =>
  n = 257 => BArray32768.get64 current (oo + 256) = BArray32768.get64 initial (oo + 256).
proof. rewrite /gr_prefix_result; move=> [_ hp] hn; move: hp; rewrite /gs_progress; smt(). qed.

lemma gr_prefix_result_block stream initial current initial_signs signs
    initial_squares squares n oo so attempts :
  gr_adequate (fun j => stream (32 + j)) n attempts =>
  gr_prefix_result stream initial current initial_signs signs initial_squares squares n oo so attempts =>
  gr_prefix_result stream initial current initial_signs signs initial_squares squares n oo so
    (gs_stream_attempts (gr_block_cap attempts)).
proof.
  move=> had hprefix.
  rewrite /gr_prefix_result in hprefix; have [hsigns hp] := hprefix.
  have [_ ha] := gr_adequate_bounds _ _ _ had.
  have [hb _] := gr_block_cap_bounds attempts ha.
  have [hab _] := gs_stream_bounds (gr_block_cap attempts) hb.
  have [heq _] := gr_block_selection (fun j => stream (32 + j)) n attempts
    (gr_block_cap attempts) had _; first trivial.
  rewrite /gr_prefix_result; split; first exact hsigns.
  apply (gr_progress_rebase (fun j => stream (32 + j)) initial current
    initial_squares squares n oo attempts (gs_stream_attempts (gr_block_cap attempts)));
    first exact hab.
  + apply/eq_sym; exact heq.
  exact hp.
qed.

(* Actual source linkage is still Hoare partial correctness here. A separate
   conditional termination theorem establishes losslessness under adequacy. *)
lemma gr_sample_gauss_N_prefix_correct
    (seed0 : BArray64.t) (nonce0 : W64.t) (n sample_offset sign_offset attempts : int)
    (initial : BArray32768.t) (initial_signs : BArray512.t) (initial_squares : BArray16.t) :
  hoare [StreamSigner._sf_sample_gauss_N_full_at :
    seedp = seed0 /\ nonce = nonce0 /\ len = W64.of_int n /\
    W64.to_uint sampleoff = sample_offset /\ W64.to_uint signoff = sign_offset /\
    rp = initial /\ signsp = initial_signs /\ sqsump = initial_squares /\
    (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
    0 <= sign_offset /\ sign_offset + 32 <= 512 /\
    W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 initial_squares 1) < 281474976710656 /\
    gr_adequate (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j)) n attempts
    ==>
    gr_prefix_result (shake_stream_byte (shake_initial_words seed0 nonce0)) initial res.`1
      initial_signs res.`2 initial_squares res.`3 n sample_offset sign_offset attempts].
proof.
  conseq (sample_gauss_N_full_at_correct seed0 nonce0 n sample_offset sign_offset
    initial initial_signs initial_squares) => //.
  move=> &hr hpre result hresult.
  apply gr_stream_result_prefix; last exact hresult.
  smt().
qed.
