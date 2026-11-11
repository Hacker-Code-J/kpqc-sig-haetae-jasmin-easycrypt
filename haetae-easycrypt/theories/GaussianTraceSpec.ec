require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import BArray4096 BArray8192 BArray26 BArray16 BArray8 SigmaCorrectness.

type gauss_event = W64.t * W64.t * W64.t * W64.t.
type gauss_trace_state = BArray4096.t * W64.t * W64.t * int.

(* Consecutive 26-byte candidates, independent of the imperative copy loop. *)
op gauss_chunk (buf : BArray8192.t) (offset : int) : BArray26.t =
  BArray26.init (fun k => BArray8192.get8 buf (offset + k)).

op gauss_event_at (buf : BArray8192.t) (i : int) : gauss_event =
  sigma76_spec (gauss_chunk buf (26 * i)).

op gauss_events (buf : BArray8192.t) (attempts : int) : gauss_event list =
  map (gauss_event_at buf) (iota_ 0 attempts).

(* Once the requested count is reached, remaining candidates do not affect
   the result. Before then even a rejected candidate may overwrite the next
   output slot; the dummy-last rule suppresses only the final requested slot. *)
op gauss_trace_step (requested : int) (dont : bool)
    (state : gauss_trace_state) (event : gauss_event) : gauss_trace_state =
  if requested <= state.`4 then state else
  let values = if dont /\ state.`4 = requested - 1 then state.`1
               else BArray4096.set64 state.`1 state.`4 event.`1 in
  let mask = W64.zero - event.`4 in
  (values, state.`2 + (event.`2 `&` mask),
   state.`3 + (event.`3 `&` mask), state.`4 + W64.to_uint event.`4).

op gauss_trace_initial (values : BArray4096.t) (squares : BArray16.t) :
    gauss_trace_state =
  (values, BArray16.get64 squares 0, BArray16.get64 squares 1, 0).

op gauss_trace_prefix (buf : BArray8192.t) (requested : int) (dont : bool)
    (values : BArray4096.t) (squares : BArray16.t) (attempts : int) :
    gauss_trace_state =
  foldl (gauss_trace_step requested dont) (gauss_trace_initial values squares)
    (gauss_events buf attempts).

op gauss_normalize (lo hi : W64.t) : W64.t * W64.t =
  (lo `&` W64.of_int 281474976710655, hi + (lo `>>>` 48)).

op gauss_trace_result (buf : BArray8192.t) (requested available : int)
    (dont : bool) (values : BArray4096.t) (squares : BArray16.t)
    (count : BArray8.t) : BArray4096.t * BArray16.t * BArray8.t =
  let state = gauss_trace_prefix buf requested dont values squares (available %/ 26) in
  let normalized = gauss_normalize state.`2 state.`3 in
  (state.`1,
   BArray16.set64 (BArray16.set64 squares 0 normalized.`1) 1 normalized.`2,
   BArray8.set64 count 0 (W64.of_int state.`4)).

lemma gauss_events0 buf : gauss_events buf 0 = [].
proof. by rewrite /gauss_events iota0. qed.

lemma gauss_eventsS buf k : 0 <= k =>
  gauss_events buf (k + 1) = gauss_events buf k ++ [gauss_event_at buf k].
proof. by move=> hk; rewrite /gauss_events iotaSr 1:hk -cats1 map_cat. qed.

lemma gauss_trace_prefix0 buf n d values squares :
  gauss_trace_prefix buf n d values squares 0 = gauss_trace_initial values squares.
proof. by rewrite /gauss_trace_prefix gauss_events0. qed.

lemma gauss_trace_prefixS buf n d values squares k : 0 <= k =>
  gauss_trace_prefix buf n d values squares (k + 1) =
  gauss_trace_step n d (gauss_trace_prefix buf n d values squares k)
    (gauss_event_at buf k).
proof. by move=> hk; rewrite /gauss_trace_prefix gauss_eventsS 1:hk foldl_cat. qed.
