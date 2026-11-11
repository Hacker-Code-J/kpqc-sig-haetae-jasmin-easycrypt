require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import BArray32768 BArray8192 BArray512 BArray64 BArray16 BArray8 BArray1
  SHAKEStreamSpec GaussianStreamBuffer GaussianStreamSequence GaussianTraceSpec
  GaussianTraceProperties GaussianStreamAccumulator HyperballGaussianBounds
  HyperballFixedPointSpec HyperballNormSpec HyperballScaleSpec.
import HyperballScaleSpec.

(* A draw constrains every sample/sign entry subsequently read, and the exact
   square sum. Its unused scratch-array tails remain unspecified. *)
type hb_draw = BArray32768.t * BArray512.t * BArray16.t.

op hb_shape (l k : int) : bool =
  0 <= l <= 8 /\ 0 <= k <= 8 /\ 2 <= l + k <= 11.
op hb_request (i : int) : int = 256 + (if i < 2 then 1 else 0).
op hb_draw_count (i : int) : int = 256 * i + min i 2.
op hb_nonce (base : W64.t) (offset : int) : W64.t = base + W64.of_int offset.
op hb_stream (seed : BArray64.t) (nonce : W64.t) : int -> W8.t =
  SHAKEStreamSpec.shake_stream_byte (SHAKEStreamSpec.shake_initial_words seed nonce).
op hb_poly_events (seed : BArray64.t) (base : W64.t) (i blocks : int) : gauss_event list =
  gauss_selected_events (hb_request i)
    (gauss_stream_events (fun j => hb_stream seed (hb_nonce base i) (32 + j))
      (gs_stream_attempts blocks)).

op hb_batch_acc (seed : BArray64.t) (base : W64.t)
    (state : int * int) (blocks : int) : int * int =
  (state.`1 + 1, state.`2 + gauss_event_value_sum (hb_poly_events seed base state.`1 blocks)).
op hb_batch_fold (seed : BArray64.t) (base : W64.t) (blocks : int list) : int * int =
  foldl (hb_batch_acc seed base) (0, 0) blocks.
op hb_batch_sum (seed : BArray64.t) (base : W64.t) (blocks : int list) : int =
  (hb_batch_fold seed base blocks).`2.

op hb_batch_progress (seed : BArray64.t) (base : W64.t) (blocks : int list)
    (samples : BArray32768.t) (signs : BArray512.t) (squares : BArray16.t) : bool =
  0 <= size blocks <= 11 /\
  (forall i, 0 <= i < size blocks =>
    49 <= nth 0 blocks i /\
    size (hb_poly_events seed base i (nth 0 blocks i)) = hb_request i /\
    (forall j, 0 <= j < 256 =>
      BArray32768.get64 samples (256 * i + j) =
        nth W64.zero (map (fun (event : gauss_event) => event.`1)
          (hb_poly_events seed base i (nth 0 blocks i))) j) /\
    (forall j, 0 <= j < 32 =>
      BArray512.get8 signs (32 * i + j) = hb_stream seed (hb_nonce base i) j)) /\
  hb_cumulative_square_bound (hb_draw_count (size blocks)) squares /\
  gauss_stream_value squares = hb_batch_sum seed base blocks.

op hb_batch_complete (seed : BArray64.t) (base : W64.t) (m : int) (draw : hb_draw) : bool =
  exists blocks, size blocks = m /\ hb_batch_progress seed base blocks draw.`1 draw.`2 draw.`3.

op hb_draw_scale (draw : hb_draw) (cube three : hb_fp) (scale_const : W64.t) : BArray16.t =
  hb_pack (hb_scale_factor (hb_load draw.`3) cube three scale_const).
op hb_attempt_outputs (initial1 initial2 : BArray8192.t) (draw : hb_draw)
    (l k : int) (cube three : hb_fp) (scale_const : W64.t) : BArray8192.t * BArray8192.t =
  hb_scale_result initial1 initial2 draw.`1 draw.`2
    (hb_draw_scale draw cube three scale_const) (256 * l) (256 * (l + k)).
op hb_attempt_accept (initial1 initial2 : BArray8192.t) (draw : hb_draw)
    (l k : int) (cube three : hb_fp) (scale_const bound : W64.t) : bool =
  let result = hb_attempt_outputs initial1 initial2 draw l k cube three scale_const in
  hyperball_sqnorm result.`1 (256 * l) result.`2 (256 * k) %% W64.modulus <= W64.to_uint bound.

(* Every completed attempt is retained: all but the last reject, and the
   last status exactly determines the live accepted flag and output arrays. *)
op hb_history (seed : BArray64.t) (base : W64.t) (l k : int)
    (cube three : hb_fp) (scale_const bound : W64.t)
    (initial1 initial2 : BArray8192.t) (history : hb_draw list)
    (current1 current2 : BArray8192.t) (accepted : W64.t) : bool =
  (forall j, 0 <= j < size history =>
    hb_batch_complete seed (hb_nonce base ((l + k) * j)) (l + k) (nth witness history j)) /\
  (forall j, 0 <= j < size history - 1 =>
    !hb_attempt_accept initial1 initial2 (nth witness history j) l k cube three scale_const bound) /\
  (if history = [] then current1 = initial1 /\ current2 = initial2 /\ accepted = W64.zero
   else
     (current1, current2) = hb_attempt_outputs initial1 initial2 (last witness history)
       l k cube three scale_const /\
     accepted = W64.of_int (b2i (hb_attempt_accept initial1 initial2 (last witness history)
       l k cube three scale_const bound))).

op hb_result (seed : BArray64.t) (base : W64.t) (l k : int)
    (cube three : hb_fp) (scale_const bound : W64.t)
    (initial1 initial2 current1 current2 : BArray8192.t)
    (byte_result : BArray1.t) (counter_result : BArray8.t) : bool =
  exists history,
    0 < size history /\
    hb_history seed base l k cube three scale_const bound initial1 initial2 history
      current1 current2 W64.one /\
    BArray1.get8 byte_result 0 = hb_stream seed (hb_nonce base ((l + k) * size history)) 0 /\
    BArray8.get64 counter_result 0 = hb_nonce base ((l + k) * size history).
