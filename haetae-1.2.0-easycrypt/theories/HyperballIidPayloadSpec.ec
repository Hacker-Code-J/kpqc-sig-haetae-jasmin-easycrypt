require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianPayloadSpec GaussianPayloadBufferSpec
  GaussianStreamAccumulator HyperballReferenceConstants.

op hip_mode (mode : int) : bool = mode=2 \/ mode=3 \/ mode=5.
op hip_polys (mode : int) : int = hb_ref_l mode+hb_ref_k mode.
op hip_requests (index : int) : int = if index<2 then 257 else 256.
op hip_prefix_count (index : int) : int = 256*index+min index 2.
op hip_count (mode : int) : int = 256*hip_polys mode.
op hip_total (mode : int) : int = hip_count mode+2.

op hip_samples0 : BArray32768.t = BArray32768.init (fun _ => W8.zero).
op hip_signs0 : BArray512.t = BArray512.init (fun _ => W8.zero).
op hip_squares0 : BArray16.t = BArray16.init (fun _ => W8.zero).
op hip_initial : gib_result = (hip_samples0,hip_signs0,hip_squares0).

(* Positions 256 and 513 are accepted dummy payloads. They contribute to
   the square sum, while the physical vector stores 256 values per call. *)
op hip_payload_index (index : int) : int =
  if index<256 then index else if index<512 then index+1 else index+2.
op hip_visible_payload (history : int list) : int list =
  take 256 history ++ take 256 (drop 257 history) ++ drop 514 history.
op hip_projection (history : int list) : int list * int =
  (map gpd_magnitude (hip_visible_payload history),gpd_sum history).
op hip_observe (mode : int) (state : gib_result) : int list * int =
  (map (fun i => W64.to_uint (BArray32768.get64 state.`1 i)) (iota_ 0 (hip_count mode)),
   gauss_stream_value state.`3).

(* One Gaussian batch of a Hyperball attempt, with explicit iid bytes.
   These are the actual buffered sign-copy/carry/consumer calls. *)
module HyperballIidGaussian = {
  proc sample(mode : int) : gib_result = {
    var state : gib_result;
    var index : int;
    state <- hip_initial;
    index <- 0;
    while (index<hip_polys mode) {
      state <@ GaussianIidBuffer.sample(state.`1,state.`2,state.`3,
        hip_requests index,256*index,32*index);
      index <- index+1;
    }
    return state;
  }
}.

(* The ghost retains the complete payload from every accepted candidate,
   including both dummies. The result keeps the original three arrays. *)
module HyperballIidPayload = {
  proc sample(mode : int) : gpb_result = {
    var state : gib_result;
    var step : gpb_result;
    var history : int list;
    var index : int;
    state <- hip_initial;
    history <- [];
    index <- 0;
    while (index<hip_polys mode) {
      step <@ GaussianPayloadBuffer.sample(state.`1,state.`2,state.`3,
        hip_requests index,256*index,32*index);
      state <- step.`1;
      history <- history++step.`2;
      index <- index+1;
    }
    return (state,history);
  }
}.
