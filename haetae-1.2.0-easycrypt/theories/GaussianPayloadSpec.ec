require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import SigmaCorrectness GaussianTraceSpec GaussianTraceProperties GaussianAccumulatorCorrectness
  GaussianUniformBytes GaussianBlockSampling GaussianRetryCore HyperballGaussianBounds.

(* Lossless proof-only encoding of rounded magnitude plus the two raw square
   limbs. The complete payload is retained even for an unstored dummy. *)
op gpd_base : int = 18446744073709551616.
op gpd_pack (event : gauss_event) : int =
  W64.to_uint event.`1 + gpd_base * gauss_limb_value event.`2 event.`3.
op gpd_magnitude (code : int) : int = code %% gpd_base.
op gpd_square (code : int) : int = code %/ gpd_base.
op gpd_record (code : int) : int * int = (gpd_magnitude code,gpd_square code).
op gpd_sum (codes : int list) : int = foldr (fun code total => gpd_square code+total) 0 codes.
op gpd_valid (code : int) : bool = 0 <= code /\ 0 <= gpd_square code <= hb_event_max.

op gpd_observer (candidate : BArray26.t) : int * bool =
  let event = sigma76_spec candidate in
  (gpd_pack event,gauss_event_accepted event).
op gpd_trial : (int * bool) distr = dmap gbc_candidate gpd_observer.
op gpd_accepted : int distr = gr_output gpd_trial.

op gpd_events (pending : W8.t list) : gauss_event list =
  gauss_events (BArray8192.of_list pending) (size pending %/ 26).
op gpd_selected (pending : W8.t list) (requested : int) : int list =
  map gpd_pack (gauss_selected_events requested (gpd_events pending)).
op gpd_scan (requested : int) (history : int list) (pending : W8.t list) : int list =
  gbs_scan requested history (map gpd_observer (gbc_chunks (size pending %/ 26) pending)).
op gpd_projection (initial_value : int) (history : int list) : int list * int =
  (map gpd_magnitude (take 256 history),initial_value+gpd_sum history).
