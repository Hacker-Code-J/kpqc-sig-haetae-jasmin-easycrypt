require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import BArray4096.

op gauss_requested (counts : W64.t) : int =
  W64.to_uint (counts `&` W64.of_int 4294967295).

op gauss_available (counts : W64.t) : int =
  W64.to_uint (counts `>>>` 32).

(* Rejected attempts may leave a speculative candidate at the next output
   slot. The promised frame therefore starts at the requested output limit,
   rather than at the number of accepted coefficients returned. *)
op gauss_output_frame (before after : BArray4096.t) (limit : int) : bool =
  forall j, limit <= j < 512 =>
    BArray4096.get64 after j = BArray4096.get64 before j.
