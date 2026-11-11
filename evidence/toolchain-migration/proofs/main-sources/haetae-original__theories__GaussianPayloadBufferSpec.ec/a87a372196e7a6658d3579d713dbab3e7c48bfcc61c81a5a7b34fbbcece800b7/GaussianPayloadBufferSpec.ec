require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianUniformBytes GaussianPayloadSpec.

type gpb_result = gib_result * int list.

(* The full array computation and its word-count guard are unchanged.
   The extra history records every accepted payload, including the dummy. *)
module GaussianPayloadBuffer = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gpb_result = {
    var count : BArray8.t;
    var bytes, pending : W8.t list;
    var accepted : int;
    var history : int list;
    count <- witness;
    history <- [];
    pending <$ gbc_bytes 6664;
    signsp <- gib_signs signsp sign_offset pending;
    pending <- drop 32 pending;
    (rp, sqsump, count) <- gib_consume rp sqsump count pending n (n = 257) sample_offset;
    history <- gpd_scan n history pending;
    accepted <- W64.to_uint (BArray8.get64 count 0);
    while (accepted < n) {
      pending <- gib_remainder pending;
      bytes <$ gib_block;
      pending <- pending ++ bytes;
      (rp, sqsump, count) <- gib_consume rp sqsump count pending (n - accepted)
        (n = 257) (sample_offset + accepted);
      history <- gpd_scan n history pending;
      accepted <- accepted + W64.to_uint (BArray8.get64 count 0);
    }
    return ((rp, signsp, sqsump), history);
  }
}.

(* This projection retains the identical finite byte draws and candidate
   boundaries. Its stopping count is obtained from the recorded history. *)
module GaussianPayloadHistory = {
  proc sample(n : int) : int list = {
    var bytes, pending : W8.t list;
    var history : int list;
    history <- [];
    pending <$ gbc_bytes 6664;
    pending <- drop 32 pending;
    history <- gpd_scan n history pending;
    while (size history < n) {
      pending <- gib_remainder pending;
      bytes <$ gib_block;
      pending <- pending ++ bytes;
      history <- gpd_scan n history pending;
    }
    return history;
  }
}.
