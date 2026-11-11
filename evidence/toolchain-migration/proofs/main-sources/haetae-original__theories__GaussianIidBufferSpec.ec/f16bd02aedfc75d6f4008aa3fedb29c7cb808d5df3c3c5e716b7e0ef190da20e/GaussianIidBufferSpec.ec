require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import ApiTarget GaussianTraceSpec GaussianTraceProperties GaussianWindowSpec.

type gib_result = BArray32768.t * BArray512.t * BArray16.t.

(* The source is an explicit distribution of independent bytes.  This
   operational model does not call SHAKE. *)
op gib_block : W8.t list distr = dlist W8.dword 136.

op gib_fill (before : BArray8192.t) (offset : int) (bytes : W8.t list) : BArray8192.t =
  BArray8192.init (fun j =>
    if offset <= j < offset + 136 then nth W8.zero bytes (j - offset)
    else BArray8192.get8 before j).

op gib_signs (before : BArray512.t) (offset : int) (bytes : W8.t list) : BArray512.t =
  BArray512.init (fun j =>
    if offset <= j < offset + 32 then nth W8.zero bytes (j - offset)
    else BArray512.get8 before j).

op gib_commit (before : BArray32768.t) (offset requested : int)
    (values : BArray4096.t) : BArray32768.t =
  BArray32768.init (fun j =>
    if 8 * offset <= j < 8 * (offset + requested) then
      BArray4096.get8 values (j - 8 * offset)
    else BArray32768.get8 before j).

op gib_counts (requested available : int) : W64.t =
  W64.of_int (available * 4294967296 + requested).

(* The full finite trace retains speculative writes and the unwritten
   dummy's square.  Only the caller's requested window is committed. *)
op [opaque] gib_consume (values : BArray32768.t) (squares : BArray16.t)
    (count : BArray8.t) (pending : W8.t list) (requested : int)
    (dummy : bool) (offset : int) : BArray32768.t * BArray16.t * BArray8.t =
  let result = gauss_trace_result (BArray8192.of_list pending) requested (size pending)
    dummy (gauss_output_window values offset) squares count in
  (gib_commit values offset requested result.`1, result.`2, result.`3).

op gib_remainder (pending : W8.t list) : W8.t list =
  drop (26 * (size pending %/ 26)) pending.

op gib_magnitudes (result : gib_result) (offset : int) : int list =
  map (fun j => W64.to_uint (BArray32768.get64 result.`1 (offset + j))) (iota_ 0 256).

op gib_visible (values : BArray32768.t) (offset accepted : int) : int list =
  map (fun j => W64.to_uint (BArray32768.get64 values (offset + j)))
    (iota_ 0 (min accepted 256)).

op gib_accepted (pending : W8.t list) : int list =
  map W64.to_uint (gauss_accepted_values
    (gauss_events (BArray8192.of_list pending) (size pending %/ 26))).

op gib_bounds (requested sample_offset sign_offset : int) : bool =
  (requested = 256 \/ requested = 257) /\
  0 <= sample_offset /\ sample_offset + requested <= 4096 /\
  0 <= sign_offset /\ sign_offset + 32 <= 512.

module GIBSigner = ApiTarget.M(ApiTarget.Syscall).

module GaussianIidBuffer = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var buf : BArray8192.t;
    var count : BArray8.t;
    var bytes : W8.t list;
    var block, available, remaining, accepted : int;
    var has_prefix : bool;
    buf <- witness;
    count <- witness;
    block <- 0;
    while (block < 49) {
      bytes <$ gib_block;
      buf <- gib_fill buf (136 * block) bytes;
      block <- block + 1;
    }
    signsp <@ GIBSigner.__sample_gauss_N_copy_signs_at
      (signsp, buf, W64.of_int 32, W64.of_int sign_offset);
    available <- 6632;
    has_prefix <- true;
    (rp, sqsump, count) <@ GIBSigner.__sample_gauss_at
      (rp, sqsump, count, buf, gib_counts n available, W64.of_int (n - 256),
       W64.of_int 32, W64.of_int sample_offset);
    accepted <- W64.to_uint (BArray8.get64 count 0);
    while (accepted < n) {
      remaining <- available %% 26;
      buf <@ GIBSigner._sample_gauss_N_carry
        (buf, W64.of_int available, W64.of_int 32, W64.of_int (b2i has_prefix),
         W64.of_int remaining);
      bytes <$ gib_block;
      buf <- gib_fill buf remaining bytes;
      available <- remaining + 136;
      (rp, sqsump, count) <@ GIBSigner.__sample_gauss_at
        (rp, sqsump, count, buf, gib_counts (n - accepted) available,
         W64.of_int (n - 256), W64.zero, W64.of_int (sample_offset + accepted));
      accepted <- accepted + W64.to_uint (BArray8.get64 count 0);
      has_prefix <- false;
    }
    return (rp, signsp, sqsump);
  }
}.

(* Same block draws, expressed as a pending byte list.  The next iteration
   retains exactly the unconsumed tail, including candidates spanning a
   136-byte boundary.  The stopping guard does not inspect that tail. *)
module GaussianIidBufferFunctional = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var count : BArray8.t;
    var bytes, pending : W8.t list;
    var block, accepted : int;
    count <- witness;
    pending <- [];
    block <- 0;
    while (block < 49) {
      bytes <$ gib_block;
      pending <- pending ++ bytes;
      block <- block + 1;
    }
    signsp <- gib_signs signsp sign_offset pending;
    pending <- drop 32 pending;
    (rp, sqsump, count) <- gib_consume rp sqsump count pending n (n = 257) sample_offset;
    accepted <- W64.to_uint (BArray8.get64 count 0);
    while (accepted < n) {
      pending <- gib_remainder pending;
      bytes <$ gib_block;
      pending <- pending ++ bytes;
      (rp, sqsump, count) <- gib_consume rp sqsump count pending (n - accepted)
        (n = 257) (sample_offset + accepted);
      accepted <- accepted + W64.to_uint (BArray8.get64 count 0);
    }
    return (rp, signsp, sqsump);
  }
}.
