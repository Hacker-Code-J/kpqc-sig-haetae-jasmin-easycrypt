require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import GaussianStreamSpec GaussianStreamComposition GaussianOffsetBridge
  GaussianConsumerSpec GaussianStreamBuffer.

lemma gr_consumer_lossless
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int) :
  phoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo /\
    bufp = buf /\ rp = initial ==> true] = 1%r.
proof.
  conseq (_ : _ ==> _ : >= 1%r) => //.
  conseq (_ : _ ==> GaussianWindowSpec.gauss_big_output_frame initial res.`1 oo n : >= 1%r) => //.
  by conseq (GaussianOffsetBridge.sample_gauss_at_total_frame initial buf n b bo oo) => />.
qed.

(* The bounded actual consumer preserves the continuous-stream invariant
   and terminates. Its square accumulator may already include earlier calls. *)
lemma gs_progress_consume_total (f : int -> W8.t)
    (initial current : BArray32768.t) (initial_squares squares : BArray16.t)
    (n oo attempts accepted : int) (buf : BArray8192.t)
    (available bo : int) (count0 : BArray8.t) :
  phoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = current /\ sqsump = squares /\ coefcntp = count0 /\ bufp = buf /\
    gauss_requested counts = n - accepted /\ gauss_available counts = available /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo + accepted /\
    dont_write_last = W64.of_int (n - 256) /\
    gs_progress f initial current initial_squares squares n oo attempts accepted /\
    accepted < n /\ 0 <= oo /\ oo + n <= 4096 /\
    0 <= available /\ 0 <= bo /\ bo + available <= 8192 /\
    gs_buffer_segment f buf bo (26 * attempts) available
    ==>
    gs_progress f initial res.`1 initial_squares res.`2 n oo
      (attempts + available %/ 26)
      (accepted + W64.to_uint (BArray8.get64 res.`3 0))] = 1%r.
proof.
  conseq (gr_consumer_lossless
    current buf (n - accepted) available bo (oo + accepted))
    (GaussianStreamComposition.gs_progress_consume_correct
      f initial current initial_squares squares n oo attempts accepted buf available bo count0) => //.
  move=> &m hpre.
  have hp : gs_progress f initial current initial_squares squares n oo attempts accepted by smt().
  have [hn [ha [hc hrest]]] := hp.
  smt().
qed.

(* Capture the input arrays at the call boundary, so callers need only
   instantiate the logical stream position and bounds in a pHoare proof. *)
lemma gs_progress_consume_total_dynamic (f : int -> W8.t)
    (initial : BArray32768.t) (initial_squares : BArray16.t)
    (n oo attempts accepted available bo : int) :
  phoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    gauss_requested counts = n - accepted /\ gauss_available counts = available /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo + accepted /\
    dont_write_last = W64.of_int (n - 256) /\
    gs_progress f initial rp initial_squares sqsump n oo attempts accepted /\
    accepted < n /\ 0 <= oo /\ oo + n <= 4096 /\
    0 <= available /\ 0 <= bo /\ bo + available <= 8192 /\
    gs_buffer_segment f bufp bo (26 * attempts) available
    ==>
    gs_progress f initial res.`1 initial_squares res.`2 n oo
      (attempts + available %/ 26)
      (accepted + W64.to_uint (BArray8.get64 res.`3 0))] = 1%r.
proof.
  exists* rp, sqsump, bufp, coefcntp; elim* => current squares buf count0.
  by conseq (gs_progress_consume_total f initial current initial_squares squares
    n oo attempts accepted buf available bo count0) => />.
qed.
