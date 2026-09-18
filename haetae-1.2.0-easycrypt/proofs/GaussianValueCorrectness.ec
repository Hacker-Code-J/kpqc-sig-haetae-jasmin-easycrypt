require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import ApiTarget GaussianConsumerSpec GaussianWindowSpec GaussianTraceSpec
  GaussianOffsetBridge GaussianAccumulatorCorrectness.

(* The actual signing helper consumes the input window at bo. Its returned
   square buffer represents the exact sum of the selected truncated-square
   limbs; this is not an ideal real-square or whole-signature claim. *)
lemma sample_gauss_at_value_correct
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int)
    (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo /\
    W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 squares 1) < 281474976710656
    ==>
    gauss_limb_value (BArray16.get64 res.`2 0) (BArray16.get64 res.`2 1) =
      gauss_accumulator_integer_total (gauss_input_window buf bo) n (b %/ 26) squares /\
    gauss_big_output_frame initial res.`1 oo n].
proof.
  conseq (GaussianOffsetBridge.sample_gauss_at_trace_correct
    initial buf n b bo oo d squares count0) => //.
  move=> &m hpre result [htrace hframe].
  split; last exact hframe.
  have hs : result.`2 =
      (gauss_trace_result (gauss_input_window buf bo) n b (d <> W64.zero)
        (gauss_output_window initial oo) squares count0).`2 by smt().
  rewrite hs.
  apply (gauss_trace_result_canonical_both_exact (gauss_input_window buf bo)
    n b (d <> W64.zero) (gauss_output_window initial oo) squares count0); smt().
qed.

lemma sample_gauss_at_value_total
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int)
    (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [GaussianOffsetBridge.Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo /\
    W64.to_uint (BArray16.get64 squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 squares 1) < 281474976710656
    ==>
    gauss_limb_value (BArray16.get64 res.`2 0) (BArray16.get64 res.`2 1) =
      gauss_accumulator_integer_total (gauss_input_window buf bo) n (b %/ 26) squares /\
    gauss_big_output_frame initial res.`1 oo n] = 1%r.
proof.
  by conseq (GaussianOffsetBridge.sample_gauss_at_total_frame initial buf n b bo oo)
    (sample_gauss_at_value_correct initial buf n b bo oo d squares count0) => />.
qed.
