require import AllCore IntDiv List Ring StdOrder Real.

require import BArray1024 BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTScheduleBridge
  KeygenM23SingularFFTGlobalTrace
  KeygenMode2ParentTarget.

import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTScheduleBridge
  KeygenM23SingularFFTGlobalTrace.

theory KeygenM23SingularFFTErrorTrace.

(* This theory fixes the intended schedule-wide coordinatewise error budget.
   The missing proof obligation is still the stage-local closeness lift that
   would establish [actual_fft_schedule_trace data xp fft_trace_eps]. *)

op fft_trace_eps_num (round : int) : int =
     if round = 0 then 1
else if round = 1 then 6
else if round = 2 then 25
else if round = 3 then 94
else if round = 4 then 337
else if round = 5 then 1174
else if round = 6 then 4009
else if round = 7 then 13486
else if round = 8 then 44833
else 0.

op fft_trace_eps (round : int) : real =
  (fft_trace_eps_num round)%r / 65536%r.

op actual_fft_schedule_explicit_trace
    (data : BArray2048.t) (xp : BArray1024.t) : bool =
  actual_fft_schedule_trace data xp fft_trace_eps.

lemma fft_trace_eps0 :
  fft_trace_eps 0 = 1%r / 65536%r.
proof. by rewrite /fft_trace_eps /fft_trace_eps_num. qed.

lemma fft_trace_eps8 :
  fft_trace_eps 8 = 44833%r / 65536%r.
proof. by rewrite /fft_trace_eps /fft_trace_eps_num. qed.

lemma fft_trace_eps_num_step (round : int) :
  0 <= round < 8 =>
  fft_trace_eps_num (round + 1) =
    3 * fft_trace_eps_num round + 2 * 3 ^ round + 1.
proof.
move=> hround.
have hcases :
     round = 0 \/ round = 1 \/ round = 2 \/ round = 3
  \/ round = 4 \/ round = 5 \/ round = 6 \/ round = 7 by smt().
elim hcases => [->|hcases]; first by rewrite /fft_trace_eps_num /=.
elim hcases => [->|hcases]; first by rewrite /fft_trace_eps_num /=.
elim hcases => [->|hcases]; first by rewrite /fft_trace_eps_num /=.
elim hcases => [->|hcases]; first by rewrite /fft_trace_eps_num /=.
elim hcases => [->|hcases]; first by rewrite /fft_trace_eps_num /=.
elim hcases => [->|hcases]; first by rewrite /fft_trace_eps_num /=.
elim hcases => [->|->]; by rewrite /fft_trace_eps_num /=.
qed.

lemma fft_trace_eps_step (round : int) :
  0 <= round < 8 =>
  fft_trace_eps (round + 1) =
    3%r * fft_trace_eps round +
    ((2 * 3 ^ round + 1)%r / 65536%r).
proof.
move=> hround.
rewrite /fft_trace_eps (fft_trace_eps_num_step round hround).
rewrite !fromintD !fromintM.
field.
trivial.
qed.

lemma actual_fft_schedule_prefix0_close_explicit_bound2
    (data : BArray2048.t) (xp : BArray1024.t) (j : int) :
  0 <= j < 256 =>
  fft_coefficient_bound xp 2 =>
  cclose (fft_trace_eps 0)
    (fft_schedule_prefix_decode_at
      (actual_fft_init_data data xp)
      KeygenMode2ParentTarget.jfft_roots
      0 j)
    (ideal_schedule_prefix (actual_fft_ideal_input xp) 0 j).
proof.
move=> hj hcoeff.
rewrite fft_trace_eps0.
exact (actual_fft_schedule_prefix0_close_bound2 data xp j hj hcoeff).
qed.

lemma actual_fft_full_odd_dft256_close_from_explicit_trace
    (data : BArray2048.t) (xp : BArray1024.t) (j : int) :
  0 <= j < 256 =>
  actual_fft_schedule_safe data xp =>
  actual_fft_schedule_explicit_trace data xp =>
  cclose (44833%r / 65536%r)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_full
        (actual_fft_init_data data xp)
        KeygenMode2ParentTarget.jfft_roots)
      j)
    (odd_dft256 (fft_coefficient_vector xp) j).
proof.
move=> hj hsafe htrace.
have hclose :=
  actual_fft_full_odd_dft256_close_from_trace
    data xp fft_trace_eps j hj hsafe htrace.
rewrite fft_trace_eps8 in hclose.
exact hclose.
qed.

lemma actual_fft_full_odd_dft256_close_from_bound2_explicit_trace
    (data : BArray2048.t) (xp : BArray1024.t) (j : int) :
  0 <= j < 256 =>
  fft_coefficient_bound xp 2 =>
  actual_fft_schedule_explicit_trace data xp =>
  cclose (44833%r / 65536%r)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_full
        (actual_fft_init_data data xp)
        KeygenMode2ParentTarget.jfft_roots)
      j)
    (odd_dft256 (fft_coefficient_vector xp) j).
proof.
move=> hj hcoeff htrace.
have hclose :=
  actual_fft_full_odd_dft256_close_from_bound2_trace
    data xp fft_trace_eps j hj hcoeff htrace.
rewrite fft_trace_eps8 in hclose.
exact hclose.
qed.

end KeygenM23SingularFFTErrorTrace.
