require import AllCore IntDiv List Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray1024 BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTScheduleBridge
  KeygenM23SingularFFTScheduleBounds
  KeygenMode2ParentTarget.

import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTScheduleBridge
  KeygenM23SingularFFTScheduleBounds.

theory KeygenM23SingularFFTGlobalTrace.

(* This file packages the decoded initializer, discharged schedule safety,
   and schedule observer into the shape needed by the remaining error proof:
   a round-0 base fact and a final reduction from a schedule-wide close
   invariant to the target odd DFT endpoint. *)

op actual_fft_init_data
    (data : BArray2048.t) (xp : BArray1024.t) : BArray2048.t =
  KeygenM23SingularFFTSpec.fft_init_and_bitrev
    data xp
    KeygenMode2ParentTarget.jfft_roots
    KeygenMode2ParentTarget.jfft_brv8.

op actual_fft_ideal_input (xp : BArray1024.t) : cvector =
  twist256 (fft_coefficient_vector xp).

op actual_fft_schedule_safe
    (data : BArray2048.t) (xp : BArray1024.t) : bool =
  fft_schedule_safe
    (actual_fft_init_data data xp)
    KeygenMode2ParentTarget.jfft_roots.

op actual_fft_schedule_trace
    (data : BArray2048.t) (xp : BArray1024.t) (eps : int -> real) : bool =
  forall round j,
    0 <= round <= 8 =>
    0 <= j < 256 =>
    cclose (eps round)
      (fft_schedule_prefix_decode_at
        (actual_fft_init_data data xp)
        KeygenMode2ParentTarget.jfft_roots
        round j)
      (ideal_schedule_prefix (actual_fft_ideal_input xp) round j).

lemma actual_fft_schedule_prefix0_close_bound2
    (data : BArray2048.t) (xp : BArray1024.t) (j : int) :
  0 <= j < 256 =>
  fft_coefficient_bound xp 2 =>
  cclose (1%r / 65536%r)
    (fft_schedule_prefix_decode_at
      (actual_fft_init_data data xp)
      KeygenMode2ParentTarget.jfft_roots
      0 j)
    (ideal_schedule_prefix (actual_fft_ideal_input xp) 0 j).
proof.
move=> hj hbound.
rewrite /fft_schedule_prefix_decode_at
        fft_schedule_decode_prefix0
        /actual_fft_init_data /actual_fft_ideal_input
        ideal_schedule_prefix0 /=.
exact
  (actual_fft_init_and_bitrev_close_bound2
    data xp j hj hbound).
qed.

lemma actual_fft_schedule_prefix0_vector_close_bound2
    (data : BArray2048.t) (xp : BArray1024.t) :
  fft_coefficient_bound xp 2 =>
  fft_vector_close (1%r / 65536%r)
    (actual_fft_init_data data xp)
    (ideal_schedule_prefix (actual_fft_ideal_input xp) 0).
proof.
move=> hbound.
rewrite /actual_fft_init_data /actual_fft_ideal_input
        ideal_schedule_prefix0.
exact (actual_fft_init_and_bitrev_vector_close_bound2 data xp hbound).
qed.

lemma actual_fft_full_decode
    (data : BArray2048.t) (xp : BArray1024.t) (j : int) :
  0 <= j < 256 =>
  actual_fft_schedule_safe data xp =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_full
      (actual_fft_init_data data xp)
      KeygenMode2ParentTarget.jfft_roots)
    j =
  fft_full_decode_at
    (actual_fft_init_data data xp)
    KeygenMode2ParentTarget.jfft_roots j.
proof.
move=> hj hsafe.
exact
  (fft_full_decode
    (actual_fft_init_data data xp)
    KeygenMode2ParentTarget.jfft_roots
    j hj hsafe).
qed.

lemma actual_fft_schedule_safe_from_bound2
    (data : BArray2048.t) (xp : BArray1024.t) :
  fft_coefficient_bound xp 2 =>
  actual_fft_schedule_safe data xp.
proof.
move=> hbound.
rewrite /actual_fft_schedule_safe /actual_fft_init_data.
exact
  (KeygenM23SingularFFTScheduleBounds.actual_fft_schedule_safe_bound2
    data xp hbound).
qed.

lemma actual_fft_full_decode_bound2
    (data : BArray2048.t) (xp : BArray1024.t) (j : int) :
  0 <= j < 256 =>
  fft_coefficient_bound xp 2 =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_full
      (actual_fft_init_data data xp)
      KeygenMode2ParentTarget.jfft_roots)
    j =
  fft_full_decode_at
    (actual_fft_init_data data xp)
    KeygenMode2ParentTarget.jfft_roots j.
proof.
move=> hj hbound.
exact
  (actual_fft_full_decode
    data xp j hj
    (actual_fft_schedule_safe_from_bound2 data xp hbound)).
qed.

lemma actual_fft_full_close_from_trace
    (data : BArray2048.t) (xp : BArray1024.t)
    (eps : int -> real) (j : int) :
  0 <= j < 256 =>
  actual_fft_schedule_safe data xp =>
  actual_fft_schedule_trace data xp eps =>
  cclose (eps 8)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_full
        (actual_fft_init_data data xp)
        KeygenMode2ParentTarget.jfft_roots)
      j)
    (ideal_fft256 (actual_fft_ideal_input xp) j).
proof.
move=> hj hsafe htrace.
have hdecode := actual_fft_full_decode data xp j hj hsafe.
have htrace8 := htrace 8 j _ hj.
+ smt().
rewrite /actual_fft_schedule_trace in htrace8.
rewrite /ideal_fft256
        /fft_full_decode_at
        /KeygenM23SingularFFTSpec.fft_stages_i in htrace8.
rewrite hdecode.
exact htrace8.
qed.

lemma actual_fft_full_odd_dft256_close_from_trace
    (data : BArray2048.t) (xp : BArray1024.t)
    (eps : int -> real) (j : int) :
  0 <= j < 256 =>
  actual_fft_schedule_safe data xp =>
  actual_fft_schedule_trace data xp eps =>
  cclose (eps 8)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_full
        (actual_fft_init_data data xp)
        KeygenMode2ParentTarget.jfft_roots)
      j)
    (odd_dft256 (fft_coefficient_vector xp) j).
proof.
move=> hj hsafe htrace.
have hk : j \in range 0 256 by rewrite mem_range.
have hclose :=
  actual_fft_full_close_from_trace
    data xp eps j hj hsafe htrace.
rewrite /actual_fft_ideal_input
        (ideal_odd_fft256_correct
          (fft_coefficient_vector xp) j hk) in hclose.
exact hclose.
qed.

lemma actual_fft_full_odd_dft256_close_from_bound2_trace
    (data : BArray2048.t) (xp : BArray1024.t)
    (eps : int -> real) (j : int) :
  0 <= j < 256 =>
  fft_coefficient_bound xp 2 =>
  actual_fft_schedule_trace data xp eps =>
  cclose (eps 8)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_full
        (actual_fft_init_data data xp)
        KeygenMode2ParentTarget.jfft_roots)
      j)
    (odd_dft256 (fft_coefficient_vector xp) j).
proof.
move=> hj hbound htrace.
exact
  (actual_fft_full_odd_dft256_close_from_trace
    data xp eps j hj
    (actual_fft_schedule_safe_from_bound2 data xp hbound)
    htrace).
qed.

end KeygenM23SingularFFTGlobalTrace.
