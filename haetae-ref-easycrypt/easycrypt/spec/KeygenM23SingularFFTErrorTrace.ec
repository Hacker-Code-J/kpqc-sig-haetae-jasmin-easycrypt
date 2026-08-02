require import AllCore IntDiv List Ring StdOrder Real.

require import BArray1024 BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTScheduleBridge
  KeygenM23SingularFFTScheduleBounds
  KeygenM23SingularFFTStageBridge
  KeygenM23SingularFFTStageErrorBridge
  KeygenM23SingularFFTGlobalTrace
  KeygenMode2ParentTarget.

import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTScheduleBridge
  KeygenM23SingularFFTScheduleBounds
  KeygenM23SingularFFTStageBridge
  KeygenM23SingularFFTStageErrorBridge
  KeygenM23SingularFFTGlobalTrace.

theory KeygenM23SingularFFTErrorTrace.

(* The explicit budget records the initializer error and the eight rounded
   butterfly stages.  The stage bridge below discharges the recurrence at
   every coordinate of every reachable schedule prefix. *)

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

lemma actual_fft_schedule_explicit_trace_bound2
    (data : BArray2048.t) (xp : BArray1024.t) :
  fft_coefficient_bound xp 2 =>
  actual_fft_schedule_explicit_trace data xp.
proof.
move=> hcoeff.
rewrite /actual_fft_schedule_explicit_trace /actual_fft_schedule_trace.
have hgeneral :
  forall round, 0 <= round => round <= 8 =>
    forall j, 0 <= j < 256 =>
    cclose (fft_trace_eps round)
      (fft_schedule_prefix_decode_at
        (actual_fft_init_data data xp)
        KeygenMode2ParentTarget.jfft_roots
        round j)
      (ideal_schedule_prefix
        (actual_fft_ideal_input xp) round j).
+ apply intind.
  + move=> _ j hj.
    exact
      (actual_fft_schedule_prefix0_close_explicit_bound2
        data xp j hj hcoeff).
  + move=> round hround0 ih hroundS8 j hj.
    have hround : 0 <= round < 8 by smt().
    pose init := actual_fft_init_data data xp.
    pose st :=
      KeygenM23SingularFFTSpec.fft_schedule_prefix
        init KeygenMode2ParentTarget.jfft_roots round.
    have hround_le : 0 <= round <= 8 by smt().
    have hparams :
      fft_schedule_params_at round st.`2 st.`3 st.`4.
    + rewrite /st /init.
      exact
        (fft_schedule_prefix_params
          (actual_fft_init_data data xp)
          KeygenMode2ParentTarget.jfft_roots round hround_le).
    have hreach : fft_stage_reachable_params st.`2 st.`3 st.`4.
    + exact
        (fft_schedule_params_reachable
          round st.`2 st.`3 st.`4 hround hparams).
    have hstage :=
      fft_stage_reachable_schedule st.`2 st.`3 st.`4 hreach.
    have hbounds_here :=
      actual_fft_schedule_prefix_safe_bound2
        data xp round hround_le hcoeff.
    rewrite /actual_fft_init_data_bound2 /actual_fft_init_data in hbounds_here.
    have hword : fft_word_bound st.`1 (fft_round_word_bound round).
    + move: hbounds_here => [_ hword].
      rewrite /st /init.
      exact hword.
    have hroundS_le : 0 <= round + 1 <= 8 by smt().
    have hbounds_next :=
      actual_fft_schedule_prefix_safe_bound2
        data xp (round + 1) hroundS_le hcoeff.
    rewrite /actual_fft_init_data_bound2 /actual_fft_init_data in hbounds_next.
    have hsafe_prefixS :
      fft_schedule_prefix_safe
        init KeygenMode2ParentTarget.jfft_roots (round + 1).
    + move: hbounds_next => [hsafe _].
      rewrite /init.
      exact hsafe.
    have hsafe :
      fft_stage_safe st.`1 KeygenMode2ParentTarget.jfft_roots
        st.`2 st.`3 st.`4.
    + rewrite /st.
      exact
        (fft_schedule_prefix_safe_here
          init KeygenMode2ParentTarget.jfft_roots
          round hround0 hsafe_prefixS).
    have hclose :
      forall i, 0 <= i < 256 =>
      cclose (fft_trace_eps round)
        (fft_decode_at st.`1 i)
        (ideal_schedule_prefix
          (actual_fft_ideal_input xp) round i).
    + move=> i hi.
      have hsafe_prev :=
        fft_schedule_prefix_safe_prev
          init KeygenMode2ParentTarget.jfft_roots
          round hround0 hsafe_prefixS.
      have hdecode :=
        fft_schedule_decode_prefix
          init KeygenMode2ParentTarget.jfft_roots
          round i hround_le hi hsafe_prev.
      have hround8 : round <= 8 by smt().
      have hclose_i := ih hround8 i hi.
      rewrite /st.
      rewrite hdecode.
      exact hclose_i.
    have hstage_close :=
      actual_fft_stage_close_at
        st.`1
        (ideal_schedule_prefix (actual_fft_ideal_input xp) round)
        round st.`2 st.`3 st.`4 j (fft_trace_eps round)
        hround hparams hstage hj hsafe hword hclose.
    rewrite -(fft_trace_eps_step round hround) in hstage_close.
    rewrite -(ideal_schedule_prefixS
      (actual_fft_ideal_input xp) round hround0) in hstage_close.
    rewrite /fft_schedule_prefix_decode_at
            fft_schedule_decode_prefixS 1:hround0
            /fft_schedule_decode_step /=.
    rewrite
      (fft_schedule_decode_prefix_machine
        init KeygenMode2ParentTarget.jfft_roots round j hround0).
    rewrite /st /init in hstage_close.
    exact hstage_close.
move=> round j [hround0 hround8] hj.
exact (hgeneral round hround0 hround8 j hj).
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

lemma actual_fft_full_odd_dft256_close_bound2
    (data : BArray2048.t) (xp : BArray1024.t) (j : int) :
  0 <= j < 256 =>
  fft_coefficient_bound xp 2 =>
  cclose (44833%r / 65536%r)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_full
        (actual_fft_init_data data xp)
        KeygenMode2ParentTarget.jfft_roots)
      j)
    (odd_dft256 (fft_coefficient_vector xp) j).
proof.
move=> hj hcoeff.
exact
  (actual_fft_full_odd_dft256_close_from_bound2_explicit_trace
    data xp j hj hcoeff
    (actual_fft_schedule_explicit_trace_bound2 data xp hcoeff)).
qed.

end KeygenM23SingularFFTErrorTrace.
