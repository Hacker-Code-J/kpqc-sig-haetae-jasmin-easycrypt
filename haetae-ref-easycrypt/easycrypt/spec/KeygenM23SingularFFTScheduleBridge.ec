require import AllCore IntDiv List Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTStageBridge.

import KeygenM23ComplexReal.
import KeygenM23SingularFFTInitBridge.
import KeygenM23SingularFFTStageBridge.

theory KeygenM23SingularFFTScheduleBridge.

(* Prefix state [round] is the state immediately before stage [round + 1]. *)
op fft_schedule_params_at
    (round : int) (m md2 stride : W64.t) : bool =
     (round = 0 /\ m = W64.of_int 2 /\
      md2 = W64.of_int 1 /\ stride = W64.of_int 256)
  \/ (round = 1 /\ m = W64.of_int 4 /\
      md2 = W64.of_int 2 /\ stride = W64.of_int 128)
  \/ (round = 2 /\ m = W64.of_int 8 /\
      md2 = W64.of_int 4 /\ stride = W64.of_int 64)
  \/ (round = 3 /\ m = W64.of_int 16 /\
      md2 = W64.of_int 8 /\ stride = W64.of_int 32)
  \/ (round = 4 /\ m = W64.of_int 32 /\
      md2 = W64.of_int 16 /\ stride = W64.of_int 16)
  \/ (round = 5 /\ m = W64.of_int 64 /\
      md2 = W64.of_int 32 /\ stride = W64.of_int 8)
  \/ (round = 6 /\ m = W64.of_int 128 /\
      md2 = W64.of_int 64 /\ stride = W64.of_int 4)
  \/ (round = 7 /\ m = W64.of_int 256 /\
      md2 = W64.of_int 128 /\ stride = W64.of_int 2)
  \/ (round = 8 /\ m = W64.of_int 512 /\
      md2 = W64.of_int 256 /\ stride = W64.of_int 1).

op fft_schedule_prefix_safe
    (data roots : BArray2048.t) (processed : int) : bool =
  forall round, 0 <= round < processed =>
    let st =
      KeygenM23SingularFFTSpec.fft_schedule_prefix data roots round in
    fft_stage_safe st.`1 roots st.`2 st.`3 st.`4.

type fft_schedule_decode_state =
  KeygenM23SingularFFTSpec.fft_schedule_state * complex.

op fft_schedule_decode_step
    (roots : BArray2048.t) (j : int)
    (st : fft_schedule_decode_state) (round : int)
    : fft_schedule_decode_state =
  let machine = st.`1 in
  (KeygenM23SingularFFTSpec.fft_round_step roots machine round,
   fft_stage_decode_at
     machine.`1 roots machine.`2 machine.`3 machine.`4 j).

op fft_schedule_decode_prefix
    (data roots : BArray2048.t) (processed j : int)
    : fft_schedule_decode_state =
  foldl (fft_schedule_decode_step roots j)
    ((data, W64.of_int 2, W64.of_int 1, W64.of_int 256),
     fft_decode_at data j)
    (iota_ 0 processed).

op fft_schedule_prefix_decode_at
    (data roots : BArray2048.t) (processed j : int) : complex =
  (fft_schedule_decode_prefix data roots processed j).`2.

op fft_schedule_safe (data roots : BArray2048.t) : bool =
  fft_schedule_prefix_safe
    data roots KeygenM23SingularFFTSpec.fft_stages_i.

op fft_full_decode_at
    (data roots : BArray2048.t) (j : int) : complex =
  fft_schedule_prefix_decode_at
    data roots KeygenM23SingularFFTSpec.fft_stages_i j.

lemma fft_schedule_params_at0 :
  fft_schedule_params_at 0
    (W64.of_int 2) (W64.of_int 1) (W64.of_int 256).
proof. by rewrite /fft_schedule_params_at; auto. qed.

lemma fft_schedule_params_step
    (round : int) (m md2 stride : W64.t) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_schedule_params_at (round + 1)
    (m `<<` W8.of_int 1)
    (md2 `<<` W8.of_int 1)
    (stride `>>` W8.of_int 1).
proof.
rewrite /fft_schedule_params_at.
move=> hround hstate.
case: hstate => [hs0|hrest0].
+ move: hs0 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify; auto.
case: hrest0 => [hs1|hrest1].
+ move: hs1 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify; auto.
case: hrest1 => [hs2|hrest2].
+ move: hs2 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify; auto.
case: hrest2 => [hs3|hrest3].
+ move: hs3 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify; auto.
case: hrest3 => [hs4|hrest4].
+ move: hs4 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify; auto.
case: hrest4 => [hs5|hrest5].
+ move: hs5 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify; auto.
case: hrest5 => [hs6|hrest6].
+ move: hs6 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify; auto.
case: hrest6 => [hs7|hs8].
+ move: hs7 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify; auto.
by move: hs8 hround => />.
qed.

lemma fft_schedule_params_reachable
    (round : int) (m md2 stride : W64.t) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_stage_reachable_params m md2 stride.
proof.
rewrite /fft_schedule_params_at /fft_stage_reachable_params.
move=> hround hstate.
case: hstate => [hs0|hrest0].
+ move: hs0 => />.
case: hrest0 => [hs1|hrest1].
+ move: hs1 => />.
case: hrest1 => [hs2|hrest2].
+ move: hs2 => />.
case: hrest2 => [hs3|hrest3].
+ move: hs3 => />.
case: hrest3 => [hs4|hrest4].
+ move: hs4 => />.
case: hrest4 => [hs5|hrest5].
+ move: hs5 => />.
case: hrest5 => [hs6|hrest6].
+ move: hs6 => />.
case: hrest6 => [hs7|hs8].
+ move: hs7 => />.
by move: hs8 hround => />.
qed.

lemma fft_schedule_prefix_params
    (data roots : BArray2048.t) (processed : int) :
  0 <= processed <= 8 =>
  let st =
    KeygenM23SingularFFTSpec.fft_schedule_prefix data roots processed in
  fft_schedule_params_at processed st.`2 st.`3 st.`4.
proof.
move=> [hprocessed0 hprocessed8].
have hgeneral :
  forall p, 0 <= p => p <= 8 =>
    let st =
      KeygenM23SingularFFTSpec.fft_schedule_prefix data roots p in
    fft_schedule_params_at p st.`2 st.`3 st.`4.
+ apply intind.
  + move=> _.
    rewrite KeygenM23SingularFFTSpec.fft_schedule_prefix0 /=.
    exact fft_schedule_params_at0.
  + move=> p hp0 ih hp8.
    rewrite KeygenM23SingularFFTSpec.fft_schedule_prefixS 1:hp0.
    rewrite /KeygenM23SingularFFTSpec.fft_round_step /=.
    apply fft_schedule_params_step.
    + smt().
    apply ih.
    smt().
exact (hgeneral processed hprocessed0 hprocessed8).
qed.

lemma fft_schedule_prefix_reachable
    (data roots : BArray2048.t) (round : int) :
  0 <= round < 8 =>
  let st =
    KeygenM23SingularFFTSpec.fft_schedule_prefix data roots round in
  fft_stage_reachable_params st.`2 st.`3 st.`4.
proof.
move=> hround.
have hparams :=
  fft_schedule_prefix_params data roots round _.
+ smt().
exact
  (fft_schedule_params_reachable
    round
    (KeygenM23SingularFFTSpec.fft_schedule_prefix data roots round).`2
    (KeygenM23SingularFFTSpec.fft_schedule_prefix data roots round).`3
    (KeygenM23SingularFFTSpec.fft_schedule_prefix data roots round).`4
    hround hparams).
qed.

lemma fft_schedule_prefix_safe_prev
    (data roots : BArray2048.t) (processed : int) :
  0 <= processed =>
  fft_schedule_prefix_safe data roots (processed + 1) =>
  fft_schedule_prefix_safe data roots processed.
proof.
move=> hprocessed hsafe.
rewrite /fft_schedule_prefix_safe.
move=> round [hround0 hroundlt].
move: hsafe; rewrite /fft_schedule_prefix_safe.
move=> h.
have hroundS : 0 <= round < processed + 1.
+ split.
  + exact hround0.
  smt().
exact (h round hroundS).
qed.

lemma fft_schedule_prefix_safe_here
    (data roots : BArray2048.t) (processed : int) :
  0 <= processed =>
  fft_schedule_prefix_safe data roots (processed + 1) =>
  let st =
    KeygenM23SingularFFTSpec.fft_schedule_prefix data roots processed in
  fft_stage_safe st.`1 roots st.`2 st.`3 st.`4.
proof.
move=> hprocessed hsafe.
move: hsafe; rewrite /fft_schedule_prefix_safe.
move=> h.
have hprocessedS : 0 <= processed < processed + 1.
+ split.
  + exact hprocessed.
  smt().
exact (h processed hprocessedS).
qed.

lemma fft_schedule_decode_prefix0
    (data roots : BArray2048.t) (j : int) :
  fft_schedule_decode_prefix data roots 0 j =
    ((data, W64.of_int 2, W64.of_int 1, W64.of_int 256),
     fft_decode_at data j).
proof. by rewrite /fft_schedule_decode_prefix iota0. qed.

lemma fft_schedule_decode_prefixS
    (data roots : BArray2048.t) (processed j : int) :
  0 <= processed =>
  fft_schedule_decode_prefix data roots (processed + 1) j =
    fft_schedule_decode_step roots j
      (fft_schedule_decode_prefix data roots processed j) processed.
proof.
move=> hprocessed.
by rewrite /fft_schedule_decode_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma fft_schedule_decode_prefix_machine
    (data roots : BArray2048.t) (processed j : int) :
  0 <= processed =>
  (fft_schedule_decode_prefix data roots processed j).`1 =
  KeygenM23SingularFFTSpec.fft_schedule_prefix data roots processed.
proof.
move=> hprocessed.
elim/intind: processed hprocessed => [|p hp0 ih].
+ by rewrite fft_schedule_decode_prefix0
             KeygenM23SingularFFTSpec.fft_schedule_prefix0.
rewrite fft_schedule_decode_prefixS 1:hp0.
rewrite KeygenM23SingularFFTSpec.fft_schedule_prefixS 1:hp0.
by rewrite /fft_schedule_decode_step /= ih.
qed.

lemma fft_schedule_decode_prefix
    (data roots : BArray2048.t) (processed j : int) :
  0 <= processed <= 8 =>
  0 <= j < 256 =>
  fft_schedule_prefix_safe data roots processed =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_schedule_prefix
      data roots processed).`1 j =
  fft_schedule_prefix_decode_at data roots processed j.
proof.
move=> [hprocessed0 hprocessed8] hj hsafe.
have hgeneral :
  forall p, 0 <= p => p <= 8 =>
    fft_schedule_prefix_safe data roots p =>
    fft_decode_at
      (KeygenM23SingularFFTSpec.fft_schedule_prefix data roots p).`1 j =
    fft_schedule_prefix_decode_at data roots p j.
+ apply intind.
  + move=> _ _.
    by rewrite KeygenM23SingularFFTSpec.fft_schedule_prefix0
               /fft_schedule_prefix_decode_at
               fft_schedule_decode_prefix0.
  + move=> p hp0 ih hp8 hsafeS.
    have hp_lt8 : p < 8 by smt().
    have hreach := fft_schedule_prefix_reachable data roots p _.
    + smt().
    have hsafe_here :=
      fft_schedule_prefix_safe_here data roots p hp0 hsafeS.
    have hmachine :=
      fft_schedule_decode_prefix_machine data roots p j hp0.
    rewrite KeygenM23SingularFFTSpec.fft_schedule_prefixS 1:hp0.
    rewrite /KeygenM23SingularFFTSpec.fft_round_step /=.
    rewrite /fft_schedule_prefix_decode_at
            fft_schedule_decode_prefixS 1:hp0.
    rewrite /fft_schedule_decode_step /= hmachine.
    exact
      (fft_stage_decode_reachable
        (KeygenM23SingularFFTSpec.fft_schedule_prefix data roots p).`1
        roots
        (KeygenM23SingularFFTSpec.fft_schedule_prefix data roots p).`2
        (KeygenM23SingularFFTSpec.fft_schedule_prefix data roots p).`3
        (KeygenM23SingularFFTSpec.fft_schedule_prefix data roots p).`4
        j hreach hj hsafe_here).
exact (hgeneral processed hprocessed0 hprocessed8 hsafe).
qed.

lemma fft_full_decode
    (data roots : BArray2048.t) (j : int) :
  0 <= j < 256 =>
  fft_schedule_safe data roots =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_full data roots) j =
  fft_full_decode_at data roots j.
proof.
move=> hj hsafe.
rewrite /KeygenM23SingularFFTSpec.fft_full
        /fft_full_decode_at /fft_schedule_safe
        /KeygenM23SingularFFTSpec.fft_stages_i.
exact (fft_schedule_decode_prefix data roots 8 j _ hj hsafe).
qed.

end KeygenM23SingularFFTScheduleBridge.
