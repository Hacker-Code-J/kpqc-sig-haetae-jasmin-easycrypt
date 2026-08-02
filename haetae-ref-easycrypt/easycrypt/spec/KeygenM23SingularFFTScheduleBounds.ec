require import AllCore IntDiv Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray1024 BArray2048.
require import
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTStageBridge
  KeygenM23SingularFFTStageBounds
  KeygenM23SingularFFTScheduleBridge
  KeygenMode2ParentTarget.

import KeygenM23SingularFFTBounds.
import KeygenM23SingularFFTInitBridge.
import KeygenM23SingularFFTStageBridge.
import KeygenM23SingularFFTScheduleBridge.
import KeygenM23SingularFFTStageBounds.

theory KeygenM23SingularFFTScheduleBounds.

op actual_fft_init_data_bound2
    (data : BArray2048.t) (xp : BArray1024.t) : BArray2048.t =
  KeygenM23SingularFFTSpec.fft_init_and_bitrev
    data xp
    KeygenMode2ParentTarget.jfft_roots
    KeygenMode2ParentTarget.jfft_brv8.

lemma fft_schedule_prefix_safe_bound
    (data roots : BArray2048.t) (processed : int) :
  0 <= processed <= 8 =>
  fft_word_bound data 131072 =>
  fft_root_word_bound roots =>
  fft_schedule_prefix_safe data roots processed /\
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_schedule_prefix
      data roots processed).`1
    (fft_round_word_bound processed).
proof.
move=> [hprocessed0 hprocessed8] hdata hroots.
have hgeneral :
  forall p, 0 <= p => p <= 8 =>
    fft_schedule_prefix_safe data roots p /\
    fft_word_bound
      (KeygenM23SingularFFTSpec.fft_schedule_prefix
        data roots p).`1
      (fft_round_word_bound p).
+ apply intind.
  + move=> _.
    split.
    + rewrite /fft_schedule_prefix_safe.
      move=> round hround.
      smt().
    rewrite KeygenM23SingularFFTSpec.fft_schedule_prefix0 /=.
    by rewrite fft_round_word_bound0.
  + move=> p hp0 ih hp8.
    have hp_lt8 : p < 8 by smt().
    have hp_exec : 0 <= p < 8 by smt().
    have [hsafeP hboundP] := ih _.
    + smt().
    pose st := KeygenM23SingularFFTSpec.fft_schedule_prefix data roots p.
    have hreach :
      fft_stage_reachable_params st.`2 st.`3 st.`4.
    + rewrite /st.
      exact
        (fft_schedule_prefix_reachable
          data roots p hp_exec).
    have hround_exec := fft_round_word_bound_exec p hp_exec.
    have hstage :=
      fft_stage_safe_bound_reachable
        st.`1 roots st.`2 st.`3 st.`4
        (fft_round_word_bound p)
        hreach hround_exec hboundP hroots.
    move: hstage => [hsafe_here hboundS].
    split.
    + rewrite /fft_schedule_prefix_safe.
      move=> round hround.
      case (round < p) => hlt.
      + have hroundP : 0 <= round < p by smt().
        exact (hsafeP round hroundP).
      have -> : round = p by smt().
      rewrite /st.
      exact hsafe_here.
    rewrite KeygenM23SingularFFTSpec.fft_schedule_prefixS 1:hp0.
    rewrite /KeygenM23SingularFFTSpec.fft_round_step /=.
    rewrite fft_round_word_boundS 1:hp0.
    rewrite /st.
    exact hboundS.
exact (hgeneral processed hprocessed0 hprocessed8).
qed.

lemma fft_schedule_safe_bound
    (data roots : BArray2048.t) :
  fft_word_bound data 131072 =>
  fft_root_word_bound roots =>
  fft_schedule_safe data roots /\
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_full data roots)
    (fft_round_word_bound 8).
proof.
move=> hdata hroots.
have [hsafe hbound] :=
  fft_schedule_prefix_safe_bound
    data roots 8 _ hdata hroots.
+ smt().
split.
+ exact hsafe.
rewrite /KeygenM23SingularFFTSpec.fft_full
        /KeygenM23SingularFFTSpec.fft_stages_i.
exact hbound.
qed.

lemma actual_fft_schedule_prefix_safe_bound2
    (data : BArray2048.t) (xp : BArray1024.t) (processed : int) :
  0 <= processed <= 8 =>
  fft_coefficient_bound xp 2 =>
  fft_schedule_prefix_safe
    (actual_fft_init_data_bound2 data xp)
    KeygenMode2ParentTarget.jfft_roots
    processed /\
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_schedule_prefix
      (actual_fft_init_data_bound2 data xp)
      KeygenMode2ParentTarget.jfft_roots
      processed).`1
    (fft_round_word_bound processed).
proof.
move=> hprocessed hcoeff.
apply
  (fft_schedule_prefix_safe_bound
    (actual_fft_init_data_bound2 data xp)
    KeygenMode2ParentTarget.jfft_roots
    processed
    hprocessed).
+ rewrite /actual_fft_init_data_bound2.
  exact (actual_fft_init_word_bound2 data xp hcoeff).
exact actual_fft_root_word_bound.
qed.

lemma actual_fft_schedule_safe_bound2
    (data : BArray2048.t) (xp : BArray1024.t) :
  fft_coefficient_bound xp 2 =>
  fft_schedule_safe
    (actual_fft_init_data_bound2 data xp)
    KeygenMode2ParentTarget.jfft_roots.
proof.
move=> hcoeff.
have [hsafe _] :=
  actual_fft_schedule_prefix_safe_bound2 data xp 8 _ hcoeff.
+ smt().
exact hsafe.
qed.

lemma actual_fft_full_word_bound2
    (data : BArray2048.t) (xp : BArray1024.t) :
  fft_coefficient_bound xp 2 =>
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_full
      (actual_fft_init_data_bound2 data xp)
      KeygenMode2ParentTarget.jfft_roots)
    859963392.
proof.
move=> hcoeff.
have [_ hbound] :=
  actual_fft_schedule_prefix_safe_bound2 data xp 8 _ hcoeff.
+ smt().
rewrite /KeygenM23SingularFFTSpec.fft_full
        /KeygenM23SingularFFTSpec.fft_stages_i in hbound.
rewrite fft_round_word_bound_8 in hbound.
exact hbound.
qed.

end KeygenM23SingularFFTScheduleBounds.
