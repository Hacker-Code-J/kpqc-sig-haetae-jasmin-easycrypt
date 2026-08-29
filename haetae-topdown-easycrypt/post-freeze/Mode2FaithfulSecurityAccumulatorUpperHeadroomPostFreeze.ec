require import AllCore IntDiv List Ring StdOrder Real.

from Jasmin require import JModel_x86.

require import BArray1024 BArray2048 BArray8192.
require import
  KeygenM23ComplexReal
  KeygenM23SingularSpec
  KeygenM23FixedPointSemantics
  KeygenM23SingularBoundary
  KeygenM23SingularIntegerSemantics
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety.

import RField RealOrder.
import
  KeygenM23ComplexReal
  KeygenM23FixedPointSemantics
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety.

theory Mode2FaithfulSecurityAccumulatorUpperHeadroomPostFreeze.

(* This file isolates the deterministic part of the accumulator safety
   argument that only needs the next-prefix upper cap plus the coordinate
   headroom.  The lower prefix inequality is recovered from the already-safe
   actual trace, so this theory carries no probabilistic or numeric tail
   reasoning. *)

op mode2_accumulator_prefix_upper_headroom
    (s1 s2 : BArray8192.t) (processed j : int) : bool =
  mode2_ideal_energy_prefix s1 s2 processed j +
    mode2_energy_error_prefix s1 s2 processed j <
      accumulator_q16_signed_limit.

op mode2_accumulator_upper_headroom_step
    (s1 s2 : BArray8192.t) (slot j : int) : bool =
  mode2_accumulator_coordinate_headroom s1 s2 slot j /\
  mode2_accumulator_prefix_upper_headroom s1 s2 (slot + 1) j.

op mode2_accumulator_upper_headroom_bad_event
    (s1 s2 : BArray8192.t) (processed : int) : bool =
  exists slot j,
    0 <= slot < processed /\
    0 <= j < KeygenM23SingularSpec.singular_words_i /\
    ! mode2_accumulator_upper_headroom_step s1 s2 slot j.

op mode2_accumulator_upper_headroom_trace
    (s1 s2 : BArray8192.t) (processed : int) : bool =
  0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i /\
  forall slot j,
    0 <= slot < processed =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mode2_accumulator_upper_headroom_step s1 s2 slot j.

lemma mode2_accumulator_upper_headroom_trace_iff_no_bad_event
    (s1 s2 : BArray8192.t) (processed : int) :
  0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  (mode2_accumulator_upper_headroom_trace s1 s2 processed <=>
   ! mode2_accumulator_upper_headroom_bad_event s1 s2 processed).
proof.
move=> hprocessed.
rewrite /mode2_accumulator_upper_headroom_trace
        /mode2_accumulator_upper_headroom_bad_event.
smt().
qed.

lemma actual_mode2_accumulate_prefix_nonnegative_s32_fits
    (s1 s2 : BArray8192.t) (processed j : int) :
  0 <= processed =>
  processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  actual_mode2_accumulate_safe_trace s1 s2 processed =>
  KeygenM23SingularBoundary.nonnegative_s32_fits
    (W32.to_sint (BArray1024.get32
      (mode2_actual_accumulate_prefix s1 s2 processed).`2 j)).
proof.
move: processed.
apply intind.
+ move=> _ hj _.
   rewrite /mode2_actual_accumulate_prefix
           KeygenM23SingularFFTSpec.mode2_accumulate_prefix0 /=.
   rewrite /KeygenM23SingularSpec.clear_sum.
   rewrite clear_prefix_get_zero 1:/# 1:/# 1:hj.
   rewrite /KeygenM23SingularBoundary.nonnegative_s32_fits
           /W32.to_sint /W32.smod W32.to_uint0 /=.
   smt().
+ move=> processed hprocessed ih hcap hj htrace.
   have hprevcap :
       processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i by smt().
   have hslot :
       0 <= processed < processed + 1 by smt().
   have hsafe := htrace processed j hslot hj.
   rewrite mode2_actual_accumulate_prefixS 1:hprocessed.
   rewrite /KeygenM23SingularFFTSpec.mode2_accumulate_step /=.
   rewrite accumulate_fft_sqabs_get 1:hj.
   rewrite
     (KeygenM23SingularIntegerSemantics.accumulate_step_at_to_sint
       (mode2_actual_fft_output s1 s2 processed)
       (mode2_actual_accumulate_prefix s1 s2 processed).`2
       j hj hsafe).
   move: hsafe.
   rewrite /KeygenM23SingularBoundary.fft_accumulate_safe.
   smt().
qed.

lemma mode2_actual_accumulate_step_safe_from_upper_headroom
    (s1 s2 : BArray8192.t) (slot j : int) :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  mode2_accumulator_inputs_bound2 s1 s2 =>
  actual_mode2_accumulate_safe_trace s1 s2 slot =>
  mode2_accumulator_coordinate_headroom s1 s2 slot j =>
  mode2_accumulator_prefix_upper_headroom s1 s2 (slot + 1) j =>
  let pre = mode2_actual_accumulate_prefix s1 s2 slot in
  let input = mode2_actual_fft_output s1 s2 slot in
  KeygenM23SingularBoundary.fft_accumulate_safe
    (BArray1024.get32 pre.`2 j)
    (BArray2048.get32 input (2 * j))
    (BArray2048.get32 input (2 * j + 1)).
proof.
move=> hslot hj hinputs htrace hcoord hnext.
have hslot0 : 0 <= slot by move: hslot; smt().
have hslotcap :
    slot <= KeygenM23SingularFFTSpec.mode2_slice_count_i by
  move: hslot; smt().
have hprefixfit :=
  actual_mode2_accumulate_prefix_nonnegative_s32_fits
    s1 s2 slot j hslot0 hslotcap hj htrace.
have hclose :=
  mode2_actual_fft_output_close_bound2
    s1 s2 slot j hinputs hslot hj.
have hwords :=
  fft_output_word_bound127
    (mode2_actual_fft_output s1 s2 slot) j
    mode2_fft_endpoint_eps
    (mode2_ideal_fft_at s1 s2 slot j)
    hclose.
move: hcoord => [hrcap hicap].
have [hreal himag] := hwords hrcap hicap.
have hsqsafe :=
  fft_sqabs_safe_from_bound127
    (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j))
    (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j + 1))
    hreal himag.
have hsqclose :=
  fft_sqabs_decode_ideal_error
    (mode2_actual_fft_output s1 s2 slot) j
    mode2_fft_endpoint_eps
    (mode2_ideal_fft_at s1 s2 slot j).
have hsqerr := hsqclose hsqsafe hclose.
have hsqdecode :
    fft_sqabs_decode_at (mode2_actual_fft_output s1 s2 slot) j =
    q16_decode_int
      (KeygenM23SingularBoundary.fft_sqabs_int
        (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j))
        (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j + 1))).
+ rewrite /fft_sqabs_decode_at /q16_decode_word.
  have hsqto :
      W32.to_sint
        (KeygenM23SingularSpec.fft_sqabs_at
          (mode2_actual_fft_output s1 s2 slot) j) =
      KeygenM23SingularBoundary.fft_sqabs_int
        (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j))
        (BArray2048.get32
          (mode2_actual_fft_output s1 s2 slot) (2 * j + 1)).
  + apply KeygenM23SingularIntegerSemantics.fft_sqabs_at_to_sint.
    exact hsqsafe.
  by rewrite hsqto.
have hprefix0 :
    0 <= W32.to_sint
      (BArray1024.get32
        (mode2_actual_accumulate_prefix s1 s2 slot).`2 j).
+ move: hprefixfit.
  rewrite /KeygenM23SingularBoundary.nonnegative_s32_fits.
  move=> [hprefix0 _].
  exact hprefix0.
have hsqint0 :
    0 <= KeygenM23SingularBoundary.fft_sqabs_int
      (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j))
      (BArray2048.get32
        (mode2_actual_fft_output s1 s2 slot) (2 * j + 1)).
+ move: hsqsafe.
  rewrite /KeygenM23SingularBoundary.fft_sqabs_safe
          /KeygenM23SingularBoundary.nonnegative_s32_fits.
  move=> [_ [_ [hsqint0 _]]].
  exact hsqint0.
have hsumint0 :
    0 <=
      W32.to_sint
        (BArray1024.get32
          (mode2_actual_accumulate_prefix s1 s2 slot).`2 j) +
      KeygenM23SingularBoundary.fft_sqabs_int
        (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j))
        (BArray2048.get32
          (mode2_actual_fft_output s1 s2 slot) (2 * j + 1)).
+ exact (IntOrder.addr_ge0 _ _ hprefix0 hsqint0).
have hsumfit :
    KeygenM23SingularBoundary.nonnegative_s32_fits
      (W32.to_sint
         (BArray1024.get32 (mode2_actual_accumulate_prefix s1 s2 slot).`2 j) +
       KeygenM23SingularBoundary.fft_sqabs_int
         (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j))
         (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j + 1))).
+ have hpreverr :=
     mode2_actual_accumulate_prefix_error
       s1 s2 slot j hslot0 hslotcap hj hinputs htrace.
   have hsumlt :
       q16_decode_int
         (W32.to_sint
            (BArray1024.get32
              (mode2_actual_accumulate_prefix s1 s2 slot).`2 j) +
          KeygenM23SingularBoundary.fft_sqabs_int
            (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j))
            (BArray2048.get32 (mode2_actual_fft_output s1 s2 slot) (2 * j + 1))) <
         accumulator_q16_signed_limit.
   + rewrite q16_decode_intD /accumulator_decode_at /q16_decode_word -hsqdecode.
     have hidealnext :=
       mode2_ideal_energy_prefixS s1 s2 slot j hslot0.
     have herrnext :=
       mode2_energy_error_prefixS s1 s2 slot j hslot0.
     rewrite /mode2_accumulator_prefix_upper_headroom in hnext.
     have hprevupper :
         accumulator_decode_at
             (mode2_actual_accumulate_prefix s1 s2 slot).`2 j -
           mode2_ideal_energy_prefix s1 s2 slot j <=
         mode2_energy_error_prefix s1 s2 slot j.
     + apply
         (ler_trans
           `|accumulator_decode_at
                (mode2_actual_accumulate_prefix s1 s2 slot).`2 j -
              mode2_ideal_energy_prefix s1 s2 slot j|).
       + exact (ler_norm _).
       exact hpreverr.
     rewrite /accumulator_decode_at /q16_decode_word in hprevupper.
     have hstepupper :
         fft_sqabs_decode_at (mode2_actual_fft_output s1 s2 slot) j -
           cnorm2 (mode2_ideal_fft_at s1 s2 slot j) <=
         sqabs_ideal_error_budget mode2_fft_endpoint_eps
           (mode2_ideal_fft_at s1 s2 slot j).
     + apply
         (ler_trans
           `|fft_sqabs_decode_at (mode2_actual_fft_output s1 s2 slot) j -
              cnorm2 (mode2_ideal_fft_at s1 s2 slot j)|).
       + exact (ler_norm _).
       exact hsqerr.
     have hprevdecode :
         q16_decode_word
             (BArray1024.get32
               (mode2_actual_accumulate_prefix s1 s2 slot).`2 j) <=
         mode2_ideal_energy_prefix s1 s2 slot j +
           mode2_energy_error_prefix s1 s2 slot j by smt().
     have hstepdecode :
         fft_sqabs_decode_at (mode2_actual_fft_output s1 s2 slot) j <=
         cnorm2 (mode2_ideal_fft_at s1 s2 slot j) +
           sqabs_ideal_error_budget mode2_fft_endpoint_eps
             (mode2_ideal_fft_at s1 s2 slot j) by smt().
     have hnextcap :
         (mode2_ideal_energy_prefix s1 s2 slot j +
           cnorm2 (mode2_ideal_fft_at s1 s2 slot j)) +
         (mode2_energy_error_prefix s1 s2 slot j +
           sqabs_ideal_error_budget mode2_fft_endpoint_eps
             (mode2_ideal_fft_at s1 s2 slot j)) <
         accumulator_q16_signed_limit.
     + move: hnext.
       rewrite hidealnext herrnext.
       trivial.
     apply
       (ler_lt_trans
         (mode2_ideal_energy_prefix s1 s2 slot j +
            mode2_energy_error_prefix s1 s2 slot j +
          (cnorm2 (mode2_ideal_fft_at s1 s2 slot j) +
           sqabs_ideal_error_budget mode2_fft_endpoint_eps
             (mode2_ideal_fft_at s1 s2 slot j)))).
     + apply ler_add.
       + exact hprevdecode.
       exact hstepdecode.
     + have -> :
         mode2_ideal_energy_prefix s1 s2 slot j +
            mode2_energy_error_prefix s1 s2 slot j +
          (cnorm2 (mode2_ideal_fft_at s1 s2 slot j) +
           sqabs_ideal_error_budget mode2_fft_endpoint_eps
             (mode2_ideal_fft_at s1 s2 slot j)) =
         (mode2_ideal_energy_prefix s1 s2 slot j +
           cnorm2 (mode2_ideal_fft_at s1 s2 slot j)) +
         (mode2_energy_error_prefix s1 s2 slot j +
           sqabs_ideal_error_budget mode2_fft_endpoint_eps
             (mode2_ideal_fft_at s1 s2 slot j)) by ring.
       exact hnextcap.
   exact (q16_decode_int_nonnegative_s32_fits _ hsumint0 hsumlt).
rewrite /KeygenM23SingularBoundary.fft_accumulate_safe.
split.
+ exact hsqsafe.
split.
+ exact hprefixfit.
exact hsumfit.
qed.

lemma mode2_accumulator_upper_headroom_trace_prefix
    (s1 s2 : BArray8192.t) (processed : int) :
  0 <= processed =>
  mode2_accumulator_upper_headroom_trace s1 s2 (processed + 1) =>
  mode2_accumulator_upper_headroom_trace s1 s2 processed.
proof.
move=> hprocessed.
rewrite /mode2_accumulator_upper_headroom_trace.
move=> [hrange hsteps].
split.
+ smt().
+ move=> slot j hslot hj.
   apply hsteps.
   + smt().
   exact hj.
qed.

lemma mode2_actual_accumulate_safe_from_upper_headroom
    (s1 s2 : BArray8192.t) (processed : int) :
  0 <= processed =>
  processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  mode2_accumulator_inputs_bound2 s1 s2 =>
  mode2_accumulator_upper_headroom_trace s1 s2 processed =>
  actual_mode2_accumulate_safe_trace s1 s2 processed.
proof.
move: processed.
apply intind.
+ move=> _ _ _.
   rewrite /actual_mode2_accumulate_safe_trace.
   smt().
+ move=> processed hprocessed ih hcap hinputs hheadroom.
   have hprevcap :
       processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i by smt().
   have hprevheadroom :=
     mode2_accumulator_upper_headroom_trace_prefix
       s1 s2 processed hprocessed hheadroom.
   have hprev := ih hprevcap hinputs hprevheadroom.
   move: hheadroom.
   rewrite /mode2_accumulator_upper_headroom_trace.
   move=> [_ hsteps].
   rewrite /actual_mode2_accumulate_safe_trace in hprev.
   rewrite /actual_mode2_accumulate_safe_trace.
   move=> slot j hslot hj.
   case (slot = processed) => hlast.
   + subst slot.
     have hcurrent :
         0 <= processed <
           KeygenM23SingularFFTSpec.mode2_slice_count_i by smt().
     have hstep :
         mode2_accumulator_upper_headroom_step s1 s2 processed j.
     + apply hsteps.
       + smt().
       exact hj.
     move: hstep => [hcoord hnext].
     exact
       (mode2_actual_accumulate_step_safe_from_upper_headroom
         s1 s2 processed j hcurrent hj hinputs hprev hcoord hnext).
   have hprevious : 0 <= slot < processed by smt().
   exact (hprev slot j hprevious hj).
qed.

end Mode2FaithfulSecurityAccumulatorUpperHeadroomPostFreeze.
