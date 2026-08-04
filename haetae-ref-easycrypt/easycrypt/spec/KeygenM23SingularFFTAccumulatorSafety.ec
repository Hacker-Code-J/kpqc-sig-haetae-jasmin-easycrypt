require import AllCore IntDiv List Ring StdOrder Real.

from Jasmin require import JModel_x86.

require import BArray1024 BArray2048 BArray8192.
require import
  KeygenM23ComplexReal
  KeygenM23FixedPointSemantics
  KeygenM23SingularBoundary
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularIntegerSemantics
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTAccumulatorBridge.

import RField RealOrder.
import
  KeygenM23ComplexReal
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTAccumulatorBridge.

theory KeygenM23SingularFFTAccumulatorSafety.

op accumulator_q16_signed_limit : real =
  2147483648%r / 65536%r.

op accumulator_q16_coordinate_cap : real = 127%r.

op accumulator_q16_word_cap : int = 8323072.

op mode2_accumulator_prefix_headroom
    (s1 s2 : BArray8192.t) (processed j : int) : bool =
  mode2_energy_error_prefix s1 s2 processed j <=
    mode2_ideal_energy_prefix s1 s2 processed j /\
  mode2_ideal_energy_prefix s1 s2 processed j +
    mode2_energy_error_prefix s1 s2 processed j <
      accumulator_q16_signed_limit.

op mode2_accumulator_coordinate_headroom
    (s1 s2 : BArray8192.t) (slot j : int) : bool =
  `|creal (mode2_ideal_fft_at s1 s2 slot j)| + mode2_fft_endpoint_eps <=
    accumulator_q16_coordinate_cap /\
  `|cimag (mode2_ideal_fft_at s1 s2 slot j)| + mode2_fft_endpoint_eps <=
    accumulator_q16_coordinate_cap.

op mode2_accumulator_headroom_step
    (s1 s2 : BArray8192.t) (slot j : int) : bool =
  mode2_accumulator_prefix_headroom s1 s2 slot j /\
  mode2_accumulator_coordinate_headroom s1 s2 slot j /\
  mode2_accumulator_prefix_headroom s1 s2 (slot + 1) j.

(* This conservative failure event is an analytic proof surface: its absence
   implies machine safety below, but its presence is not claimed to be
   equivalent to an actual signed-W32 overflow. *)
op mode2_accumulator_headroom_bad_event
    (s1 s2 : BArray8192.t) (processed : int) : bool =
  exists slot j,
    0 <= slot < processed /\
    0 <= j < KeygenM23SingularSpec.singular_words_i /\
    !mode2_accumulator_headroom_step s1 s2 slot j.

op mode2_accumulator_headroom_trace
    (s1 s2 : BArray8192.t) (processed : int) : bool =
  0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i /\
  forall slot j,
    0 <= slot < processed =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mode2_accumulator_headroom_step s1 s2 slot j.

lemma mode2_accumulator_headroom_trace_iff_no_bad_event
    (s1 s2 : BArray8192.t) (processed : int) :
  0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  (mode2_accumulator_headroom_trace s1 s2 processed <=>
   !mode2_accumulator_headroom_bad_event s1 s2 processed).
proof.
move=> hprocessed.
rewrite /mode2_accumulator_headroom_trace
        /mode2_accumulator_headroom_bad_event.
smt().
qed.

lemma mode2_fft_endpoint_eps_ge0 :
  0%r <= mode2_fft_endpoint_eps.
proof. by rewrite /mode2_fft_endpoint_eps; smt(). qed.

lemma sqabs_ideal_error_budget_ge0
    (eps : real) (ideal : complex) :
  0%r <= eps =>
  0%r <= sqabs_ideal_error_budget eps ideal.
proof.
move=> heps.
rewrite /sqabs_ideal_error_budget /cnorm2_perturbation_budget.
have hcreal : 0%r <= `|creal ideal| by apply RealOrder.normr_ge0.
have hcimag : 0%r <= `|cimag ideal| by apply RealOrder.normr_ge0.
smt().
qed.

lemma mode2_ideal_energy_prefix_ge0
    (s1 s2 : BArray8192.t) (processed j : int) :
  0 <= processed =>
  0%r <= mode2_ideal_energy_prefix s1 s2 processed j.
proof.
move: processed.
apply intind.
+ smt().
+ move=> processed hprocessed ih.
  have hrec :=
    mode2_ideal_energy_prefixS s1 s2 processed j hprocessed.
  have hstep : 0%r <= cnorm2 (mode2_ideal_fft_at s1 s2 processed j) by
    apply cnorm2_ge0.
  smt().
qed.

lemma mode2_energy_error_prefix_ge0
    (s1 s2 : BArray8192.t) (processed j : int) :
  0 <= processed =>
  0%r <= mode2_energy_error_prefix s1 s2 processed j.
proof.
move: processed.
apply intind.
+ smt().
+ move=> processed hprocessed ih.
  have hrec :=
    mode2_energy_error_prefixS s1 s2 processed j hprocessed.
  have hstep :=
    sqabs_ideal_error_budget_ge0
      mode2_fft_endpoint_eps
      (mode2_ideal_fft_at s1 s2 processed j)
      mode2_fft_endpoint_eps_ge0.
  smt().
qed.

lemma q16_decode_int_nonnegative_s32_fits (z : int) :
  0 <= z =>
  q16_decode_int z < accumulator_q16_signed_limit =>
  KeygenM23SingularBoundary.nonnegative_s32_fits z.
proof.
rewrite /q16_decode_int /accumulator_q16_signed_limit
        /KeygenM23SingularBoundary.nonnegative_s32_fits.
smt().
qed.

lemma q16_decode_word_nonnegative_s32_fits (w : W32.t) :
  0%r <= q16_decode_word w =>
  q16_decode_word w < accumulator_q16_signed_limit =>
  KeygenM23SingularBoundary.nonnegative_s32_fits (W32.to_sint w).
proof.
rewrite q16_decode_wordE /q16_decode_int /accumulator_q16_signed_limit
        /KeygenM23SingularBoundary.nonnegative_s32_fits.
smt().
qed.

lemma q16_decode_word_bound127 (w : W32.t) :
  `|q16_decode_word w| <= accumulator_q16_coordinate_cap =>
  -accumulator_q16_word_cap <= W32.to_sint w <=
    accumulator_q16_word_cap.
proof.
rewrite /q16_decode_word /q16_decode_int
        /accumulator_q16_coordinate_cap
        /accumulator_q16_word_cap ler_norml.
move=> [hlo hhi].
have hscale : 0%r < 65536%r by trivial.
have hlo0 : (-127)%r <= (W32.to_sint w)%r / 65536%r by
  rewrite fromintN.
have hlo' :
    (-127)%r * 65536%r <= (W32.to_sint w)%r.
+ exact
    (iffLR _ _
      (ler_pdivl_mulr 65536%r (-127)%r
        (W32.to_sint w)%r hscale) hlo0).
have hhi' :
    (W32.to_sint w)%r <= 127%r * 65536%r.
+ exact
    (iffLR _ _
      (ler_pdivr_mulr 65536%r 127%r
        (W32.to_sint w)%r hscale) hhi).
rewrite -le_fromint -le_fromint.
move: hlo' hhi'.
smt().
qed.

lemma close_coordinate_bound127
    (eps x y : real) :
  `|x - y| <= eps =>
  `|y| + eps <= accumulator_q16_coordinate_cap =>
  `|x| <= accumulator_q16_coordinate_cap.
proof.
move=> hclose hcap.
have htri := ler_norm_add (x - y) y.
move: htri.
have -> : x - y + y = x by ring.
smt().
qed.

lemma fft_output_word_bound127
    (input : BArray2048.t) (j : int)
    (eps : real) (ideal : complex) :
  cclose eps (fft_decode_at input j) ideal =>
  `|creal ideal| + eps <= accumulator_q16_coordinate_cap =>
  `|cimag ideal| + eps <= accumulator_q16_coordinate_cap =>
  -accumulator_q16_word_cap <=
    W32.to_sint (BArray2048.get32 input (2 * j)) <=
    accumulator_q16_word_cap /\
  -accumulator_q16_word_cap <=
    W32.to_sint (BArray2048.get32 input (2 * j + 1)) <=
    accumulator_q16_word_cap.
proof.
rewrite /cclose /fft_decode_at /creal /cimag /=.
move=> [hre him] hrc hic.
split.
+ apply q16_decode_word_bound127.
   exact (close_coordinate_bound127
     eps
     (q16_decode_word (BArray2048.get32 input (2 * j)))
     (creal ideal) hre hrc).
+ apply q16_decode_word_bound127.
   exact (close_coordinate_bound127
     eps
     (q16_decode_word (BArray2048.get32 input (2 * j + 1)))
     (cimag ideal) him hic).
qed.

lemma mulrnd16_self_bounds127 (w : W32.t) :
  -accumulator_q16_word_cap <= W32.to_sint w <=
    accumulator_q16_word_cap =>
  KeygenM23SingularBoundary.mulrnd16_safe w w /\
  0 <= KeygenM23FixedPointSemantics.mulrnd16_int
        (W32.to_sint w) (W32.to_sint w) <= 1057030144.
proof.
move=> hw.
have hcap : 0 <= accumulator_q16_word_cap by
  rewrite /accumulator_q16_word_cap.
have hproduct :=
  symmetric_product_bound
    (W32.to_sint w) (W32.to_sint w)
    accumulator_q16_word_cap accumulator_q16_word_cap
    hcap hcap hw hw.
have hsq0 : 0 <= W32.to_sint w * W32.to_sint w.
+ case (0 <= W32.to_sint w) => hw0.
   + exact (IntOrder.mulr_ge0 _ _ hw0 hw0).
   have hn : 0 <= -W32.to_sint w by smt().
   have hh := IntOrder.mulr_ge0
     (-W32.to_sint w) (-W32.to_sint w) hn hn.
   smt().
have hround :=
  KeygenM23FixedPointSemantics.q16_round_error
    (W32.to_sint w * W32.to_sint w).
rewrite /accumulator_q16_word_cap
        /KeygenM23FixedPointSemantics.q16_scale
        /KeygenM23FixedPointSemantics.q16_half in hproduct.
rewrite /accumulator_q16_word_cap
        /KeygenM23FixedPointSemantics.q16_scale
        /KeygenM23FixedPointSemantics.q16_half in hsq0.
rewrite /accumulator_q16_word_cap
        /KeygenM23FixedPointSemantics.q16_scale
        /KeygenM23FixedPointSemantics.q16_half in hround.
rewrite /KeygenM23SingularBoundary.mulrnd16_safe
        /KeygenM23SingularBoundary.s64_fits
        /KeygenM23SingularBoundary.s32_fits
        /KeygenM23FixedPointSemantics.mulrnd16_int
        /accumulator_q16_word_cap
        /KeygenM23FixedPointSemantics.q16_scale
        /KeygenM23FixedPointSemantics.q16_half.
do split; smt().
qed.

lemma fft_sqabs_safe_from_bound127 (real imag : W32.t) :
  -accumulator_q16_word_cap <= W32.to_sint real <=
    accumulator_q16_word_cap =>
  -accumulator_q16_word_cap <= W32.to_sint imag <=
    accumulator_q16_word_cap =>
  KeygenM23SingularBoundary.fft_sqabs_safe real imag.
proof.
move=> hr hi.
have [hsr hbr] := mulrnd16_self_bounds127 real hr.
have [hsi hbi] := mulrnd16_self_bounds127 imag hi.
rewrite /KeygenM23SingularBoundary.fft_sqabs_safe
        /KeygenM23SingularBoundary.fft_sqabs_int
        /KeygenM23SingularBoundary.nonnegative_s32_fits.
do split; smt().
qed.

lemma local_sqabs_budget_below_prefix_headroom
    (s1 s2 : BArray8192.t) (slot j : int) :
  0 <= slot =>
  mode2_accumulator_prefix_headroom s1 s2 (slot + 1) j =>
  sqabs_ideal_error_budget mode2_fft_endpoint_eps
      (mode2_ideal_fft_at s1 s2 slot j) +
    cnorm2 (mode2_ideal_fft_at s1 s2 slot j) <
      accumulator_q16_signed_limit.
proof.
move=> hslot hnext.
move: hnext => [_ hcap].
have hprev0 :=
  mode2_ideal_energy_prefix_ge0 s1 s2 slot j hslot.
have herr0 :=
  mode2_energy_error_prefix_ge0 s1 s2 slot j hslot.
rewrite mode2_ideal_energy_prefixS 1:hslot
        mode2_energy_error_prefixS 1:hslot in hcap.
smt().
qed.

lemma actual_accumulator_prefix_decode_headroom
    (s1 s2 : BArray8192.t) (processed j : int) :
  0 <= processed =>
  processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  mode2_accumulator_inputs_bound2 s1 s2 =>
  actual_mode2_accumulate_safe_trace s1 s2 processed =>
  mode2_accumulator_prefix_headroom s1 s2 processed j =>
  0%r <= accumulator_decode_at
    (mode2_actual_accumulate_prefix s1 s2 processed).`2 j /\
  accumulator_decode_at
    (mode2_actual_accumulate_prefix s1 s2 processed).`2 j <
      accumulator_q16_signed_limit.
proof.
move=> hprocessed hcap hj hinputs htrace hhead.
move: hhead => [herrdom hlimit].
have herr0 :=
  mode2_energy_error_prefix_ge0 s1 s2 processed j hprocessed.
have haccerr :=
  mode2_actual_accumulate_prefix_error
    s1 s2 processed j hprocessed hcap hj hinputs htrace.
split.
+ move: haccerr herrdom herr0.
   smt().
+ move: haccerr hlimit.
   smt().
qed.

lemma mode2_actual_accumulate_step_safe_from_headroom
    (s1 s2 : BArray8192.t) (slot j : int) :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  mode2_accumulator_inputs_bound2 s1 s2 =>
  actual_mode2_accumulate_safe_trace s1 s2 slot =>
  mode2_accumulator_headroom_step s1 s2 slot j =>
  let pre = mode2_actual_accumulate_prefix s1 s2 slot in
  let input = mode2_actual_fft_output s1 s2 slot in
  KeygenM23SingularBoundary.fft_accumulate_safe
    (BArray1024.get32 pre.`2 j)
    (BArray2048.get32 input (2 * j))
    (BArray2048.get32 input (2 * j + 1)).
proof.
move=> hslot hj hinputs htrace.
have hslot0 : 0 <= slot by
  move: hslot; smt().
have hslotcap :
    slot <= KeygenM23SingularFFTSpec.mode2_slice_count_i by
  move: hslot; smt().
rewrite /=.
move=> [hprefix [hcoord hnext]].
have hacc :=
  actual_accumulator_prefix_decode_headroom
    s1 s2 slot j _ _ hj hinputs htrace hprefix.
+ smt().
+ smt().
move: hacc => [hacc0 hacclt].
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
have hprefixfit :=
  q16_decode_word_nonnegative_s32_fits
    (BArray1024.get32
      (mode2_actual_accumulate_prefix s1 s2 slot).`2 j)
    hacc0 hacclt.
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
     move: hnext.
     rewrite /mode2_accumulator_prefix_headroom.
     move=> [_ hnextcap].
     have hidealnext :=
       mode2_ideal_energy_prefixS s1 s2 slot j hslot0.
     have herrnext :=
       mode2_energy_error_prefixS s1 s2 slot j hslot0.
     rewrite /accumulator_decode_at /q16_decode_word in hpreverr.
     move: hpreverr hsqerr hnextcap hidealnext herrnext.
     smt().
   exact (q16_decode_int_nonnegative_s32_fits _ hsumint0 hsumlt).
rewrite /KeygenM23SingularBoundary.fft_accumulate_safe.
split.
+ exact hsqsafe.
split.
+ exact hprefixfit.
exact hsumfit.
qed.

lemma mode2_accumulator_headroom_trace_prefix
    (s1 s2 : BArray8192.t) (processed : int) :
  0 <= processed =>
  mode2_accumulator_headroom_trace s1 s2 (processed + 1) =>
  mode2_accumulator_headroom_trace s1 s2 processed.
proof.
move=> hprocessed.
rewrite /mode2_accumulator_headroom_trace.
move=> [hrange hsteps].
split.
+ smt().
move=> slot j hslot hj.
apply hsteps.
+ smt().
exact hj.
qed.

lemma mode2_actual_accumulate_safe_from_headroom
    (s1 s2 : BArray8192.t) (processed : int) :
  0 <= processed =>
  processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  mode2_accumulator_inputs_bound2 s1 s2 =>
  mode2_accumulator_headroom_trace s1 s2 processed =>
  actual_mode2_accumulate_safe_trace s1 s2 processed.
proof.
move: processed.
apply intind.
+ move=> _ _ _.
  rewrite /actual_mode2_accumulate_safe_trace.
  smt().
+ move=> processed hprocessed ih hcap hinputs hheadroom.
  have hprevcap :
      processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i by
    smt().
  have hprevheadroom :=
    mode2_accumulator_headroom_trace_prefix
      s1 s2 processed hprocessed hheadroom.
  have hprev := ih hprevcap hinputs hprevheadroom.
  move: hheadroom.
  rewrite /mode2_accumulator_headroom_trace.
  move=> [_ hsteps].
  rewrite /actual_mode2_accumulate_safe_trace in hprev.
  rewrite /actual_mode2_accumulate_safe_trace.
  move=> slot j hslot hj.
  case (slot = processed) => hlast.
  + subst slot.
    have hcurrent :
        0 <= processed <
          KeygenM23SingularFFTSpec.mode2_slice_count_i by
      smt().
    have hstep : mode2_accumulator_headroom_step s1 s2 processed j.
    + apply hsteps.
      + smt().
      exact hj.
    exact
      (mode2_actual_accumulate_step_safe_from_headroom
        s1 s2 processed j hcurrent hj hinputs hprev hstep).
  have hprevious : 0 <= slot < processed by
    smt().
  exact (hprev slot j hprevious hj).
qed.

end KeygenM23SingularFFTAccumulatorSafety.
