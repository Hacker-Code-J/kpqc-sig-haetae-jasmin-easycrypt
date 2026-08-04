require import AllCore IntDiv List Ring StdOrder Real.

from Jasmin require import JModel_x86.

require import BArray512 BArray1024 BArray2048 BArray8192.
require import
  KeygenM23ComplexReal
  KeygenM23FixedPointSemantics
  KeygenM23IdealRootDFT
  KeygenM23SingularSpec
  KeygenM23SingularBoundary
  KeygenM23SingularIntegerSemantics
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTGlobalTrace
  KeygenM23SingularFFTErrorTrace
  KeygenMode2ParentTarget.

import RField RealOrder.
import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTGlobalTrace
  KeygenM23SingularFFTErrorTrace.

theory KeygenM23SingularFFTAccumulatorBridge.

op fft_sqabs_decode_at (input : BArray2048.t) (j : int) : real =
  q16_decode_word (KeygenM23SingularSpec.fft_sqabs_at input j).

op accumulator_decode_at (sum : BArray1024.t) (j : int) : real =
  q16_decode_word (BArray1024.get32 sum j).

op cnorm2_perturbation_budget
    (eps : real) (ideal : complex) : real =
  eps * (2%r * `|creal ideal| + eps) +
  eps * (2%r * `|cimag ideal| + eps).

op sqabs_ideal_error_budget
    (eps : real) (ideal : complex) : real =
  1%r / 65536%r + cnorm2_perturbation_budget eps ideal.

lemma fft_sqabs_decode_error
    (input : BArray2048.t) (j : int) :
  let real = BArray2048.get32 input (2 * j) in
  let imag = BArray2048.get32 input (2 * j + 1) in
  KeygenM23SingularBoundary.fft_sqabs_safe real imag =>
  `|fft_sqabs_decode_at input j - cnorm2 (fft_decode_at input j)| <=
    1%r / 65536%r.
proof.
rewrite /=.
move=> hsafe.
have hword :
    W32.to_sint (KeygenM23SingularSpec.fft_sqabs_at input j) =
    KeygenM23SingularBoundary.fft_sqabs_int
      (BArray2048.get32 input (2 * j))
      (BArray2048.get32 input (2 * j + 1)).
+ apply KeygenM23SingularIntegerSemantics.fft_sqabs_at_to_sint.
  exact hsafe.
have hreal :=
  q16_mulrnd16_decode_error
    (W32.to_sint (BArray2048.get32 input (2 * j)))
    (W32.to_sint (BArray2048.get32 input (2 * j))).
have himag :=
  q16_mulrnd16_decode_error
    (W32.to_sint (BArray2048.get32 input (2 * j + 1)))
    (W32.to_sint (BArray2048.get32 input (2 * j + 1))).
rewrite /fft_sqabs_decode_at /q16_decode_word hword.
rewrite /KeygenM23SingularBoundary.fft_sqabs_int q16_decode_intD.
rewrite /cnorm2 /fft_decode_at /creal /cimag /=.
have hsum :=
  ler_norm_add
    (q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int
         (W32.to_sint (BArray2048.get32 input (2 * j)))
         (W32.to_sint (BArray2048.get32 input (2 * j)))) -
     q16_decode_int
       (W32.to_sint (BArray2048.get32 input (2 * j))) *
     q16_decode_int
       (W32.to_sint (BArray2048.get32 input (2 * j))))
    (q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int
         (W32.to_sint (BArray2048.get32 input (2 * j + 1)))
         (W32.to_sint (BArray2048.get32 input (2 * j + 1)))) -
     q16_decode_int
       (W32.to_sint (BArray2048.get32 input (2 * j + 1))) *
     q16_decode_int
       (W32.to_sint (BArray2048.get32 input (2 * j + 1)))).
have heq :
    q16_decode_int
      (KeygenM23FixedPointSemantics.mulrnd16_int
        (W32.to_sint (BArray2048.get32 input (2 * j)))
        (W32.to_sint (BArray2048.get32 input (2 * j)))) +
    q16_decode_int
      (KeygenM23FixedPointSemantics.mulrnd16_int
        (W32.to_sint (BArray2048.get32 input (2 * j + 1)))
        (W32.to_sint (BArray2048.get32 input (2 * j + 1)))) -
    (q16_decode_int (W32.to_sint (BArray2048.get32 input (2 * j))) *
       q16_decode_int (W32.to_sint (BArray2048.get32 input (2 * j))) +
     q16_decode_int (W32.to_sint (BArray2048.get32 input (2 * j + 1))) *
       q16_decode_int (W32.to_sint (BArray2048.get32 input (2 * j + 1)))) =
    (q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int
         (W32.to_sint (BArray2048.get32 input (2 * j)))
         (W32.to_sint (BArray2048.get32 input (2 * j)))) -
     q16_decode_int (W32.to_sint (BArray2048.get32 input (2 * j))) *
       q16_decode_int (W32.to_sint (BArray2048.get32 input (2 * j)))) +
    (q16_decode_int
       (KeygenM23FixedPointSemantics.mulrnd16_int
         (W32.to_sint (BArray2048.get32 input (2 * j + 1)))
         (W32.to_sint (BArray2048.get32 input (2 * j + 1)))) -
     q16_decode_int (W32.to_sint (BArray2048.get32 input (2 * j + 1))) *
       q16_decode_int (W32.to_sint (BArray2048.get32 input (2 * j + 1)))) by
  ring.
rewrite heq.
smt().
qed.

lemma square_perturbation
    (eps x y : real) :
  0%r <= eps =>
  `|x - y| <= eps =>
  `|x * x - y * y| <= eps * (2%r * `|y| + eps).
proof.
move=> heps hxy.
have hde : 0%r <= `|x - y| by
  apply RealOrder.normr_ge0.
have hy : 0%r <= `|y| by
  apply RealOrder.normr_ge0.
have hdd :
    `|x - y| * `|x - y| <= eps * eps.
+ apply ler_pmul => //.
have hyd :
    `|y| * `|x - y| <= `|y| * eps.
+ apply ler_wpmul2l => //.
have heq :
    x * x - y * y =
      (x - y) * (x - y) + y * (x - y) + y * (x - y) by
  ring.
rewrite heq.
have hsum0 :=
  ler_norm_add
    ((x - y) * (x - y))
    (y * (x - y) + y * (x - y)).
have hsum1 :=
  ler_norm_add (y * (x - y)) (y * (x - y)).
rewrite !normrM in hsum0.
rewrite !normrM in hsum1.
have hbudget :
    eps * eps + (`|y| * eps + `|y| * eps) =
      eps * (2%r * `|y| + eps) by
  ring.
smt().
qed.

lemma cclose_cnorm2_perturbation
    (eps : real) (actual ideal : complex) :
  cclose eps actual ideal =>
  `|cnorm2 actual - cnorm2 ideal| <=
    cnorm2_perturbation_budget eps ideal.
proof.
move=> hclose.
have heps := cclose_ge0 eps actual ideal hclose.
move: hclose; rewrite /cclose; move=> [hre him].
have hr :=
  square_perturbation eps (creal actual) (creal ideal) heps hre.
have hi :=
  square_perturbation eps (cimag actual) (cimag ideal) heps him.
rewrite /cnorm2.
have heq :
    (creal actual * creal actual + cimag actual * cimag actual) -
    (creal ideal * creal ideal + cimag ideal * cimag ideal) =
    (creal actual * creal actual - creal ideal * creal ideal) +
    (cimag actual * cimag actual - cimag ideal * cimag ideal) by
  ring.
rewrite heq.
have hsum :=
  ler_norm_add
    (creal actual * creal actual - creal ideal * creal ideal)
    (cimag actual * cimag actual - cimag ideal * cimag ideal).
rewrite /cnorm2_perturbation_budget.
smt().
qed.

lemma fft_sqabs_decode_ideal_error
    (input : BArray2048.t) (j : int)
    (eps : real) (ideal : complex) :
  let real = BArray2048.get32 input (2 * j) in
  let imag = BArray2048.get32 input (2 * j + 1) in
  KeygenM23SingularBoundary.fft_sqabs_safe real imag =>
  cclose eps (fft_decode_at input j) ideal =>
  `|fft_sqabs_decode_at input j - cnorm2 ideal| <=
    sqabs_ideal_error_budget eps ideal.
proof.
rewrite /=.
move=> hsafe hclose.
have hlocal := fft_sqabs_decode_error input j hsafe.
have hideal :=
  cclose_cnorm2_perturbation
    eps (fft_decode_at input j) ideal hclose.
have htri :=
  ler_dist_add
    (cnorm2 (fft_decode_at input j))
    (fft_sqabs_decode_at input j)
    (cnorm2 ideal).
rewrite /sqabs_ideal_error_budget.
smt().
qed.

lemma clear_prefix_get_zero
    (sum : BArray1024.t) (processed j : int) :
  0 <= processed =>
  processed <= KeygenM23SingularSpec.singular_words_i =>
  0 <= j < processed =>
  BArray1024.get32
    (KeygenM23SingularSpec.clear_prefix sum processed) j = W32.zero.
proof.
move: processed.
apply intind.
+ move=> _ hj.
  smt().
+ move=> processed hprocessed ih hcap hj.
  rewrite KeygenM23SingularSpec.clear_prefixS 1://
          /KeygenM23SingularSpec.clear_step.
  rewrite BArray1024.get_set32E 1:/# 1:/#.
  case (processed = j) => heq.
  + trivial.
  + apply ih; smt().
qed.

lemma clear_sum_decode_at_zero
    (sum : BArray1024.t) (j : int) :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  accumulator_decode_at (KeygenM23SingularSpec.clear_sum sum) j = 0%r.
proof.
move=> hj.
rewrite /accumulator_decode_at /KeygenM23SingularSpec.clear_sum.
rewrite clear_prefix_get_zero 1:/# 1:/# 1:hj.
by rewrite /q16_decode_word /q16_decode_int
           /W32.to_sint /W32.smod W32.to_uint0 /=.
qed.

lemma accumulate_prefix_get_unprocessed
    (sum : BArray1024.t) (input : BArray2048.t)
    (processed j : int) :
  0 <= processed =>
  processed <= KeygenM23SingularSpec.singular_words_i =>
  processed <= j < KeygenM23SingularSpec.singular_words_i =>
  BArray1024.get32
    (KeygenM23SingularSpec.accumulate_prefix sum input processed) j =
  BArray1024.get32 sum j.
proof.
move: processed.
apply intind.
+ move=> _ hj.
  by rewrite KeygenM23SingularSpec.accumulate_prefix0.
+ move=> processed hprocessed ih hcap hj.
  rewrite KeygenM23SingularSpec.accumulate_prefixS 1://
          /KeygenM23SingularSpec.accumulate_step.
  rewrite BArray1024.get_set32E 1:/# 1:/#.
  rewrite ifF 1:/#.
  apply ih; smt().
qed.

lemma accumulate_prefix_get_processed
    (sum : BArray1024.t) (input : BArray2048.t)
    (processed j : int) :
  0 <= processed =>
  processed <= KeygenM23SingularSpec.singular_words_i =>
  0 <= j < processed =>
  BArray1024.get32
    (KeygenM23SingularSpec.accumulate_prefix sum input processed) j =
  BArray1024.get32
    (KeygenM23SingularSpec.accumulate_step input sum j) j.
proof.
move: processed.
apply intind.
+ move=> _ hj.
  smt().
+ move=> processed hprocessed ih hcap hj.
  rewrite KeygenM23SingularSpec.accumulate_prefixS 1://.
  case (j = processed) => howner.
  + subst j.
    rewrite /KeygenM23SingularSpec.accumulate_step.
    rewrite !BArray1024.get_set32E 1:/# 1:/# 1:/# 1:/# /=.
    rewrite accumulate_prefix_get_unprocessed 1:hprocessed 1:/# 1:/#.
    done.
  + rewrite
      (KeygenM23SingularIntegerSemantics.accumulate_step_frame
        input
        (KeygenM23SingularSpec.accumulate_prefix sum input processed)
        processed j) 1:/# 1:/# 1:/#.
    apply ih; smt().
qed.

lemma accumulate_fft_sqabs_get
    (sum : BArray1024.t) (input : BArray2048.t) (j : int) :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  BArray1024.get32
    (KeygenM23SingularSpec.accumulate_fft_sqabs sum input) j =
  BArray1024.get32
    (KeygenM23SingularSpec.accumulate_step input sum j) j.
proof.
move=> hj.
rewrite /KeygenM23SingularSpec.accumulate_fft_sqabs.
apply accumulate_prefix_get_processed => //.
qed.

lemma accumulate_fft_sqabs_decode_step
    (sum : BArray1024.t) (input : BArray2048.t) (j : int) :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  let real = BArray2048.get32 input (2 * j) in
  let imag = BArray2048.get32 input (2 * j + 1) in
  KeygenM23SingularBoundary.fft_accumulate_safe
    (BArray1024.get32 sum j) real imag =>
  accumulator_decode_at
    (KeygenM23SingularSpec.accumulate_fft_sqabs sum input) j =
  accumulator_decode_at sum j + fft_sqabs_decode_at input j.
proof.
move=> hj.
rewrite /=.
move=> hsafe.
have hstep :
    W32.to_sint
      (BArray1024.get32
        (KeygenM23SingularSpec.accumulate_step input sum j) j) =
    W32.to_sint (BArray1024.get32 sum j) +
      KeygenM23SingularBoundary.fft_sqabs_int
        (BArray2048.get32 input (2 * j))
        (BArray2048.get32 input (2 * j + 1)).
+ apply KeygenM23SingularIntegerSemantics.accumulate_step_at_to_sint => //.
have hsq :
    W32.to_sint (KeygenM23SingularSpec.fft_sqabs_at input j) =
    KeygenM23SingularBoundary.fft_sqabs_int
      (BArray2048.get32 input (2 * j))
      (BArray2048.get32 input (2 * j + 1)).
+ apply KeygenM23SingularIntegerSemantics.fft_sqabs_at_to_sint.
  move: hsafe.
  rewrite /KeygenM23SingularBoundary.fft_accumulate_safe /=.
  smt().
rewrite /accumulator_decode_at /fft_sqabs_decode_at
        /q16_decode_word accumulate_fft_sqabs_get 1:hj hstep hsq.
by rewrite q16_decode_intD.
qed.

lemma accumulate_fft_sqabs_decode_ideal_step
    (sum : BArray1024.t) (input : BArray2048.t) (j : int)
    (eps : real) (ideal : complex) :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  let real = BArray2048.get32 input (2 * j) in
  let imag = BArray2048.get32 input (2 * j + 1) in
  KeygenM23SingularBoundary.fft_accumulate_safe
    (BArray1024.get32 sum j) real imag =>
  cclose eps (fft_decode_at input j) ideal =>
  `|accumulator_decode_at
       (KeygenM23SingularSpec.accumulate_fft_sqabs sum input) j -
     (accumulator_decode_at sum j + cnorm2 ideal)| <=
    sqabs_ideal_error_budget eps ideal.
proof.
move=> hj.
rewrite /=.
move=> hsafe hclose.
have hdecode :=
  accumulate_fft_sqabs_decode_step sum input j hj hsafe.
have hlocal0 :=
  fft_sqabs_decode_ideal_error input j eps ideal.
have hsq :
    KeygenM23SingularBoundary.fft_sqabs_safe
      (BArray2048.get32 input (2 * j))
      (BArray2048.get32 input (2 * j + 1)).
+ move: hsafe.
  rewrite /KeygenM23SingularBoundary.fft_accumulate_safe /=.
  smt().
have hlocal := hlocal0 hsq hclose.
rewrite hdecode.
have heq :
    accumulator_decode_at sum j + fft_sqabs_decode_at input j -
      (accumulator_decode_at sum j + cnorm2 ideal) =
    fft_sqabs_decode_at input j - cnorm2 ideal by
  ring.
by rewrite heq.
qed.

op mode2_fft_endpoint_eps : real = 44833%r / 65536%r.

op mode2_actual_accumulate_prefix
    (s1 s2 : BArray8192.t) (processed : int) :
    KeygenM23SingularFFTSpec.mode2_pipeline_state =
  KeygenM23SingularFFTSpec.mode2_accumulate_prefix
    s1 s2
    KeygenMode2ParentTarget.jfft_roots
    KeygenMode2ParentTarget.jfft_brv8
    processed.

op mode2_actual_fft_output
    (s1 s2 : BArray8192.t) (slot : int) : BArray2048.t =
  let pre = mode2_actual_accumulate_prefix s1 s2 slot in
  KeygenM23SingularFFTSpec.mode2_fft
    pre.`1 s1 s2
    KeygenMode2ParentTarget.jfft_roots
    KeygenMode2ParentTarget.jfft_brv8
    slot.

op mode2_ideal_fft_at
    (s1 s2 : BArray8192.t) (slot j : int) : complex =
  odd_dft256
    (fft_coefficient_vector
      (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot))
    j.

op mode2_ideal_energy_step
    (s1 s2 : BArray8192.t) (j : int)
    (energy : real) (slot : int) : real =
  energy + cnorm2 (mode2_ideal_fft_at s1 s2 slot j).

op mode2_ideal_energy_prefix
    (s1 s2 : BArray8192.t) (processed j : int) : real =
  foldl (mode2_ideal_energy_step s1 s2 j) 0%r
    (iota_ 0 processed).

op mode2_energy_error_step
    (s1 s2 : BArray8192.t) (j : int)
    (err : real) (slot : int) : real =
  err +
    sqabs_ideal_error_budget mode2_fft_endpoint_eps
      (mode2_ideal_fft_at s1 s2 slot j).

op mode2_energy_error_prefix
    (s1 s2 : BArray8192.t) (processed j : int) : real =
  foldl (mode2_energy_error_step s1 s2 j) 0%r
    (iota_ 0 processed).

op mode2_accumulator_inputs_bound2
    (s1 s2 : BArray8192.t) : bool =
  forall slot,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    fft_coefficient_bound
      (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot) 2.

op actual_mode2_accumulate_safe_trace
    (s1 s2 : BArray8192.t) (processed : int) : bool =
  forall slot j,
    0 <= slot < processed =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    let pre = mode2_actual_accumulate_prefix s1 s2 slot in
    let input = mode2_actual_fft_output s1 s2 slot in
    KeygenM23SingularBoundary.fft_accumulate_safe
      (BArray1024.get32 pre.`2 j)
      (BArray2048.get32 input (2 * j))
      (BArray2048.get32 input (2 * j + 1)).

lemma mode2_ideal_energy_prefix0
    (s1 s2 : BArray8192.t) (j : int) :
  mode2_ideal_energy_prefix s1 s2 0 j = 0%r.
proof. by rewrite /mode2_ideal_energy_prefix iota0. qed.

lemma mode2_ideal_energy_prefixS
    (s1 s2 : BArray8192.t) (processed j : int) :
  0 <= processed =>
  mode2_ideal_energy_prefix s1 s2 (processed + 1) j =
    mode2_ideal_energy_prefix s1 s2 processed j +
      cnorm2 (mode2_ideal_fft_at s1 s2 processed j).
proof.
move=> hprocessed.
by rewrite /mode2_ideal_energy_prefix iotaSr 1:hprocessed foldl_rcons
           /mode2_ideal_energy_step.
qed.

lemma mode2_energy_error_prefix0
    (s1 s2 : BArray8192.t) (j : int) :
  mode2_energy_error_prefix s1 s2 0 j = 0%r.
proof. by rewrite /mode2_energy_error_prefix iota0. qed.

lemma mode2_energy_error_prefixS
    (s1 s2 : BArray8192.t) (processed j : int) :
  0 <= processed =>
  mode2_energy_error_prefix s1 s2 (processed + 1) j =
    mode2_energy_error_prefix s1 s2 processed j +
      sqabs_ideal_error_budget mode2_fft_endpoint_eps
        (mode2_ideal_fft_at s1 s2 processed j).
proof.
move=> hprocessed.
by rewrite /mode2_energy_error_prefix iotaSr 1:hprocessed foldl_rcons
           /mode2_energy_error_step.
qed.

lemma actual_mode2_accumulate_safe_trace_prefix
    (s1 s2 : BArray8192.t) (processed : int) :
  0 <= processed =>
  actual_mode2_accumulate_safe_trace s1 s2 (processed + 1) =>
  actual_mode2_accumulate_safe_trace s1 s2 processed.
proof.
move=> hprocessed htrace.
rewrite /actual_mode2_accumulate_safe_trace in htrace.
rewrite /actual_mode2_accumulate_safe_trace.
move=> slot j hslot hj.
have hslot' : 0 <= slot < processed + 1 by smt().
exact (htrace slot j hslot' hj).
qed.

lemma mode2_actual_fft_output_close_bound2
    (s1 s2 : BArray8192.t) (slot j : int) :
  mode2_accumulator_inputs_bound2 s1 s2 =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  cclose mode2_fft_endpoint_eps
    (fft_decode_at (mode2_actual_fft_output s1 s2 slot) j)
    (mode2_ideal_fft_at s1 s2 slot j).
proof.
move=> hinputs hslot hj.
have hclose :=
  actual_fft_full_odd_dft256_close_bound2
    (mode2_actual_accumulate_prefix s1 s2 slot).`1
    (KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot)
    j hj (hinputs slot hslot).
rewrite /mode2_actual_fft_output
        /KeygenM23SingularFFTSpec.mode2_fft
        /actual_fft_init_data
        /mode2_ideal_fft_at
        /mode2_fft_endpoint_eps.
exact hclose.
qed.

lemma mode2_actual_accumulate_prefixS
    (s1 s2 : BArray8192.t) (processed : int) :
  0 <= processed =>
  mode2_actual_accumulate_prefix s1 s2 (processed + 1) =
    KeygenM23SingularFFTSpec.mode2_accumulate_step
      s1 s2
      KeygenMode2ParentTarget.jfft_roots
      KeygenMode2ParentTarget.jfft_brv8
      (mode2_actual_accumulate_prefix s1 s2 processed)
      processed.
proof.
move=> hprocessed.
rewrite /mode2_actual_accumulate_prefix.
exact
  (KeygenM23SingularFFTSpec.mode2_accumulate_prefixS
    s1 s2
    KeygenMode2ParentTarget.jfft_roots
    KeygenMode2ParentTarget.jfft_brv8
    processed hprocessed).
qed.

lemma mode2_actual_accumulate_prefix_error
    (s1 s2 : BArray8192.t) (processed j : int) :
  0 <= processed =>
  processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  mode2_accumulator_inputs_bound2 s1 s2 =>
  actual_mode2_accumulate_safe_trace s1 s2 processed =>
  `|accumulator_decode_at
       (mode2_actual_accumulate_prefix s1 s2 processed).`2 j -
     mode2_ideal_energy_prefix s1 s2 processed j| <=
    mode2_energy_error_prefix s1 s2 processed j.
proof.
move: processed.
apply intind.
+ move=> _ hj _ _.
  rewrite /mode2_actual_accumulate_prefix
          KeygenM23SingularFFTSpec.mode2_accumulate_prefix0 /=.
  rewrite clear_sum_decode_at_zero 1:hj
          mode2_ideal_energy_prefix0 mode2_energy_error_prefix0.
  by rewrite subrr normr0.
+ move=> processed hprocessed ih hcap hj hinputs htrace.
  have hprev_trace :=
    actual_mode2_accumulate_safe_trace_prefix
      s1 s2 processed hprocessed htrace.
  have hprev_cap :
      processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i by
    smt().
  have hprev := ih hprev_cap hj hinputs hprev_trace.
  have hslot :
      0 <= processed < KeygenM23SingularFFTSpec.mode2_slice_count_i by
    smt().
  have hslotnext : 0 <= processed < processed + 1 by smt().
  have hsafe := htrace processed j hslotnext hj.
  have hclose :=
    mode2_actual_fft_output_close_bound2
      s1 s2 processed j hinputs hslot hj.
  have hstep :=
    accumulate_fft_sqabs_decode_ideal_step
      (mode2_actual_accumulate_prefix s1 s2 processed).`2
      (mode2_actual_fft_output s1 s2 processed)
      j mode2_fft_endpoint_eps
      (mode2_ideal_fft_at s1 s2 processed j)
      hj hsafe hclose.
  rewrite mode2_actual_accumulate_prefixS 1:hprocessed.
  rewrite /KeygenM23SingularFFTSpec.mode2_accumulate_step /=.
  rewrite mode2_ideal_energy_prefixS 1:hprocessed
          mode2_energy_error_prefixS 1:hprocessed.
  have hshift :
      `|accumulator_decode_at
           (mode2_actual_accumulate_prefix s1 s2 processed).`2 j +
         cnorm2 (mode2_ideal_fft_at s1 s2 processed j) -
        (mode2_ideal_energy_prefix s1 s2 processed j +
         cnorm2 (mode2_ideal_fft_at s1 s2 processed j))| =
      `|accumulator_decode_at
           (mode2_actual_accumulate_prefix s1 s2 processed).`2 j -
         mode2_ideal_energy_prefix s1 s2 processed j| by
    congr; ring.
  have htri :=
    ler_dist_add
      (accumulator_decode_at
         (mode2_actual_accumulate_prefix s1 s2 processed).`2 j +
       cnorm2 (mode2_ideal_fft_at s1 s2 processed j))
      (accumulator_decode_at
        (KeygenM23SingularSpec.accumulate_fft_sqabs
          (mode2_actual_accumulate_prefix s1 s2 processed).`2
          (mode2_actual_fft_output s1 s2 processed)) j)
      (mode2_ideal_energy_prefix s1 s2 processed j +
       cnorm2 (mode2_ideal_fft_at s1 s2 processed j)).
  rewrite hshift in htri.
  have hbudget :
      sqabs_ideal_error_budget mode2_fft_endpoint_eps
        (mode2_ideal_fft_at s1 s2 processed j) +
      mode2_energy_error_prefix s1 s2 processed j =
      mode2_energy_error_prefix s1 s2 processed j +
      sqabs_ideal_error_budget mode2_fft_endpoint_eps
        (mode2_ideal_fft_at s1 s2 processed j) by
    ring.
  rewrite -hbudget.
  apply
    (ler_trans
      (`|accumulator_decode_at
           (KeygenM23SingularSpec.accumulate_fft_sqabs
             (mode2_actual_accumulate_prefix s1 s2 processed).`2
             (mode2_actual_fft_output s1 s2 processed)) j -
         (accumulator_decode_at
            (mode2_actual_accumulate_prefix s1 s2 processed).`2 j +
          cnorm2 (mode2_ideal_fft_at s1 s2 processed j))| +
       `|accumulator_decode_at
            (mode2_actual_accumulate_prefix s1 s2 processed).`2 j -
          mode2_ideal_energy_prefix s1 s2 processed j|)).
  + exact htri.
  apply ler_add.
  + exact hstep.
  exact hprev.
qed.

lemma mode2_actual_accumulate_full_error
    (s1 s2 : BArray8192.t) (j : int) :
  0 <= j < KeygenM23SingularSpec.singular_words_i =>
  mode2_accumulator_inputs_bound2 s1 s2 =>
  actual_mode2_accumulate_safe_trace
    s1 s2 KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  `|accumulator_decode_at
       (KeygenM23SingularFFTSpec.mode2_accumulate
         s1 s2
         KeygenMode2ParentTarget.jfft_roots
         KeygenMode2ParentTarget.jfft_brv8) j -
     mode2_ideal_energy_prefix
       s1 s2 KeygenM23SingularFFTSpec.mode2_slice_count_i j| <=
    mode2_energy_error_prefix
      s1 s2 KeygenM23SingularFFTSpec.mode2_slice_count_i j.
proof.
move=> hj hinputs htrace.
have h :=
  mode2_actual_accumulate_prefix_error
    s1 s2 KeygenM23SingularFFTSpec.mode2_slice_count_i j
    _ _ hj hinputs htrace.
+ rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i.
  smt().
+ done.
rewrite /mode2_actual_accumulate_prefix
        /KeygenM23SingularFFTSpec.mode2_accumulate in h.
exact h.
qed.

end KeygenM23SingularFFTAccumulatorBridge.
