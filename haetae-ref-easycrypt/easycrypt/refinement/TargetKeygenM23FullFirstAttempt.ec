require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray32 BArray128 BArray2048 BArray2080 BArray2752
               BArray8192 BArray32768 SBArray128_32
               KeygenMode2ParentTarget
               KeygenSamplerCallersSpec KeygenM23MatrixSpec
               KeygenM23FinalizeSpec
               KeygenM23FinalizeArraySemantics
               KeygenM23FinalizeHAETAEBridge
               KeygenM23ComplexReal
               KeygenM23IdealRootDFT
               KeygenM23SingularFFTSpec
               KeygenM23SingularFFTInitBridge
               KeygenM23SingularFFTBounds
               KeygenM23SingularFFTScheduleBounds
               KeygenM23SingularFFTGlobalTrace
               KeygenM23SingularFFTErrorTrace
               TargetKeygenMode2ParentComposition
               TargetKeygenM23FinalizeComposition
               TargetKeygenM23FinalizeSemanticComposition
               TargetKeygenM23Singular
               TargetKeygenM23SingularFFTInputBounds.

import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTGlobalTrace
  KeygenM23SingularFFTErrorTrace
  TargetKeygenM23SingularFFTInputBounds.

theory TargetKeygenM23FullFirstAttempt.

module Parent = KeygenMode2ParentTarget.M.

type first_attempt_trace = [
  FirstAttemptTrace of
    bool &
    BArray128.t & BArray32768.t &
    BArray8192.t & BArray8192.t & BArray8192.t &
    BArray8192.t & BArray8192.t & BArray8192.t & BArray8192.t &
    W64.t & W64.t & W64.t & W64.t
].

(* The initial reject word is one, so the first iteration is unconditional.
   This mirror peels that iteration through the checked observer, normalizing
   its identity protection calls, and then retains the singular guard,
   unchanged retry tail, and packing calls. *)
module Mode2FullFirstAttempt = {
  proc run
      (vkp : BArray2080.t, skp : BArray2752.t,
       seedp : BArray32.t) :
      (BArray2080.t * BArray2752.t) * first_attempt_trace = {
    var seedbuf : BArray128.t;
    var mat : BArray32768.t;
    var avec : BArray8192.t;
    var bp : BArray8192.t;
    var s1 : BArray8192.t;
    var s1hat : BArray8192.t;
    var s2 : BArray8192.t;
    var sampled_s2 : BArray8192.t;
    var pre_bp : BArray8192.t;
    var counter : W64.t;
    var kr : W64.t;
    var mr : W64.t;
    var vkbr : W64.t;
    var reject : W64.t;
    var nonce : W64.t;
    var count : W64.t;
    var ms : W64.t;
    var sv : W64.t;
    var bound : W64.t;
    var rhop : BArray32.t;
    var keyp : BArray32.t;
    var first_trace : first_attempt_trace;

    kr <- W64.of_int 2;
    mr <- W64.of_int 3;
    vkbr <- W64.of_int 992;
    (seedbuf, mat, avec, s1, sampled_s2, counter,
     pre_bp, s1hat, bp, s2) <@
      TargetKeygenM23FinalizeComposition.CheckedMode2ParentM23Finalize.run
        (witness, witness, witness, witness, witness,
         witness, witness, seedp);

    sv <@ Parent._singular_full (s1, s2, 3, 2, 5, 58, 24);
    bound <- W64.of_int 611098;
    ms <- init_msf;
    sv <- protect_64 sv ms;
    bound <- protect_64 bound ms;
    reject <- W64.zero;
    if (bound \ult sv) {
      reject <- W64.one;
    } else {
    }
    first_trace <-
      FirstAttemptTrace
        (reject = W64.zero)
        seedbuf mat avec s1 sampled_s2
        pre_bp s1hat bp s2
        counter sv bound reject;

    while (reject <> W64.zero) {
      s1 <@ Parent._kp_polyvec_expand_eta
        (s1, seedbuf, counter, mr);
      nonce <- counter;
      nonce <- nonce + mr;
      s2 <@ Parent._kp_polyvec_expand_eta
        (s2, seedbuf, nonce, kr);
      counter <- counter + mr;
      counter <- counter + kr;
      (bp, s1hat) <@ Parent._kp_m23_matrix
        (bp, s1hat, mat, s1, kr, mr);
      count <- kr;
      count <- count * W64.of_int 256;
      ms <- init_msf;
      bp <- protect_ptr bp ms;
      s1 <- protect_ptr s1 ms;
      s2 <- protect_ptr s2 ms;
      avec <- protect_ptr avec ms;
      seedbuf <- protect_ptr seedbuf ms;
      kr <- protect_64 kr ms;
      mr <- protect_64 mr ms;
      count <- protect_64 count ms;
      (bp, s2) <@ Parent._keypair_finalize_m23
        (bp, s2, avec, count);
      sv <@ Parent._singular_full (s1, s2, 3, 2, 5, 58, 24);
      bound <- W64.of_int 611098;
      ms <- init_msf;
      sv <- protect_64 sv ms;
      bound <- protect_64 bound ms;
      reject <- W64.zero;
      if (bound \ult sv) {
        reject <- W64.one;
      } else {
      }
    }

    rhop <- SBArray128_32.get_sub8 seedbuf 0;
    keyp <- SBArray128_32.get_sub8 seedbuf 96;
    vkp <@ Parent._pack_vk_m23
      (vkp, bp, rhop, kr);
    skp <@ Parent._pack_sk_m23
      (skp, vkp, s1, s2, keyp,
       vkbr, mr, kr);
    return ((vkp, skp), first_trace);
  }
}.

op first_attempt_snapshot_facts
    (raw_seed : BArray32.t)
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace
      accepted seedbuf mat
      avec s1 sampled_s2 pre_bp s1hat final_bp final_s2
      counter sv bound reject =>
    TargetKeygenM23FinalizeComposition.mode2_sampler_facts
      seedbuf mat avec s1 sampled_s2 counter
      witness witness witness witness raw_seed /\
    TargetKeygenM23FinalizeComposition.mode2_m23_facts
      mat s1 pre_bp s1hat
      witness witness /\
    KeygenM23FinalizeSpec.finalize_output
      pre_bp sampled_s2 avec final_bp final_s2 /\
    KeygenM23FinalizeArraySemantics.finalize_semantic_output
      pre_bp sampled_s2 avec final_bp final_s2 /\
    KeygenM23FinalizeHAETAEBridge.finalize_haetae_semantic_output
      pre_bp sampled_s2 avec final_bp final_s2 /\
    sv =
      KeygenM23SingularFFTSpec.mode2_singular_word
        s1 final_s2
        KeygenMode2ParentTarget.jfft_roots
        KeygenMode2ParentTarget.jfft_brv8 /\
    counter = W64.of_int 5 /\
    bound = W64.of_int 611098 /\
    reject = (if bound \ult sv then W64.one else W64.zero) /\
    accepted = (reject = W64.zero).

op first_attempt_trace_accepted
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace accepted _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      accepted.

op first_attempt_trace_score
    (trace : first_attempt_trace) : W64.t =
  with trace =
    FirstAttemptTrace _ _ _ _ _ _ _ _ _ _ _ sv _ _ =>
      sv.

op first_attempt_trace_score_within_bound
    (trace : first_attempt_trace) : bool =
  W64.to_uint (first_attempt_trace_score trace) <= 611098.

op first_attempt_trace_guard
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace _ _ _ _ _ _ _ _ _ _ _ sv bound _ =>
      ! (bound \ult sv).

op first_attempt_trace_fft_inputs_bound2
    (trace : first_attempt_trace) : bool =
  with trace =
    FirstAttemptTrace _ _ _ _ s1 _ _ _ _ final_s2 _ _ _ _ =>
      mode2_fft_inputs_bound2 s1 final_s2.

(* The immutable first-attempt snapshot closes the input premise for each of
   the three s1 and two finalized-s2 slices.  These corollaries do not describe
   later retry attempts or the squared-magnitude accumulator. *)

lemma mode2_singular_reject_zeroE (sv : W64.t) :
  ((if W64.of_int 611098 \ult sv then W64.one else W64.zero) =
     W64.zero) <=>
  W64.to_uint sv <= 611098.
proof.
have hone : W64.one <> W64.zero by
  rewrite W64.to_uint_eq W64.to_uint1 W64.to_uint0.
case (W64.of_int 611098 \ult sv) => hcmp.
+ move: (TargetKeygenM23Singular.mode2_singular_guardE sv).
  by rewrite hcmp /= hone.
+ move: (TargetKeygenM23Singular.mode2_singular_guardE sv).
  by rewrite hcmp /=.
qed.

lemma first_attempt_snapshot_score_guardE
    (seed0 : BArray32.t) (trace : first_attempt_trace) :
  first_attempt_snapshot_facts seed0 trace =>
  (first_attempt_trace_accepted trace <=>
   first_attempt_trace_score_within_bound trace).
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /first_attempt_snapshot_facts
        /first_attempt_trace_accepted
        /first_attempt_trace_score_within_bound
        /first_attempt_trace_score /=.
move=> [hsampler [hm23 [hfinal [harray [hhaetae
  [hscore [hcounter [hbound [hreject haccept]]]]]]]]].
rewrite haccept hreject hbound.
exact (mode2_singular_reject_zeroE sv).
qed.

lemma first_attempt_snapshot_trace_guardE
    (seed0 : BArray32.t) (trace : first_attempt_trace) :
  first_attempt_snapshot_facts seed0 trace =>
  (first_attempt_trace_guard trace <=>
   first_attempt_trace_score_within_bound trace).
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /first_attempt_snapshot_facts
        /first_attempt_trace_guard
        /first_attempt_trace_score_within_bound
        /first_attempt_trace_score /=.
move=> [hsampler [hm23 [hfinal [harray [hhaetae
  [hscore [hcounter [hbound [hreject haccept]]]]]]]]].
rewrite hbound.
exact (TargetKeygenM23Singular.mode2_singular_guardE sv).
qed.

lemma first_attempt_snapshot_fft_inputs_bound2
    (seed0 : BArray32.t) (trace : first_attempt_trace) :
  first_attempt_snapshot_facts seed0 trace =>
  first_attempt_trace_fft_inputs_bound2 trace.
proof.
case: trace =>
  accepted seedbuf mat avec s1 sampled_s2 pre_bp s1hat
  final_bp final_s2 counter sv bound reject.
rewrite /first_attempt_snapshot_facts
        /first_attempt_trace_fft_inputs_bound2 /=.
move=> [hsampler [_ [_ [harray _]]]].
exact
  (mode2_fft_inputs_bound2_of_mode2_sampler_finalize
    seedbuf mat avec s1 sampled_s2 counter
    witness witness witness witness seed0
    pre_bp final_bp final_s2 hsampler harray).
qed.

lemma first_attempt_snapshot_fft_slot_schedule_safe
    (seed0 : BArray32.t)
    accepted seedbuf mat avec s1 sampled_s2
    pre_bp s1hat final_bp final_s2
    counter sv bound reject
    (data : BArray2048.t) (slot : int) :
  first_attempt_snapshot_facts seed0
    (FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2
      pre_bp s1hat final_bp final_s2
      counter sv bound reject) =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  KeygenM23SingularFFTGlobalTrace.actual_fft_schedule_safe
    data (KeygenM23SingularFFTSpec.mode2_slice s1 final_s2 slot).
proof.
move=> hsnapshot hslot.
have hinputs :=
  first_attempt_snapshot_fft_inputs_bound2 seed0
    (FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2
      pre_bp s1hat final_bp final_s2
      counter sv bound reject) hsnapshot.
rewrite /first_attempt_trace_fft_inputs_bound2 in hinputs.
exact
  (mode2_fft_slot_schedule_safe
    data s1 final_s2 slot hinputs hslot).
qed.

lemma first_attempt_snapshot_fft_slot_full_word_bound2
    (seed0 : BArray32.t)
    accepted seedbuf mat avec s1 sampled_s2
    pre_bp s1hat final_bp final_s2
    counter sv bound reject
    (data : BArray2048.t) (slot : int) :
  first_attempt_snapshot_facts seed0
    (FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2
      pre_bp s1hat final_bp final_s2
      counter sv bound reject) =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  KeygenM23SingularFFTBounds.fft_word_bound
    (KeygenM23SingularFFTSpec.fft_full
      (KeygenM23SingularFFTScheduleBounds.actual_fft_init_data_bound2
        data (KeygenM23SingularFFTSpec.mode2_slice s1 final_s2 slot))
      KeygenMode2ParentTarget.jfft_roots)
    859963392.
proof.
move=> hsnapshot hslot.
have hinputs :=
  first_attempt_snapshot_fft_inputs_bound2 seed0
    (FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2
      pre_bp s1hat final_bp final_s2
      counter sv bound reject) hsnapshot.
rewrite /first_attempt_trace_fft_inputs_bound2 in hinputs.
exact
  (mode2_fft_slot_full_word_bound2
    data s1 final_s2 slot hinputs hslot).
qed.

lemma first_attempt_snapshot_fft_slot_full_odd_dft256_close_bound2
    (seed0 : BArray32.t)
    accepted seedbuf mat avec s1 sampled_s2
    pre_bp s1hat final_bp final_s2
    counter sv bound reject
    (data : BArray2048.t) (slot j : int) :
  first_attempt_snapshot_facts seed0
    (FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2
      pre_bp s1hat final_bp final_s2
      counter sv bound reject) =>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  0 <= j < 256 =>
  cclose (44833%r / 65536%r)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_full
        (actual_fft_init_data data
          (KeygenM23SingularFFTSpec.mode2_slice
            s1 final_s2 slot))
        KeygenMode2ParentTarget.jfft_roots)
      j)
    (odd_dft256
      (fft_coefficient_vector
        (KeygenM23SingularFFTSpec.mode2_slice
          s1 final_s2 slot))
      j).
proof.
move=> hsnapshot hslot hj.
have hinputs :=
  first_attempt_snapshot_fft_inputs_bound2 seed0
    (FirstAttemptTrace
      accepted seedbuf mat avec s1 sampled_s2
      pre_bp s1hat final_bp final_s2
      counter sv bound reject) hsnapshot.
rewrite /first_attempt_trace_fft_inputs_bound2 in hinputs.
exact
  (mode2_fft_slot_full_odd_dft256_close_bound2
    data s1 final_s2 slot j hinputs hslot hj).
qed.

lemma mode2_full_first_attempt_equiv :
  equiv [
    Parent._keypair_full_m23 ~ Mode2FullFirstAttempt.run :
    vkp{1} = vkp{2} /\ skp{1} = skp{2} /\ seedp{1} = seedp{2} /\
    k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
    best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
    singular_bound{1} = 611098
    ==>
    res{1} = res{2}.`1].
proof.
proc.
inline
  TargetKeygenM23FinalizeComposition.CheckedMode2ParentM23Finalize.run.
inline
  TargetKeygenMode2ParentComposition.CheckedMode2ParentSamplerPrefix.run.
unroll {1} ^while.
rcondt {1} ^if.
+ auto; call (_ : true); auto; call (_ : true); auto;
  call (_ : true); auto.
  move=> &hr _.
  rewrite /W64.one /W64.zero.
  smt(W64.of_uintK).
wp.
simplify.
sp 26 17.
seq 3 3 :
  (={vkp, skp, seedp} /\
   raw_seed0{2} = seedp{2} /\
   seedbufp{1} = seedbuf1{2} /\
   matp{1} = mat1{2} /\
   ap{1} = avec1{2} /\
   s1p{1} = s11{2} /\
   s2p{1} = s21{2} /\
   bp{1} = bp0{2} /\
   s1hatp{1} = s1hatp{2} /\
   kr{1} = kr{2} /\ mr{1} = mr{2} /\ vkbr{1} = vkbr{2} /\
   kr{1} = W64.of_int 2 /\ mr{1} = W64.of_int 3 /\
   vkbr{1} = W64.of_int 992 /\
   k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
   best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
   singular_bound{1} = 611098).
+ call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  auto => />;
    rewrite /KeygenSamplerCallersSpec.mode2_k_i
            /KeygenSamplerCallersSpec.mode2_m_i /=.
seq 6 5 :
  (={vkp, skp, seedp} /\
   raw_seed0{2} = seedp{2} /\
   seedbufp{1} = seedbuf1{2} /\
   matp{1} = mat1{2} /\
   ap{1} = avec1{2} /\
   s1p{1} = s11{2} /\
   s2p{1} = s21{2} /\
   bp{1} = bp0{2} /\
   s1hatp{1} = s1hatp{2} /\
   counter{1} = counter1{2} /\
   kr{1} = kr{2} /\ mr{1} = mr{2} /\ vkbr{1} = vkbr{2} /\
   kr{1} = W64.of_int 2 /\ mr{1} = W64.of_int 3 /\
   vkbr{1} = W64.of_int 992 /\
   k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
   best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
   singular_bound{1} = 611098).
+ call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  auto => />;
    rewrite /KeygenSamplerCallersSpec.mode2_k_i
            /KeygenSamplerCallersSpec.mode2_m_i /=.
seq 2 3 :
  (={vkp, skp, seedp} /\
   raw_seed0{2} = seedp{2} /\
   seedbufp{1} = seedbuf0{2} /\
   matp{1} = mat0{2} /\
   ap{1} = avec0{2} /\
   s1p{1} = s10{2} /\
   s2p{1} = s20{2} /\
   bp{1} = bp0{2} /\
   s1hatp{1} = s1hatp{2} /\
   counter{1} = counter0{2} /\
   kr{1} = kr{2} /\ mr{1} = mr{2} /\ vkbr{1} = vkbr{2} /\
   kr{1} = W64.of_int 2 /\ mr{1} = W64.of_int 3 /\
   vkbr{1} = W64.of_int 992 /\
   k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
   best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
   singular_bound{1} = 611098).
+ auto => />;
    rewrite /KeygenSamplerCallersSpec.mode2_k_i
            /KeygenSamplerCallersSpec.mode2_m_i /=.
seq 1 1 :
  (={vkp, skp, seedp} /\
   raw_seed0{2} = seedp{2} /\
   seedbufp{1} = seedbuf0{2} /\
   matp{1} = mat0{2} /\
   ap{1} = avec0{2} /\
   s1p{1} = s10{2} /\
   s2p{1} = s20{2} /\
   bp{1} = bp0{2} /\
   s1hatp{1} = s1hatp{2} /\
   counter{1} = counter0{2} /\
   kr{1} = kr{2} /\ mr{1} = mr{2} /\ vkbr{1} = vkbr{2} /\
   kr{1} = W64.of_int 2 /\ mr{1} = W64.of_int 3 /\
   vkbr{1} = W64.of_int 992 /\
   k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
   best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
   singular_bound{1} = 611098).
+ call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  auto => />;
    rewrite /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.mode2_cols_i /=.
seq 12 5 :
  (={vkp, skp, seedp} /\
   seedbufp{1} = seedbuf{2} /\
   matp{1} = mat{2} /\
   ap{1} = avec{2} /\
   s1p{1} = s1{2} /\
   s2p{1} = s2{2} /\
   bp{1} = bp{2} /\
   s1hatp{1} = s1hat{2} /\
   counter{1} = counter{2} /\
   kr{1} = kr{2} /\ mr{1} = mr{2} /\ vkbr{1} = vkbr{2} /\
   kr{1} = W64.of_int 2 /\ mr{1} = W64.of_int 3 /\
   vkbr{1} = W64.of_int 992 /\
   k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
   best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
   singular_bound{1} = 611098).
+ wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  auto => />;
    rewrite /KeygenM23MatrixSpec.mode2_b_words_i
            /KeygenM23MatrixSpec.mode2_rows_i
            /KeygenM23MatrixSpec.poly_words_i /=.
seq 7 8 :
  (={vkp, skp, seedp, counter, kr, mr, vkbr, sv, bound, reject, bp} /\
   seedbufp{1} = seedbuf{2} /\
   matp{1} = mat{2} /\
   ap{1} = avec{2} /\
   s1p{1} = s1{2} /\
   s2p{1} = s2{2} /\
   s1hatp{1} = s1hat{2} /\
   kr{1} = W64.of_int 2 /\ mr{1} = W64.of_int 3 /\
   vkbr{1} = W64.of_int 992 /\
   k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
   best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
   singular_bound{1} = 611098).
+ wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  auto.
sim (: true): (={vkp, skp}).
while
  (={vkp, skp, counter, kr, mr, vkbr, sv, bound, reject, bp} /\
   seedbufp{1} = seedbuf{2} /\
   matp{1} = mat{2} /\
   ap{1} = avec{2} /\
   s1p{1} = s1{2} /\
   s2p{1} = s2{2} /\
   s1hatp{1} = s1hat{2} /\
   kr{1} = W64.of_int 2 /\ mr{1} = W64.of_int 3 /\
   vkbr{1} = W64.of_int 992 /\
   k{1} = 2 /\ m{1} = 3 /\ vkbytes{1} = 992 /\
   best_count{1} = 5 /\ tau{1} = 58 /\ rem{1} = 24 /\
   singular_bound{1} = 611098).
+ wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  wp.
  call (_ : ={arg} ==> ={res}).
  + by proc; sim.
  auto.
auto.
qed.

lemma mode2_full_first_attempt_snapshot_correct
    (seed0 : BArray32.t) :
  hoare [
    Mode2FullFirstAttempt.run :
    seedp = seed0
    ==>
    first_attempt_snapshot_facts seed0 res.`2].
proof.
proc.
seq 4 :
  (TargetKeygenM23FinalizeComposition.mode2_sampler_facts
     seedbuf mat avec s1 sampled_s2 counter
     witness witness witness witness seed0 /\
   TargetKeygenM23FinalizeComposition.mode2_m23_facts
     mat s1 pre_bp s1hat witness witness /\
   KeygenM23FinalizeSpec.finalize_output
     pre_bp sampled_s2 avec bp s2 /\
   KeygenM23FinalizeArraySemantics.finalize_semantic_output
     pre_bp sampled_s2 avec bp s2 /\
   KeygenM23FinalizeHAETAEBridge.finalize_haetae_semantic_output
     pre_bp sampled_s2 avec bp s2).
+ call
    (TargetKeygenM23FinalizeSemanticComposition.checked_mode2_parent_m23_finalize_haetae_correct
       witness witness witness witness witness witness witness seed0).
  auto => />.
wp.
call (_ : true).
auto.
wp.
call (_ : true).
auto.
wp.
while (first_attempt_snapshot_facts seed0 first_trace).
+ wp.
  call (_ : true).
  auto.
  wp.
  call (_ : true).
  auto.
  wp.
  call (_ : true).
  auto.
  wp.
  call (_ : true).
  auto.
  wp.
  call (_ : true).
  auto.
  auto.
wp.
ecall
  (TargetKeygenM23Singular.singular_full_mode2_word_exact
     s1 s2).
auto.
auto => />;
  rewrite /first_attempt_snapshot_facts /SLH64.protect_64.
qed.

lemma mode2_full_first_attempt_fft_inputs_bound2_correct
    (seed0 : BArray32.t) :
  hoare [
    Mode2FullFirstAttempt.run :
    seedp = seed0
    ==>
    first_attempt_snapshot_facts seed0 res.`2 /\
    first_attempt_trace_fft_inputs_bound2 res.`2].
proof.
conseq (mode2_full_first_attempt_snapshot_correct seed0).
move=> &hr hpre result hsnapshot.
split; first exact hsnapshot.
exact
  (first_attempt_snapshot_fft_inputs_bound2
    seed0 result.`2 hsnapshot).
qed.

lemma mode2_full_first_attempt_score_guard_correct
    (seed0 : BArray32.t) :
  hoare [
    Mode2FullFirstAttempt.run :
    seedp = seed0
    ==>
    first_attempt_snapshot_facts seed0 res.`2 /\
    (first_attempt_trace_accepted res.`2 <=>
     first_attempt_trace_score_within_bound res.`2)].
proof.
conseq (mode2_full_first_attempt_snapshot_correct seed0).
move=> &hr hpre result hsnapshot.
split; first exact hsnapshot.
exact
  (first_attempt_snapshot_score_guardE
     seed0 result.`2 hsnapshot).
qed.

lemma mode2_full_first_attempt_accepted_correct
    (seed0 : BArray32.t) :
  hoare [
    Mode2FullFirstAttempt.run :
    seedp = seed0
    ==>
    first_attempt_trace_accepted res.`2 =>
      first_attempt_snapshot_facts seed0 res.`2 /\
      first_attempt_trace_guard res.`2].
proof.
conseq (mode2_full_first_attempt_score_guard_correct seed0).
move=> &hr hpre result [hsnapshot haccept_score] haccept.
split; first exact hsnapshot.
have hguard_score :
    first_attempt_trace_guard result.`2 <=>
    first_attempt_trace_score_within_bound result.`2.
+ exact
    (first_attempt_snapshot_trace_guardE
       seed0 result.`2 hsnapshot).
smt().
qed.

end TargetKeygenM23FullFirstAttempt.
