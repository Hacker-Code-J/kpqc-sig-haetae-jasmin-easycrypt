require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray128 BArray8192 BArray32768.
require import KeygenMode2ParentTarget
               KeygenSamplerCallersSpec
               KeygenM23MatrixSpec
               TargetKeygenM23Matrix
               TargetKeygenM23Finalize
               TargetKeygenM23SingularTotality
               Mode2FaithfulSecurityRetryEtaProgressPostFreeze.

theory Mode2FaithfulSecurityCheckedRetryStepPostFreeze.

module Parent = KeygenMode2ParentTarget.M.

(* This proof-only observer mirrors exactly one body iteration of the retry
   loop in [TargetKeygenM23FullFirstAttempt.Mode2FullFirstAttempt.run].
   It does not claim semantic correctness, distribution preservation,
   acceptance probability, whole-loop termination, packing correctness,
   or equality with [HAETAE.kg].  It only exposes one checked retry step,
   its counter transition, and its conditional losslessness premise. *)
module CheckedMode2RetryStep = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t, counter : W64.t)
      : BArray128.t * BArray32768.t *
        BArray8192.t * BArray8192.t * BArray8192.t * W64.t *
        BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8192.t *
        W64.t * W64.t * W64.t = {
    var kr : W64.t;
    var mr : W64.t;
    var nonce : W64.t;
    var count : W64.t;
    var ms : W64.t;
    var sampled_s2 : BArray8192.t;
    var pre_bp : BArray8192.t;
    var sv : W64.t;
    var bound : W64.t;
    var reject : W64.t;

    kr <- W64.of_int 2;
    mr <- W64.of_int 3;
    s1 <@ Parent._kp_polyvec_expand_eta (s1, seedbuf, counter, mr);
    nonce <- counter;
    nonce <- nonce + mr;
    s2 <@ Parent._kp_polyvec_expand_eta (s2, seedbuf, nonce, kr);
    counter <- counter + mr;
    counter <- counter + kr;
    (bp, s1hatp) <@ Parent._kp_m23_matrix
      (bp, s1hatp, mat, s1, kr, mr);
    pre_bp <- bp;
    sampled_s2 <- s2;
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

    return
      (seedbuf, mat, avec, s1, sampled_s2, counter,
       pre_bp, s1hatp, bp, s2, sv, bound, reject);
  }
}.

lemma checked_mode2_retry_step_counterE retry :
  Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_retry_eta_nowrap retry =>
  W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i retry) +
    (W64.of_int KeygenSamplerCallersSpec.mode2_m_i +
     W64.of_int KeygenSamplerCallersSpec.mode2_k_i) =
  W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i (retry + 1)).
proof.
move=> hnowrap.
have hspan :
    W64.of_int KeygenSamplerCallersSpec.mode2_m_i +
    W64.of_int KeygenSamplerCallersSpec.mode2_k_i =
    W64.of_int KeygenSamplerCallersSpec.mode2_retry_span_i.
+ rewrite /KeygenSamplerCallersSpec.mode2_retry_span_i
          /KeygenSamplerCallersSpec.mode2_m_i
          /KeygenSamplerCallersSpec.mode2_k_i
          -W64.of_intD.
  congr.
  ring.
rewrite hspan.
exact
  (Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_retry_counter_plus5E retry hnowrap).
qed.

lemma checked_mode2_retry_step_progress_ll
    (seed0 : BArray128.t) retry (eta_limit : int -> int) :
  phoare [CheckedMode2RetryStep.run :
    seedbuf = seed0 /\
    counter =
      W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i retry) /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_nowrap retry /\
    Mode2FaithfulSecurityRetryEtaProgressPostFreeze
      .mode2_retry_eta_progress seed0 retry eta_limit
    ==>
    res.`6 =
      W64.of_int
        (KeygenSamplerCallersSpec.mode2_retry_counter_i (retry + 1))] = 1%r.
proof.
proc.
wp.
call TargetKeygenM23SingularTotality.m23sing_total_singular_full_mode2_ll.
call TargetKeygenM23Finalize.keypair_finalize_m23_ll.
wp.
call TargetKeygenM23Matrix.kp_m23_matrix_mode2_ll.
wp.
call
  (Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_eta_retry_s2_count2_progress_ll
    seed0 retry eta_limit).
wp.
call
  (Mode2FaithfulSecurityRetryEtaProgressPostFreeze
    .mode2_eta_retry_s1_count3_progress_ll
    seed0 retry eta_limit).
auto => />.
move=> _ _ _ _ _ _ _ _ _.
rewrite /KeygenSamplerCallersSpec.mode2_retry_counter_i
        /KeygenSamplerCallersSpec.mode2_retry_span_i
        /KeygenSamplerCallersSpec.mode2_m_i
        /KeygenSamplerCallersSpec.mode2_k_i.
congr.
ring.
qed.

end Mode2FaithfulSecurityCheckedRetryStepPostFreeze.
