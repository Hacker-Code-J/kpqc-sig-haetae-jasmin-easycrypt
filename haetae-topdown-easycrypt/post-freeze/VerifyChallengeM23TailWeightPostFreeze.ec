require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2VerifyPrepareNorm RawVerifyApiTarget RawApiVerifyMuTrace
               VerifyChallengeM23WeightPostFreeze
               VerifyChallengeM23TailCanonicalPostFreeze.

theory VerifyChallengeM23TailWeightPostFreeze.

module Raw = RawVerifyApiTarget.M.
module TailMuTrace = RawApiVerifyMuTrace.VerifyTailMuTrace.
module FullM23MuTrace = RawApiVerifyMuTrace.VerifyFullM23MuTrace.
module FullMode2MuTrace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module InternalMode2MuTrace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module RawApiMuTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module CryptolabMuTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

op mode2_tau : int = VerifyChallengeM23WeightPostFreeze.mode2_tau.
op challenge_weight = VerifyChallengeM23WeightPostFreeze.challenge_weight.

(* Structural partial correctness only: reuse the established Raw/focused
   sampler identity to transfer the focused tau-58 weight theorem. *)
lemma raw_verify_challenge_m23_tau58_canonical_weight :
  hoare [Raw.__verify_challenge_m23 :
    tau = W64.of_int mode2_tau
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res /\
    challenge_weight res = mode2_tau].
proof.
conseq
  VerifyChallengeM23TailCanonicalPostFreeze.raw_verify_challenge_m23_equiv_focused
  VerifyChallengeM23WeightPostFreeze.verify_challenge_m23_tau58_canonical_weight.
+ move=> &1 hpre.
   exists Glob.mem{1}.
   exists (cp{1}, highp{1}, highlen{1}, lsbp{1}, mup{1}, tau{1}).
   by auto.
+ move=> &1 &2 [_ hres] hpost.
   rewrite hres.
   exact hpost.
qed.

(* VerifyTailMuTrace always reaches the challenge call, so the observed
   cprime inherits the full tau-58 canonicality and exact-weight contract
   on every terminating run, independent of acceptance. *)
lemma verify_tail_mu_trace_tau58_canonical_weight :
  hoare [TailMuTrace.run :
    tau_i = mode2_tau
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge TailMuTrace.observed_cprime /\
    challenge_weight TailMuTrace.observed_cprime = mode2_tau].
proof.
proc.
wp.
call (_ : true ==> true); first by auto.
wp.
call raw_verify_challenge_m23_tau58_canonical_weight.
auto => />.
rewrite /protect_64.
trivial.
qed.

(* The enclosing traces assign observed_cprime only on the tail path, so the
   lifted theorem must remain conditional on tail_reached. *)
lemma verify_full_m23_mu_trace_tau58_canonical_weight :
  hoare [FullM23MuTrace.run :
    tau_i = mode2_tau
    ==>
    FullM23MuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      FullM23MuTrace.observed_cprime /\
    challenge_weight FullM23MuTrace.observed_cprime = mode2_tau].
proof.
proc.
sp 38.
if.
+ auto => />.
+ seq 11 :
    (tau_i = mode2_tau /\ !FullM23MuTrace.tail_reached).
  + call (_ : true ==> true); first by auto.
    auto.
  + sp 5.
    seq 1 :
      (tau_i = mode2_tau /\ !FullM23MuTrace.tail_reached).
    + if; auto.
    + seq 15 :
        (tau_i = mode2_tau /\ !FullM23MuTrace.tail_reached).
      + auto.
      + seq 1 :
          (tau_i = mode2_tau /\ !FullM23MuTrace.tail_reached).
        + call (_ : true ==> true); first by auto.
          auto.
        + sp 5.
          if.
          + auto => />.
          + seq 12 :
              (tau_i = mode2_tau /\ !FullM23MuTrace.tail_reached).
            + call (_ : true ==> true); first by auto.
              auto.
            + seq 9 :
                (tau_i = mode2_tau /\ !FullM23MuTrace.tail_reached).
              + call (_ : true ==> true); first by auto.
                auto.
              + seq 12 :
                  (tau_i = mode2_tau /\ !FullM23MuTrace.tail_reached).
                + call (_ : true ==> true); first by auto.
                  auto.
                + seq 7 :
                    (tau_i = mode2_tau /\ !FullM23MuTrace.tail_reached).
                  + call (_ : true ==> true); first by auto.
                    auto.
                  + sp 2.
                    if.
                    + wp.
                      call verify_tail_mu_trace_tau58_canonical_weight.
                      auto => />.
                    + auto => />.
qed.

lemma verify_full_mode2_mu_trace_tail_canonical_weight :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    FullMode2MuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      FullMode2MuTrace.observed_cprime /\
    challenge_weight FullMode2MuTrace.observed_cprime = mode2_tau].
proof.
proc.
wp.
call verify_full_m23_mu_trace_tau58_canonical_weight.
auto.
qed.

lemma verify_internal_mode2_mu_trace_tail_canonical_weight :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    InternalMode2MuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      InternalMode2MuTrace.observed_cprime /\
    challenge_weight InternalMode2MuTrace.observed_cprime = mode2_tau].
proof.
proc.
wp.
call verify_full_mode2_mu_trace_tail_canonical_weight.
auto.
qed.

lemma verify_raw_api_mu_trace_tail_canonical_weight :
  hoare [RawApiMuTrace.run :
    true
    ==>
    RawApiMuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      RawApiMuTrace.observed_cprime /\
    challenge_weight RawApiMuTrace.observed_cprime = mode2_tau].
proof.
proc.
sp 15.
if.
+ auto.
+ wp.
   call verify_internal_mode2_mu_trace_tail_canonical_weight.
   wp.
   call (_ : true ==> true); first by auto.
   wp.
   call (_ : true ==> true); first by auto.
   auto => />.
qed.

lemma verify_cryptolab_mu_trace_tail_canonical_weight :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    CryptolabMuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      CryptolabMuTrace.observed_cprime /\
    challenge_weight CryptolabMuTrace.observed_cprime = mode2_tau].
proof.
proc.
seq 2 :
  (RawApiMuTrace.tail_reached =>
   Mode2VerifyPrepareNorm.canonical_challenge
     RawApiMuTrace.observed_cprime /\
   challenge_weight RawApiMuTrace.observed_cprime = mode2_tau).
+ inline Raw._verify_publish_reject.
   wp.
   call verify_raw_api_mu_trace_tail_canonical_weight.
   auto => />.
+ if.
   + auto.
   + wp.
     call (_ : true ==> true); first by auto.
     auto => />.
qed.

end VerifyChallengeM23TailWeightPostFreeze.
