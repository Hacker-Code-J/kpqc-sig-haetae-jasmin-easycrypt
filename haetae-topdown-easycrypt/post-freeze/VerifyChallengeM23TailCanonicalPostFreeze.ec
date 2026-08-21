require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2VerifyPrepareNorm RawVerifyApiTarget VerifyCoreTarget
               RawApiVerifyMuTrace
               VerifyChallengeM23SamplerStructurePostFreeze.

theory VerifyChallengeM23TailCanonicalPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Focused = VerifyCoreTarget.M.
module TailMuTrace = RawApiVerifyMuTrace.VerifyTailMuTrace.
module FullM23MuTrace = RawApiVerifyMuTrace.VerifyFullM23MuTrace.
module FullMode2MuTrace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module InternalMode2MuTrace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module RawApiMuTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module CryptolabMuTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

(* The raw-API extraction and the five-helper Verify extraction contain the
   same generated challenge procedure.  Keep that identity explicit before
   transferring the focused structural theorem to the raw trace. *)
lemma raw_verify_challenge_m23_equiv_focused :
  equiv [Raw.__verify_challenge_m23 ~ Focused.__verify_challenge_m23 :
    ={Glob.mem, cp, highp, highlen, lsbp, mup, tau}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_verify_challenge_m23_tau58_canonical :
  hoare [Raw.__verify_challenge_m23 :
    tau = W64.of_int VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res].
proof.
conseq raw_verify_challenge_m23_equiv_focused
  VerifyChallengeM23SamplerStructurePostFreeze.verify_challenge_m23_tau58_canonical.
+ move=> &1 hpre.
   exists Glob.mem{1}.
   exists (cp{1}, highp{1}, highlen{1}, lsbp{1}, mup{1}, tau{1}).
   by auto.
+ move=> &1 &2 [_ hres] hpost.
   rewrite hres.
   exact hpost.
qed.

(* VerifyTailMuTrace always executes the challenge call, so its observation is
   canonical for every terminating tau-58 run, independently of acceptance. *)
lemma verify_tail_mu_trace_tau58_canonical :
  hoare [TailMuTrace.run :
    tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge
      TailMuTrace.observed_cprime].
proof.
proc.
wp.
call (_ : true ==> true); first by auto.
wp.
call raw_verify_challenge_m23_tau58_canonical.
auto => />.
rewrite /protect_64.
trivial.
qed.

(* The enclosing traces initialize their observations with witness values and
   assign them only on the reached tail path.  Their correct contract is thus
   conditional on tail_reached, not an unconditional canonicality claim. *)
lemma verify_full_m23_mu_trace_tau58_canonical :
  hoare [FullM23MuTrace.run :
    tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau
    ==>
    FullM23MuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      FullM23MuTrace.observed_cprime].
proof.
proc.
sp 38.
if.
+ auto => />.
+ seq 11 :
    (tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau /\
     !FullM23MuTrace.tail_reached).
  + call (_ : true ==> true); first by auto.
    auto.
  + sp 5.
    seq 1 :
      (tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau /\
       !FullM23MuTrace.tail_reached).
    + if; auto.
    + seq 15 :
        (tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau /\
         !FullM23MuTrace.tail_reached).
      + auto.
      + seq 1 :
          (tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau /\
           !FullM23MuTrace.tail_reached).
        + call (_ : true ==> true); first by auto.
          auto.
        + sp 5.
          if.
          + auto => />.
          + seq 12 :
              (tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau /\
               !FullM23MuTrace.tail_reached).
            + call (_ : true ==> true); first by auto.
              auto.
            + seq 9 :
                (tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau /\
                 !FullM23MuTrace.tail_reached).
              + call (_ : true ==> true); first by auto.
                auto.
              + seq 12 :
                  (tau_i = VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau /\
                   !FullM23MuTrace.tail_reached).
                + call (_ : true ==> true); first by auto.
                  auto.
                + seq 7 :
                    (tau_i =
                       VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau /\
                     !FullM23MuTrace.tail_reached).
                  + call (_ : true ==> true); first by auto.
                    auto.
                  + sp 2.
                    if.
                    + wp.
                      call verify_tail_mu_trace_tau58_canonical.
                      auto => />.
                    + auto => />.
qed.

lemma verify_full_mode2_mu_trace_tail_canonical :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    FullMode2MuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      FullMode2MuTrace.observed_cprime].
proof.
proc.
wp.
call verify_full_m23_mu_trace_tau58_canonical.
auto.
qed.

lemma verify_internal_mode2_mu_trace_tail_canonical :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    InternalMode2MuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      InternalMode2MuTrace.observed_cprime].
proof.
proc.
wp.
call verify_full_mode2_mu_trace_tail_canonical.
auto.
qed.

lemma verify_raw_api_mu_trace_tail_canonical :
  hoare [RawApiMuTrace.run :
    true
    ==>
    RawApiMuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      RawApiMuTrace.observed_cprime].
proof.
proc.
sp 15.
if.
+ auto.
+ wp.
   call verify_internal_mode2_mu_trace_tail_canonical.
   wp.
   call (_ : true ==> true); first by auto.
   wp.
   call (_ : true ==> true); first by auto.
   auto => />.
qed.

lemma verify_cryptolab_mu_trace_tail_canonical :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    CryptolabMuTrace.tail_reached =>
    Mode2VerifyPrepareNorm.canonical_challenge
      CryptolabMuTrace.observed_cprime].
proof.
proc.
seq 2 :
  (RawApiMuTrace.tail_reached =>
   Mode2VerifyPrepareNorm.canonical_challenge
     RawApiMuTrace.observed_cprime).
+ inline Raw._verify_publish_reject.
   wp.
   call verify_raw_api_mu_trace_tail_canonical.
   auto => />.
+ if.
   + auto.
   + wp.
     call (_ : true ==> true); first by auto.
     auto => />.
qed.

end VerifyChallengeM23TailCanonicalPostFreeze.
