require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

require import SignCoreChallengeTracePostFreeze
               SignChallengeM23CarrierBridgePostFreeze
               Mode2ConcreteHonestSigningTranscriptPostFreeze
               Mode2ChallengeGatedROMPostFreeze
               Mode2ChallengeROMProgrammingPostFreeze
               HAETAE_Algebra HAETAE_Params HAETAE_ROM
               HAETAE_Transcript HAETAE_ROM_Programming.

theory Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.

import HAETAE_Algebra.
import HAETAE_Params.
import HAETAE_ROM.
import HAETAE_Transcript.
import HAETAE_ROM_Programming.
import Mode2ChallengeGatedROMPostFreeze.

(* Programmed multi-query surface.  Since the raw challenge is produced only
   during the call, freshness is stated beforehand for every carrier-valid cp
   that the call may expose.  This conservative premise rules out repeated
   challenge queries without adding a distributional or collision claim. *)

op concrete_transcript =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2.

op concrete_site =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_programming_site_mode2.

op challenge_of_barray =
  SignChallengeM23CarrierBridgePostFreeze.challenge_of_barray.

op valid_mode2_carrier_challenge =
  SignChallengeM23CarrierBridgePostFreeze.valid_mode2_carrier_challenge.

op concrete_programming_fresh
    (hashes : ro_query list) (programmed : programming_site list)
    (sk : skey) (m : message) (ctx : context)
    (coins : random_coins) : bool =
  forall cp,
    valid_mode2_carrier_challenge (challenge_of_barray cp) =>
    programming_site_fresh hashes programmed
      (concrete_site sk m ctx coins cp).

lemma concrete_programming_fresh_empty sk m ctx coins :
  concrete_programming_fresh [] [] sk m ctx coins.
proof.
rewrite /concrete_programming_fresh => cp hvalid.
by rewrite /programming_site_fresh
           /programming_site_prequeried
           /programming_site_reprograms /=.
qed.

op programmed_signing_log_inv
    (trs : transcript list)
    (signature_sites : programming_site list)
    (hashes : ro_query list)
    (programmed : programming_site list)
    (bad_prequery bad_reprogram bad_entropy : bool) : bool =
  Mode2ChallengeROMProgrammingPostFreeze.mode2_transcript_log_min_entropy_clear
    trs /\
  signature_sites = map (actual_signature_programming_site Mode2) trs /\
  programmed = map (actual_signature_programming_site Mode2) trs /\
  hashes = [] /\
  ! bad_prequery /\
  ! bad_reprogram /\
  ! bad_entropy.

module Mode2ConcreteHonestProgrammedSigningOracle(O : Mode2Oracle) = {
  module C =
    Mode2ChallengeROMProgrammingPostFreeze.Mode2CountedLazyROM(O)

  var transcripts : transcript list

  proc init() : unit = {
    C.init();
    transcripts <- [];
  }

  proc sign(
      sk : skey, m : message, ctx : context, coins : random_coins,
      sigu : int, siglenu : int, mu : int, mlen : int,
      preu : int, prelen : int, rndu : int, sku : int) : W64.t = {
    var r : W64.t;
    var tr : transcript;
    var site : programming_site;

    r <@ SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.run(
      sigu, siglenu, mu, mlen, preu, prelen, rndu, sku);
    tr <- concrete_transcript sk m ctx coins
      SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp;
    site <- concrete_site sk m ctx coins
      SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp;
    C.observe_transcript(tr);
    C.program(site);
    transcripts <- tr :: transcripts;
    return r;
  }

  proc bad() : bool = {
    var b : bool;

    b <@ C.bad();
    return b;
  }
}.

section ConcreteProgrammedSigningOracleFacts.

declare module O <: Mode2Oracle
  {-Mode2ConcreteHonestProgrammedSigningOracle}.

lemma mode2_concrete_programmed_signing_init_establishes_inv :
  hoare [Mode2ConcreteHonestProgrammedSigningOracle(O).init :
    true
    ==>
    programmed_signing_log_inv
      Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy].
proof.
proc.
wp.
call
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_counted_lazy_rom_init_clears
    (O)).
auto => />.
qed.

lemma mode2_concrete_programmed_signing_sign_preserves_inv
    (sk0 : skey) (m0 : message) (ctx0 : context)
    (coins0 : random_coins) (trs0 : transcript list) :
  hoare [Mode2ConcreteHonestProgrammedSigningOracle(O).sign :
    sk = sk0 /\ m = m0 /\ ctx = ctx0 /\ coins = coins0 /\
    Mode2ConcreteHonestProgrammedSigningOracle.transcripts = trs0 /\
    programmed_signing_log_inv
      Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy /\
    concrete_programming_fresh
      Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      sk0 m0 ctx0 coins0
    ==>
    Mode2ConcreteHonestProgrammedSigningOracle.transcripts =
      concrete_transcript sk0 m0 ctx0 coins0
        SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp
      :: trs0 /\
    programmed_signing_log_inv
      Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy].
proof.
proc.
inline Mode2ConcreteHonestProgrammedSigningOracle(O).C.observe_transcript
       Mode2ConcreteHonestProgrammedSigningOracle(O).C.program.
wp.
call (_ : true ==> true); first by auto.
wp.
call
  (SignCoreChallengeTracePostFreeze.sign_raw_api_trace_concrete_honest_site_clear
    sk0 m0 ctx0 coins0).
auto => />.
rewrite /programmed_signing_log_inv
        /Mode2ChallengeROMProgrammingPostFreeze.mode2_transcript_log_min_entropy_clear
        /concrete_programming_fresh
        /programming_site_fresh /=.
move=> &hr hall hpre hreprogram hentropy hfresh
        observed_cp s hsubset hcard heq
        s0 hsubset0 hcard0 heq0.
have hvalid_cp :
    valid_mode2_carrier_challenge (challenge_of_barray observed_cp).
+ exists s.
  split.
  + split; [exact hsubset | exact hcard].
  + exact heq.
have hfresh_cp := hfresh observed_cp hvalid_cp.
move: hfresh_cp => [_ hnoreprogram].
have hmin :
    ! Mode2ChallengeROMProgrammingPostFreeze.mode2_min_entropy_failure
        (concrete_transcript sk0 m0 ctx0 coins0 observed_cp).
+ apply
    Mode2ChallengeROMProgrammingPostFreeze.mode2_carrier_valid_no_min_entropy_failure.
  exists s0.
  split.
  + split; [exact hsubset0 | exact hcard0].
  + exact heq0.
split; first exact hmin.
split; [exact hnoreprogram | exact hmin].
qed.

lemma mode2_concrete_programmed_signing_bad_false_under_inv :
  hoare [Mode2ConcreteHonestProgrammedSigningOracle(O).bad :
    programmed_signing_log_inv
      Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy
    ==>
    ! res /\
    programmed_signing_log_inv
      Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy].
proof.
proc.
call
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_counted_lazy_rom_bad_false_when_clear
    (O)).
auto => />.
qed.

end section ConcreteProgrammedSigningOracleFacts.

end Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.
