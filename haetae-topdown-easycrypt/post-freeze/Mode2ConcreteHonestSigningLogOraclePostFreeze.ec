require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

require import SignCoreChallengeTracePostFreeze
               Mode2ConcreteHonestSigningTranscriptPostFreeze
               Mode2ConcreteHonestSigningBadGamePostFreeze
               Mode2ChallengeGatedROMPostFreeze
               Mode2ChallengeROMProgrammingPostFreeze
               HAETAE_Algebra HAETAE_Params HAETAE_ROM
               HAETAE_Transcript HAETAE_ROM_Programming.

theory Mode2ConcreteHonestSigningLogOraclePostFreeze.

import HAETAE_Algebra.
import HAETAE_Params.
import HAETAE_ROM.
import HAETAE_Transcript.
import HAETAE_ROM_Programming.
import Mode2ChallengeGatedROMPostFreeze.

(* Reusable multi-query logging surface.  Each call receives its abstract
   sk/message/context/coins as ghost witnesses alongside independent raw ABI
   arguments.  The invariant does not assert a raw-memory refinement between
   those two interfaces.  No ROM get/program call, termination claim, or
   distributional claim is introduced. *)

op concrete_transcript =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2.

op signing_log_inv
    (trs : transcript list)
    (sites : programming_site list)
    (hashes : ro_query list)
    (programmed : programming_site list)
    (bad_prequery bad_reprogram bad_entropy : bool) : bool =
  Mode2ChallengeROMProgrammingPostFreeze.mode2_transcript_log_min_entropy_clear
    trs /\
  sites = map (actual_signature_programming_site Mode2) trs /\
  hashes = [] /\
  programmed = [] /\
  ! bad_prequery /\
  ! bad_reprogram /\
  ! bad_entropy.

module Mode2ConcreteHonestSigningLogOracle(O : Mode2Oracle) = {
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

    r <@ SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.run(
      sigu, siglenu, mu, mlen, preu, prelen, rndu, sku);
    tr <- concrete_transcript sk m ctx coins
      SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp;
    C.observe_transcript(tr);
    transcripts <- tr :: transcripts;
    return r;
  }

  proc bad() : bool = {
    var b : bool;

    b <@ C.bad();
    return b;
  }
}.

section ConcreteSigningLogOracleFacts.

declare module O <: Mode2Oracle {-Mode2ConcreteHonestSigningLogOracle}.

lemma mode2_concrete_signing_log_init_establishes_inv :
  hoare [Mode2ConcreteHonestSigningLogOracle(O).init :
    true
    ==>
    signing_log_inv
      Mode2ConcreteHonestSigningLogOracle.transcripts
      Mode2ConcreteHonestSigningLogOracle.C.signature_sites
      Mode2ConcreteHonestSigningLogOracle.C.hash_queries
      Mode2ConcreteHonestSigningLogOracle.C.programmed_sites
      Mode2ConcreteHonestSigningLogOracle.C.bad_prequery
      Mode2ConcreteHonestSigningLogOracle.C.bad_reprogram
      Mode2ConcreteHonestSigningLogOracle.C.bad_mode2_entropy].
proof.
proc.
wp.
call
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_counted_lazy_rom_init_clears
    (O)).
auto => />.
qed.

lemma mode2_concrete_signing_log_sign_preserves_inv
    (sk0 : skey) (m0 : message) (ctx0 : context)
    (coins0 : random_coins) (trs0 : transcript list) :
  hoare [Mode2ConcreteHonestSigningLogOracle(O).sign :
    sk = sk0 /\ m = m0 /\ ctx = ctx0 /\ coins = coins0 /\
    Mode2ConcreteHonestSigningLogOracle.transcripts = trs0 /\
    signing_log_inv
      Mode2ConcreteHonestSigningLogOracle.transcripts
      Mode2ConcreteHonestSigningLogOracle.C.signature_sites
      Mode2ConcreteHonestSigningLogOracle.C.hash_queries
      Mode2ConcreteHonestSigningLogOracle.C.programmed_sites
      Mode2ConcreteHonestSigningLogOracle.C.bad_prequery
      Mode2ConcreteHonestSigningLogOracle.C.bad_reprogram
      Mode2ConcreteHonestSigningLogOracle.C.bad_mode2_entropy
    ==>
    Mode2ConcreteHonestSigningLogOracle.transcripts =
      concrete_transcript sk0 m0 ctx0 coins0
        SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp
      :: trs0 /\
    signing_log_inv
      Mode2ConcreteHonestSigningLogOracle.transcripts
      Mode2ConcreteHonestSigningLogOracle.C.signature_sites
      Mode2ConcreteHonestSigningLogOracle.C.hash_queries
      Mode2ConcreteHonestSigningLogOracle.C.programmed_sites
      Mode2ConcreteHonestSigningLogOracle.C.bad_prequery
      Mode2ConcreteHonestSigningLogOracle.C.bad_reprogram
      Mode2ConcreteHonestSigningLogOracle.C.bad_mode2_entropy].
proof.
proc.
inline Mode2ConcreteHonestSigningLogOracle(O).C.observe_transcript.
wp.
call
  (Mode2ConcreteHonestSigningBadGamePostFreeze.sign_raw_api_trace_concrete_honest_entropy_clear
    sk0 m0 ctx0 coins0).
auto => />.
rewrite /signing_log_inv
        /Mode2ChallengeROMProgrammingPostFreeze.mode2_transcript_log_min_entropy_clear /=.
move=> &hr hall hpre hreprogram hentropy
        observed_cp s hsubset hcard heq.
have hmin :
    ! Mode2ChallengeROMProgrammingPostFreeze.mode2_min_entropy_failure
        (concrete_transcript sk0 m0 ctx0 coins0 observed_cp).
+ apply
    Mode2ChallengeROMProgrammingPostFreeze.mode2_carrier_valid_no_min_entropy_failure.
  exists s.
  split.
  + split; [exact hsubset | exact hcard].
  + exact heq.
split; exact hmin.
qed.

lemma mode2_concrete_signing_log_bad_false_under_inv :
  hoare [Mode2ConcreteHonestSigningLogOracle(O).bad :
    signing_log_inv
      Mode2ConcreteHonestSigningLogOracle.transcripts
      Mode2ConcreteHonestSigningLogOracle.C.signature_sites
      Mode2ConcreteHonestSigningLogOracle.C.hash_queries
      Mode2ConcreteHonestSigningLogOracle.C.programmed_sites
      Mode2ConcreteHonestSigningLogOracle.C.bad_prequery
      Mode2ConcreteHonestSigningLogOracle.C.bad_reprogram
      Mode2ConcreteHonestSigningLogOracle.C.bad_mode2_entropy
    ==>
    ! res /\
    signing_log_inv
      Mode2ConcreteHonestSigningLogOracle.transcripts
      Mode2ConcreteHonestSigningLogOracle.C.signature_sites
      Mode2ConcreteHonestSigningLogOracle.C.hash_queries
      Mode2ConcreteHonestSigningLogOracle.C.programmed_sites
      Mode2ConcreteHonestSigningLogOracle.C.bad_prequery
      Mode2ConcreteHonestSigningLogOracle.C.bad_reprogram
      Mode2ConcreteHonestSigningLogOracle.C.bad_mode2_entropy].
proof.
proc.
call
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_counted_lazy_rom_bad_false_when_clear
    (O)).
auto => />.
qed.

end section ConcreteSigningLogOracleFacts.

end Mode2ConcreteHonestSigningLogOraclePostFreeze.
