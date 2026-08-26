require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

require import SignCoreChallengeTracePostFreeze
               Mode2ConcreteHonestSigningTranscriptPostFreeze
               Mode2ChallengeGatedROMPostFreeze
               Mode2ChallengeROMProgrammingPostFreeze
               HAETAE_Algebra HAETAE_Transcript.

theory Mode2ConcreteHonestSigningBadGamePostFreeze.

import HAETAE_Algebra.
import HAETAE_Transcript.
import Mode2ChallengeGatedROMPostFreeze.

(* One-shot logging game only.  The raw signing trace supplies the concrete
   challenge ghost; the abstract sk/message/context/coins remain external
   witnesses used to build the patched transcript.  This layer does not
   assert a refinement from raw memory to those witnesses, issue or program a
   ROM query, prove termination, or introduce a distributional claim. *)

op concrete_transcript =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2.

op concrete_site =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_programming_site_mode2.

op concrete_site_clear =
  SignCoreChallengeTracePostFreeze.concrete_honest_site_clear.

module Mode2ConcreteHonestSigningBadGame(O : Mode2Oracle) = {
  module C =
    Mode2ChallengeROMProgrammingPostFreeze.Mode2CountedLazyROM(O)

  var transcripts : transcript list

  proc main(
      sk : skey, m : message, ctx : context, coins : random_coins,
      sigu : int, siglenu : int, mu : int, mlen : int,
      preu : int, prelen : int, rndu : int, sku : int) : bool = {
    var bad : bool;
    var r : W64.t;
    var tr : transcript;

    C.init();
    transcripts <- [];
    r <@ SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.run(
      sigu, siglenu, mu, mlen, preu, prelen, rndu, sku);
    tr <- concrete_transcript sk m ctx coins
      SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp;
    C.observe_transcript(tr);
    transcripts <- tr :: transcripts;
    bad <@ C.bad();
    return bad;
  }
}.

lemma concrete_site_clear_no_min_entropy_failure sk m ctx coins cp :
  concrete_site_clear sk m ctx coins cp =>
  ! Mode2ChallengeROMProgrammingPostFreeze.mode2_min_entropy_failure
      (concrete_transcript sk m ctx coins cp).
proof.
move=> [hvalid _].
apply
  Mode2ChallengeROMProgrammingPostFreeze.mode2_carrier_valid_no_min_entropy_failure.
rewrite
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2_challengeE.
exact hvalid.
qed.

lemma sign_raw_api_trace_concrete_honest_entropy_clear
    (sk : skey) (m : message) (ctx : context)
    (coins : random_coins) :
  hoare [SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.run :
    true
    ==>
    ! Mode2ChallengeROMProgrammingPostFreeze.mode2_min_entropy_failure
        (concrete_transcript sk m ctx coins
          SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp)].
proof.
conseq
  (SignCoreChallengeTracePostFreeze.sign_raw_api_trace_concrete_honest_site_clear
    sk m ctx coins).
move=> &hr _ hclear.
apply concrete_site_clear_no_min_entropy_failure.
qed.

section ConcreteSigningBadGameFacts.

declare module O <: Mode2Oracle {-Mode2ConcreteHonestSigningBadGame}.

lemma mode2_concrete_honest_signing_bad_game_false
    (sk0 : skey) (m0 : message) (ctx0 : context)
    (coins0 : random_coins) :
  hoare [Mode2ConcreteHonestSigningBadGame(O).main :
    sk = sk0 /\ m = m0 /\ ctx = ctx0 /\ coins = coins0
    ==>
    ! res /\
    Mode2ConcreteHonestSigningBadGame.transcripts =
      [concrete_transcript sk0 m0 ctx0 coins0
        SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp] /\
    Mode2ConcreteHonestSigningBadGame.C.signature_sites =
      [concrete_site sk0 m0 ctx0 coins0
        SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp] /\
    Mode2ConcreteHonestSigningBadGame.C.hash_queries = [] /\
    Mode2ConcreteHonestSigningBadGame.C.programmed_sites = []].
proof.
proc.
inline Mode2ConcreteHonestSigningBadGame(O).C.observe_transcript.
call
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_counted_lazy_rom_bad_false_when_clear
    (O)).
wp.
call
  (sign_raw_api_trace_concrete_honest_entropy_clear
    sk0 m0 ctx0 coins0).
wp.
call
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_counted_lazy_rom_init_clears
    (O)).
auto => />.
qed.

end section ConcreteSigningBadGameFacts.

end Mode2ConcreteHonestSigningBadGamePostFreeze.
