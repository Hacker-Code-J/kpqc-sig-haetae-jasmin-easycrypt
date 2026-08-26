require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2ConcreteHonestProgrammedSigningOraclePostFreeze
               SignCoreChallengeTracePostFreeze
               Mode2ConcreteHonestSigningTranscriptPostFreeze
               Mode2ChallengeGatedROMPostFreeze
               Mode2ChallengeROMProgrammingPostFreeze
               HAETAE_Algebra HAETAE_Params HAETAE_ROM
               HAETAE_Transcript HAETAE_ROM_Programming.

theory Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.

import HAETAE_Algebra.
import HAETAE_Params.
import HAETAE_ROM.
import HAETAE_Transcript.
import HAETAE_ROM_Programming.
import Mode2ChallengeGatedROMPostFreeze.

(* Deterministic freshness adapter only.  A new abstract signing query must be
   distinct from every accumulated concrete transcript query.  This removes
   the universal carrier-site freshness premise without asserting that query
   distinctness follows probabilistically or from the raw ABI inputs. *)

op concrete_transcript =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2.

op concrete_site =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_programming_site_mode2.

op concrete_signing_query
    (sk : skey) (m : message) (ctx : context)
    (coins : random_coins) : ro_query =
  challenge_hash_query Mode2
    (sig_commitment_highbits (sign_internal Mode2 sk m ctx coins))
    (sig_commitment_lowbits (sign_internal Mode2 sk m ctx coins))
    (sig_message_hash (sign_internal Mode2 sk m ctx coins)).

op transcript_site_query (tr : transcript) : ro_query =
  programming_site_query (actual_signature_programming_site Mode2 tr).

op accumulated_query_fresh
    (trs : transcript list)
    (sk : skey) (m : message) (ctx : context)
    (coins : random_coins) : bool =
  forall tr, tr \in trs =>
    transcript_site_query tr <> concrete_signing_query sk m ctx coins.

op transcript_queries_unique (trs : transcript list) : bool =
  uniq (map transcript_site_query trs).

op distinct_programmed_signing_inv
    (trs : transcript list)
    (signature_sites : programming_site list)
    (hashes : ro_query list)
    (programmed : programming_site list)
    (bad_prequery bad_reprogram bad_entropy : bool) : bool =
  Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.programmed_signing_log_inv
    trs signature_sites hashes programmed
    bad_prequery bad_reprogram bad_entropy /\
  transcript_queries_unique trs.

lemma concrete_site_queryE sk m ctx coins cp :
  programming_site_query (concrete_site sk m ctx coins cp) =
  concrete_signing_query sk m ctx coins.
proof.
by rewrite /concrete_site
           /Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_programming_site_mode2
           /actual_signature_programming_site
           /signature_programming_site_of_transcript
           /programming_site_query
           /transcript_signature_challenge_query
           /Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2
           /transcript_of_signature /transcript_signature
           /Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_signature_mode2
           /Mode2ConcreteHonestSigningTranscriptPostFreeze.signature_with_challenge
           /sig_commitment_highbits /sig_commitment_lowbits
           /sig_message_hash /concrete_signing_query /=.
qed.

lemma concrete_transcript_site_queryE sk m ctx coins cp :
  transcript_site_query (concrete_transcript sk m ctx coins cp) =
  concrete_signing_query sk m ctx coins.
proof.
rewrite /transcript_site_query.
exact (concrete_site_queryE sk m ctx coins cp).
qed.

lemma accumulated_query_fresh_no_reprograms trs sk m ctx coins cp :
  accumulated_query_fresh trs sk m ctx coins =>
  ! programming_site_reprograms
      (map (actual_signature_programming_site Mode2) trs)
      (concrete_site sk m ctx coins cp).
proof.
move=> hfresh.
rewrite /programming_site_reprograms.
apply/hasPn => old hold.
move/List.mapP: hold => [tr [htr ->]].
rewrite /programming_sites_conflict /programming_sites_same_query
        concrete_site_queryE.
apply/negP => hconflict.
move: hconflict => [hsame _].
move: (hfresh tr htr).
rewrite /transcript_site_query.
smt().
qed.

lemma distinct_query_implies_concrete_programming_fresh
    trs signature_sites hashes programmed
    bad_prequery bad_reprogram bad_entropy sk m ctx coins :
  Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.programmed_signing_log_inv
    trs signature_sites hashes programmed
    bad_prequery bad_reprogram bad_entropy =>
  accumulated_query_fresh trs sk m ctx coins =>
  Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.concrete_programming_fresh
    hashes programmed sk m ctx coins.
proof.
rewrite
  /Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.programmed_signing_log_inv.
move=> [_ [_ [hprogrammed [hhashes _]]]] hfresh.
rewrite
  /Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.concrete_programming_fresh.
move=> cp hvalid.
rewrite /programming_site_fresh hhashes hprogrammed.
split.
+ by rewrite /programming_site_prequeried.
+ exact (accumulated_query_fresh_no_reprograms
          trs sk m ctx coins cp hfresh).
qed.

lemma transcript_queries_unique_cons sk m ctx coins cp trs :
  transcript_queries_unique trs =>
  accumulated_query_fresh trs sk m ctx coins =>
  transcript_queries_unique
    (concrete_transcript sk m ctx coins cp :: trs).
proof.
rewrite /transcript_queries_unique /= concrete_transcript_site_queryE.
move=> huniq hfresh.
split; last exact huniq.
apply/negP => hmem.
move/List.mapP: hmem => [tr [htr heq]].
apply (hfresh tr htr).
apply eq_sym.
exact heq.
qed.

section DistinctProgrammedSigningFacts.

declare module O <: Mode2Oracle
  {-Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle}.

lemma distinct_programmed_signing_init_establishes_inv :
  hoare [Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle(O).init :
    true
    ==>
    distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy].
proof.
proc.
wp.
call
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_counted_lazy_rom_init_clears
    (O)).
auto => />.
qed.

lemma distinct_programmed_signing_sign_preserves_inv
    (sk0 : skey) (m0 : message) (ctx0 : context)
    (coins0 : random_coins) (trs0 : transcript list) :
  hoare [Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle(O).sign :
    sk = sk0 /\ m = m0 /\ ctx = ctx0 /\ coins = coins0 /\
    Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.transcripts = trs0 /\
    distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy /\
    accumulated_query_fresh trs0 sk0 m0 ctx0 coins0
    ==>
    Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.transcripts =
      concrete_transcript sk0 m0 ctx0 coins0
        SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp
      :: trs0 /\
    distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy].
proof.
conseq
  (Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.mode2_concrete_programmed_signing_sign_preserves_inv
    (O) sk0 m0 ctx0 coins0 trs0).
+ move=> &hr [hsk [hm [hctx [hcoins [htrs [hdist hfresh]]]]]].
  move: hdist => [hinv huniq].
  have hinv0 := hinv.
  rewrite htrs in hinv0.
  split; first exact hsk.
  split; first exact hm.
  split; first exact hctx.
  split; first exact hcoins.
  split; first exact htrs.
  split; first exact hinv.
  exact
    (distinct_query_implies_concrete_programming_fresh
      trs0
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites{hr}
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries{hr}
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites{hr}
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery{hr}
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram{hr}
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy{hr}
      sk0 m0 ctx0 coins0 hinv0 hfresh).
+ move=> &hr hpre bad_entropy bad_prequery bad_reprogram
          programmed_sites signature_sites transcripts observed_cp
          [htrs hinv].
  move: hpre => [_ [_ [_ [_ [htrs0 [hdist hfresh]]]]]].
  move: hdist => [_ huniq].
  rewrite htrs0 in huniq.
  split; first exact htrs.
  split; first exact hinv.
  rewrite htrs.
  apply transcript_queries_unique_cons.
  + exact huniq.
  + exact hfresh.
qed.

lemma distinct_programmed_signing_bad_false_under_inv :
  hoare [Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle(O).bad :
    distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy
    ==>
    ! res /\
    distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.transcripts
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle.C.bad_mode2_entropy].
proof.
conseq
  (Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.mode2_concrete_programmed_signing_bad_false_under_inv
    (O)).
+ move=> &hr [hinv huniq].
  exact hinv.
+ move=> &hr [hinv huniq] result [hfalse hinv'].
  split; first exact hfalse.
  split; [exact hinv' | exact huniq].
qed.

end section DistinctProgrammedSigningFacts.

end Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.
