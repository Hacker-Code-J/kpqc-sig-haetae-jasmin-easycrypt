require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

require import SignCoreChallengeTracePostFreeze
               Mode2ConcreteHonestSigningTranscriptPostFreeze
               Mode2ConcreteHonestProgrammedSigningOraclePostFreeze
               Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze
               Mode2ChallengeGatedROMPostFreeze
               Mode2ChallengeROMProgrammingPostFreeze
               HAETAE_Algebra HAETAE_Params HAETAE_ROM
               HAETAE_Transcript HAETAE_ROM_Programming.

theory Mode2ConcreteHonestProgrammedSigningQueryOraclePostFreeze.

import HAETAE_Algebra.
import HAETAE_Params.
import HAETAE_ROM.
import HAETAE_Transcript.
import HAETAE_ROM_Programming.
import Mode2ChallengeGatedROMPostFreeze.

(* Deterministic query/sign wrapper only.  This layer exposes adversary-visible
   ROM get together with the existing concrete programmed signing surface, but
   it does not add an adversary-wide probability bound, a raw-memory
   refinement, a termination claim, or any distributional statement.  A get
   only records a possible prequery; it becomes bad if a later program targets
   that query.  The raw sign ABI still is not a SIG.SignOracle interface. *)

op concrete_transcript =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2.

op concrete_site =
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_programming_site_mode2.

op concrete_signing_query =
  Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.concrete_signing_query.

op concrete_programming_fresh =
  Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.concrete_programming_fresh.

op accumulated_query_fresh =
  Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.accumulated_query_fresh.

op transcript_queries_unique =
  Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.transcript_queries_unique.

(* [hashes] is intentionally unconstrained: get extends it, while sign uses a
   separate explicit non-membership premise for its concrete query. *)
op query_programmed_signing_inv
    (trs : transcript list)
    (signature_sites : programming_site list)
    (hashes : ro_query list)
    (programmed : programming_site list)
    (bad_prequery bad_reprogram bad_entropy : bool) : bool =
  Mode2ChallengeROMProgrammingPostFreeze.mode2_transcript_log_min_entropy_clear
    trs /\
  signature_sites = map (actual_signature_programming_site Mode2) trs /\
  programmed = map (actual_signature_programming_site Mode2) trs /\
  ! bad_prequery /\
  ! bad_reprogram /\
  ! bad_entropy.

op query_distinct_programmed_signing_inv
    (trs : transcript list)
    (signature_sites : programming_site list)
    (hashes : ro_query list)
    (programmed : programming_site list)
    (bad_prequery bad_reprogram bad_entropy : bool) : bool =
  query_programmed_signing_inv
    trs signature_sites hashes programmed
    bad_prequery bad_reprogram bad_entropy /\
  transcript_queries_unique trs.

lemma concrete_site_not_prequeried
    hashes sk m ctx coins cp :
  ! (concrete_signing_query sk m ctx coins \in hashes) =>
  ! programming_site_prequeried hashes
      (concrete_site sk m ctx coins cp).
proof.
move=> hfresh.
rewrite /programming_site_prequeried.
rewrite
  (Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.concrete_site_queryE
    sk m ctx coins cp).
exact hfresh.
qed.

lemma explicit_query_fresh_implies_concrete_programming_fresh
    trs signature_sites hashes programmed
    bad_prequery bad_reprogram bad_entropy
    sk m ctx coins :
  query_programmed_signing_inv
    trs signature_sites hashes programmed
    bad_prequery bad_reprogram bad_entropy =>
  ! (concrete_signing_query sk m ctx coins \in hashes) =>
  accumulated_query_fresh trs sk m ctx coins =>
  concrete_programming_fresh hashes programmed sk m ctx coins.
proof.
move=> hinv hqfresh htfresh.
move: hinv => [_ [_ [hprogrammed _]]].
rewrite /concrete_programming_fresh.
move=> cp hvalid.
rewrite /programming_site_fresh hprogrammed.
split.
+ exact (concrete_site_not_prequeried hashes sk m ctx coins cp hqfresh).
+ exact
     (Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.accumulated_query_fresh_no_reprograms
       trs sk m ctx coins cp htfresh).
qed.

module Mode2ConcreteHonestProgrammedSigningQueryOracle(O : Mode2Oracle) = {
  module Base =
    Mode2ConcreteHonestProgrammedSigningOraclePostFreeze.Mode2ConcreteHonestProgrammedSigningOracle(O)

  proc init() : unit = {
    Base.init();
  }

  proc get(q : ro_query) : ro_output = {
    var y : ro_output;

    y <@ Base.C.get(q);
    return y;
  }

  proc sign(
      sk : skey, m : message, ctx : context, coins : random_coins,
      sigu : int, siglenu : int, mu : int, mlen : int,
      preu : int, prelen : int, rndu : int, sku : int) : W64.t = {
    var r : W64.t;
    r <@ Base.sign(sk, m, ctx, coins,
      sigu, siglenu, mu, mlen, preu, prelen, rndu, sku);
    return r;
  }

  proc bad() : bool = {
    var b : bool;

    b <@ Base.bad();
    return b;
  }
}.

section QueryOracleFacts.

declare module O <: Mode2Oracle
  {-Mode2ConcreteHonestProgrammedSigningQueryOracle}.

lemma mode2_concrete_programmed_query_init_establishes_inv :
  hoare [Mode2ConcreteHonestProgrammedSigningQueryOracle(O).init :
    true
    ==>
    query_distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy].
proof.
proc.
inline Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.init.
wp.
call
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_counted_lazy_rom_init_clears
    (O)).
auto => />.
qed.

lemma mode2_concrete_programmed_query_get_exact_preserves_inv
    (q0 : ro_query) (trs0 : transcript list) (hashes0 : ro_query list) :
  hoare [Mode2ConcreteHonestProgrammedSigningQueryOracle(O).get :
    q = q0 /\
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts = trs0 /\
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries = hashes0 /\
    query_distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy
    ==>
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts = trs0 /\
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries =
      q0 :: hashes0 /\
    query_distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy].
proof.
proc.
inline Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.C.get.
wp.
call (_ : true).
auto => />.
qed.

lemma mode2_concrete_programmed_query_get_challenge_count_step
    (n : int) :
  hoare [Mode2ConcreteHonestProgrammedSigningQueryOracle(O).get :
    challenge_query_log_count
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries <= n /\
    query_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy
    ==>
    challenge_query_log_count
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries <= n + 1 /\
    query_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy].
proof.
proc.
inline Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.C.get.
wp.
call (_ : true).
auto => />.
move=> &hr hcount hall hpre hreprogram hentropy.
have hstep :=
  challenge_query_log_count_cons_le q{hr}
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries{hr}.
smt().
qed.

lemma mode2_concrete_programmed_query_get_nonchallenge_preserves_challenge_count
    (n : int) :
  hoare [Mode2ConcreteHonestProgrammedSigningQueryOracle(O).get :
    ! ro_query_is_challenge q /\
    challenge_query_log_count
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries <= n /\
    query_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy
    ==>
    challenge_query_log_count
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries <= n /\
    query_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy].
proof.
proc.
inline Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.C.get.
wp.
call (_ : true).
auto => />.
move=> &hr hnonchallenge hcount hall hpre hreprogram hentropy.
rewrite
  (challenge_query_log_count_nonchallenge_cons q{hr}
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries{hr}
    hnonchallenge).
exact hcount.
qed.

lemma mode2_concrete_programmed_query_sign_preserves_inv
    (sk0 : skey) (m0 : message) (ctx0 : context)
    (coins0 : random_coins) (trs0 : transcript list)
    (hashes0 : ro_query list) :
  hoare [Mode2ConcreteHonestProgrammedSigningQueryOracle(O).sign :
    sk = sk0 /\ m = m0 /\ ctx = ctx0 /\ coins = coins0 /\
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts = trs0 /\
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries = hashes0 /\
    query_distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy /\
    ! (concrete_signing_query sk0 m0 ctx0 coins0 \in hashes0) /\
    accumulated_query_fresh trs0 sk0 m0 ctx0 coins0
    ==>
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts =
      concrete_transcript sk0 m0 ctx0 coins0
        SignCoreChallengeTracePostFreeze.SignRawApiMuCpTrace.observed_cp
      :: trs0 /\
    Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries = hashes0 /\
    query_distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy].
proof.
proc.
inline Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.sign.
inline Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.C.observe_transcript
       Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.C.program.
wp.
call (_ : true ==> true); first by auto.
wp.
call
  (SignCoreChallengeTracePostFreeze.sign_raw_api_trace_concrete_honest_site_clear
    sk0 m0 ctx0 coins0).
auto => />.
rewrite /query_distinct_programmed_signing_inv
        /query_programmed_signing_inv
        /Mode2ChallengeROMProgrammingPostFreeze.mode2_transcript_log_min_entropy_clear /=.
move=> &hr hall hpre hreprogram hentropy huniq
        hqueryfresh htranscriptfresh
        observed_cp s hsubset hcard heq
        s0 hsubset0 hcard0 heq0.
have hreprfresh :=
  Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.accumulated_query_fresh_no_reprograms
    trs0 sk0 m0 ctx0 coins0 observed_cp htranscriptfresh.
have hmin :
    ! Mode2ChallengeROMProgrammingPostFreeze.mode2_min_entropy_failure
        (concrete_transcript sk0 m0 ctx0 coins0 observed_cp).
+ apply
    Mode2ChallengeROMProgrammingPostFreeze.mode2_carrier_valid_no_min_entropy_failure.
  exists s0.
  split.
  + split; [exact hsubset0 | exact hcard0].
  + exact heq0.
split.
+ split; first exact hmin.
  split; [exact hreprfresh | exact hmin].
+ have huniq_cons :=
    Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.transcript_queries_unique_cons
      sk0 m0 ctx0 coins0 observed_cp trs0 huniq htranscriptfresh.
  move: huniq_cons.
  rewrite /transcript_queries_unique
          /Mode2ConcreteHonestProgrammedSigningFreshnessPostFreeze.transcript_queries_unique /=.
  move=> [hnot _].
  exact hnot.
qed.

lemma mode2_concrete_programmed_query_bad_false_under_inv :
  hoare [Mode2ConcreteHonestProgrammedSigningQueryOracle(O).bad :
    query_distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy
    ==>
    ! res /\
    query_distinct_programmed_signing_inv
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.transcripts
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.signature_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.hash_queries
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.programmed_sites
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_prequery
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_reprogram
      Mode2ConcreteHonestProgrammedSigningQueryOracle.Base.C.bad_mode2_entropy].
proof.
proc.
inline Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.bad.
inline Mode2ConcreteHonestProgrammedSigningQueryOracle(O).Base.C.bad.
auto => />.
qed.

end section QueryOracleFacts.

end Mode2ConcreteHonestProgrammedSigningQueryOraclePostFreeze.
