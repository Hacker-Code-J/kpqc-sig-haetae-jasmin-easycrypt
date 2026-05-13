require import AllCore Real Distr List FSet PROM StdOrder Mu_mem.
require import HAETAE_Params HAETAE_Algebra HAETAE_Distributions.
require import HAETAE_ROM HAETAE_Transcript.
require import HAETAE_Rejection.
require import HAETAE_Reductions.

theory HAETAE_ROM_Programming.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Distributions.
import HAETAE_ROM.
import HAETAE_Transcript.
import HAETAE_Rejection.
import HAETAE_Reductions.
import RealOrder.

type programming_site = ro_query * ro_output.

op programming_site_query (site : programming_site) : ro_query = site.`1.
op programming_site_output (site : programming_site) : ro_output = site.`2.

op programming_site_of_transcript
   (md : mode) (tr : transcript) (y : ro_output) : programming_site =
  (transcript_challenge_query md tr, y).

op signature_programming_site_of_transcript
   (md : mode) (tr : transcript) (y : ro_output) : programming_site =
  (transcript_signature_challenge_query md tr, y).

op transcript_signature_challenge_output (tr : transcript) : ro_output =
  ro_output_of_challenge (sig_challenge (transcript_signature tr)).

op actual_signature_programming_site
   (md : mode) (tr : transcript) : programming_site =
  signature_programming_site_of_transcript md tr
    (transcript_signature_challenge_output tr).

op honest_signing_programming_site
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : programming_site =
  actual_signature_programming_site md
    (transcript_from_honest_signing md sk m ctx coins).

op honest_signing_programming_site_query
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : ro_query =
  programming_site_query
    (honest_signing_programming_site md sk m ctx coins).

op programmed_site_query_min_entropy_bound_for
   (d : random_coins distr)
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (qs : ro_query list) (bd : real) : bool =
  forall q, q \in qs =>
    mu d
      (fun coins =>
        honest_signing_programming_site_query md sk m ctx coins = q) <= bd.

op programmed_site_query_min_entropy_bound
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (qs : ro_query list) (bd : real) : bool =
  programmed_site_query_min_entropy_bound_for drandom_coins md sk m ctx qs bd.

op programming_site_matches_transcript
   (md : mode) (tr : transcript) (site : programming_site) : bool =
  programming_site_query site = transcript_challenge_query md tr /\
  transcript_challenge_matches tr (programming_site_output site).

op reprogramming_failure
   (md : mode) (tr : transcript) (site : programming_site) : bool =
  ! programming_site_matches_transcript md tr site.

op challenge_entropy_support_ok (md : mode) (tr : transcript) : bool =
  challenge_sparse md (transcript_challenge tr).

op min_entropy_failure (md : mode) (tr : transcript) : bool =
  ! challenge_entropy_support_ok md tr.

op transcript_log_min_entropy_clear (md : mode) (trs : transcript list) : bool =
  all (fun tr => ! min_entropy_failure md tr) trs.

op signing_record_log_min_entropy_clear
   (md : mode) (rs : signing_transcript_record list) : bool =
  all (fun r => ! min_entropy_failure md (signing_record_transcript r)) rs.

op fs_with_aborts_failure
   (md : mode) (tr : transcript) (site : programming_site) : bool =
  reprogramming_failure md tr site \/ min_entropy_failure md tr.

op transcript_signature_programming_site_clear
   (md : mode) (tr : transcript) : bool =
  ! fs_with_aborts_failure md tr (actual_signature_programming_site md tr).

op transcript_log_signature_programming_sites_clear
   (md : mode) (trs : transcript list) : bool =
  all (transcript_signature_programming_site_clear md) trs.

op fs_with_aborts_bound_obligation : bool =
  0%r <= fs_with_aborts_reprogramming_term /\
  0%r <= fs_with_aborts_min_entropy_term.

type counted_rom_event =
  [ CountedHashQuery of ro_query
  | CountedSignatureSite of programming_site
  | CountedProgrammedSite of programming_site
  | CountedMinEntropyCheck of transcript ].

op counted_event_is_hash_query (ev : counted_rom_event) : bool =
  with ev = CountedHashQuery _ => true
  with ev = CountedSignatureSite _ => false
  with ev = CountedProgrammedSite _ => false
  with ev = CountedMinEntropyCheck _ => false.

op counted_event_is_signature_site (ev : counted_rom_event) : bool =
  with ev = CountedHashQuery _ => false
  with ev = CountedSignatureSite _ => true
  with ev = CountedProgrammedSite _ => false
  with ev = CountedMinEntropyCheck _ => false.

op counted_event_is_programmed_site (ev : counted_rom_event) : bool =
  with ev = CountedHashQuery _ => false
  with ev = CountedSignatureSite _ => false
  with ev = CountedProgrammedSite _ => true
  with ev = CountedMinEntropyCheck _ => false.

op counted_event_is_min_entropy_check (ev : counted_rom_event) : bool =
  with ev = CountedHashQuery _ => false
  with ev = CountedSignatureSite _ => false
  with ev = CountedProgrammedSite _ => false
  with ev = CountedMinEntropyCheck _ => true.

op ro_query_is_challenge (q : ro_query) : bool =
  with q = MessageHashQuery _ => false
  with q = ChallengeHashQuery _ => true
  with q = MatrixExpandQuery _ => false
  with q = SamplerExpandQuery _ => false.

op challenge_query_log_count (qs : ro_query list) : int =
  card (oflist (filter ro_query_is_challenge qs)).

lemma challenge_query_log_count_cons_le q qs :
  challenge_query_log_count (q :: qs) <=
  challenge_query_log_count qs + 1.
proof.
rewrite /challenge_query_log_count.
case q => /=.
+ smt().
+ move=> site.
  rewrite oflist_cons fsetUC fcardU1.
  smt().
+ smt().
+ smt().
qed.

lemma challenge_query_log_count_nonchallenge_cons q qs :
  ! ro_query_is_challenge q =>
  challenge_query_log_count (q :: qs) =
  challenge_query_log_count qs.
proof.
rewrite /challenge_query_log_count.
case q => /=.
+ by done.
+ by done.
+ by done.
+ by done.
qed.

lemma challenge_query_log_count_message_cons pk ctx m qs :
  challenge_query_log_count (message_hash_query pk ctx m :: qs) =
  challenge_query_log_count qs.
proof.
apply challenge_query_log_count_nonchallenge_cons.
by rewrite /message_hash_query /ro_query_is_challenge.
qed.

lemma challenge_query_log_count_matrix_cons md sd qs :
  challenge_query_log_count (matrix_expand_query md sd :: qs) =
  challenge_query_log_count qs.
proof.
apply challenge_query_log_count_nonchallenge_cons.
by rewrite /matrix_expand_query /ro_query_is_challenge.
qed.

lemma challenge_query_log_count_sampler_cons coins qs :
  challenge_query_log_count (sampler_expand_query coins :: qs) =
  challenge_query_log_count qs.
proof.
apply challenge_query_log_count_nonchallenge_cons.
by rewrite /sampler_expand_query /ro_query_is_challenge.
qed.

op counted_trace_hash_queries (evs : counted_rom_event list) : int =
  size (filter counted_event_is_hash_query evs).

op counted_trace_signature_sites (evs : counted_rom_event list) : int =
  size (filter counted_event_is_signature_site evs).

op counted_trace_programmed_sites (evs : counted_rom_event list) : int =
  size (filter counted_event_is_programmed_site evs).

op counted_trace_min_entropy_checks (evs : counted_rom_event list) : int =
  size (filter counted_event_is_min_entropy_check evs).

op programming_sites_same_query
   (left right : programming_site) : bool =
  programming_site_query left = programming_site_query right.

op programming_sites_conflict
   (left right : programming_site) : bool =
  programming_sites_same_query left right /\
  programming_site_output left <> programming_site_output right.

op programming_site_prequeried
   (queries : ro_query list) (site : programming_site) : bool =
  programming_site_query site \in queries.

op programming_site_reprograms
   (programmed : programming_site list) (site : programming_site) : bool =
  has (fun old => programming_sites_conflict site old) programmed.

op programming_site_fresh
   (queries : ro_query list) (programmed : programming_site list)
   (site : programming_site) : bool =
  ! programming_site_prequeried queries site /\
  ! programming_site_reprograms programmed site.

op programming_transcript_fresh
   (md : mode) (queries : ro_query list)
   (programmed : programming_site list) (tr : transcript) : bool =
  programming_site_fresh queries programmed
    (actual_signature_programming_site md tr) /\
  ! min_entropy_failure md tr.

op rom_counted_programming_bad
   (queries : ro_query list) (programmed : programming_site list)
   (entropy_bad : bool) : bool =
  entropy_bad \/
  has (fun site => programming_site_prequeried queries site) programmed \/
  has (fun site => programming_site_reprograms programmed site) programmed.

op rom_counted_state_bad
   (queries : ro_query list) (programmed : programming_site list)
   (bad_min_entropy : bool) : bool =
  rom_counted_programming_bad queries programmed bad_min_entropy.

op counted_rom_programming_bound_obligation : bool =
  0%r <= counted_rom_programming_loss_term.

module CountedLazyROM(O : Oracle) = {
  var hash_queries : ro_query list
  var programmed_sites : programming_site list
  var signature_sites : programming_site list
  var bad_prequery : bool
  var bad_reprogram : bool
  var bad_min_entropy : bool

  proc init() : unit = {
    O.init();
    hash_queries <- [];
    programmed_sites <- [];
    signature_sites <- [];
    bad_prequery <- false;
    bad_reprogram <- false;
    bad_min_entropy <- false;
  }

  proc get(q : ro_query) : ro_output = {
    var y : ro_output;

    y <@ O.get(q);
    hash_queries <- q :: hash_queries;
    return y;
  }

  proc program(site : programming_site) : unit = {
    bad_prequery <-
      bad_prequery \/ programming_site_prequeried hash_queries site;
    bad_reprogram <-
      bad_reprogram \/ programming_site_reprograms programmed_sites site;
    programmed_sites <- site :: programmed_sites;
    O.set(programming_site_query site, programming_site_output site);
  }

  proc observe_signature_site(site : programming_site) : unit = {
    signature_sites <- site :: signature_sites;
  }

  proc observe_transcript(md : mode, tr : transcript) : unit = {
    var site : programming_site;

    site <- actual_signature_programming_site md tr;
    bad_min_entropy <- bad_min_entropy \/ min_entropy_failure md tr;
    signature_sites <- site :: signature_sites;
  }

  proc bad() : bool = {
    return bad_prequery \/ bad_reprogram \/ bad_min_entropy;
  }
}.

module type SigningCoinSampler = {
  proc sample() : random_coins
}.

module DirectSigningCoinSampler : SigningCoinSampler = {
  proc sample() : random_coins = {
    var coins : random_coins;

    coins <$ drandom_coins;
    return coins;
  }
}.

section CountedLazyROMStateFacts.

declare module O <: Oracle {-CountedLazyROM}.

lemma counted_lazy_rom_init_clears :
  hoare[CountedLazyROM(O).init :
    true ==>
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy /\
    CountedLazyROM.programmed_sites = []].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma counted_lazy_rom_init_clears_hash_queries :
  hoare[CountedLazyROM(O).init :
    true ==> CountedLazyROM.hash_queries = []].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma counted_lazy_rom_get_preserves_clear :
  hoare[CountedLazyROM(O).get :
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy /\
    CountedLazyROM.programmed_sites = [] ==>
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy /\
    CountedLazyROM.programmed_sites = []].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma counted_lazy_rom_get_nonchallenge_preserves_challenge_query_count n :
  hoare[CountedLazyROM(O).get :
    ! ro_query_is_challenge q /\
    challenge_query_log_count CountedLazyROM.hash_queries <= n ==>
    challenge_query_log_count CountedLazyROM.hash_queries <= n].
proof.
proc.
wp.
call (_: true).
by auto => />; smt.
qed.

lemma counted_lazy_rom_get_preserves_bad_clear :
  hoare[CountedLazyROM(O).get :
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy ==>
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma counted_lazy_rom_get_preserves_min_entropy_clear :
  hoare[CountedLazyROM(O).get :
    ! CountedLazyROM.bad_min_entropy ==>
    ! CountedLazyROM.bad_min_entropy].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma counted_lazy_rom_observe_transcript_preserves_clear :
  hoare[CountedLazyROM(O).observe_transcript :
    ! min_entropy_failure md tr /\
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy /\
    CountedLazyROM.programmed_sites = [] ==>
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy /\
    CountedLazyROM.programmed_sites = []].
proof.
proc.
wp.
skip.
move=> &hr [min_ok [preq_ok [reprog_ok [entropy_ok programmed_ok]]]].
by rewrite min_ok entropy_ok.
qed.

lemma counted_lazy_rom_observe_transcript_preserves_min_entropy_clear :
  hoare[CountedLazyROM(O).observe_transcript :
    ! min_entropy_failure md tr /\
    ! CountedLazyROM.bad_min_entropy ==>
    ! CountedLazyROM.bad_min_entropy].
proof.
proc.
wp.
skip.
move=> &hr [min_ok entropy_ok].
by rewrite min_ok entropy_ok.
qed.

lemma counted_lazy_rom_observe_transcript_preserves_bad_clear :
  hoare[CountedLazyROM(O).observe_transcript :
    ! min_entropy_failure md tr /\
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy ==>
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy].
proof.
proc.
wp.
skip.
move=> &hr [min_ok [preq_ok [reprog_ok entropy_ok]]].
by rewrite min_ok entropy_ok.
qed.

lemma counted_lazy_rom_program_preserves_bad_clear_if_fresh :
  hoare[CountedLazyROM(O).program :
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy /\
    programming_site_fresh
      CountedLazyROM.hash_queries
      CountedLazyROM.programmed_sites site ==>
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy].
proof.
proc.
wp.
call (_: true).
by auto => />.
qed.

lemma counted_lazy_rom_program_preserves_min_entropy_clear :
  hoare[CountedLazyROM(O).program :
    ! CountedLazyROM.bad_min_entropy ==>
    ! CountedLazyROM.bad_min_entropy].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma counted_lazy_rom_bad_preserves_min_entropy_clear :
  hoare[CountedLazyROM(O).bad :
    ! CountedLazyROM.bad_min_entropy ==>
    ! CountedLazyROM.bad_min_entropy].
proof.
proc.
skip.
by auto.
qed.

lemma counted_lazy_rom_bad_false_when_clear :
  hoare[CountedLazyROM(O).bad :
    ! CountedLazyROM.bad_prequery /\
    ! CountedLazyROM.bad_reprogram /\
    ! CountedLazyROM.bad_min_entropy ==>
    ! res].
proof.
proc.
skip.
move=> &hr [preq_ok [reprog_ok entropy_ok]].
by rewrite preq_ok reprog_ok entropy_ok.
qed.

end section CountedLazyROMStateFacts.

module type CountedROMInterface = {
  proc get(q : ro_query) : ro_output
  proc program(site : programming_site) : unit
  proc observe_signature_site(site : programming_site) : unit
  proc observe_transcript(md : mode, tr : transcript) : unit
}.

module type CountedROMClient(C : CountedROMInterface) = {
  proc run() : unit {
    C.get,
    C.program,
    C.observe_signature_site,
    C.observe_transcript
  }
}.

module CountedLazyROMBadGame(
  O : Oracle,
  A : CountedROMClient
) = {
  module C = CountedLazyROM(O)
  module A = A(C)

  proc main() : bool = {
    var bad : bool;

    C.init();
    A.run();
    bad <@ C.bad();
    return bad;
  }
}.

module ProgramChallenge(O : Oracle) = {
  proc program(site : programming_site) : unit = {
    O.set(programming_site_query site, programming_site_output site);
  }
}.

module type TranscriptProgrammer(O : Oracle) = {
  proc program(md : mode, tr : transcript, y : ro_output) : unit
}.

module TranscriptProgrammerFromSite(O : Oracle) = {
  proc program(md : mode, tr : transcript, y : ro_output) : unit = {
    ProgramChallenge(O).program(programming_site_of_transcript md tr y);
  }
}.

lemma programming_site_self_matches md tr y :
  transcript_challenge_matches tr y =>
  programming_site_matches_transcript md tr
    (programming_site_of_transcript md tr y).
proof.
by rewrite /programming_site_matches_transcript
           /programming_site_of_transcript
           /programming_site_query /programming_site_output.
qed.

lemma programming_site_self_no_reprogramming_failure md tr y :
  transcript_challenge_matches tr y =>
  ! reprogramming_failure md tr (programming_site_of_transcript md tr y).
proof.
move=> match_y.
rewrite /reprogramming_failure.
by rewrite (programming_site_self_matches md tr y match_y).
qed.

lemma fs_with_aborts_failureE md tr site :
  fs_with_aborts_failure md tr site =
  (reprogramming_failure md tr site \/ min_entropy_failure md tr).
proof. by rewrite /fs_with_aborts_failure. qed.

lemma programming_site_prequeried_cons qs site :
  programming_site_prequeried (programming_site_query site :: qs) site.
proof. by rewrite /programming_site_prequeried. qed.

lemma programming_site_prequeried_cons_preserve q qs site :
  programming_site_prequeried qs site =>
  programming_site_prequeried (q :: qs) site.
proof. by rewrite /programming_site_prequeried /=; smt. qed.

lemma programming_site_prequeried_output_irrelevant qs q y1 y2 :
  programming_site_prequeried qs (q, y1) =
  programming_site_prequeried qs (q, y2).
proof. by rewrite /programming_site_prequeried /programming_site_query. qed.

lemma programming_site_prequeried_witness qs q y :
  q \in qs =>
  programming_site_prequeried qs (q, y).
proof. by rewrite /programming_site_prequeried /programming_site_query. qed.

lemma honest_signing_programming_site_queryE md sk m ctx coins :
  honest_signing_programming_site_query md sk m ctx coins =
  challenge_hash_query md
    (commitment_highbits md sk m ctx coins)
    (commitment_lowbits md sk m ctx coins)
    (message_hash (public_key_of_secret md sk) ctx m).
proof.
by rewrite /honest_signing_programming_site_query
           /honest_signing_programming_site
           /actual_signature_programming_site
           /signature_programming_site_of_transcript
           /programming_site_query
           /transcript_from_honest_signing
           /transcript_of_signature
           /sig_commitment_highbits /sig_commitment_lowbits
           /sig_message_hash /sign_internal /=.
qed.

op programmed_site_entropy_token_from_query (q : ro_query) : int =
  with q = ChallengeHashQuery x => nth 0 x.`3 0
  with q = MessageHashQuery _ => 0
  with q = MatrixExpandQuery _ => 0
  with q = SamplerExpandQuery _ => 0.

lemma honest_signing_programming_site_query_entropy_token
  md sk m ctx coins :
  programmed_site_entropy_token_from_query
    (honest_signing_programming_site_query md sk m ctx coins) =
  signing_entropy_token_of_coins coins.
proof.
rewrite honest_signing_programming_site_queryE
        /challenge_hash_query
        /programmed_site_entropy_token_from_query /=.
by apply commitment_lowbits_entropy_token.
qed.

lemma honest_signing_programming_site_query_token_injective
  md sk m ctx x q :
  signing_entropy_token_in_range x =>
  honest_signing_programming_site_query md sk m ctx
    (signing_entropy_token_to_coins x) = q =>
  x = programmed_site_entropy_token_from_query q.
proof.
move=> xrange query_eq.
have h :=
  honest_signing_programming_site_query_entropy_token
    md sk m ctx (signing_entropy_token_to_coins x).
rewrite query_eq (signing_entropy_token_to_coins_tokenK x) in h.
by rewrite h.
qed.

lemma signing_distribution_programming_site_query_spread
  (d : random_coins distr) md sk m ctx q :
  signing_randomness_token_spread d =>
  mu d
    (fun coins =>
      honest_signing_programming_site_query md sk m ctx coins = q) <=
  1%r / challenge_support_cardinality_lower_bound.
proof.
move=> token_spread.
apply (ler_trans
  (mu d
    (fun coins =>
      signing_entropy_token_of_coins coins =
      programmed_site_entropy_token_from_query q))).
+ apply mu_le => coins _ query_eq.
  have h :=
    honest_signing_programming_site_query_entropy_token
      md sk m ctx coins.
  rewrite query_eq in h.
  by smt.
apply (ler_trans
  signing_randomness_point_bound).
+ by rewrite /signing_randomness_token_spread in token_spread;
     apply token_spread.
by rewrite /signing_randomness_point_bound
           /signing_entropy_token_cardinality
           /challenge_support_cardinality_lower_bound.
qed.

lemma honest_signing_programming_site_query_spread
  md sk m ctx q :
  mu drandom_coins
    (fun coins =>
      honest_signing_programming_site_query md sk m ctx coins = q) <=
  1%r / challenge_support_cardinality_lower_bound.
proof.
by apply signing_distribution_programming_site_query_spread;
   apply signing_coin_distribution_token_spread.
qed.

lemma honest_signing_programming_site_query_spread_bound
  md sk m ctx qs :
  programmed_site_query_min_entropy_bound md sk m ctx qs
    (1%r / challenge_support_cardinality_lower_bound).
proof.
rewrite /programmed_site_query_min_entropy_bound.
move=> q _.
by apply honest_signing_programming_site_query_spread.
qed.

lemma honest_signing_programming_site_query_spread_bound_for
  (d : random_coins distr) md sk m ctx qs :
  signing_randomness_token_spread d =>
  programmed_site_query_min_entropy_bound_for d md sk m ctx qs
    (1%r / challenge_support_cardinality_lower_bound).
proof.
move=> spread q _.
by apply signing_distribution_programming_site_query_spread.
qed.

lemma honest_signing_programming_site_query_is_challenge
  md sk m ctx coins :
  ro_query_is_challenge
    (honest_signing_programming_site_query md sk m ctx coins).
proof.
by rewrite honest_signing_programming_site_queryE
           /challenge_hash_query /ro_query_is_challenge.
qed.

lemma programming_site_prequeried_honest_challenge_filter
  qs md sk m ctx coins :
  programming_site_prequeried qs
    (honest_signing_programming_site md sk m ctx coins) =
  programming_site_prequeried (filter ro_query_is_challenge qs)
    (honest_signing_programming_site md sk m ctx coins).
proof.
rewrite /programming_site_prequeried
        /honest_signing_programming_site_query.
rewrite mem_filter.
by rewrite honest_signing_programming_site_query_is_challenge.
qed.

lemma programming_site_prequeried_honest_message_consE
  pk ctx m qs md sk sm sctx coins :
  programming_site_prequeried (message_hash_query pk ctx m :: qs)
    (honest_signing_programming_site md sk sm sctx coins) =
  programming_site_prequeried qs
    (honest_signing_programming_site md sk sm sctx coins).
proof.
rewrite /programming_site_prequeried
        /programming_site_query
        /honest_signing_programming_site
        /actual_signature_programming_site
        /signature_programming_site_of_transcript
        /transcript_signature_challenge_query
        /transcript_from_honest_signing
        /transcript_of_signature
        /message_hash_query /challenge_hash_query /=.
by smt.
qed.

lemma honest_signing_programming_site_outputE md sk m ctx coins :
  programming_site_output
    (honest_signing_programming_site md sk m ctx coins) =
  ro_output_of_challenge
    (challenge_hash md
      (commitment_highbits md sk m ctx coins)
      (commitment_lowbits md sk m ctx coins)
      (message_hash (public_key_of_secret md sk) ctx m)).
proof.
by rewrite /honest_signing_programming_site
           /actual_signature_programming_site
           /signature_programming_site_of_transcript
           /programming_site_output
           /transcript_signature_challenge_output
           /transcript_from_honest_signing
           /transcript_of_signature /sig_challenge
           /sign_internal /=.
qed.

lemma honest_signing_programming_site_functional_output
  md sk1 m1 ctx1 coins1 sk2 m2 ctx2 coins2 :
  honest_signing_programming_site_query md sk1 m1 ctx1 coins1 =
  honest_signing_programming_site_query md sk2 m2 ctx2 coins2 =>
  programming_site_output
    (honest_signing_programming_site md sk1 m1 ctx1 coins1) =
  programming_site_output
    (honest_signing_programming_site md sk2 m2 ctx2 coins2).
proof.
rewrite !honest_signing_programming_site_queryE
        !honest_signing_programming_site_outputE.
by smt.
qed.

lemma honest_signing_programming_sites_no_conflict
  md sk1 m1 ctx1 coins1 sk2 m2 ctx2 coins2 :
  ! programming_sites_conflict
      (honest_signing_programming_site md sk1 m1 ctx1 coins1)
      (honest_signing_programming_site md sk2 m2 ctx2 coins2).
proof.
rewrite /programming_sites_conflict /programming_sites_same_query.
case: (programming_site_query
        (honest_signing_programming_site md sk1 m1 ctx1 coins1) =
       programming_site_query
        (honest_signing_programming_site md sk2 m2 ctx2 coins2)) => //.
move=> query_eq.
rewrite /=.
by apply (honest_signing_programming_site_functional_output
            md sk1 m1 ctx1 coins1 sk2 m2 ctx2 coins2).
qed.

lemma actual_signature_programming_site_sign_internalE
  md pk sk m ctx coins :
  pk = public_key_of_secret md sk =>
  actual_signature_programming_site md
    (transcript_of_signature md pk m ctx
      (sign_internal md sk m ctx coins)) =
  honest_signing_programming_site md sk m ctx coins.
proof.
move=> pkE.
rewrite /honest_signing_programming_site /transcript_from_honest_signing.
by rewrite pkE.
qed.

lemma actual_signature_programming_site_sign_internal_any_pkE
  md pk sk m ctx coins :
  actual_signature_programming_site md
    (transcript_of_signature md pk m ctx
      (sign_internal md sk m ctx coins)) =
  honest_signing_programming_site md sk m ctx coins.
proof.
by rewrite /honest_signing_programming_site /transcript_from_honest_signing
           /actual_signature_programming_site
           /signature_programming_site_of_transcript
           /transcript_signature_challenge_query
           /transcript_signature_challenge_output
           /transcript_of_signature /=.
qed.

lemma actual_signature_programming_site_prequeried_after_cons
  md pk sk m ctx coins q qs :
  pk = public_key_of_secret md sk =>
  programming_site_prequeried qs
    (honest_signing_programming_site md sk m ctx coins) =>
  programming_site_prequeried (q :: qs)
    (actual_signature_programming_site md
      (transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx coins))).
proof.
move=> pkE pre.
rewrite (actual_signature_programming_site_sign_internalE
           md pk sk m ctx coins pkE).
by apply programming_site_prequeried_cons_preserve.
qed.

lemma actual_signature_programming_site_prequeried_after_message_hash
  md pk sk m ctx coins qpk qctx qm qs :
  pk = public_key_of_secret md sk =>
  programming_site_prequeried qs
    (honest_signing_programming_site md sk m ctx coins) =>
  programming_site_prequeried (message_hash_query qpk qctx qm :: qs)
    (actual_signature_programming_site md
      (transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx coins))).
proof.
move=> pkE pre.
by apply (actual_signature_programming_site_prequeried_after_cons
            md pk sk m ctx coins (message_hash_query qpk qctx qm) qs).
qed.

lemma actual_signature_programming_site_prequeried_message_hashE
  md pk sk m ctx coins qpk qctx qm qs :
  pk = public_key_of_secret md sk =>
  programming_site_prequeried (message_hash_query qpk qctx qm :: qs)
    (actual_signature_programming_site md
      (transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx coins))) =
  programming_site_prequeried qs
    (honest_signing_programming_site md sk m ctx coins).
proof.
move=> pkE.
rewrite (actual_signature_programming_site_sign_internalE
           md pk sk m ctx coins pkE).
by rewrite programming_site_prequeried_honest_message_consE.
qed.

lemma actual_signature_programming_site_prequeried_message_hash_any_pkE
  md pk sk m ctx coins qpk qctx qm qs :
  programming_site_prequeried (message_hash_query qpk qctx qm :: qs)
    (actual_signature_programming_site md
      (transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx coins))) =
  programming_site_prequeried qs
    (honest_signing_programming_site md sk m ctx coins).
proof.
rewrite (actual_signature_programming_site_sign_internal_any_pkE
           md pk sk m ctx coins).
by rewrite programming_site_prequeried_honest_message_consE.
qed.

op programming_site_conflict_free
   (site : programming_site) (sites : programming_site list) : bool =
  all (fun old => ! programming_sites_conflict site old) sites.

op programming_site_log_conflict_free_for_honest
   (md : mode) (sk : skey) (sites : programming_site list) : bool =
  forall m ctx coins,
    programming_site_conflict_free
      (honest_signing_programming_site md sk m ctx coins) sites.

lemma programming_site_log_conflict_free_for_honest_nil md sk :
  programming_site_log_conflict_free_for_honest md sk [].
proof. by rewrite /programming_site_log_conflict_free_for_honest
                  /programming_site_conflict_free.
qed.

lemma programming_site_log_conflict_free_for_honest_cons
  md sk m ctx coins sites :
  programming_site_log_conflict_free_for_honest md sk sites =>
  programming_site_log_conflict_free_for_honest md sk
    (honest_signing_programming_site md sk m ctx coins :: sites).
proof.
rewrite /programming_site_log_conflict_free_for_honest.
move=> log m' ctx' coins'.
rewrite /programming_site_conflict_free /=.
split.
+ by apply honest_signing_programming_sites_no_conflict.
by apply log.
qed.

lemma programming_site_conflict_free_no_reprograms site sites :
  programming_site_conflict_free site sites =>
  ! programming_site_reprograms sites site.
proof.
rewrite /programming_site_conflict_free /programming_site_reprograms.
move/allP=> no_conflict.
apply/hasPn=> old old_mem.
by apply no_conflict.
qed.

lemma actual_signature_programming_site_sign_internal_conflict_step
  md pk sk m ctx coins sites :
  pk = public_key_of_secret md sk =>
  programming_site_log_conflict_free_for_honest md sk sites =>
  ! programming_site_reprograms sites
      (actual_signature_programming_site md
        (transcript_of_signature md pk m ctx
          (sign_internal md sk m ctx coins))) /\
  programming_site_log_conflict_free_for_honest md sk
    (actual_signature_programming_site md
      (transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx coins)) :: sites).
proof.
move=> pkE log.
have siteE :=
  actual_signature_programming_site_sign_internalE
    md pk sk m ctx coins pkE.
split.
+ rewrite siteE.
  apply programming_site_conflict_free_no_reprograms.
  by apply log.
rewrite siteE.
by apply programming_site_log_conflict_free_for_honest_cons.
qed.

lemma programmed_site_reprogram_one_step_conflict_free_zero
  md sk m ctx sites :
  (forall coins,
    programming_site_conflict_free
      (honest_signing_programming_site md sk m ctx coins) sites) =>
  mu drandom_coins
    (fun coins =>
      programming_site_reprograms sites
        (honest_signing_programming_site md sk m ctx coins)) =
  0%r.
proof.
move=> conflict_free.
rewrite (mu_eq _ _ (fun (_ : random_coins) => false)).
+ move=> coins.
  by rewrite (programming_site_conflict_free_no_reprograms
                (honest_signing_programming_site md sk m ctx coins)
                sites (conflict_free coins)).
by rewrite mu0.
qed.

lemma programmed_site_prequery_one_step_fset_bound_for
  (d : random_coins distr) md sk m ctx qs bd :
  programmed_site_query_min_entropy_bound_for d md sk m ctx qs bd =>
  mu d
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (card (oflist qs))%r * bd.
proof.
rewrite /programmed_site_query_min_entropy_bound_for
        /programming_site_prequeried
        /honest_signing_programming_site_query.
move=> spread.
rewrite (mu_eq _ _
  (fun coins =>
    exists q, q \in oflist qs /\
      programming_site_query
        (honest_signing_programming_site md sk m ctx coins) = q)).
+ move=> coins.
  by smt.
apply (mu_mem_le_gen (oflist qs) d
        (fun q coins =>
          programming_site_query
            (honest_signing_programming_site md sk m ctx coins) = q)
        bd).
move=> q q_mem.
apply spread.
by rewrite -mem_oflist.
qed.

lemma programmed_site_prequery_one_step_fset_bound
  md sk m ctx qs bd :
  programmed_site_query_min_entropy_bound md sk m ctx qs bd =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (card (oflist qs))%r * bd.
proof.
rewrite /programmed_site_query_min_entropy_bound.
by apply programmed_site_prequery_one_step_fset_bound_for.
qed.

lemma programmed_site_prequery_one_step_budget_bound_for
  (d : random_coins distr) md sk m ctx qs :
  (card (oflist qs))%r <= rom_hash_query_budget + 1%r =>
  programmed_site_query_min_entropy_bound_for d md sk m ctx qs
    (1%r / challenge_support_cardinality_lower_bound) =>
  mu d
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> card_budget spread.
have h :=
  programmed_site_prequery_one_step_fset_bound_for
    d md sk m ctx qs
    (1%r / challenge_support_cardinality_lower_bound) spread.
apply (ler_trans ((card (oflist qs))%r *
        (1%r / challenge_support_cardinality_lower_bound))).
+ by apply h.
have inv_nonneg :
  0%r <= inv challenge_support_cardinality_lower_bound.
+ by rewrite invr_ge0; apply challenge_support_cardinality_lower_bound_nonnegative.
have := ler_wpmul2r
  (1%r / challenge_support_cardinality_lower_bound)
  inv_nonneg
  (card (oflist qs))%r
  (rom_hash_query_budget + 1%r)
  card_budget.
by smt.
qed.

lemma programmed_site_prequery_one_step_budget_bound
  md sk m ctx qs :
  (card (oflist qs))%r <= rom_hash_query_budget + 1%r =>
  programmed_site_query_min_entropy_bound md sk m ctx qs
    (1%r / challenge_support_cardinality_lower_bound) =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> card_budget.
rewrite /programmed_site_query_min_entropy_bound.
by apply programmed_site_prequery_one_step_budget_bound_for.
qed.

lemma programmed_site_prequery_one_step_challenge_fset_bound_for
  (d : random_coins distr) md sk m ctx qs bd :
  programmed_site_query_min_entropy_bound_for d md sk m ctx
    (filter ro_query_is_challenge qs) bd =>
  mu d
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (card (oflist (filter ro_query_is_challenge qs)))%r * bd.
proof.
move=> spread.
rewrite (mu_eq _ _
  (fun coins =>
    programming_site_prequeried (filter ro_query_is_challenge qs)
      (honest_signing_programming_site md sk m ctx coins))).
+ move=> coins.
  by rewrite programming_site_prequeried_honest_challenge_filter.
by apply programmed_site_prequery_one_step_fset_bound_for.
qed.

lemma programmed_site_prequery_one_step_challenge_fset_bound
  md sk m ctx qs bd :
  programmed_site_query_min_entropy_bound md sk m ctx
    (filter ro_query_is_challenge qs) bd =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (card (oflist (filter ro_query_is_challenge qs)))%r * bd.
proof.
rewrite /programmed_site_query_min_entropy_bound.
by apply programmed_site_prequery_one_step_challenge_fset_bound_for.
qed.

lemma programmed_site_prequery_one_step_challenge_budget_bound_for
  (d : random_coins distr) md sk m ctx qs :
  (card (oflist (filter ro_query_is_challenge qs)))%r <=
    rom_hash_query_budget + 1%r =>
  programmed_site_query_min_entropy_bound_for d md sk m ctx
    (filter ro_query_is_challenge qs)
    (1%r / challenge_support_cardinality_lower_bound) =>
  mu d
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> card_budget spread.
have h :=
  programmed_site_prequery_one_step_challenge_fset_bound_for
    d md sk m ctx qs
    (1%r / challenge_support_cardinality_lower_bound) spread.
apply (ler_trans ((card (oflist (filter ro_query_is_challenge qs)))%r *
        (1%r / challenge_support_cardinality_lower_bound))).
+ by apply h.
have inv_nonneg :
  0%r <= inv challenge_support_cardinality_lower_bound.
+ by rewrite invr_ge0; apply challenge_support_cardinality_lower_bound_nonnegative.
have := ler_wpmul2r
  (1%r / challenge_support_cardinality_lower_bound)
  inv_nonneg
  (card (oflist (filter ro_query_is_challenge qs)))%r
  (rom_hash_query_budget + 1%r)
  card_budget.
by smt.
qed.

lemma programmed_site_prequery_one_step_challenge_budget_bound
  md sk m ctx qs :
  (card (oflist (filter ro_query_is_challenge qs)))%r <=
    rom_hash_query_budget + 1%r =>
  programmed_site_query_min_entropy_bound md sk m ctx
    (filter ro_query_is_challenge qs)
    (1%r / challenge_support_cardinality_lower_bound) =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> card_budget.
rewrite /programmed_site_query_min_entropy_bound.
by apply programmed_site_prequery_one_step_challenge_budget_bound_for.
qed.

lemma programmed_site_prequery_one_step_challenge_concrete_bound
  md sk m ctx qs :
  (card (oflist (filter ro_query_is_challenge qs)))%r <=
    rom_hash_query_budget + 1%r =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> card_budget.
apply programmed_site_prequery_one_step_challenge_budget_bound.
+ by apply card_budget.
by apply honest_signing_programming_site_query_spread_bound.
qed.

lemma programmed_site_prequery_one_step_challenge_concrete_bound_for
  (d : random_coins distr) md sk m ctx qs :
  signing_randomness_token_spread d =>
  (card (oflist (filter ro_query_is_challenge qs)))%r <=
    rom_hash_query_budget + 1%r =>
  mu d
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> spread card_budget.
apply programmed_site_prequery_one_step_challenge_budget_bound_for.
+ by apply card_budget.
by apply honest_signing_programming_site_query_spread_bound_for.
qed.

lemma challenge_query_log_count_budget_card_bound hc qs :
  0 <= hc =>
  hc <= hash_query_budget_count =>
  challenge_query_log_count qs <= hc + 1 =>
  (card (oflist (filter ro_query_is_challenge qs)))%r <=
    rom_hash_query_budget + 1%r.
proof.
rewrite /challenge_query_log_count
        /rom_hash_query_budget /hash_query_count /hash_query_budget_count.
smt.
qed.

lemma programmed_site_prequery_one_step_challenge_counter_bound
  md sk m ctx qs hc :
  0 <= hc =>
  hc <= hash_query_budget_count =>
  challenge_query_log_count qs <= hc + 1 =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> hc_ge0 hc_budget query_count.
apply programmed_site_prequery_one_step_challenge_concrete_bound.
by apply (challenge_query_log_count_budget_card_bound hc qs).
qed.

lemma programmed_site_prequery_one_step_challenge_counter_bound_for
  (d : random_coins distr) md sk m ctx qs hc :
  signing_randomness_token_spread d =>
  0 <= hc =>
  hc <= hash_query_budget_count =>
  challenge_query_log_count qs <= hc + 1 =>
  mu d
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> spread hc_ge0 hc_budget query_count.
apply programmed_site_prequery_one_step_challenge_concrete_bound_for.
+ by apply spread.
by apply (challenge_query_log_count_budget_card_bound hc qs).
qed.

lemma programmed_site_prequery_one_step_message_hash_counter_bound
  md pk sk m ctx qpk qctx qm qs hc :
  0 <= hc =>
  hc <= hash_query_budget_count =>
  challenge_query_log_count qs <= hc + 1 =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried (message_hash_query qpk qctx qm :: qs)
        (actual_signature_programming_site md
          (transcript_of_signature md pk m ctx
            (sign_internal md sk m ctx coins)))) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> hc_ge0 hc_budget query_count.
rewrite (mu_eq _ _
  (fun coins =>
    programming_site_prequeried qs
      (honest_signing_programming_site md sk m ctx coins))).
+ move=> coins.
  by rewrite (actual_signature_programming_site_prequeried_message_hash_any_pkE
                md pk sk m ctx coins qpk qctx qm qs).
by apply (programmed_site_prequery_one_step_challenge_counter_bound
            md sk m ctx qs hc).
qed.

lemma direct_signing_coin_sampler_prequery_bound
  md sk m ctx qs hc :
  0 <= hc =>
  hc <= hash_query_budget_count =>
  challenge_query_log_count qs <= hc + 1 =>
  phoare[DirectSigningCoinSampler.sample :
    true ==>
    programming_site_prequeried qs
      (honest_signing_programming_site md sk m ctx res)] <=
  ((rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound).
proof.
move=> hc_ge0 hc_budget query_count.
bypr=> &m _.
byphoare (_: true ==>
  programming_site_prequeried qs
    (honest_signing_programming_site md sk m ctx res)) => //.
proc.
rnd (fun coins =>
  programming_site_prequeried qs
    (honest_signing_programming_site md sk m ctx coins)).
auto => />.
by apply (programmed_site_prequery_one_step_challenge_counter_bound
	            md sk m ctx qs hc).
qed.

lemma direct_signing_coin_sampler_budgeted_prequery_bound
  md sk m ctx qs :
  challenge_query_log_count qs <= hash_query_budget_count + 1 =>
  phoare[DirectSigningCoinSampler.sample :
    true ==>
    programming_site_prequeried qs
      (honest_signing_programming_site md sk m ctx res)] <=
  ((rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound).
proof.
move=> query_count.
apply (direct_signing_coin_sampler_prequery_bound
         md sk m ctx qs hash_query_budget_count).
  + by rewrite /hash_query_budget_count; smt.
  + by smt.
by smt.
qed.

lemma direct_signing_coin_sampler_message_hash_prequery_bound
  md pk sk m ctx qpk qctx qm qs hc :
  0 <= hc =>
  hc <= hash_query_budget_count =>
  challenge_query_log_count qs <= hc + 1 =>
  phoare[DirectSigningCoinSampler.sample :
    true ==>
    programming_site_prequeried (message_hash_query qpk qctx qm :: qs)
      (actual_signature_programming_site md
        (transcript_of_signature md pk m ctx
          (sign_internal md sk m ctx res)))] <=
	  ((rom_hash_query_budget + 1%r) /
	    challenge_support_cardinality_lower_bound).
proof.
move=> hc_ge0 hc_budget query_count.
bypr=> &m0 _.
byphoare (_: true ==>
  programming_site_prequeried (message_hash_query qpk qctx qm :: qs)
    (actual_signature_programming_site md
      (transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx res)))) => //.
proc.
rnd (fun coins =>
  programming_site_prequeried (message_hash_query qpk qctx qm :: qs)
    (actual_signature_programming_site md
      (transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx coins)))).
auto => />.
by apply (programmed_site_prequery_one_step_message_hash_counter_bound
            md pk sk m ctx qpk qctx qm qs hc).
qed.

lemma direct_signing_coin_sampler_message_hash_budgeted_prequery_bound
  md pk sk m ctx qpk qctx qm qs :
  challenge_query_log_count qs <= hash_query_budget_count + 1 =>
  phoare[DirectSigningCoinSampler.sample :
    true ==>
    programming_site_prequeried (message_hash_query qpk qctx qm :: qs)
      (actual_signature_programming_site md
        (transcript_of_signature md pk m ctx
          (sign_internal md sk m ctx res)))] <=
	  ((rom_hash_query_budget + 1%r) /
	    challenge_support_cardinality_lower_bound).
proof.
move=> query_count.
apply (direct_signing_coin_sampler_message_hash_prequery_bound
  md pk sk m ctx qpk qctx qm qs hash_query_budget_count).
+ by rewrite /hash_query_budget_count; smt.
+ by smt.
by smt.
qed.

lemma programmed_site_prequery_one_step_concrete_bound
  md sk m ctx qs :
  (card (oflist qs))%r <= rom_hash_query_budget + 1%r =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> card_budget.
apply programmed_site_prequery_one_step_budget_bound.
+ by apply card_budget.
by apply honest_signing_programming_site_query_spread_bound.
qed.

lemma programmed_site_prequery_reprogram_one_step_concrete_bound
  md sk m ctx qs sites :
  (forall coins,
    programming_site_conflict_free
      (honest_signing_programming_site md sk m ctx coins) sites) =>
  (card (oflist qs))%r <= rom_hash_query_budget + 1%r =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins) \/
      programming_site_reprograms sites
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
move=> conflict_free card_budget.
apply (ler_trans
  (mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)))).
+ apply mu_le => coins _.
  case.
  + by move=> preq.
  move=> reprog.
  have no_reprog :
    ! programming_site_reprograms sites
        (honest_signing_programming_site md sk m ctx coins).
  + by apply (programming_site_conflict_free_no_reprograms
                (honest_signing_programming_site md sk m ctx coins)
                sites (conflict_free coins)).
  by move: no_reprog; rewrite reprog.
by apply programmed_site_prequery_one_step_concrete_bound.
qed.

lemma programmed_site_query_min_entropy_bound_constant_impossible
  md sk m ctx qs bd q :
  q \in qs =>
  (forall coins,
    honest_signing_programming_site_query md sk m ctx coins = q) =>
  bd < 1%r =>
  programmed_site_query_min_entropy_bound md sk m ctx qs bd => false.
proof.
move=> q_mem query_constant bd_lt1 spread.
have hit1 :
  1%r =
  mu drandom_coins
    (fun coins =>
      honest_signing_programming_site_query md sk m ctx coins = q).
+ rewrite eq_sym.
  apply eq1_mu.
  + by apply signing_coin_distribution_lossless.
  by move=> coins _; apply query_constant.
have hit_le_bd := spread q q_mem.
by smt.
qed.

lemma programming_site_reprograms_conflict_cons site old programmed :
  programming_sites_conflict site old =>
  programming_site_reprograms (old :: programmed) site.
proof.
move=> conflict.
by rewrite /programming_site_reprograms /= conflict.
qed.

lemma rom_counted_programming_bad_min_entropy queries programmed :
  rom_counted_programming_bad queries programmed true.
proof. by rewrite /rom_counted_programming_bad. qed.

lemma rom_counted_programming_bad_prequery_cons queries programmed site
  entropy_bad :
  programming_site_prequeried queries site =>
  rom_counted_programming_bad queries (site :: programmed) entropy_bad.
proof.
move=> preq.
rewrite /rom_counted_programming_bad /= preq.
by case entropy_bad.
qed.

lemma counted_rom_programming_bound_obligation_holds :
  counted_rom_programming_bound_obligation.
proof.
by rewrite /counted_rom_programming_bound_obligation
   counted_rom_programming_loss_term_nonnegative.
qed.

section CountedLazyROMBadFlags.

declare module O <: Oracle.
declare module A <: CountedROMClient {-O, -CountedLazyROM, -CountedLazyROMBadGame}.

op counted_lazy_rom_bad_flags_budget_sound (p : real) : bool =
  p <= counted_rom_programming_loss_term.

lemma counted_lazy_rom_bad_flags_universal_bound &m :
  1%r >= Pr[CountedLazyROMBadGame(O, A).main() @ &m : res].
proof.
byphoare (_: true ==> true) => //.
qed.

lemma counted_lazy_rom_bad_flags_query_budget_bound &m :
  counted_lazy_rom_bad_flags_budget_sound
    (Pr[CountedLazyROMBadGame(O, A).main() @ &m : res]) =>
  Pr[CountedLazyROMBadGame(O, A).main() @ &m : res] <=
    counted_rom_programming_loss_term.
proof.
by rewrite /counted_lazy_rom_bad_flags_budget_sound.
qed.

lemma counted_lazy_rom_bad_flags_query_budget_bound_subunit &m :
  counted_lazy_rom_bad_flags_budget_sound
    (Pr[CountedLazyROMBadGame(O, A).main() @ &m : res]) =>
  Pr[CountedLazyROMBadGame(O, A).main() @ &m : res] < 1%r.
proof.
move=> budget_sound.
apply (ler_lt_trans counted_rom_programming_loss_term).
+ by move: budget_sound; rewrite /counted_lazy_rom_bad_flags_budget_sound.
by apply counted_rom_programming_loss_term_subunit.
qed.

end section CountedLazyROMBadFlags.

lemma fs_with_aborts_no_programming_failure md tr y :
  transcript_challenge_matches tr y =>
  fs_with_aborts_failure md tr (programming_site_of_transcript md tr y) =
  min_entropy_failure md tr.
proof.
move=> match_y.
rewrite /fs_with_aborts_failure.
by rewrite (programming_site_self_no_reprogramming_failure md tr y match_y).
qed.

lemma transcript_signature_challenge_output_matches tr :
  transcript_signature_challenge_matches tr
    (transcript_signature_challenge_output tr).
proof.
by rewrite /transcript_signature_challenge_matches
           /transcript_signature_challenge_output
           /ro_challenge_hash /ro_output_to_challenge
           /ro_output_of_challenge.
qed.

lemma honest_transcript_challenge_entropy_support md sk m ctx coins :
  challenge_entropy_support_ok md
    (transcript_from_honest_signing md sk m ctx coins).
proof.
rewrite /challenge_entropy_support_ok /transcript_from_honest_signing
        /transcript_of_signature /transcript_challenge /signature_challenge
        /sig_challenge /sign_internal /challenge_hash /=.
by apply challenge_from_seed_sparse.
qed.

lemma honest_transcript_no_min_entropy_failure md sk m ctx coins :
  ! min_entropy_failure md
      (transcript_from_honest_signing md sk m ctx coins).
proof.
by rewrite /min_entropy_failure
   honest_transcript_challenge_entropy_support.
qed.

lemma signing_transcript_relation_challenge_entropy_support
  md pk m ctx sig tr :
  signing_transcript_relation md pk m ctx sig tr =>
  challenge_entropy_support_ok md tr.
proof.
rewrite /signing_transcript_relation /signing_simulation_relation.
move=> rel.
case: rel => hsim rest.
case: hsim => _ witness.
case: rest => trE _.
elim witness => sk coins attempt.
rewrite trE /challenge_entropy_support_ok /transcript_of_signature
        /transcript_challenge /signature_challenge /=.
move: attempt.
rewrite /signing_attempt_relation.
move=> [_ [_ ->]].
rewrite /sig_challenge /sign_internal /challenge_hash /=.
by apply challenge_from_seed_sparse.
qed.

lemma signing_transcript_relation_no_min_entropy_failure
  md pk m ctx sig tr :
  signing_transcript_relation md pk m ctx sig tr =>
  ! min_entropy_failure md tr.
proof.
move=> rel.
rewrite /min_entropy_failure.
by rewrite (signing_transcript_relation_challenge_entropy_support
              md pk m ctx sig tr rel).
qed.

lemma signing_record_relation_no_min_entropy_failure md pk r :
  signing_record_relation md pk r =>
  ! min_entropy_failure md (signing_record_transcript r).
proof.
rewrite /signing_record_relation.
move=> rel.
by apply (signing_transcript_relation_no_min_entropy_failure md pk
            (signing_record_message r)
            (signing_record_context r)
            (signing_record_signature r)).
qed.

lemma signing_record_log_sound_no_min_entropy md pk rs :
  signing_record_log_sound md pk rs =>
  signing_record_log_min_entropy_clear md rs.
proof.
rewrite /signing_record_log_sound /signing_record_log_min_entropy_clear.
elim: rs => [|r rs ih] //=.
move=> [rel sound].
split.
+ by apply (signing_record_relation_no_min_entropy_failure md pk r).
+ by apply ih.
qed.

lemma signing_record_log_sound_transcripts_no_min_entropy md pk rs :
  signing_record_log_sound md pk rs =>
  transcript_log_min_entropy_clear md (signing_record_transcripts rs).
proof.
rewrite /signing_record_log_sound /transcript_log_min_entropy_clear
        /signing_record_transcripts.
elim: rs => [|r rs ih] //=.
move=> [rel sound].
split.
+ by apply (signing_record_relation_no_min_entropy_failure md pk r).
+ by apply ih.
qed.

lemma fs_with_aborts_no_failure_for_signing_relation
  md pk m ctx sig tr site :
  signing_transcript_relation md pk m ctx sig tr =>
  programming_site_matches_transcript md tr site =>
  ! fs_with_aborts_failure md tr site.
proof.
move=> rel match_site.
rewrite /fs_with_aborts_failure /reprogramming_failure match_site /=.
by apply (signing_transcript_relation_no_min_entropy_failure
            md pk m ctx sig tr rel).
qed.

lemma fs_with_aborts_no_failure_for_signing_record md pk r site :
  signing_record_relation md pk r =>
  programming_site_matches_transcript
    md (signing_record_transcript r) site =>
  ! fs_with_aborts_failure md (signing_record_transcript r) site.
proof.
rewrite /signing_record_relation.
move=> rel match_site.
by apply (fs_with_aborts_no_failure_for_signing_relation md pk
            (signing_record_message r)
            (signing_record_context r)
            (signing_record_signature r)
            (signing_record_transcript r) site).
qed.

lemma fs_with_aborts_no_failure_for_honest_programming md sk m ctx coins y :
  transcript_challenge_matches
    (transcript_from_honest_signing md sk m ctx coins) y =>
  ! fs_with_aborts_failure md
      (transcript_from_honest_signing md sk m ctx coins)
      (programming_site_of_transcript md
        (transcript_from_honest_signing md sk m ctx coins) y).
proof.
move=> match_y.
rewrite /fs_with_aborts_failure.
rewrite (programming_site_self_no_reprogramming_failure md
		           (transcript_from_honest_signing md sk m ctx coins) y match_y).
by rewrite honest_transcript_no_min_entropy_failure.
qed.

lemma transcript_valid_programming_site_signature_query md tr y :
  transcript_valid md tr =>
  programming_site_query (programming_site_of_transcript md tr y) =
  programming_site_query (signature_programming_site_of_transcript md tr y).
proof.
move=> valid.
rewrite /programming_site_query /programming_site_of_transcript
        /signature_programming_site_of_transcript /=.
by apply transcript_valid_signature_challenge_query.
qed.

lemma transcript_valid_signature_programming_site_matches md tr y :
  transcript_valid md tr =>
  transcript_signature_challenge_matches tr y =>
  programming_site_matches_transcript md tr
    (signature_programming_site_of_transcript md tr y).
proof.
move=> valid match_y.
rewrite /programming_site_matches_transcript
        /signature_programming_site_of_transcript
        /programming_site_query /programming_site_output /=.
rewrite -(transcript_valid_signature_challenge_query md tr valid).
move: match_y.
rewrite -(transcript_valid_signature_challenge_matches md tr y valid).
by [].
qed.

lemma transcript_valid_signature_programming_site_no_reprogramming
  md tr y :
  transcript_valid md tr =>
  transcript_signature_challenge_matches tr y =>
  ! reprogramming_failure md tr
      (signature_programming_site_of_transcript md tr y).
proof.
move=> valid match_y.
rewrite /reprogramming_failure.
by rewrite (transcript_valid_signature_programming_site_matches
              md tr y valid match_y).
qed.

lemma transcript_valid_actual_signature_programming_site_matches md tr :
  transcript_valid md tr =>
  programming_site_matches_transcript md tr
    (actual_signature_programming_site md tr).
proof.
move=> valid.
rewrite /actual_signature_programming_site.
apply (transcript_valid_signature_programming_site_matches md tr
         (transcript_signature_challenge_output tr) valid).
by apply transcript_signature_challenge_output_matches.
qed.

lemma transcript_valid_actual_signature_programming_site_no_reprogramming
  md tr :
  transcript_valid md tr =>
  ! reprogramming_failure md tr (actual_signature_programming_site md tr).
proof.
move=> valid.
rewrite /reprogramming_failure.
by rewrite (transcript_valid_actual_signature_programming_site_matches
              md tr valid).
qed.

lemma valid_forking_pair_signature_programming_site_query md tr1 tr2 y1 y2 :
  valid_forking_pair md tr1 tr2 =>
  programming_site_query (signature_programming_site_of_transcript md tr1 y1) =
  programming_site_query (signature_programming_site_of_transcript md tr2 y2).
proof.
move=> fork_pair.
rewrite /programming_site_query
        /signature_programming_site_of_transcript /=.
by apply valid_forking_pair_signature_challenge_query.
qed.

lemma valid_forking_pair_programming_site_query md tr1 tr2 y1 y2 :
  valid_forking_pair md tr1 tr2 =>
  programming_site_query (programming_site_of_transcript md tr1 y1) =
  programming_site_query (programming_site_of_transcript md tr2 y2).
proof.
move=> fork_pair.
rewrite /programming_site_query /programming_site_of_transcript /=.
by apply valid_forking_pair_challenge_query.
qed.

lemma valid_forking_pair_self_programming_sites_no_reprogramming
  md tr1 tr2 y1 y2 :
  valid_forking_pair md tr1 tr2 =>
  transcript_challenge_matches tr1 y1 =>
  transcript_challenge_matches tr2 y2 =>
  ! reprogramming_failure md tr1
      (programming_site_of_transcript md tr1 y1) /\
  ! reprogramming_failure md tr2
      (programming_site_of_transcript md tr2 y2).
proof.
move=> _ match1 match2.
split.
+ by apply programming_site_self_no_reprogramming_failure.
+ by apply programming_site_self_no_reprogramming_failure.
qed.

lemma fs_bound_parts_nonnegative :
  fs_with_aborts_bound_obligation =>
  0%r <= fs_with_aborts_reprogramming_term /\
  0%r <= fs_with_aborts_min_entropy_term.
proof. by rewrite /fs_with_aborts_bound_obligation. qed.

lemma fs_with_aborts_bound_obligation_holds :
  fs_with_aborts_bound_obligation.
proof.
rewrite /fs_with_aborts_bound_obligation.
split.
+ by apply fs_with_aborts_reprogramming_term_nonnegative.
+ by apply fs_with_aborts_min_entropy_term_nonnegative.
qed.

end HAETAE_ROM_Programming.
