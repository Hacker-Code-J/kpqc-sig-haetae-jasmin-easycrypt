require import AllCore Distr FMap List PROM Real StdOrder.

require import Mode2ChallengeGatedROMPostFreeze
               Mode2ChallengeROMAdapterPostFreeze
               HAETAE_Algebra
               HAETAE_Params
               HAETAE_ROM
               HAETAE_ROM_Programming
               HAETAE_Transcript.

theory Mode2ChallengeROMProgrammingPostFreeze.

import HAETAE_Algebra.
import HAETAE_Params.
import HAETAE_ROM.
import HAETAE_ROM_Programming.
import HAETAE_Transcript.
import Mode2ChallengeGatedROMPostFreeze.
import Mode2ChallengeROMAdapterPostFreeze.

(* Parallel Mode-2 programming layer for the actual 0/1 weight-58 carrier.
   The legacy HAETAE_ROM_Programming theory remains unchanged because its
   entropy predicate is tied to prefix-signed challenge_sparse.  This theory
   reuses only its carrier-independent programming-site bookkeeping. *)

op mode2_challenge_entropy_support_ok (tr : transcript) : bool =
  valid_mode2_carrier_challenge (transcript_challenge tr).

op mode2_min_entropy_failure (tr : transcript) : bool =
  ! mode2_challenge_entropy_support_ok tr.

op mode2_fs_with_aborts_failure
    (tr : transcript) (site : programming_site) : bool =
  reprogramming_failure Mode2 tr site \/
  mode2_min_entropy_failure tr.

op mode2_programming_transcript_fresh
    (queries : ro_query list)
    (programmed : programming_site list)
    (tr : transcript) : bool =
  programming_site_fresh queries programmed
    (actual_signature_programming_site Mode2 tr) /\
  ! mode2_min_entropy_failure tr.

op mode2_transcript_log_min_entropy_clear
    (trs : transcript list) : bool =
  all (fun tr => ! mode2_min_entropy_failure tr) trs.

module Mode2CountedLazyROM(O : Mode2Oracle) = {
  var hash_queries : ro_query list
  var programmed_sites : programming_site list
  var signature_sites : programming_site list
  var bad_prequery : bool
  var bad_reprogram : bool
  var bad_mode2_entropy : bool

  proc init() : unit = {
    O.init();
    hash_queries <- [];
    programmed_sites <- [];
    signature_sites <- [];
    bad_prequery <- false;
    bad_reprogram <- false;
    bad_mode2_entropy <- false;
  }

  proc get(q : ro_query) : ro_output = {
    var y : ro_output;

    y <@ O.get(q);
    hash_queries <- q :: hash_queries;
    return y;
  }

  proc program(site : programming_site) : unit = {
    bad_prequery <-
      bad_prequery \/
      programming_site_prequeried hash_queries site;
    bad_reprogram <-
      bad_reprogram \/
      programming_site_reprograms programmed_sites site;
    programmed_sites <- site :: programmed_sites;
    O.set(programming_site_query site, programming_site_output site);
  }

  proc observe_signature_site(site : programming_site) : unit = {
    signature_sites <- site :: signature_sites;
  }

  proc observe_transcript(tr : transcript) : unit = {
    var site : programming_site;

    site <- actual_signature_programming_site Mode2 tr;
    bad_mode2_entropy <-
      bad_mode2_entropy \/ mode2_min_entropy_failure tr;
    signature_sites <- site :: signature_sites;
  }

  proc bad() : bool = {
    return bad_prequery \/ bad_reprogram \/ bad_mode2_entropy;
  }
}.

section Mode2CountedLazyROMStateFacts.

declare module O <: Mode2Oracle {-Mode2CountedLazyROM}.

lemma mode2_counted_lazy_rom_init_clears :
  hoare[Mode2CountedLazyROM(O).init :
    true ==>
    ! Mode2CountedLazyROM.bad_prequery /\
    ! Mode2CountedLazyROM.bad_reprogram /\
    ! Mode2CountedLazyROM.bad_mode2_entropy /\
    Mode2CountedLazyROM.hash_queries = [] /\
    Mode2CountedLazyROM.programmed_sites = [] /\
    Mode2CountedLazyROM.signature_sites = []].
proof.
proc.
wp.
call (_ : true).
by auto.
qed.

lemma mode2_counted_lazy_rom_get_preserves_bad_clear :
  hoare[Mode2CountedLazyROM(O).get :
    ! Mode2CountedLazyROM.bad_prequery /\
    ! Mode2CountedLazyROM.bad_reprogram /\
    ! Mode2CountedLazyROM.bad_mode2_entropy ==>
    ! Mode2CountedLazyROM.bad_prequery /\
    ! Mode2CountedLazyROM.bad_reprogram /\
    ! Mode2CountedLazyROM.bad_mode2_entropy].
proof.
proc.
wp.
call (_ : true).
by auto.
qed.

lemma mode2_counted_lazy_rom_program_preserves_bad_clear_if_fresh :
  hoare[Mode2CountedLazyROM(O).program :
    ! Mode2CountedLazyROM.bad_prequery /\
    ! Mode2CountedLazyROM.bad_reprogram /\
    ! Mode2CountedLazyROM.bad_mode2_entropy /\
    programming_site_fresh
      Mode2CountedLazyROM.hash_queries
      Mode2CountedLazyROM.programmed_sites site ==>
    ! Mode2CountedLazyROM.bad_prequery /\
    ! Mode2CountedLazyROM.bad_reprogram /\
    ! Mode2CountedLazyROM.bad_mode2_entropy].
proof.
proc.
wp.
call (_ : true).
by auto => />.
qed.

lemma mode2_counted_lazy_rom_observe_transcript_preserves_bad_clear :
  hoare[Mode2CountedLazyROM(O).observe_transcript :
    ! mode2_min_entropy_failure tr /\
    ! Mode2CountedLazyROM.bad_prequery /\
    ! Mode2CountedLazyROM.bad_reprogram /\
    ! Mode2CountedLazyROM.bad_mode2_entropy ==>
    ! Mode2CountedLazyROM.bad_prequery /\
    ! Mode2CountedLazyROM.bad_reprogram /\
    ! Mode2CountedLazyROM.bad_mode2_entropy].
proof.
proc.
wp.
skip.
move=> &hr [hmin [hpre [hreprogram hentropy]]].
by rewrite hmin hentropy.
qed.

lemma mode2_counted_lazy_rom_bad_false_when_clear :
  hoare[Mode2CountedLazyROM(O).bad :
    ! Mode2CountedLazyROM.bad_prequery /\
    ! Mode2CountedLazyROM.bad_reprogram /\
    ! Mode2CountedLazyROM.bad_mode2_entropy ==>
    ! res].
proof.
proc.
skip.
move=> &hr [hpre [hreprogram hentropy]].
by rewrite hpre hreprogram hentropy.
qed.

end section Mode2CountedLazyROMStateFacts.

lemma dmode2_carrier_challenge_valid_full :
  mu dmode2_carrier_challenge valid_mode2_carrier_challenge = 1%r.
proof.
apply eq1_mu.
+ exact dmode2_carrier_challenge_lossless.
+ move=> ch hch.
  move: hch.
  rewrite dmode2_carrier_challenge_support.
  trivial.
qed.

lemma dmode2_fresh_challenge_query_output_valid_full :
  mu dmode2_fresh_challenge_query_output
     (fun y =>
        valid_mode2_carrier_challenge
          (HAETAE_ROM.ro_challenge_hash y)) = 1%r.
proof.
rewrite dmode2_fresh_challenge_query_output_challenge_pr.
exact dmode2_carrier_challenge_valid_full.
qed.

lemma mode2_gated_rom_mode2_fresh_get_valid_carrier_1
    w1 w0 muh :
  phoare[Mode2ChallengeGatedRO.FRO.get :
    arg = HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh /\
    HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh
      \notin Mode2ChallengeGatedRO.FRO.m
    ==> valid_mode2_carrier_challenge
          (HAETAE_ROM.ro_challenge_hash res)] = 1%r.
proof.
proc.
wp.
rnd.
auto => /> &hr _.
rewrite gated_dro_output_mode2E.
exact dmode2_fresh_challenge_query_output_valid_full.
qed.

lemma mode2_fresh_output_challenge_valid y :
  y \in dmode2_fresh_challenge_query_output =>
  valid_mode2_carrier_challenge
    (HAETAE_ROM.ro_challenge_hash y).
proof.
rewrite /dmode2_fresh_challenge_query_output supp_dmap.
move=> [ch [hch ->]].
rewrite /HAETAE_ROM.ro_challenge_hash
        /HAETAE_ROM.ro_output_to_challenge
        /HAETAE_ROM.ro_output_of_challenge /=.
move: hch.
rewrite dmode2_carrier_challenge_support.
trivial.
qed.

lemma mode2_matching_output_implies_entropy_support_ok tr y :
  valid_mode2_carrier_challenge
    (HAETAE_ROM.ro_challenge_hash y) =>
  transcript_challenge_matches tr y =>
  mode2_challenge_entropy_support_ok tr.
proof.
move=> hvalid hmatch.
rewrite /mode2_challenge_entropy_support_ok.
rewrite -hmatch.
exact hvalid.
qed.

lemma mode2_carrier_valid_no_min_entropy_failure tr :
  valid_mode2_carrier_challenge (transcript_challenge tr) =>
  ! mode2_min_entropy_failure tr.
proof.
rewrite /mode2_min_entropy_failure
        /mode2_challenge_entropy_support_ok.
trivial.
qed.

lemma mode2_fs_with_aborts_no_failure_for_site tr site :
  programming_site_matches_transcript Mode2 tr site =>
  valid_mode2_carrier_challenge (transcript_challenge tr) =>
  ! mode2_fs_with_aborts_failure tr site.
proof.
move=> hmatch hvalid.
rewrite /mode2_fs_with_aborts_failure
        /reprogramming_failure hmatch /=
        /mode2_min_entropy_failure
        /mode2_challenge_entropy_support_ok hvalid.
trivial.
qed.

lemma mode2_fs_with_aborts_no_failure_for_programming_site tr y :
  transcript_challenge_matches tr y =>
  valid_mode2_carrier_challenge (transcript_challenge tr) =>
  ! mode2_fs_with_aborts_failure tr
      (programming_site_of_transcript Mode2 tr y).
proof.
move=> hmatch hvalid.
apply (mode2_fs_with_aborts_no_failure_for_site tr
         (programming_site_of_transcript Mode2 tr y)).
+ exact (programming_site_self_matches Mode2 tr y hmatch).
+ exact hvalid.
qed.

lemma mode2_fresh_output_match_no_failure tr y :
  y \in dmode2_fresh_challenge_query_output =>
  transcript_challenge_matches tr y =>
  ! mode2_fs_with_aborts_failure tr
      (programming_site_of_transcript Mode2 tr y).
proof.
move=> hy hmatch.
apply (mode2_fs_with_aborts_no_failure_for_programming_site tr y hmatch).
apply (mode2_matching_output_implies_entropy_support_ok tr y).
+ exact (mode2_fresh_output_challenge_valid y hy).
+ exact hmatch.
qed.

(* Deliberately absent: an honest-signing no-failure theorem.  The frozen
   transcript_from_honest_signing path still constructs prefix-signed
   challenge_from_seed values, so connecting it to this carrier requires a
   separate signing-challenge distribution bridge. *)

end Mode2ChallengeROMProgrammingPostFreeze.
