require import AllCore Distr List Real FSet FMap StdOrder FelTactic Mu_mem.
require import Sig_ROM HAETAE_Scheme HAETAE_Params HAETAE_Algebra.
require import HAETAE_Distributions.
require import HAETAE_Assumptions.
require import HAETAE_Transcript.
require import HAETAE_Reductions.
require import HAETAE_Rejection HAETAE_ROM HAETAE_ROM_Programming.
require Hybrid.

theory HAETAE_HopGames.

import HAETAE_Scheme.
import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Distributions.
import HAETAE_Assumptions.
import HAETAE_Transcript.
import HAETAE_Reductions.
import HAETAE_Rejection.
import HAETAE_ROM.
import HAETAE_ROM_Programming.
import RealOrder.

module type SigningSimulator(H : SIG.POracle) = {
  proc init(pk : pkey, sk : skey) : unit
  proc sign(m : message, ctx : context) : signature
}.

module RealSigningSimulator(S : SIG.Scheme) (H : SIG.POracle) = {
  var sk : skey

  proc init(pk : pkey, sk0 : skey) : unit = {
    sk <- sk0;
  }

  proc sign(m : message, ctx : context) : signature = {
    var sig : signature;

    sig <@ S(H).sign(sk, m, ctx);
    return sig;
  }
}.

module EUF_CMA_SimulatedSign(
  H : SIG.Oracle,
  S : SIG.Scheme,
  A : SIG.Adversary,
  Sim : SigningSimulator
) = {
  var queries : SIG.query list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var sig : signature;

      sig <@ Sim(H).sign(m, ctx);
      queries <- (m, ctx) :: queries;
      return sig;
    }
  }

  module A = A(H, O)

  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    queries <- [];
    (pk, sk) <@ S(H).kg();
    Sim(H).init(pk, sk);
    (m, ctx, sig) <@ A.forge(pk);
    ok <@ S(H).verify(pk, m, ctx, sig);
    return ok /\ SIG.fresh_msg queries m ctx;
  }
}.

op transcript_log_consistent
   (md : mode) (pk : pkey) (qs : SIG.query list)
   (trs : transcript list) (rs : signing_transcript_record list) : bool =
  qs = signing_record_queries rs /\
  trs = signing_record_transcripts rs /\
  signing_record_log_sound md pk rs.

lemma transcript_log_consistent_nil md pk :
  transcript_log_consistent md pk [] [] [].
proof. by rewrite /transcript_log_consistent
                  /signing_record_queries /signing_record_transcripts
                  /signing_record_log_sound.
qed.

lemma transcript_log_consistent_cons md pk qs trs rs m ctx sig tr :
  transcript_log_consistent md pk qs trs rs =>
  signing_record_relation md pk (m, ctx, sig, tr) =>
  transcript_log_consistent md pk
    ((m, ctx) :: qs)
    (tr :: trs)
    ((m, ctx, sig, tr) :: rs).
proof.
rewrite /transcript_log_consistent.
move=> [qE [trE sound]] rel.
rewrite qE trE.
split.
+ by rewrite signing_record_queries_cons /signing_record_query
             /signing_record_message /signing_record_context.
split.
+ by rewrite signing_record_transcripts_cons /signing_record_transcript.
by apply signing_record_log_sound_cons.
qed.

lemma transcript_log_consistent_no_min_entropy md pk qs trs rs :
  transcript_log_consistent md pk qs trs rs =>
  transcript_log_min_entropy_clear md trs.
proof.
rewrite /transcript_log_consistent.
move=> [_ [trsE sound]].
rewrite trsE.
by apply (signing_record_log_sound_transcripts_no_min_entropy md pk rs).
qed.

lemma transcript_log_consistent_valid md pk qs trs rs :
  transcript_log_consistent md pk qs trs rs =>
  transcript_log_valid md trs.
proof.
rewrite /transcript_log_consistent.
move=> [_ [trsE sound]].
rewrite trsE.
by apply (signing_record_log_sound_transcripts_valid md pk rs).
qed.

op transcript_log_ready (md : mode) (trs : transcript list) : bool =
  transcript_log_valid md trs /\
  transcript_log_min_entropy_clear md trs.

op budgeted_programmed_query_count_discipline
   (hash_count signing_count : int) : bool =
  0 <= hash_count /\
  hash_count <= hash_query_budget_count /\
  0 <= signing_count /\
  signing_count <= signature_query_budget_count.

op budgeted_paper_sim_signing_count_discipline
   (signing_count : int) : bool =
  0 <= signing_count /\
  signing_count <= signature_query_budget_count.

op budgeted_paper_sim_sampler_freshness_discipline
   (hash_count signing_count : int)
   (hash_qs sampler_qs : ro_query list) : bool =
  0 <= hash_count /\
  hash_count <= hash_query_budget_count /\
  size hash_qs <= hash_count /\
  0 <= signing_count /\
  signing_count <= signature_query_budget_count /\
  size sampler_qs <= signing_count.

op sampler_rom_covered
   (rom : (ro_query, ro_output * PROM.flag) fmap)
   (hash_qs sampler_qs : ro_query list) : bool =
  forall seed_coins,
    sampler_expand_query seed_coins \in rom =>
    sampler_expand_query seed_coins \in hash_qs \/
    sampler_expand_query seed_coins \in sampler_qs.

lemma sampler_rom_covered_fresh_after_clean_seed
    seed_coins rom hash_qs sampler_qs bad :
  sampler_rom_covered rom hash_qs sampler_qs =>
  ! (bad \/
     sampler_expand_query seed_coins \in hash_qs \/
     sampler_expand_query seed_coins \in sampler_qs) =>
  sampler_expand_query seed_coins \notin rom.
proof.
by rewrite /sampler_rom_covered; smt.
qed.

lemma sampler_rom_covered_self_log_preserves
    seed_coins rom hash_qs sampler_qs :
  sampler_rom_covered rom hash_qs sampler_qs =>
  sampler_rom_covered rom hash_qs
    (sampler_expand_query seed_coins :: sampler_qs).
proof.
by rewrite /sampler_rom_covered; smt.
qed.

lemma sampler_rom_covered_old_log_clean_boundary
    seed_coins rom hash_qs sampler_qs bad :
  sampler_rom_covered rom hash_qs sampler_qs =>
  ! (bad \/
     sampler_expand_query seed_coins \in hash_qs \/
     sampler_expand_query seed_coins \in sampler_qs) =>
  sampler_expand_query seed_coins \notin rom /\
  sampler_rom_covered rom hash_qs
    (sampler_expand_query seed_coins :: sampler_qs).
proof.
move=> covered clean.
split.
+ by apply (sampler_rom_covered_fresh_after_clean_seed
       seed_coins rom hash_qs sampler_qs bad).
by apply (sampler_rom_covered_self_log_preserves seed_coins).
qed.

op budgeted_programmed_reprogram_discipline
   (pk : pkey) (sk : skey)
   (programmed : programming_site list) (bad_reprogram : bool) : bool =
  pk = public_key_of_secret haetae_mode sk /\
  programming_site_log_conflict_free_for_honest haetae_mode sk programmed /\
  ! bad_reprogram.

op budgeted_programmed_challenge_query_discipline
   (hash_count : int) (queries : ro_query list) : bool =
  0 <= hash_count /\
  hash_count <= hash_query_budget_count /\
  challenge_query_log_count queries <= hash_count + 1.

lemma transcript_log_consistent_ready md pk qs trs rs :
  transcript_log_consistent md pk qs trs rs =>
  transcript_log_ready md trs.
proof.
move=> consistent.
rewrite /transcript_log_ready.
split.
+ by apply (transcript_log_consistent_valid md pk qs trs rs).
by apply (transcript_log_consistent_no_min_entropy md pk qs trs rs).
qed.

lemma transcript_log_valid_member md trs tr :
  transcript_log_valid md trs =>
  tr \in trs =>
  transcript_valid md tr.
proof.
rewrite /transcript_log_valid.
move/allP=> valid_all mem_tr.
by apply valid_all.
qed.

lemma transcript_log_min_entropy_clear_member md trs tr :
  transcript_log_min_entropy_clear md trs =>
  tr \in trs =>
  ! min_entropy_failure md tr.
proof.
rewrite /transcript_log_min_entropy_clear.
move/allP=> clear_all mem_tr.
by apply clear_all.
qed.

lemma transcript_log_ready_member_valid md trs tr :
  transcript_log_ready md trs =>
  tr \in trs =>
  transcript_valid md tr.
proof.
rewrite /transcript_log_ready.
move=> [valid _] mem_tr.
by apply (transcript_log_valid_member md trs tr).
qed.

lemma transcript_log_ready_member_no_min_entropy md trs tr :
  transcript_log_ready md trs =>
  tr \in trs =>
  ! min_entropy_failure md tr.
proof.
rewrite /transcript_log_ready.
move=> [_ clear_log] mem_tr.
by apply (transcript_log_min_entropy_clear_member md trs tr).
qed.

lemma transcript_log_ready_no_failure_for_matching_site md trs tr site :
  transcript_log_ready md trs =>
  tr \in trs =>
  programming_site_matches_transcript md tr site =>
  ! fs_with_aborts_failure md tr site.
proof.
move=> ready mem_tr match_site.
rewrite /fs_with_aborts_failure /reprogramming_failure match_site /=.
by apply (transcript_log_ready_member_no_min_entropy md trs tr).
qed.

lemma transcript_log_ready_no_failure_for_programming_site md trs tr y :
  transcript_log_ready md trs =>
  tr \in trs =>
  transcript_challenge_matches tr y =>
  ! fs_with_aborts_failure md tr
      (programming_site_of_transcript md tr y).
proof.
move=> ready mem_tr match_y.
apply (transcript_log_ready_no_failure_for_matching_site md trs tr
         (programming_site_of_transcript md tr y) ready mem_tr).
by apply programming_site_self_matches.
qed.

lemma transcript_log_ready_no_failure_for_signature_programming_site
  md trs tr y :
  transcript_log_ready md trs =>
  tr \in trs =>
  transcript_signature_challenge_matches tr y =>
  ! fs_with_aborts_failure md tr
      (signature_programming_site_of_transcript md tr y).
proof.
move=> ready mem_tr match_y.
have valid := transcript_log_ready_member_valid md trs tr ready mem_tr.
apply (transcript_log_ready_no_failure_for_matching_site md trs tr
         (signature_programming_site_of_transcript md tr y) ready mem_tr).
by apply transcript_valid_signature_programming_site_matches.
qed.

lemma transcript_log_ready_actual_signature_site_clear_member md trs tr :
  transcript_log_ready md trs =>
  tr \in trs =>
  transcript_signature_programming_site_clear md tr.
proof.
move=> ready mem_tr.
rewrite /transcript_signature_programming_site_clear
        /actual_signature_programming_site.
apply (transcript_log_ready_no_failure_for_signature_programming_site
         md trs tr (transcript_signature_challenge_output tr)
         ready mem_tr).
by apply transcript_signature_challenge_output_matches.
qed.

lemma transcript_log_ready_signature_sites_clear md trs :
  transcript_log_ready md trs =>
  transcript_log_signature_programming_sites_clear md trs.
proof.
move=> ready.
rewrite /transcript_log_signature_programming_sites_clear.
apply/allP=> tr mem_tr.
by apply (transcript_log_ready_actual_signature_site_clear_member md trs).
qed.

op internal_transcript_state_sound
   (md : mode) (pk : pkey) (sk : skey) (qs : SIG.query list)
   (trs : transcript list) (rs : signing_transcript_record list) : bool =
  pk = public_key_of_secret md sk /\
  transcript_log_consistent md pk qs trs rs.

lemma internal_transcript_state_sound_nil md sk :
  internal_transcript_state_sound md
    (public_key_of_secret md sk) sk [] [] [].
proof.
rewrite /internal_transcript_state_sound.
split.
+ by trivial.
+ by apply transcript_log_consistent_nil.
qed.

lemma internal_transcript_state_sound_keygen md sd :
  internal_transcript_state_sound md
    (keygen_internal md sd).`1
    (keygen_internal md sd).`2
    [] [] [].
proof.
rewrite /internal_transcript_state_sound.
split.
+ by rewrite /keygen_internal.
+ by apply transcript_log_consistent_nil.
qed.

lemma internal_transcript_state_sound_no_min_entropy
  md pk sk qs trs rs :
  internal_transcript_state_sound md pk sk qs trs rs =>
  transcript_log_min_entropy_clear md trs.
proof.
rewrite /internal_transcript_state_sound.
move=> [_ log_sound].
by apply (transcript_log_consistent_no_min_entropy md pk qs trs rs).
qed.

lemma internal_transcript_state_sound_valid md pk sk qs trs rs :
  internal_transcript_state_sound md pk sk qs trs rs =>
  transcript_log_valid md trs.
proof.
rewrite /internal_transcript_state_sound.
move=> [_ log_sound].
by apply (transcript_log_consistent_valid md pk qs trs rs).
qed.

lemma internal_transcript_state_sound_log_ready md pk sk qs trs rs :
  internal_transcript_state_sound md pk sk qs trs rs =>
  transcript_log_ready md trs.
proof.
rewrite /internal_transcript_state_sound.
move=> [_ log_sound].
by apply (transcript_log_consistent_ready md pk qs trs rs).
qed.

lemma transcript_log_consistent_sign_internal_cons
  md sk qs trs rs m ctx coins :
  transcript_log_consistent md (public_key_of_secret md sk) qs trs rs =>
  transcript_log_consistent md
    (public_key_of_secret md sk)
    ((m, ctx) :: qs)
    (transcript_of_signature md (public_key_of_secret md sk) m ctx
      (sign_internal md sk m ctx coins) :: trs)
    ((m, ctx, sign_internal md sk m ctx coins,
      transcript_of_signature md (public_key_of_secret md sk) m ctx
        (sign_internal md sk m ctx coins)) :: rs).
proof.
move=> log_sound.
apply transcript_log_consistent_cons.
+ by apply log_sound.
+ by apply sign_internal_record_relation.
qed.

lemma internal_transcript_state_sound_sign_internal_cons
  md pk sk qs trs rs m ctx coins :
  internal_transcript_state_sound md pk sk qs trs rs =>
  internal_transcript_state_sound md pk sk
    ((m, ctx) :: qs)
    (transcript_of_signature md pk m ctx
      (sign_internal md sk m ctx coins) :: trs)
    ((m, ctx, sign_internal md sk m ctx coins,
      transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx coins)) :: rs).
proof.
rewrite /internal_transcript_state_sound.
move=> [pkE log_sound].
split=> //.
move: log_sound.
rewrite pkE.
move=> log_sound.
apply (transcript_log_consistent_sign_internal_cons md sk qs trs rs
         m ctx coins).
by apply log_sound.
qed.

lemma sign_internal_transcript_no_min_entropy md pk sk m ctx coins :
  pk = public_key_of_secret md sk =>
  ! min_entropy_failure md
      (transcript_of_signature md pk m ctx
        (sign_internal md sk m ctx coins)).
proof.
move=> pkE.
rewrite pkE.
by apply (signing_transcript_relation_no_min_entropy_failure md
            (public_key_of_secret md sk) m ctx
            (sign_internal md sk m ctx coins));
   apply sign_internal_transcript_relation.
qed.

module EUF_CMA_TranscriptSimulatedSign(
  H : SIG.Oracle,
  S : SIG.Scheme,
  A : SIG.Adversary,
  Sim : SigningSimulator
) = {
  var pk_current : pkey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var sig : signature;
      var tr : transcript;

      sig <@ Sim(H).sign(m, ctx);
      tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
      queries <- (m, ctx) :: queries;
      transcripts <- tr :: transcripts;
      records <- (m, ctx, sig, tr) :: records;
      return sig;
    }
  }

  module A = A(H, O)

  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    queries <- [];
    transcripts <- [];
    records <- [];
    (pk, sk) <@ S(H).kg();
    pk_current <- pk;
    Sim(H).init(pk, sk);
    (m, ctx, sig) <@ A.forge(pk);
    ok <@ S(H).verify(pk, m, ctx, sig);
    return ok /\ SIG.fresh_msg queries m ctx;
  }
}.

module EUF_CMA_InternalTranscriptSign(
  H : SIG.Oracle,
  A : SIG.Adversary
) = {
  var pk_current : pkey
  var sk_current : skey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var seed_coins : random_coins;
      var coins : random_coins;
      var sig : signature;
      var tr : transcript;

      coins <$ drandom_coins;
      sig <- sign_internal haetae_mode sk_current m ctx coins;
      tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
      queries <- (m, ctx) :: queries;
      transcripts <- tr :: transcripts;
      records <- (m, ctx, sig, tr) :: records;
      return sig;
    }
  }

  module A = A(H, O)

  proc main() : bool = {
    var sd : seed;
    var rhoprime : seed;
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    queries <- [];
    transcripts <- [];
    records <- [];
    sd <$ dseed;
    rhoprime <- haetae_keygen_rhoprime sd;
    (pk, sk) <- keygen_internal haetae_mode rhoprime;
    pk_current <- pk;
    sk_current <- sk;
    (m, ctx, sig) <@ A.forge(pk);
    ok <- verify_internal haetae_mode pk m ctx sig;
    return ok /\ SIG.fresh_msg queries m ctx;
  }
}.

module EUF_CMA_ROMInternalTranscriptSign(
  H : SIG.Oracle,
  A : SIG.Adversary
) = {
  var pk_current : pkey
  var sk_current : skey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var seed_coins : random_coins;
      var coins : random_coins;
      var pk : pkey;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;

      seed_coins <$ drandom_coins;
      ro_y <@ H.get(sampler_expand_query seed_coins);
      coins <- ro_signing_coins ro_y;
      pk <- public_key_of_secret haetae_mode sk_current;
      ro_y <@ H.get(message_hash_query pk ctx m);
      mu <- ro_message_hash ro_y;
      highbits <- commitment_highbits haetae_mode sk_current m ctx coins;
      lowbits <- commitment_lowbits haetae_mode sk_current m ctx coins;
      ro_y <@ H.get(challenge_hash_query haetae_mode highbits lowbits mu);
      sig <- sign_internal haetae_mode sk_current m ctx coins;
      tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
      queries <- (m, ctx) :: queries;
      transcripts <- tr :: transcripts;
      records <- (m, ctx, sig, tr) :: records;
      return sig;
    }
  }

  module A = A(H, O)

  proc main() : bool = {
    var sd : seed;
    var rhoprime : seed;
    var ro_y : ro_output;
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    queries <- [];
    transcripts <- [];
    records <- [];
    sd <$ dseed;
    rhoprime <- haetae_keygen_rhoprime sd;
    ro_y <@ H.get(matrix_expand_query haetae_mode rhoprime);
    (pk, sk) <- keygen_internal haetae_mode rhoprime;
    pk_current <- pk;
    sk_current <- sk;
    (m, ctx, sig) <@ A.forge(pk);
    ok <- verify_internal haetae_mode pk m ctx sig;
    return ok /\ SIG.fresh_msg queries m ctx;
  }
}.

module ROMInternalTranscriptAsNMA(A : SIG.Adversary) (H : SIG.POracle) = {
  var pk_current : pkey
  var sk_current : skey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var seed_coins : random_coins;
      var coins : random_coins;
      var pk : pkey;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;

      seed_coins <$ drandom_coins;
      ro_y <@ H.get(sampler_expand_query seed_coins);
      coins <- ro_signing_coins ro_y;
      pk <- public_key_of_secret haetae_mode sk_current;
      ro_y <@ H.get(message_hash_query pk ctx m);
      mu <- ro_message_hash ro_y;
      highbits <- commitment_highbits haetae_mode sk_current m ctx coins;
      lowbits <- commitment_lowbits haetae_mode sk_current m ctx coins;
      ro_y <@ H.get(challenge_hash_query haetae_mode highbits lowbits mu);
      sig <- sign_internal haetae_mode sk_current m ctx coins;
      tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
      queries <- (m, ctx) :: queries;
      transcripts <- tr :: transcripts;
      records <- (m, ctx, sig, tr) :: records;
      return sig;
    }
  }

  module A = A(H, O)

  proc forge(pk : pkey) : message * context * signature = {
    var r : message * context * signature;

    pk_current <- pk;
    sk_current <- secret_key_of_seed haetae_mode pk.`1;
    queries <- [];
    transcripts <- [];
    records <- [];
    r <@ A.forge(pk);
    return r;
  }
}.

op public_sim_source
   (pk : pkey) (m : message) (ctx : context)
   (coins : random_coins) : byte list =
  coins ++ pk.`1 ++ ctx ++ m.

op public_sim_response_aux_vector :
  mode -> pkey -> message -> context -> random_coins -> polyveck =
  fun md pk m ctx coins =>
    deterministic_unit_polyveck md 29
      (public_sim_source pk m ctx coins).

op public_sim_response_vector :
  mode -> pkey -> message -> context -> random_coins -> polyvecl =
  fun md pk m ctx coins =>
    deterministic_unit_polyvecl md 17
      (public_sim_source pk m ctx coins).

op public_sim_hint_vector :
  mode -> pkey -> message -> context -> random_coins -> hint_t =
  fun md pk m ctx coins =>
    deterministic_unit_polyveck md 41
      (public_sim_source pk m ctx coins).

op public_sim_commitment_lowbits :
  mode -> pkey -> message -> context -> random_coins -> poly =
  fun md pk m ctx coins =>
    let raw = deterministic_polyveck md
      (public_sim_source pk m ctx coins) in
    let row0 = nth poly_zero raw 0 in
    mkseq
      (fun i =>
        if i = 0 then signing_entropy_token_of_coins coins
        else poly_coeff row0 i)
      n.

op public_sim_commitment_challenge :
  mode -> pkey -> message -> context -> random_coins -> challenge =
  fun md pk m ctx coins =>
    challenge_hash md
      (public_sim_response_aux_vector md pk m ctx coins)
      (public_sim_commitment_lowbits md pk m ctx coins)
      (message_hash pk ctx m).

op public_sim_commitment_highbits :
  mode -> pkey -> message -> context -> random_coins -> polyveck =
  fun md pk m ctx coins =>
    let ch = public_sim_commitment_challenge md pk m ctx coins in
    reconstructed_highbits md
      (public_sim_response_aux_vector md pk m ctx coins)
      (public_key_challenge_term md pk ch).

op public_sim_signature_token :
  mode -> pkey -> message -> context -> random_coins -> sig_token =
  fun md pk m ctx coins =>
    ( public_sim_response_vector md pk m ctx coins,
      public_sim_response_aux_vector md pk m ctx coins,
      public_sim_hint_vector md pk m ctx coins).

op public_sim_signature :
  mode -> pkey -> message -> context -> random_coins -> signature =
  fun md pk m ctx coins =>
    let highbits = public_sim_commitment_highbits md pk m ctx coins in
    let lowbits = public_sim_commitment_lowbits md pk m ctx coins in
    let mu = message_hash pk ctx m in
    let ch = public_sim_commitment_challenge md pk m ctx coins in
    (highbits, lowbits, mu, ch,
     public_sim_signature_token md pk m ctx coins, 0, 0).

lemma public_sim_commitment_lowbitsE md sk m ctx coins :
  public_sim_commitment_lowbits md (public_key_of_secret md sk) m ctx coins =
  commitment_lowbits md sk m ctx coins.
proof.
by rewrite /public_sim_commitment_lowbits /commitment_lowbits
           /commitment_raw /public_sim_source /commitment_source
           /public_key_of_secret.
qed.

lemma public_sim_response_aux_vectorE md sk m ctx coins :
  public_sim_response_aux_vector md (public_key_of_secret md sk) m ctx coins =
  response_aux_vector md sk m ctx coins.
proof.
by rewrite /public_sim_response_aux_vector /response_aux_vector
           /public_sim_source /response_source /public_key_of_secret.
qed.

lemma public_sim_commitment_challengeE md sk m ctx coins :
  public_sim_commitment_challenge md (public_key_of_secret md sk) m ctx coins =
  commitment_challenge md sk m ctx coins.
proof.
by rewrite /public_sim_commitment_challenge /commitment_challenge
           public_sim_response_aux_vectorE public_sim_commitment_lowbitsE.
qed.

lemma public_sim_commitment_highbitsE md sk m ctx coins :
  public_sim_commitment_highbits md (public_key_of_secret md sk) m ctx coins =
  commitment_highbits md sk m ctx coins.
proof.
by rewrite /public_sim_commitment_highbits /commitment_highbits
           public_sim_commitment_challengeE
           public_sim_response_aux_vectorE.
qed.

lemma public_sim_response_vectorE md sk m ctx coins :
  public_sim_response_vector md (public_key_of_secret md sk) m ctx coins =
  response_vector md sk m ctx coins.
proof.
by rewrite /public_sim_response_vector /response_vector
           /public_sim_source /response_source /public_key_of_secret.
qed.

lemma public_sim_hint_vectorE md sk m ctx coins :
  public_sim_hint_vector md (public_key_of_secret md sk) m ctx coins =
  hint_vector md sk m ctx coins.
proof.
by rewrite /public_sim_hint_vector /hint_vector
           /public_sim_source /response_source /public_key_of_secret.
qed.

lemma public_sim_signature_tokenE md sk m ctx coins :
  public_sim_signature_token md (public_key_of_secret md sk) m ctx coins =
  signature_token md sk m ctx coins.
proof.
by rewrite /public_sim_signature_token /signature_token
           public_sim_response_vectorE
           public_sim_response_aux_vectorE
           public_sim_hint_vectorE.
qed.

lemma public_sim_signatureE md sk m ctx coins :
  public_sim_signature md (public_key_of_secret md sk) m ctx coins =
  sign_internal md sk m ctx coins.
proof.
by rewrite /public_sim_signature /sign_internal
           public_sim_commitment_highbitsE
           public_sim_commitment_lowbitsE
           public_sim_commitment_challengeE
           public_sim_signature_tokenE.
qed.

module ROMInternalTranscriptPublicSimAsNMA(A : SIG.Adversary)
                                         (H : SIG.POracle) = {
  var pk_current : pkey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var seed_coins : random_coins;
      var coins : random_coins;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;

      seed_coins <$ drandom_coins;
      ro_y <@ H.get(sampler_expand_query seed_coins);
      coins <- ro_signing_coins ro_y;
      ro_y <@ H.get(message_hash_query pk_current ctx m);
      mu <- ro_message_hash ro_y;
      highbits <- public_sim_commitment_highbits haetae_mode
        pk_current m ctx coins;
      lowbits <- public_sim_commitment_lowbits haetae_mode
        pk_current m ctx coins;
      ro_y <@ H.get(challenge_hash_query haetae_mode highbits lowbits mu);
      sig <- public_sim_signature haetae_mode pk_current m ctx coins;
      tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
      queries <- (m, ctx) :: queries;
      transcripts <- tr :: transcripts;
      records <- (m, ctx, sig, tr) :: records;
      return sig;
    }
  }

  module A = A(H, O)

  proc forge(pk : pkey) : message * context * signature = {
    var r : message * context * signature;

    pk_current <- pk;
    queries <- [];
    transcripts <- [];
    records <- [];
    r <@ A.forge(pk);
    return r;
  }
}.

type paper_sim_signature_sample = sig_token * poly * int.

op paper_sim_sample_token (s : paper_sim_signature_sample) : sig_token =
  s.`1.
op paper_sim_sample_lowbits_carrier
   (s : paper_sim_signature_sample) : poly =
  s.`2.
op paper_sim_sample_entropy (s : paper_sim_signature_sample) : int =
  s.`3.
op paper_sim_sample_response (s : paper_sim_signature_sample) : polyvecl =
  (paper_sim_sample_token s).`1.
op paper_sim_sample_response_aux
   (s : paper_sim_signature_sample) : polyveck =
  (paper_sim_sample_token s).`2.
op paper_sim_sample_hint (s : paper_sim_signature_sample) : hint_t =
  (paper_sim_sample_token s).`3.

op paper_sim_commitment_lowbits
   (md : mode) (s : paper_sim_signature_sample) : poly =
  mkseq
    (fun i =>
      if i = 0 then paper_sim_sample_entropy s
      else poly_coeff (paper_sim_sample_lowbits_carrier s) i)
    n.

op paper_sim_commitment_challenge
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (s : paper_sim_signature_sample) : challenge =
  challenge_hash md
    (paper_sim_sample_response_aux s)
    (paper_sim_commitment_lowbits md s)
    (message_hash pk ctx m).

op paper_sim_commitment_highbits
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (s : paper_sim_signature_sample) : polyveck =
  let ch = paper_sim_commitment_challenge md pk m ctx s in
  reconstructed_highbits md
    (paper_sim_sample_response_aux s)
    (public_key_challenge_term md pk ch).

op paper_sim_signature
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (s : paper_sim_signature_sample) : signature =
  let highbits = paper_sim_commitment_highbits md pk m ctx s in
  let lowbits = paper_sim_commitment_lowbits md s in
  let mu = message_hash pk ctx m in
  let ch = paper_sim_commitment_challenge md pk m ctx s in
  (highbits, lowbits, mu, ch, paper_sim_sample_token s, 0, 0).

op paper_sim_signature_sample_wf
   (md : mode) (s : paper_sim_signature_sample) : bool =
  polyvecl_wf md (paper_sim_sample_response s) /\
  polyveck_wf md (paper_sim_sample_response_aux s) /\
  polyveck_wf md (paper_sim_sample_hint s) /\
  poly_wf (paper_sim_sample_lowbits_carrier s).

lemma paper_sim_commitment_lowbits_wf md s :
  poly_wf (paper_sim_commitment_lowbits md s).
proof.
by rewrite /paper_sim_commitment_lowbits /poly_wf size_mkseq /n.
qed.

lemma paper_sim_signature_valid md pk m ctx s :
  paper_sim_signature_sample_wf md s =>
  valid_signature md (paper_sim_signature md pk m ctx s).
proof.
rewrite /paper_sim_signature_sample_wf /valid_signature
        /paper_sim_signature /=.
move=> [resp_wf [aux_wf [hint_wf low_wf]]].
rewrite /paper_sim_commitment_highbits /paper_sim_commitment_challenge
        /reconstructed_highbits /=.
by smt(polyveck_add_wf paper_sim_commitment_lowbits_wf
       message_hash_size challenge_hash_wf).
qed.

op public_sim_lowbits_carrier
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (coins : random_coins) : poly =
  nth poly_zero
    (deterministic_polyveck md (public_sim_source pk m ctx coins)) 0.

op paper_sim_sample_from_public_coins
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (coins : random_coins) : paper_sim_signature_sample =
  ( public_sim_signature_token md pk m ctx coins,
    public_sim_lowbits_carrier md pk m ctx coins,
    signing_entropy_token_of_coins coins).

lemma public_sim_lowbits_carrier_wf md pk m ctx coins :
  poly_wf (public_sim_lowbits_carrier md pk m ctx coins).
proof.
rewrite /public_sim_lowbits_carrier.
apply (polyveck_wf_nth md
         (deterministic_polyveck md (public_sim_source pk m ctx coins))
         0).
+ by apply deterministic_polyveck_wf.
by smt(mode_k_gt0).
qed.

lemma paper_sim_sample_from_public_coins_wf md pk m ctx coins :
  paper_sim_signature_sample_wf md
    (paper_sim_sample_from_public_coins md pk m ctx coins).
proof.
rewrite /paper_sim_signature_sample_wf
        /paper_sim_sample_from_public_coins
        /paper_sim_sample_response /paper_sim_sample_response_aux
        /paper_sim_sample_hint /paper_sim_sample_lowbits_carrier
        /paper_sim_sample_token /public_sim_signature_token /=.
rewrite /public_sim_response_vector /public_sim_response_aux_vector
        /public_sim_hint_vector.
by smt(deterministic_unit_polyvecl_wf deterministic_unit_polyveck_wf
       public_sim_lowbits_carrier_wf).
qed.

lemma paper_sim_sample_response_public_coinsE md pk m ctx coins :
  paper_sim_sample_response
    (paper_sim_sample_from_public_coins md pk m ctx coins) =
  public_sim_response_vector md pk m ctx coins.
proof. by rewrite /paper_sim_sample_response
                  /paper_sim_sample_from_public_coins
                  /paper_sim_sample_token. qed.

lemma paper_sim_sample_response_aux_public_coinsE md pk m ctx coins :
  paper_sim_sample_response_aux
    (paper_sim_sample_from_public_coins md pk m ctx coins) =
  public_sim_response_aux_vector md pk m ctx coins.
proof. by rewrite /paper_sim_sample_response_aux
                  /paper_sim_sample_from_public_coins
                  /paper_sim_sample_token. qed.

lemma paper_sim_sample_hint_public_coinsE md pk m ctx coins :
  paper_sim_sample_hint
    (paper_sim_sample_from_public_coins md pk m ctx coins) =
  public_sim_hint_vector md pk m ctx coins.
proof. by rewrite /paper_sim_sample_hint
                  /paper_sim_sample_from_public_coins
                  /paper_sim_sample_token. qed.

lemma paper_sim_sample_token_public_coinsE md pk m ctx coins :
  paper_sim_sample_token
    (paper_sim_sample_from_public_coins md pk m ctx coins) =
  public_sim_signature_token md pk m ctx coins.
proof. by rewrite /paper_sim_sample_token
                  /paper_sim_sample_from_public_coins. qed.

lemma paper_sim_commitment_lowbits_public_coinsE md pk m ctx coins :
  paper_sim_commitment_lowbits md
    (paper_sim_sample_from_public_coins md pk m ctx coins) =
  public_sim_commitment_lowbits md pk m ctx coins.
proof.
by rewrite /paper_sim_commitment_lowbits /public_sim_commitment_lowbits
           /paper_sim_sample_from_public_coins
           /paper_sim_sample_entropy /paper_sim_sample_lowbits_carrier
           /public_sim_lowbits_carrier.
qed.

lemma paper_sim_commitment_challenge_public_coinsE md pk m ctx coins :
  paper_sim_commitment_challenge md pk m ctx
    (paper_sim_sample_from_public_coins md pk m ctx coins) =
  public_sim_commitment_challenge md pk m ctx coins.
proof.
by rewrite /paper_sim_commitment_challenge /public_sim_commitment_challenge
           paper_sim_sample_response_aux_public_coinsE
           paper_sim_commitment_lowbits_public_coinsE.
qed.

lemma paper_sim_commitment_highbits_public_coinsE md pk m ctx coins :
  paper_sim_commitment_highbits md pk m ctx
    (paper_sim_sample_from_public_coins md pk m ctx coins) =
  public_sim_commitment_highbits md pk m ctx coins.
proof.
by rewrite /paper_sim_commitment_highbits /public_sim_commitment_highbits
           paper_sim_commitment_challenge_public_coinsE
           paper_sim_sample_response_aux_public_coinsE.
qed.

lemma paper_sim_signature_public_coinsE md pk m ctx coins :
  paper_sim_signature md pk m ctx
    (paper_sim_sample_from_public_coins md pk m ctx coins) =
  public_sim_signature md pk m ctx coins.
proof.
by rewrite /paper_sim_signature /public_sim_signature
           paper_sim_commitment_highbits_public_coinsE
           paper_sim_commitment_lowbits_public_coinsE
           paper_sim_commitment_challenge_public_coinsE
           paper_sim_sample_token_public_coinsE.
qed.

op real_signing_lowbits_carrier
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : poly =
  nth poly_zero (commitment_raw md sk m ctx coins) 0.

op paper_sim_sample_from_real_signing_coins
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : paper_sim_signature_sample =
  ( signature_token md sk m ctx coins,
    real_signing_lowbits_carrier md sk m ctx coins,
    signing_entropy_token_of_coins coins).

lemma real_signing_lowbits_carrier_wf md sk m ctx coins :
  poly_wf (real_signing_lowbits_carrier md sk m ctx coins).
proof.
rewrite /real_signing_lowbits_carrier.
apply (polyveck_wf_nth md (commitment_raw md sk m ctx coins) 0).
+ by apply commitment_raw_wf.
by smt(mode_k_gt0).
qed.

lemma paper_sim_sample_from_real_signing_coins_wf md sk m ctx coins :
  paper_sim_signature_sample_wf md
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins).
proof.
rewrite /paper_sim_signature_sample_wf
        /paper_sim_sample_from_real_signing_coins
        /paper_sim_sample_response /paper_sim_sample_response_aux
        /paper_sim_sample_hint /paper_sim_sample_lowbits_carrier
        /paper_sim_sample_token /=.
by smt(response_vector_wf response_aux_vector_wf hint_vector_wf
       real_signing_lowbits_carrier_wf).
qed.

lemma paper_sim_sample_response_real_signing_coinsE md sk m ctx coins :
  paper_sim_sample_response
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins) =
  response_vector md sk m ctx coins.
proof. by rewrite /paper_sim_sample_response
                  /paper_sim_sample_from_real_signing_coins
                  /paper_sim_sample_token /signature_token. qed.

lemma paper_sim_sample_response_aux_real_signing_coinsE md sk m ctx coins :
  paper_sim_sample_response_aux
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins) =
  response_aux_vector md sk m ctx coins.
proof. by rewrite /paper_sim_sample_response_aux
                  /paper_sim_sample_from_real_signing_coins
                  /paper_sim_sample_token /signature_token. qed.

lemma paper_sim_sample_hint_real_signing_coinsE md sk m ctx coins :
  paper_sim_sample_hint
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins) =
  hint_vector md sk m ctx coins.
proof. by rewrite /paper_sim_sample_hint
                  /paper_sim_sample_from_real_signing_coins
                  /paper_sim_sample_token /signature_token. qed.

lemma paper_sim_sample_token_real_signing_coinsE md sk m ctx coins :
  paper_sim_sample_token
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins) =
  signature_token md sk m ctx coins.
proof. by rewrite /paper_sim_sample_token
                  /paper_sim_sample_from_real_signing_coins. qed.

lemma paper_sim_commitment_lowbits_real_signing_coinsE md sk m ctx coins :
  paper_sim_commitment_lowbits md
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins) =
  commitment_lowbits md sk m ctx coins.
proof.
by rewrite /paper_sim_commitment_lowbits /commitment_lowbits
           /paper_sim_sample_from_real_signing_coins
           /paper_sim_sample_entropy /paper_sim_sample_lowbits_carrier
           /real_signing_lowbits_carrier.
qed.

lemma paper_sim_commitment_challenge_real_signing_coinsE
   md sk m ctx coins :
  paper_sim_commitment_challenge md (public_key_of_secret md sk) m ctx
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins) =
  commitment_challenge md sk m ctx coins.
proof.
by rewrite /paper_sim_commitment_challenge /commitment_challenge
           paper_sim_sample_response_aux_real_signing_coinsE
           paper_sim_commitment_lowbits_real_signing_coinsE.
qed.

lemma paper_sim_commitment_highbits_real_signing_coinsE
   md sk m ctx coins :
  paper_sim_commitment_highbits md (public_key_of_secret md sk) m ctx
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins) =
  commitment_highbits md sk m ctx coins.
proof.
by rewrite /paper_sim_commitment_highbits /commitment_highbits
           paper_sim_commitment_challenge_real_signing_coinsE
           paper_sim_sample_response_aux_real_signing_coinsE.
qed.

lemma paper_sim_signature_real_signing_coinsE md sk m ctx coins :
  paper_sim_signature md (public_key_of_secret md sk) m ctx
    (paper_sim_sample_from_real_signing_coins md sk m ctx coins) =
  sign_internal md sk m ctx coins.
proof.
by rewrite /paper_sim_signature /sign_internal
           paper_sim_commitment_highbits_real_signing_coinsE
           paper_sim_commitment_lowbits_real_signing_coinsE
           paper_sim_commitment_challenge_real_signing_coinsE
           paper_sim_sample_token_real_signing_coinsE.
qed.

op paper_sim_sample_from_rejection_attempt
   (st : signing_attempt_state) : paper_sim_signature_sample =
  ( signing_attempt_state_token st,
    signing_attempt_state_lowbits_carrier st,
    signing_entropy_token_of_coins (signing_attempt_state_coins st)).

op paper_sim_abort_fallback_sample
   (md : mode) : paper_sim_signature_sample =
  ((polyvecl_zero md, polyveck_zero md, polyveck_zero md), poly_zero, 0).

op haetae_rejection_sample_from_attempt
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : paper_sim_signature_sample =
  if signing_attempt_state_rejection_accepts md pk m ctx st
  then paper_sim_sample_from_rejection_attempt st
  else paper_sim_abort_fallback_sample md.

lemma paper_sim_abort_fallback_sample_wf md :
  paper_sim_signature_sample_wf md (paper_sim_abort_fallback_sample md).
proof.
by rewrite /paper_sim_signature_sample_wf
           /paper_sim_abort_fallback_sample
           /paper_sim_sample_response /paper_sim_sample_response_aux
           /paper_sim_sample_hint /paper_sim_sample_lowbits_carrier
           /paper_sim_sample_token /= polyvecl_zero_wf polyveck_zero_wf
           poly_zero_wf.
qed.

lemma paper_sim_sample_from_rejection_attempt_of_coinsE md sk m ctx coins :
  paper_sim_sample_from_rejection_attempt
    (signing_attempt_state_of_coins md sk m ctx coins) =
  paper_sim_sample_from_real_signing_coins md sk m ctx coins.
proof.
by rewrite /paper_sim_sample_from_rejection_attempt
           /paper_sim_sample_from_real_signing_coins
           /real_signing_lowbits_carrier
           signing_attempt_state_of_coins_tokenE
           signing_attempt_state_of_coins_lowbits_carrierE
           /signing_attempt_state_coins /signing_attempt_state_of_coins.
qed.

lemma paper_sim_commitment_lowbits_rejection_attemptE md st :
  paper_sim_commitment_lowbits md
    (paper_sim_sample_from_rejection_attempt st) =
  signing_attempt_state_programmed_lowbits st.
proof.
by rewrite /paper_sim_commitment_lowbits
           /paper_sim_sample_from_rejection_attempt
           /paper_sim_sample_entropy
           /paper_sim_sample_lowbits_carrier
           /signing_attempt_state_programmed_lowbits.
qed.

lemma paper_sim_commitment_challenge_rejection_attemptE md pk m ctx st :
  signing_attempt_state_lowbits_consistent st =>
  paper_sim_commitment_challenge md pk m ctx
    (paper_sim_sample_from_rejection_attempt st) =
  signing_attempt_state_programmed_challenge md pk m ctx st.
proof.
move=> lowbits_ok.
rewrite /paper_sim_commitment_challenge
        /signing_attempt_state_programmed_challenge.
rewrite paper_sim_commitment_lowbits_rejection_attemptE.
move: lowbits_ok.
rewrite /signing_attempt_state_lowbits_consistent.
move=> <-.
by rewrite /paper_sim_sample_response_aux
           /paper_sim_sample_token
           /paper_sim_sample_from_rejection_attempt.
qed.

lemma paper_sim_commitment_highbits_rejection_attemptE md pk m ctx st :
  signing_attempt_state_lowbits_consistent st =>
  signing_attempt_state_challenge_consistent md pk m ctx st =>
  signing_attempt_state_public_equation_consistent md pk st =>
  paper_sim_commitment_highbits md pk m ctx
    (paper_sim_sample_from_rejection_attempt st) =
  signing_attempt_state_highbits st.
proof.
move=> lowbits_ok challenge_ok public_ok.
rewrite /paper_sim_commitment_highbits.
rewrite (paper_sim_commitment_challenge_rejection_attemptE
           md pk m ctx st lowbits_ok).
move: challenge_ok public_ok.
rewrite /signing_attempt_state_challenge_consistent
        /signing_attempt_state_public_equation_consistent
        /signing_attempt_state_reconstructed_highbits.
move=> challengeE publicE.
rewrite -challengeE.
rewrite /paper_sim_sample_response_aux
        /paper_sim_sample_token
        /paper_sim_sample_from_rejection_attempt.
by smt().
qed.

lemma paper_sim_signature_rejection_attempt_fieldsE md pk m ctx st :
  signing_attempt_state_field_accepts md pk m ctx st =>
  paper_sim_signature md pk m ctx
    (paper_sim_sample_from_rejection_attempt st) =
  signing_attempt_state_signature_of_fields pk m ctx st.
proof.
rewrite /signing_attempt_state_field_accepts.
move=> [lowbits_ok [challenge_ok [public_ok fields_ok]]].
rewrite /paper_sim_signature
        (paper_sim_commitment_highbits_rejection_attemptE
           md pk m ctx st lowbits_ok challenge_ok public_ok)
        paper_sim_commitment_lowbits_rejection_attemptE.
have lowbits_ok' := lowbits_ok.
move: lowbits_ok.
rewrite /signing_attempt_state_lowbits_consistent.
move=> lowbitsE.
rewrite -lowbitsE.
rewrite (paper_sim_commitment_challenge_rejection_attemptE
           md pk m ctx st lowbits_ok').
move: challenge_ok.
rewrite /signing_attempt_state_challenge_consistent.
move=> challengeE.
rewrite -challengeE.
by rewrite /signing_attempt_state_signature_of_fields
           /paper_sim_sample_token
           /paper_sim_sample_from_rejection_attempt.
qed.

lemma paper_sim_signature_rejection_attempt_matches_state md pk m ctx st :
  signing_attempt_state_field_accepts md pk m ctx st =>
  paper_sim_signature md pk m ctx
    (paper_sim_sample_from_rejection_attempt st) =
  signing_attempt_state_signature st.
proof.
move=> field_ok.
rewrite (paper_sim_signature_rejection_attempt_fieldsE
           md pk m ctx st field_ok).
move: field_ok.
rewrite /signing_attempt_state_field_accepts.
move=> [_ [_ [_ match_ok]]].
by move: match_ok;
   rewrite /signing_attempt_state_fields_match_signature => <-.
qed.

lemma paper_sim_signature_rejection_attempt_of_coinsE md sk m ctx coins :
  paper_sim_signature md (public_key_of_secret md sk) m ctx
    (paper_sim_sample_from_rejection_attempt
      (signing_attempt_state_of_coins md sk m ctx coins)) =
  sign_internal md sk m ctx coins.
proof.
rewrite (paper_sim_signature_rejection_attempt_matches_state
          md (public_key_of_secret md sk) m ctx
          (signing_attempt_state_of_coins md sk m ctx coins)
          (signing_attempt_state_of_coins_field_accepts md sk m ctx coins)).
by rewrite signing_attempt_state_of_coins_signatureE.
qed.

lemma haetae_rejection_sample_from_attempt_signatureE md pk m ctx st :
  signing_attempt_state_rejection_accepts md pk m ctx st =>
  paper_sim_signature md pk m ctx
    (haetae_rejection_sample_from_attempt md pk m ctx st) =
  signing_attempt_state_signature st.
proof.
move=> reject_ok.
rewrite /haetae_rejection_sample_from_attempt.
rewrite reject_ok.
move: reject_ok.
rewrite /signing_attempt_state_rejection_accepts
        /signing_attempt_state_verification_accepts.
move=> [[field_ok _] _].
by rewrite (paper_sim_signature_rejection_attempt_matches_state
              md pk m ctx st field_ok).
qed.

lemma haetae_rejection_sample_from_attempt_no_fallback md pk m ctx st :
  signing_attempt_state_rejection_accepts md pk m ctx st =>
  haetae_rejection_sample_from_attempt md pk m ctx st =
  paper_sim_sample_from_rejection_attempt st.
proof.
move=> reject_ok.
by rewrite /haetae_rejection_sample_from_attempt reject_ok.
qed.

lemma haetae_rejection_sample_from_attempt_of_coinsE md sk m ctx coins :
  haetae_rejection_sample_from_attempt md (public_key_of_secret md sk) m ctx
    (signing_attempt_state_of_coins md sk m ctx coins) =
  paper_sim_sample_from_real_signing_coins md sk m ctx coins.
proof.
rewrite /haetae_rejection_sample_from_attempt
        signing_attempt_state_of_coins_rejection_accepts_current.
by rewrite
           paper_sim_sample_from_rejection_attempt_of_coinsE.
qed.

lemma haetae_rejection_sample_from_attempt_of_coins_wf md sk m ctx coins :
  paper_sim_signature_sample_wf md
    (haetae_rejection_sample_from_attempt md (public_key_of_secret md sk) m ctx
       (signing_attempt_state_of_coins md sk m ctx coins)).
proof.
by rewrite haetae_rejection_sample_from_attempt_of_coinsE;
   apply paper_sim_sample_from_real_signing_coins_wf.
qed.

module type PaperSimSigningSampler = {
  proc init(pk : pkey) : unit
  proc sample_with_seed(seed_coins : random_coins, m : message, ctx : context)
    : paper_sim_signature_sample
  proc sample(m : message, ctx : context) : paper_sim_signature_sample
}.

module ROMPaperSimSigningSampler(H : SIG.POracle) : PaperSimSigningSampler = {
  var pk_current : pkey

  proc init(pk : pkey) : unit = {
    pk_current <- pk;
  }

  proc sample_with_seed(seed_coins : random_coins, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var coins : random_coins;
    var ro_y : ro_output;
    var smp : paper_sim_signature_sample;

    ro_y <@ H.get(sampler_expand_query seed_coins);
    coins <- ro_signing_coins ro_y;
    smp <- paper_sim_sample_from_public_coins haetae_mode
      pk_current m ctx coins;
    return smp;
  }

  proc sample(m : message, ctx : context) : paper_sim_signature_sample = {
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;

    seed_coins <$ drandom_coins;
    smp <@ sample_with_seed(seed_coins, m, ctx);
    return smp;
  }
}.

module RealSigningPaperSimSampler(H : SIG.POracle) : PaperSimSigningSampler = {
  var pk_current : pkey
  var sk_current : skey

  proc init(pk : pkey) : unit = {
    pk_current <- pk;
    sk_current <- secret_key_of_seed haetae_mode pk.`1;
  }

  proc sample_with_seed(seed_coins : random_coins, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var coins : random_coins;
    var ro_y : ro_output;
    var smp : paper_sim_signature_sample;

    ro_y <@ H.get(sampler_expand_query seed_coins);
    coins <- ro_signing_coins ro_y;
    smp <- paper_sim_sample_from_real_signing_coins haetae_mode
      sk_current m ctx coins;
    return smp;
  }

  proc sample(m : message, ctx : context) : paper_sim_signature_sample = {
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;

    seed_coins <$ drandom_coins;
    smp <@ sample_with_seed(seed_coins, m, ctx);
    return smp;
  }
}.

module ROSigningAttemptPaperSimSampler(H : SIG.POracle)
  : PaperSimSigningSampler = {
  var pk_current : pkey
  var sk_current : skey

  proc init(pk : pkey) : unit = {
    pk_current <- pk;
    sk_current <- secret_key_of_seed haetae_mode pk.`1;
  }

  proc sample_with_seed(seed_coins : random_coins, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var coins : random_coins;
    var ro_y : ro_output;
    var st : signing_attempt_state;
    var smp : paper_sim_signature_sample;

    ro_y <@ H.get(sampler_expand_query seed_coins);
    coins <- ro_signing_coins ro_y;
    st <- signing_attempt_state_of_coins haetae_mode
      sk_current m ctx coins;
    smp <- paper_sim_sample_from_rejection_attempt st;
    return smp;
  }

  proc sample(m : message, ctx : context) : paper_sim_signature_sample = {
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;

    seed_coins <$ drandom_coins;
    smp <@ sample_with_seed(seed_coins, m, ctx);
    return smp;
  }
}.

module HAETAERejectionPaperSimSampler(H : SIG.POracle)
  : PaperSimSigningSampler = {
  var pk_current : pkey
  var sk_current : skey

  proc init(pk : pkey) : unit = {
    pk_current <- pk;
    sk_current <- secret_key_of_seed haetae_mode pk.`1;
  }

  proc sample_with_seed(seed_coins : random_coins, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var coins : random_coins;
    var ro_y : ro_output;
    var st : signing_attempt_state;
    var smp : paper_sim_signature_sample;

    ro_y <@ H.get(sampler_expand_query seed_coins);
    coins <- ro_signing_coins ro_y;
    st <- signing_attempt_state_of_coins haetae_mode
      sk_current m ctx coins;
    smp <- haetae_rejection_sample_from_attempt haetae_mode
      pk_current m ctx st;
    return smp;
  }

  proc sample(m : message, ctx : context) : paper_sim_signature_sample = {
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;

    seed_coins <$ drandom_coins;
    smp <@ sample_with_seed(seed_coins, m, ctx);
    return smp;
  }
}.

module ExactHyperballHAETAERejectionPaperSimSampler(H : SIG.POracle)
  : PaperSimSigningSampler = {
  var pk_current : pkey
  var sk_current : skey

  proc init(pk : pkey) : unit = {
    pk_current <- pk;
    sk_current <- secret_key_of_seed haetae_mode pk.`1;
  }

  proc sample_with_seed(seed_coins : random_coins, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var st : signing_attempt_state;
    var smp : paper_sim_signature_sample;

    st <$ dexact_hyperball_signing_attempt_state haetae_mode
      sk_current m ctx;
    smp <- paper_sim_sample_from_rejection_attempt st;
    return smp;
  }

  proc sample(m : message, ctx : context) : paper_sim_signature_sample = {
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;

    seed_coins <$ drandom_coins;
    smp <@ sample_with_seed(seed_coins, m, ctx);
    return smp;
  }
}.

module ExactHyperballPaperSimSampler(H : SIG.POracle)
  : PaperSimSigningSampler = {
  var pk_current : pkey
  var sk_current : skey

  proc init(pk : pkey) : unit = {
    pk_current <- pk;
    sk_current <- secret_key_of_seed haetae_mode pk.`1;
  }

  proc sample_with_seed(seed_coins : random_coins, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var st : signing_attempt_state;
    var smp : paper_sim_signature_sample;

    st <$ dexact_hyperball_signing_attempt_state haetae_mode
      sk_current m ctx;
    smp <- paper_sim_sample_from_rejection_attempt st;
    return smp;
  }

  proc sample(m : message, ctx : context) : paper_sim_signature_sample = {
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;

    seed_coins <$ drandom_coins;
    smp <@ sample_with_seed(seed_coins, m, ctx);
    return smp;
  }
}.

module ROExactHyperballPaperSimSampler(H : SIG.POracle)
  : PaperSimSigningSampler = {
  var pk_current : pkey
  var sk_current : skey

  proc init(pk : pkey) : unit = {
    pk_current <- pk;
    sk_current <- secret_key_of_seed haetae_mode pk.`1;
  }

  proc sample_with_seed(seed_coins : random_coins, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var ro_y : ro_output;
    var st : signing_attempt_state;
    var smp : paper_sim_signature_sample;

    ro_y <@ H.get(sampler_expand_query seed_coins);
    st <$ dexact_hyperball_signing_attempt_state haetae_mode
      sk_current m ctx;
    smp <- paper_sim_sample_from_rejection_attempt st;
    return smp;
  }

  proc sample(m : message, ctx : context) : paper_sim_signature_sample = {
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;

    seed_coins <$ drandom_coins;
    smp <@ sample_with_seed(seed_coins, m, ctx);
    return smp;
  }
}.

module StructuralAttemptPaperSample = {
  proc sample(sk : skey, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var st : signing_attempt_state;
    var smp : paper_sim_signature_sample;

    st <$ dsigning_attempt_state haetae_mode sk m ctx;
    smp <- paper_sim_sample_from_rejection_attempt st;
    return smp;
  }
}.

module ExactHyperballPaperSample = {
  proc sample(sk : skey, m : message, ctx : context)
    : paper_sim_signature_sample = {
    var st : signing_attempt_state;
    var smp : paper_sim_signature_sample;

    st <$ dexact_hyperball_signing_attempt_state haetae_mode sk m ctx;
    smp <- paper_sim_sample_from_rejection_attempt st;
    return smp;
  }
}.

module ROMInternalTranscriptPaperSimAsNMA(
  A : SIG.Adversary,
  Samp : PaperSimSigningSampler
) (H : SIG.POracle) = {
  var pk_current : pkey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var smp : paper_sim_signature_sample;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;

      smp <@ Samp.sample(m, ctx);
      ro_y <@ H.get(message_hash_query pk_current ctx m);
      mu <- ro_message_hash ro_y;
      highbits <- paper_sim_commitment_highbits haetae_mode
        pk_current m ctx smp;
      lowbits <- paper_sim_commitment_lowbits haetae_mode smp;
      ro_y <@ H.get(challenge_hash_query haetae_mode highbits lowbits mu);
      sig <- paper_sim_signature haetae_mode pk_current m ctx smp;
      tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
      queries <- (m, ctx) :: queries;
      transcripts <- tr :: transcripts;
      records <- (m, ctx, sig, tr) :: records;
      return sig;
    }
  }

  module A = A(H, O)

  proc forge(pk : pkey) : message * context * signature = {
    var r : message * context * signature;

    pk_current <- pk;
    queries <- [];
    transcripts <- [];
    records <- [];
    Samp.init(pk);
    r <@ A.forge(pk);
    return r;
  }
}.

module ROMInternalTranscriptBudgetedPaperSimAsNMA(
  A : SIG.Adversary,
  Samp : PaperSimSigningSampler
) (H : SIG.POracle) = {
  var pk_current : pkey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list
  var adversary_hash_count : int
  var signing_count : int
  var adversary_hash_queries : ro_query list
  var sampler_expand_queries : ro_query list
  var sampler_bad_prequery : bool

  module AH = {
    proc get(q : ro_query) : ro_output = {
      var y : ro_output;

      if (adversary_hash_count < hash_query_budget_count) {
        if (adversary_hash_count = 0) {
          adversary_hash_count <- 1;
        } else {
          adversary_hash_count <- hash_query_budget_count;
        }
        y <@ H.get(q);
        adversary_hash_queries <- q :: adversary_hash_queries;
      } else {
        adversary_hash_count <- hash_query_budget_count;
        y <- ro_output_zero;
      }
      return y;
    }
  }

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var seed_coins : random_coins;
      var smp : paper_sim_signature_sample;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;
      var old_adversary_hash_queries : ro_query list;
      var old_sampler_expand_queries : ro_query list;
      var old_sampler_bad_prequery : bool;

      if (signing_count < signature_query_budget_count) {
        if (signing_count = 0) {
          signing_count <- 1;
        } else {
          signing_count <- signature_query_budget_count;
        }
        old_adversary_hash_queries <- adversary_hash_queries;
        old_sampler_expand_queries <- sampler_expand_queries;
        old_sampler_bad_prequery <- sampler_bad_prequery;
        seed_coins <$ drandom_coins;
        sampler_bad_prequery <-
          old_sampler_bad_prequery \/
          sampler_expand_query seed_coins \in old_adversary_hash_queries \/
          sampler_expand_query seed_coins \in old_sampler_expand_queries;
        sampler_expand_queries <-
          sampler_expand_query seed_coins :: old_sampler_expand_queries;
        smp <@ Samp.sample_with_seed(seed_coins, m, ctx);
        ro_y <@ H.get(message_hash_query pk_current ctx m);
        mu <- ro_message_hash ro_y;
        highbits <- paper_sim_commitment_highbits haetae_mode
          pk_current m ctx smp;
        lowbits <- paper_sim_commitment_lowbits haetae_mode smp;
        ro_y <@ H.get(challenge_hash_query haetae_mode highbits lowbits mu);
        sig <- paper_sim_signature haetae_mode pk_current m ctx smp;
        tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
        queries <- (m, ctx) :: queries;
        transcripts <- tr :: transcripts;
        records <- (m, ctx, sig, tr) :: records;
      } else {
        signing_count <- signature_query_budget_count;
        smp <- paper_sim_abort_fallback_sample haetae_mode;
        sig <- paper_sim_signature haetae_mode pk_current m ctx smp;
      }
      return sig;
    }
  }

  module A = A(AH, O)

  proc forge(pk : pkey) : message * context * signature = {
    var r : message * context * signature;

    pk_current <- pk;
    queries <- [];
    transcripts <- [];
    records <- [];
    adversary_hash_count <- 0;
    signing_count <- 0;
    adversary_hash_queries <- [];
    sampler_expand_queries <- [];
    sampler_bad_prequery <- false;
    Samp.init(pk);
    r <@ A.forge(pk);
    return r;
  }
}.

section ROMInternalTranscriptBudgetedPaperSimNMAQueryBudget.

declare module H <: SIG.Oracle {-ROMInternalTranscriptBudgetedPaperSimAsNMA}.
declare module A <: SIG.Adversary {-H,
                                   -ROMInternalTranscriptBudgetedPaperSimAsNMA}.
declare module Samp <: PaperSimSigningSampler
  {-A, -ROMInternalTranscriptBudgetedPaperSimAsNMA}.

lemma budgeted_paper_sim_sign_oracle_preserves_signing_count :
  hoare[ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).O.sign :
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc.
if.
+ wp.
  call (_: true).
  wp.
  call (_: true).
  wp.
  call (_: true).
  by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                      /signature_query_budget_count; smt.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /signature_query_budget_count; smt.
qed.

lemma adversary_budgeted_paper_sim_signing_count_preserved :
  hoare[
    ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).A.forge :
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc
  (budgeted_paper_sim_signing_count_discipline
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count) => //.
+ move=> />.
+ proc.
  if.
  + wp.
    call (_: true).
    by auto.
  by auto.
+ by apply budgeted_paper_sim_sign_oracle_preserves_signing_count.
qed.

lemma budgeted_paper_sim_main_signing_count_preserved :
  hoare[ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).forge :
    true ==>
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc.
wp.
call (_:
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count).
+ conseq adversary_budgeted_paper_sim_signing_count_preserved => />.
wp.
call (_: true).
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /signature_query_budget_count.
qed.

lemma sampler_expand_query_point_bound q :
  mu drandom_coins (fun coins => sampler_expand_query coins = q) <=
  signing_randomness_point_bound.
proof.
rewrite /sampler_expand_query.
case q => /=.
+ by rewrite mu0 /signing_randomness_point_bound
           /signing_entropy_token_cardinality; smt.
+ by rewrite mu0 /signing_randomness_point_bound
           /signing_entropy_token_cardinality; smt.
+ by rewrite mu0 /signing_randomness_point_bound
           /signing_entropy_token_cardinality; smt.
+ move=> target.
  apply (ler_trans
    (mu drandom_coins
       (fun coins =>
          signing_entropy_token_of_coins coins =
          signing_entropy_token_of_coins target))).
  + apply mu_le => coins _ eq_q.
    by smt.
  by apply signing_coin_distribution_token_point_bound.
qed.

lemma sampler_expand_query_log_fset_bound (qs : ro_query list) :
  mu drandom_coins
    (fun coins => sampler_expand_query coins \in qs) <=
  (card (oflist qs))%r * signing_randomness_point_bound.
proof.
rewrite (mu_eq _ _
  (fun coins =>
    exists (q : ro_query),
      q \in oflist qs /\ sampler_expand_query coins = q)).
+ move=> coins.
  by smt(mem_oflist).
apply (mu_mem_le_gen (oflist qs) drandom_coins
        (fun q coins => sampler_expand_query coins = q)
        signing_randomness_point_bound).
move=> q _.
by apply sampler_expand_query_point_bound.
qed.

lemma sampler_expand_query_log_budget_bound (qs : ro_query list) hc :
  0 <= hc =>
  hc <= hash_query_budget_count =>
  size qs <= hc =>
  mu drandom_coins
    (fun coins => sampler_expand_query coins \in qs) <=
  rom_hash_query_budget / challenge_support_cardinality_lower_bound.
proof.
move=> hc_ge0 hc_budget size_bound.
apply (ler_trans
  ((card (oflist qs))%r * signing_randomness_point_bound)).
+ by apply sampler_expand_query_log_fset_bound.
rewrite /signing_randomness_point_bound
        /rom_hash_query_budget /hash_query_count /hash_query_budget_count
        /challenge_support_cardinality_lower_bound
        /signing_entropy_token_cardinality.
  smt(fcard_oflist).
qed.

lemma sampler_expand_query_joint_log_budget_bound
    (hash_qs sampler_qs : ro_query list) hc sc :
  0 <= hc =>
  hc <= hash_query_budget_count =>
  0 <= sc =>
  sc <= signature_query_budget_count =>
  size hash_qs <= hc =>
  size sampler_qs <= sc =>
  mu drandom_coins
    (fun coins =>
      sampler_expand_query coins \in hash_qs \/
      sampler_expand_query coins \in sampler_qs) <=
  (rom_hash_query_budget + rom_signature_query_budget) /
    challenge_support_cardinality_lower_bound.
proof.
move=> hc_ge0 hc_budget sc_ge0 sc_budget hash_size sampler_size.
rewrite (mu_eq _ _
  (fun coins => sampler_expand_query coins \in hash_qs ++ sampler_qs)).
+ move=> coins.
  by rewrite mem_cat.
apply (ler_trans
  ((card (oflist (hash_qs ++ sampler_qs)))%r *
     signing_randomness_point_bound)).
+ by apply sampler_expand_query_log_fset_bound.
rewrite /signing_randomness_point_bound
        /rom_hash_query_budget /rom_signature_query_budget
        /hash_query_count /signature_query_count
        /hash_query_budget_count /signature_query_budget_count
        /challenge_support_cardinality_lower_bound
        /signing_entropy_token_cardinality.
smt(fcard_oflist size_cat).
qed.

lemma concrete_lazy_rom_sampler_expand_query_fresh_le
    seed_coins (p : random_coins -> bool) &m :
  sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m{m} =>
  Pr[HAETAE_RO.FRO.get(sampler_expand_query seed_coins) @ &m :
       p (ro_signing_coins res)] <=
  mu drandom_coins p.
proof.
move=> fresh.
byphoare (_ :
    arg = sampler_expand_query seed_coins /\
    sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m
    ==> p (ro_signing_coins res)) => //.
proc.
wp.
rnd.
auto => /> &hr _.
rewrite sampler_expand_query_dro_output_ro_signing_coins.
by rewrite lerr.
qed.

lemma concrete_lazy_rom_sampler_expand_query_fresh_eq
    seed_coins (p : random_coins -> bool) :
  phoare[HAETAE_RO.FRO.get :
    arg = sampler_expand_query seed_coins /\
    sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m
    ==> p (ro_signing_coins res)] =
  (mu drandom_coins p).
proof.
proc.
wp.
rnd.
auto => /> &hr _.
by rewrite sampler_expand_query_dro_output_ro_signing_coins.
qed.

lemma concrete_lazy_rom_get_preserves_sampler_rom_covered
    q hash_qs sampler_qs :
  hoare[HAETAE_RO.FRO.get :
    arg = q /\
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs /\
    (forall seed_coins,
       q = sampler_expand_query seed_coins =>
       q \in hash_qs \/ q \in sampler_qs) ==>
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs].
proof.
proc.
wp.
rnd.
auto => />.
rewrite /sampler_rom_covered.
smt(mem_set).
qed.

lemma concrete_lazy_rom_get_preserves_sampler_rom_covered_arg
    hash_qs sampler_qs :
  hoare[HAETAE_RO.FRO.get :
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs /\
    (forall seed_coins,
       arg = sampler_expand_query seed_coins =>
       arg \in hash_qs \/ arg \in sampler_qs) ==>
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs].
proof.
proc.
wp.
rnd.
auto => />.
rewrite /sampler_rom_covered.
smt(mem_set).
qed.

lemma concrete_lazy_rom_get_preserves_sampler_rom_covered_budgeted_logs :
  hoare[HAETAE_RO.FRO.get :
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries /\
    (forall seed_coins,
       arg = sampler_expand_query seed_coins =>
       arg \in
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries \/
       arg \in
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries) ==>
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries].
proof.
proc.
wp.
rnd.
auto => />.
rewrite /sampler_rom_covered.
smt(mem_set).
qed.

lemma concrete_lazy_rom_get_preserves_sampler_rom_covered_hash_cons
    q hash_qs sampler_qs :
  hoare[HAETAE_RO.FRO.get :
    arg = q /\
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs ==>
    sampler_rom_covered HAETAE_RO.FRO.m (q :: hash_qs) sampler_qs].
proof.
proc.
wp.
rnd.
auto => />.
rewrite /sampler_rom_covered.
smt(mem_set).
qed.

lemma concrete_lazy_rom_get_preserves_sampler_rom_covered_sampler_cons
    q hash_qs sampler_qs :
  hoare[HAETAE_RO.FRO.get :
    arg = q /\
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs ==>
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs (q :: sampler_qs)].
proof.
proc.
wp.
rnd.
auto => />.
rewrite /sampler_rom_covered.
smt(mem_set).
qed.

lemma sampler_bad_prequery_one_step_bound_nonnegative :
  0%r <= rom_hash_query_budget / challenge_support_cardinality_lower_bound.
proof.
apply divr_ge0.
+ by apply rom_hash_query_budget_nonnegative.
by apply challenge_support_cardinality_lower_bound_nonnegative.
qed.

lemma budgeted_paper_sim_sampler_bad_prequery_forge_fel_bound pk &m :
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).forge(pk) @ &m :
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
    rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound).
proof.
  fel 9
       ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
       (fun _,
          (rom_hash_query_budget + rom_signature_query_budget) /
            challenge_support_cardinality_lower_bound)
       signature_query_budget_count
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery
       [ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).AH.get :
          false;
        ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).O.sign :
          (!ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
           ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <
             signature_query_budget_count)]
       (budgeted_paper_sim_sampler_freshness_discipline
          ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
          ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
          ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
          ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries).
+ rewrite /rom_signature_query_budget /signature_query_count
          /signature_query_budget_count.
  rewrite StdBigop.Bigreal.BRA.sumri_const.
  + by smt.
  by rewrite RField.intmulr; smt.
+ by smt.
+ inline ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).forge.
  wp.
  by auto => />;
     rewrite /budgeted_paper_sim_sampler_freshness_discipline
             /hash_query_budget_count
             /signature_query_budget_count;
     smt.
+ proc.
  if.
  + conseq (: _ ==> false : = 0%r) => />.
    + hoare.
      wp.
      call (_: true).
      by auto.
  conseq (: _ ==> false : = 0%r) => />.
  + hoare.
    by auto.
+ move=> old_count.
  proc.
  if.
  + wp.
    call (_: true).
    by auto => />; rewrite /budgeted_paper_sim_sampler_freshness_discipline
                         /hash_query_budget_count
                         /signature_query_budget_count; smt.
  by auto => />; rewrite /budgeted_paper_sim_sampler_freshness_discipline
                      /signature_query_budget_count; smt.
+ move=> old_bad old_count.
  proc.
  if.
  + wp.
    call (_: true).
    by auto => />; rewrite /budgeted_paper_sim_sampler_freshness_discipline
                         /hash_query_budget_count
                         /signature_query_budget_count; smt.
  by auto => />; rewrite /budgeted_paper_sim_sampler_freshness_discipline
                      /signature_query_budget_count; smt.
+ proc.
  if.
  + seq 6 :
      (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery)
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound)
      (1%r) (1%r) (0%r).
    + wp.
      rnd.
      by auto => />; smt(signing_coin_distribution_lossless).
    + wp.
      rnd (fun seed_coins =>
        sampler_expand_query seed_coins \in
          ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries \/
        sampler_expand_query seed_coins \in
          ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries).
      auto => />.
      move=> &hr *.
      by apply (sampler_expand_query_joint_log_budget_bound
        ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{hr}
        ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{hr}
        ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{hr}
        ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{hr});
        smt.
    + by trivial.
    hoare.
    wp.
    call (_: true).
    wp.
    call (_: true).
    wp.
    call (_: true).
    by auto.
    + by smt.
  conseq (: _ ==> false : = 0%r) => />.
  + by smt.
  hoare.
  by auto => />; rewrite /signature_query_budget_count; smt.
+ move=> old_count.
  proc.
  if.
  + wp.
    call (_: true).
    wp.
    call (_: true).
    wp.
    call (_: true).
    wp.
    rnd.
    by auto => />; rewrite /budgeted_paper_sim_sampler_freshness_discipline
                         /hash_query_budget_count
                         /signature_query_budget_count; smt.
  by auto => />; rewrite /budgeted_paper_sim_sampler_freshness_discipline
                      /signature_query_budget_count; smt.
+ move=> old_bad old_count.
  proc.
  if.
  + wp.
    call (_: true).
    wp.
    call (_: true).
    wp.
    call (_: true).
    wp.
    rnd.
    by auto => />; rewrite /budgeted_paper_sim_sampler_freshness_discipline
                         /hash_query_budget_count
                         /signature_query_budget_count; smt.
  by auto => />; rewrite /budgeted_paper_sim_sampler_freshness_discipline
                      /signature_query_budget_count; smt.
qed.

lemma budgeted_paper_sim_sampler_bad_prequery_forge_fel_phoare :
  phoare[ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).forge :
       true ==> ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
    (rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound)).
proof.
bypr=> &m _.
exact (budgeted_paper_sim_sampler_bad_prequery_forge_fel_bound
         arg{m} &m).
qed.

lemma budgeted_paper_sim_sampler_bad_prequery_nma_fel_bound &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp)).main() @ &m :
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
    rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound).
proof.
byphoare (_: true ==>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery) => //.
proc.
inline HAETAE(H).verify.
wp.
call budgeted_paper_sim_sampler_bad_prequery_forge_fel_phoare.
wp.
inline HAETAE(H).kg.
wp.
call (_: true).
wp.
rnd.
wp.
call (_: true).
by auto.
qed.

lemma concrete_lazy_rom_sampler_expand_query_fresh_phoare
    seed_coins (p : random_coins -> bool) :
  phoare[HAETAE_RO.FRO.get :
      arg = sampler_expand_query seed_coins /\
      sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m
      ==> p (ro_signing_coins res)] <=
    (mu drandom_coins p).
proof.
bypr=> &m [arg_eq fresh].
rewrite arg_eq.
by apply (concrete_lazy_rom_sampler_expand_query_fresh_le seed_coins p &m fresh).
qed.

lemma concrete_lazy_rom_sampler_expand_query_fresh_arg_phoare
    (p : random_coins -> bool) :
  phoare[HAETAE_RO.FRO.get :
      (exists seed_coins,
         arg = sampler_expand_query seed_coins /\
         sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m)
      ==> p (ro_signing_coins res)] <=
    (mu drandom_coins p).
proof.
bypr=> &m [seed_coins [arg_eq fresh]].
rewrite arg_eq.
by apply (concrete_lazy_rom_sampler_expand_query_fresh_le seed_coins p &m fresh).
qed.

lemma concrete_lazy_rom_sampler_expand_query_fresh_arg_clean_phoare
    (p : random_coins -> bool) :
  phoare[HAETAE_RO.FRO.get :
      (exists seed_coins,
         arg = sampler_expand_query seed_coins /\
         sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m) /\
      ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery
      ==> p (ro_signing_coins res) /\
          ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
    (mu drandom_coins p).
proof.
proc.
wp.
rnd.
auto => /> &hr seed_coins arg_eq fresh.
rewrite sampler_expand_query_dro_output_ro_signing_coins.
by rewrite lerr.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_fresh_structural_le
    seed_coins sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg = (seed_coins, m, ctx) /\
      ROSigningAttemptPaperSimSampler.sk_current = sk /\
      sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m
      ==> p res] <=
    (mu (dsigning_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
rewrite /dsigning_attempt_state dmapE /=.
proc.
wp.
call (concrete_lazy_rom_sampler_expand_query_fresh_phoare seed_coins
  (fun coins =>
     p (paper_sim_sample_from_rejection_attempt
          (signing_attempt_state_of_coins haetae_mode
             sk m ctx coins)))).
by auto => />.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_fresh_structural_arg_le
    sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg.`2 = m /\
      arg.`3 = ctx /\
      ROSigningAttemptPaperSimSampler.sk_current = sk /\
      sampler_expand_query arg.`1 \notin HAETAE_RO.FRO.m
      ==> p res] <=
    (mu (dsigning_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
rewrite /dsigning_attempt_state dmapE /=.
proc.
wp.
call (concrete_lazy_rom_sampler_expand_query_fresh_arg_phoare
  (fun coins =>
     p (paper_sim_sample_from_rejection_attempt
          (signing_attempt_state_of_coins haetae_mode
             sk m ctx coins)))).
by auto => />; smt.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_fresh_structural_arg_clean_le
    sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg.`2 = m /\
      arg.`3 = ctx /\
      ROSigningAttemptPaperSimSampler.sk_current = sk /\
      ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
      sampler_expand_query arg.`1 \notin HAETAE_RO.FRO.m
      ==> p res /\
          ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
    (mu (dsigning_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
rewrite /dsigning_attempt_state dmapE /=.
proc.
wp.
call (concrete_lazy_rom_sampler_expand_query_fresh_arg_clean_phoare
  (fun coins =>
     p (paper_sim_sample_from_rejection_attempt
          (signing_attempt_state_of_coins haetae_mode
             sk m ctx coins)))).
by auto => />; smt.
qed.

lemma concrete_lazy_rom_sampler_expand_query_guarded_clean_phoare
    (p : random_coins -> bool) :
  phoare[HAETAE_RO.FRO.get :
      (! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery =>
       exists seed_coins,
         arg = sampler_expand_query seed_coins /\
         sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m)
      ==> p (ro_signing_coins res) /\
          ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
    (mu drandom_coins p).
proof.
proc.
wp.
rnd.
auto => /> &hr guarded.
case (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{hr}).
+ move=> bad.
  rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
  + by move=> y; case (x{hr} \in HAETAE_RO.FRO.m{hr}).
  by rewrite mu0; smt(mu_bounded).
+ move=> clean.
  elim (guarded clean) => seed_coins [arg_eq fresh].
  rewrite arg_eq fresh /=.
  rewrite sampler_expand_query_dro_output_ro_signing_coins.
  by rewrite lerr.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_guarded_clean_structural_arg_le
    sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg.`2 = m /\
      arg.`3 = ctx /\
      ROSigningAttemptPaperSimSampler.sk_current = sk /\
      (! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery =>
       sampler_expand_query arg.`1 \notin HAETAE_RO.FRO.m)
      ==> p res /\
          ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
    (mu (dsigning_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
rewrite /dsigning_attempt_state dmapE /=.
proc.
wp.
call (concrete_lazy_rom_sampler_expand_query_guarded_clean_phoare
  (fun coins =>
     p (paper_sim_sample_from_rejection_attempt
          (signing_attempt_state_of_coins haetae_mode
             sk m ctx coins)))).
by auto => />; smt.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_fresh_structural_eq
    seed_coins sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg = (seed_coins, m, ctx) /\
      ROSigningAttemptPaperSimSampler.sk_current = sk /\
      sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m
      ==> p res] =
    (mu (dsigning_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
rewrite /dsigning_attempt_state dmapE /=.
proc.
wp.
call (concrete_lazy_rom_sampler_expand_query_fresh_eq seed_coins
  (fun coins =>
     p (paper_sim_sample_from_rejection_attempt
          (signing_attempt_state_of_coins haetae_mode
             sk m ctx coins)))).
by auto => />.
qed.

lemma concrete_ro_exact_hyperball_sample_with_seed_exact
    seed_coins sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg = (seed_coins, m, ctx) /\
      ROExactHyperballPaperSimSampler.sk_current = sk
      ==> p res] =
    (mu (dexact_hyperball_signing_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
proc.
wp.
rnd.
wp.
call (_: ROExactHyperballPaperSimSampler.sk_current = sk).
wp; rnd; auto; smt(ro_output_distribution_lossless).
by auto.
qed.

lemma concrete_ro_exact_hyperball_sample_with_seed_exact_no_seed
    sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg.`2 = m /\
      arg.`3 = ctx /\
      ROExactHyperballPaperSimSampler.sk_current = sk
      ==> p res] =
    (mu (dexact_hyperball_signing_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
proc.
wp.
rnd.
wp.
call (_: ROExactHyperballPaperSimSampler.sk_current = sk).
wp; rnd; auto; smt(ro_output_distribution_lossless).
by auto.
qed.

lemma concrete_ro_exact_hyperball_sample_with_seed_exact_pr
    seed_coins m ctx (p : paper_sim_signature_sample -> bool) &m :
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] =
    mu (dexact_hyperball_signing_attempt_state haetae_mode
          ROExactHyperballPaperSimSampler.sk_current{m} m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st)).
proof.
byphoare (concrete_ro_exact_hyperball_sample_with_seed_exact
  seed_coins ROExactHyperballPaperSimSampler.sk_current{m} m ctx p) => //.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_preserves_sampler_rom_covered
    hash_qs sampler_qs :
  hoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs /\
    sampler_expand_query arg.`1 \in sampler_qs ==>
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs].
proof.
proc.
wp.
call (concrete_lazy_rom_get_preserves_sampler_rom_covered_arg
        hash_qs sampler_qs).
by auto => />; smt.
qed.

lemma concrete_ro_exact_hyperball_sample_with_seed_preserves_sampler_rom_covered
    hash_qs sampler_qs :
  hoare[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs /\
    sampler_expand_query arg.`1 \in sampler_qs ==>
    sampler_rom_covered HAETAE_RO.FRO.m hash_qs sampler_qs].
proof.
proc.
wp.
rnd.
wp.
call (concrete_lazy_rom_get_preserves_sampler_rom_covered_arg
        hash_qs sampler_qs).
by auto => />; smt.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_preserves_sampler_rom_covered_budgeted_logs :
  hoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries /\
    sampler_expand_query arg.`1 \in
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries ==>
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries].
proof.
proc.
wp.
call concrete_lazy_rom_get_preserves_sampler_rom_covered_budgeted_logs.
by auto => />; smt.
qed.

lemma concrete_ro_exact_hyperball_sample_with_seed_preserves_sampler_rom_covered_budgeted_logs :
  hoare[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries /\
    sampler_expand_query arg.`1 \in
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries ==>
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries].
proof.
proc.
wp.
rnd.
wp.
call concrete_lazy_rom_get_preserves_sampler_rom_covered_budgeted_logs.
by auto => />; smt.
qed.

lemma concrete_budgeted_ro_signing_attempt_o_sign_preserves_sampler_rom_covered :
  hoare[ROMInternalTranscriptBudgetedPaperSimAsNMA
          (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
           HAETAE_RO.FRO).O.sign :
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries ==>
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries].
proof.
proc.
if.
+ wp.
  call concrete_lazy_rom_get_preserves_sampler_rom_covered_budgeted_logs.
  wp.
  call concrete_lazy_rom_get_preserves_sampler_rom_covered_budgeted_logs.
  wp.
  call concrete_ro_signing_attempt_sample_with_seed_preserves_sampler_rom_covered_budgeted_logs.
  wp.
  rnd.
  by auto => />; smt.
by auto.
qed.

lemma concrete_budgeted_ro_exact_hyperball_o_sign_preserves_sampler_rom_covered :
  hoare[ROMInternalTranscriptBudgetedPaperSimAsNMA
          (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
           HAETAE_RO.FRO).O.sign :
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries ==>
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries].
proof.
proc.
if.
+ wp.
  call concrete_lazy_rom_get_preserves_sampler_rom_covered_budgeted_logs.
  wp.
  call concrete_lazy_rom_get_preserves_sampler_rom_covered_budgeted_logs.
  wp.
  call concrete_ro_exact_hyperball_sample_with_seed_preserves_sampler_rom_covered_budgeted_logs.
  wp.
  rnd.
  by auto => />; smt.
by auto.
qed.

lemma concrete_budgeted_ro_signing_attempt_o_sign_clean_sampler_fresh :
  hoare[ROMInternalTranscriptBudgetedPaperSimAsNMA
          (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
           HAETAE_RO.FRO).O.sign :
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries /\
    ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery ==>
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries].
proof.
conseq concrete_budgeted_ro_signing_attempt_o_sign_preserves_sampler_rom_covered
  => />.
qed.

end section ROMInternalTranscriptBudgetedPaperSimNMAQueryBudget.

module EUF_CMA_ROMInternalTranscriptCountedSign(
  H : Oracle,
  A : SIG.Adversary
) = {
  module C = CountedLazyROM(H)

  var pk_current : pkey
  var sk_current : skey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var seed_coins : random_coins;
      var coins : random_coins;
      var pk : pkey;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;

      seed_coins <$ drandom_coins;
      ro_y <@ C.get(sampler_expand_query seed_coins);
      coins <- ro_signing_coins ro_y;
      pk <- public_key_of_secret haetae_mode sk_current;
      ro_y <@ C.get(message_hash_query pk ctx m);
      mu <- ro_message_hash ro_y;
      highbits <- commitment_highbits haetae_mode sk_current m ctx coins;
      lowbits <- commitment_lowbits haetae_mode sk_current m ctx coins;
      ro_y <@ C.get(challenge_hash_query haetae_mode highbits lowbits mu);
      sig <- sign_internal haetae_mode sk_current m ctx coins;
      tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
      C.observe_transcript(haetae_mode, tr);
      queries <- (m, ctx) :: queries;
      transcripts <- tr :: transcripts;
      records <- (m, ctx, sig, tr) :: records;
      return sig;
    }
  }

  module A = A(C, O)

  proc main() : bool = {
    var sd : seed;
    var rhoprime : seed;
    var ro_y : ro_output;
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var bad : bool;

    C.init();
    queries <- [];
    transcripts <- [];
    records <- [];
    sd <$ dseed;
    rhoprime <- haetae_keygen_rhoprime sd;
    ro_y <@ C.get(matrix_expand_query haetae_mode rhoprime);
    (pk, sk) <- keygen_internal haetae_mode rhoprime;
    pk_current <- pk;
    sk_current <- sk;
    (m, ctx, sig) <@ A.forge(pk);
    bad <@ C.bad();
    return bad;
  }
}.

module EUF_CMA_ROMProgrammedTranscriptCountedSign(
  H : Oracle,
  A : SIG.Adversary
) = {
  module C = CountedLazyROM(H)

  var pk_current : pkey
  var sk_current : skey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var seed_coins : random_coins;
      var coins : random_coins;
      var pk : pkey;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;
      var site : programming_site;

      seed_coins <$ drandom_coins;
      ro_y <@ C.get(sampler_expand_query seed_coins);
      coins <- ro_signing_coins ro_y;
      pk <- public_key_of_secret haetae_mode sk_current;
      ro_y <@ C.get(message_hash_query pk ctx m);
      mu <- ro_message_hash ro_y;
      highbits <- commitment_highbits haetae_mode sk_current m ctx coins;
      lowbits <- commitment_lowbits haetae_mode sk_current m ctx coins;
      sig <- sign_internal haetae_mode sk_current m ctx coins;
      tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
      site <- actual_signature_programming_site haetae_mode tr;
      C.observe_transcript(haetae_mode, tr);
      C.program(site);
      queries <- (m, ctx) :: queries;
      transcripts <- tr :: transcripts;
      records <- (m, ctx, sig, tr) :: records;
      return sig;
    }
  }

  module A = A(C, O)

  proc main() : bool = {
    var sd : seed;
    var rhoprime : seed;
    var ro_y : ro_output;
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var bad : bool;

    C.init();
    queries <- [];
    transcripts <- [];
    records <- [];
    sd <$ dseed;
    rhoprime <- haetae_keygen_rhoprime sd;
    ro_y <@ C.get(matrix_expand_query haetae_mode rhoprime);
    (pk, sk) <- keygen_internal haetae_mode rhoprime;
    pk_current <- pk;
    sk_current <- sk;
    (m, ctx, sig) <@ A.forge(pk);
    bad <@ C.bad();
    return bad;
  }
}.

module EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(
  H : Oracle,
  A : SIG.Adversary
) = {
  module C = CountedLazyROM(H)

  var pk_current : pkey
  var sk_current : skey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list
  var adversary_hash_count : int
  var signing_count : int

  module AH = {
    proc get(q : ro_query) : ro_output = {
      var y : ro_output;

       if (adversary_hash_count < hash_query_budget_count) {
         if (adversary_hash_count = 0) {
           adversary_hash_count <- 1;
         } else {
           adversary_hash_count <- hash_query_budget_count;
         }
         y <@ C.get(q);
       } else {
         adversary_hash_count <- hash_query_budget_count;
         y <- ro_output_zero;
       }
      return y;
    }
  }

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var coins : random_coins;
      var pk : pkey;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;
      var site : programming_site;

       if (signing_count < signature_query_budget_count) {
         if (signing_count = 0) {
           signing_count <- 1;
         } else {
           signing_count <- signature_query_budget_count;
         }
        coins <@ DirectSigningCoinSampler.sample();
        pk <- public_key_of_secret haetae_mode sk_current;
        ro_y <@ C.get(message_hash_query pk ctx m);
        mu <- ro_message_hash ro_y;
        highbits <- commitment_highbits haetae_mode sk_current m ctx coins;
        lowbits <- commitment_lowbits haetae_mode sk_current m ctx coins;
        sig <- sign_internal haetae_mode sk_current m ctx coins;
        tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
        site <- actual_signature_programming_site haetae_mode tr;
        C.observe_transcript(haetae_mode, tr);
        C.program(site);
        queries <- (m, ctx) :: queries;
        transcripts <- tr :: transcripts;
         records <- (m, ctx, sig, tr) :: records;
       } else {
         signing_count <- signature_query_budget_count;
         sig <- sign_internal haetae_mode sk_current m ctx ro_random_coins_zero;
       }
      return sig;
    }
  }

  module A = A(AH, O)

  proc main() : bool = {
    var sd : seed;
    var rhoprime : seed;
    var ro_y : ro_output;
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var bad : bool;

    C.init();
    queries <- [];
    transcripts <- [];
    records <- [];
    adversary_hash_count <- 0;
    signing_count <- 0;
    sd <$ dseed;
    rhoprime <- haetae_keygen_rhoprime sd;
    ro_y <@ C.get(matrix_expand_query haetae_mode rhoprime);
    (pk, sk) <- keygen_internal haetae_mode rhoprime;
    pk_current <- pk;
    sk_current <- sk;
    (m, ctx, sig) <@ A.forge(pk);
    bad <@ C.bad();
    return bad;
  }
}.

module EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign(
  H : Oracle,
  A : SIG.Adversary,
  Samp : SigningCoinSampler
) = {
  module C = CountedLazyROM(H)

  var pk_current : pkey
  var sk_current : skey
  var queries : SIG.query list
  var transcripts : transcript list
  var records : signing_transcript_record list
  var adversary_hash_count : int
  var signing_count : int

  module AH = {
    proc get(q : ro_query) : ro_output = {
      var y : ro_output;

       if (adversary_hash_count < hash_query_budget_count) {
         if (adversary_hash_count = 0) {
           adversary_hash_count <- 1;
         } else {
           adversary_hash_count <- hash_query_budget_count;
         }
         y <@ C.get(q);
       } else {
         adversary_hash_count <- hash_query_budget_count;
         y <- ro_output_zero;
       }
      return y;
    }
  }

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var coins : random_coins;
      var pk : pkey;
      var highbits : polyveck;
      var lowbits : poly;
      var mu : crh;
      var ro_y : ro_output;
      var sig : signature;
      var tr : transcript;
      var site : programming_site;

       if (signing_count < signature_query_budget_count) {
         if (signing_count = 0) {
           signing_count <- 1;
         } else {
           signing_count <- signature_query_budget_count;
         }
        coins <@ Samp.sample();
        pk <- public_key_of_secret haetae_mode sk_current;
        ro_y <@ C.get(message_hash_query pk ctx m);
        mu <- ro_message_hash ro_y;
        highbits <- commitment_highbits haetae_mode sk_current m ctx coins;
        lowbits <- commitment_lowbits haetae_mode sk_current m ctx coins;
        sig <- sign_internal haetae_mode sk_current m ctx coins;
        tr <- transcript_of_signature haetae_mode pk_current m ctx sig;
        site <- actual_signature_programming_site haetae_mode tr;
        C.observe_transcript(haetae_mode, tr);
        C.program(site);
        queries <- (m, ctx) :: queries;
        transcripts <- tr :: transcripts;
         records <- (m, ctx, sig, tr) :: records;
       } else {
         signing_count <- signature_query_budget_count;
         sig <- sign_internal haetae_mode sk_current m ctx ro_random_coins_zero;
       }
      return sig;
    }
  }

  module A = A(AH, O)

  proc main() : bool = {
    var sd : seed;
    var rhoprime : seed;
    var ro_y : ro_output;
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var bad : bool;

    C.init();
    queries <- [];
    transcripts <- [];
    records <- [];
    adversary_hash_count <- 0;
    signing_count <- 0;
    sd <$ dseed;
    rhoprime <- haetae_keygen_rhoprime sd;
    ro_y <@ C.get(matrix_expand_query haetae_mode rhoprime);
    (pk, sk) <- keygen_internal haetae_mode rhoprime;
    pk_current <- pk;
    sk_current <- sk;
    (m, ctx, sig) <@ A.forge(pk);
    bad <@ C.bad();
    return bad;
  }
}.

section InternalTranscriptSignSound.

declare module H <: SIG.Oracle {-EUF_CMA_InternalTranscriptSign,
                                -EUF_CMA_ROMInternalTranscriptSign}.
declare module A <: SIG.Adversary {-H, -EUF_CMA_InternalTranscriptSign,
                                   -EUF_CMA_ROMInternalTranscriptSign}.

lemma internal_transcript_sign_oracle_preserves_state :
  hoare[EUF_CMA_InternalTranscriptSign(H, A).O.sign :
    internal_transcript_state_sound haetae_mode
      EUF_CMA_InternalTranscriptSign.pk_current
      EUF_CMA_InternalTranscriptSign.sk_current
      EUF_CMA_InternalTranscriptSign.queries
      EUF_CMA_InternalTranscriptSign.transcripts
      EUF_CMA_InternalTranscriptSign.records ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_InternalTranscriptSign.pk_current
      EUF_CMA_InternalTranscriptSign.sk_current
      EUF_CMA_InternalTranscriptSign.queries
      EUF_CMA_InternalTranscriptSign.transcripts
      EUF_CMA_InternalTranscriptSign.records].
proof.
proc.
wp.
rnd.
skip.
move=> &hr state_sound coins _.
by apply (internal_transcript_state_sound_sign_internal_cons
            haetae_mode
            EUF_CMA_InternalTranscriptSign.pk_current{hr}
            EUF_CMA_InternalTranscriptSign.sk_current{hr}
            EUF_CMA_InternalTranscriptSign.queries{hr}
            EUF_CMA_InternalTranscriptSign.transcripts{hr}
            EUF_CMA_InternalTranscriptSign.records{hr}
            m{hr} ctx{hr} coins).
qed.

lemma adversary_internal_transcript_state_preserved :
  hoare[A(H, EUF_CMA_InternalTranscriptSign(H, A).O).forge :
    internal_transcript_state_sound haetae_mode
      EUF_CMA_InternalTranscriptSign.pk_current
      EUF_CMA_InternalTranscriptSign.sk_current
      EUF_CMA_InternalTranscriptSign.queries
      EUF_CMA_InternalTranscriptSign.transcripts
      EUF_CMA_InternalTranscriptSign.records ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_InternalTranscriptSign.pk_current
      EUF_CMA_InternalTranscriptSign.sk_current
      EUF_CMA_InternalTranscriptSign.queries
      EUF_CMA_InternalTranscriptSign.transcripts
      EUF_CMA_InternalTranscriptSign.records].
proof.
proc (internal_transcript_state_sound haetae_mode
        EUF_CMA_InternalTranscriptSign.pk_current
        EUF_CMA_InternalTranscriptSign.sk_current
        EUF_CMA_InternalTranscriptSign.queries
        EUF_CMA_InternalTranscriptSign.transcripts
        EUF_CMA_InternalTranscriptSign.records) => //.
+ move=> />.
+ proc*.
  call (_: true).
  by auto.
+ by apply internal_transcript_sign_oracle_preserves_state.
qed.

lemma internal_transcript_sign_main_state_sound :
  hoare[EUF_CMA_InternalTranscriptSign(H, A).main :
    true ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_InternalTranscriptSign.pk_current
      EUF_CMA_InternalTranscriptSign.sk_current
      EUF_CMA_InternalTranscriptSign.queries
      EUF_CMA_InternalTranscriptSign.transcripts
      EUF_CMA_InternalTranscriptSign.records].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_InternalTranscriptSign.pk_current
          EUF_CMA_InternalTranscriptSign.sk_current
          EUF_CMA_InternalTranscriptSign.queries
          EUF_CMA_InternalTranscriptSign.transcripts
          EUF_CMA_InternalTranscriptSign.records ==>
        internal_transcript_state_sound haetae_mode
          EUF_CMA_InternalTranscriptSign.pk_current
          EUF_CMA_InternalTranscriptSign.sk_current
          EUF_CMA_InternalTranscriptSign.queries
          EUF_CMA_InternalTranscriptSign.transcripts
          EUF_CMA_InternalTranscriptSign.records).
+ by apply adversary_internal_transcript_state_preserved.
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma internal_transcript_sign_main_transcripts_valid :
  hoare[EUF_CMA_InternalTranscriptSign(H, A).main :
    true ==>
    transcript_log_valid haetae_mode
      EUF_CMA_InternalTranscriptSign.transcripts].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_InternalTranscriptSign.pk_current
          EUF_CMA_InternalTranscriptSign.sk_current
          EUF_CMA_InternalTranscriptSign.queries
          EUF_CMA_InternalTranscriptSign.transcripts
          EUF_CMA_InternalTranscriptSign.records ==>
        transcript_log_valid haetae_mode
          EUF_CMA_InternalTranscriptSign.transcripts).
+ conseq (_: internal_transcript_state_sound haetae_mode
              EUF_CMA_InternalTranscriptSign.pk_current
              EUF_CMA_InternalTranscriptSign.sk_current
              EUF_CMA_InternalTranscriptSign.queries
              EUF_CMA_InternalTranscriptSign.transcripts
              EUF_CMA_InternalTranscriptSign.records ==>
            internal_transcript_state_sound haetae_mode
              EUF_CMA_InternalTranscriptSign.pk_current
              EUF_CMA_InternalTranscriptSign.sk_current
              EUF_CMA_InternalTranscriptSign.queries
              EUF_CMA_InternalTranscriptSign.transcripts
              EUF_CMA_InternalTranscriptSign.records).
  + move=> &hr _ qs0 rs0 trs0 state_sound.
    by apply (internal_transcript_state_sound_valid
                haetae_mode
                EUF_CMA_InternalTranscriptSign.pk_current{hr}
                EUF_CMA_InternalTranscriptSign.sk_current{hr}
                qs0 trs0 rs0).
  by apply adversary_internal_transcript_state_preserved.
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma internal_transcript_sign_main_log_ready :
  hoare[EUF_CMA_InternalTranscriptSign(H, A).main :
    true ==>
    transcript_log_ready haetae_mode
      EUF_CMA_InternalTranscriptSign.transcripts].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_InternalTranscriptSign.pk_current
          EUF_CMA_InternalTranscriptSign.sk_current
          EUF_CMA_InternalTranscriptSign.queries
          EUF_CMA_InternalTranscriptSign.transcripts
          EUF_CMA_InternalTranscriptSign.records ==>
        transcript_log_ready haetae_mode
          EUF_CMA_InternalTranscriptSign.transcripts).
+ conseq (_: internal_transcript_state_sound haetae_mode
              EUF_CMA_InternalTranscriptSign.pk_current
              EUF_CMA_InternalTranscriptSign.sk_current
              EUF_CMA_InternalTranscriptSign.queries
              EUF_CMA_InternalTranscriptSign.transcripts
              EUF_CMA_InternalTranscriptSign.records ==>
            internal_transcript_state_sound haetae_mode
              EUF_CMA_InternalTranscriptSign.pk_current
              EUF_CMA_InternalTranscriptSign.sk_current
              EUF_CMA_InternalTranscriptSign.queries
              EUF_CMA_InternalTranscriptSign.transcripts
              EUF_CMA_InternalTranscriptSign.records).
  + move=> &hr _ qs0 rs0 trs0 state_sound.
    by apply (internal_transcript_state_sound_log_ready
                haetae_mode
                EUF_CMA_InternalTranscriptSign.pk_current{hr}
                EUF_CMA_InternalTranscriptSign.sk_current{hr}
                qs0 trs0 rs0).
  by apply adversary_internal_transcript_state_preserved.
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma internal_transcript_sign_main_no_min_entropy :
  hoare[EUF_CMA_InternalTranscriptSign(H, A).main :
    true ==>
    transcript_log_min_entropy_clear haetae_mode
      EUF_CMA_InternalTranscriptSign.transcripts].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_InternalTranscriptSign.pk_current
          EUF_CMA_InternalTranscriptSign.sk_current
          EUF_CMA_InternalTranscriptSign.queries
          EUF_CMA_InternalTranscriptSign.transcripts
          EUF_CMA_InternalTranscriptSign.records ==>
        transcript_log_min_entropy_clear haetae_mode
          EUF_CMA_InternalTranscriptSign.transcripts).
+ conseq (_: internal_transcript_state_sound haetae_mode
              EUF_CMA_InternalTranscriptSign.pk_current
              EUF_CMA_InternalTranscriptSign.sk_current
              EUF_CMA_InternalTranscriptSign.queries
              EUF_CMA_InternalTranscriptSign.transcripts
              EUF_CMA_InternalTranscriptSign.records ==>
            internal_transcript_state_sound haetae_mode
              EUF_CMA_InternalTranscriptSign.pk_current
              EUF_CMA_InternalTranscriptSign.sk_current
              EUF_CMA_InternalTranscriptSign.queries
              EUF_CMA_InternalTranscriptSign.transcripts
              EUF_CMA_InternalTranscriptSign.records).
  + move=> &hr _ qs0 rs0 trs0 state_sound.
    by apply (internal_transcript_state_sound_no_min_entropy
                haetae_mode
                EUF_CMA_InternalTranscriptSign.pk_current{hr}
                EUF_CMA_InternalTranscriptSign.sk_current{hr}
                qs0 trs0 rs0).
  by apply adversary_internal_transcript_state_preserved.
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma rom_internal_transcript_sign_oracle_preserves_state :
  hoare[EUF_CMA_ROMInternalTranscriptSign(H, A).O.sign :
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.pk_current
      EUF_CMA_ROMInternalTranscriptSign.sk_current
      EUF_CMA_ROMInternalTranscriptSign.queries
      EUF_CMA_ROMInternalTranscriptSign.transcripts
      EUF_CMA_ROMInternalTranscriptSign.records ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.pk_current
      EUF_CMA_ROMInternalTranscriptSign.sk_current
      EUF_CMA_ROMInternalTranscriptSign.queries
      EUF_CMA_ROMInternalTranscriptSign.transcripts
      EUF_CMA_ROMInternalTranscriptSign.records].
proof.
proc.
wp.
call (_: true).
wp.
call (_: true).
wp.
call (_: true).
wp.
rnd.
skip.
move=> &hr state_sound seed_coins _ result.
by apply (internal_transcript_state_sound_sign_internal_cons
            haetae_mode
            EUF_CMA_ROMInternalTranscriptSign.pk_current{hr}
            EUF_CMA_ROMInternalTranscriptSign.sk_current{hr}
            EUF_CMA_ROMInternalTranscriptSign.queries{hr}
            EUF_CMA_ROMInternalTranscriptSign.transcripts{hr}
            EUF_CMA_ROMInternalTranscriptSign.records{hr}
            m{hr} ctx{hr} (ro_signing_coins result)).
qed.

lemma adversary_rom_internal_transcript_state_preserved :
  hoare[A(H, EUF_CMA_ROMInternalTranscriptSign(H, A).O).forge :
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.pk_current
      EUF_CMA_ROMInternalTranscriptSign.sk_current
      EUF_CMA_ROMInternalTranscriptSign.queries
      EUF_CMA_ROMInternalTranscriptSign.transcripts
      EUF_CMA_ROMInternalTranscriptSign.records ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.pk_current
      EUF_CMA_ROMInternalTranscriptSign.sk_current
      EUF_CMA_ROMInternalTranscriptSign.queries
      EUF_CMA_ROMInternalTranscriptSign.transcripts
      EUF_CMA_ROMInternalTranscriptSign.records].
proof.
proc (internal_transcript_state_sound haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.pk_current
        EUF_CMA_ROMInternalTranscriptSign.sk_current
        EUF_CMA_ROMInternalTranscriptSign.queries
        EUF_CMA_ROMInternalTranscriptSign.transcripts
        EUF_CMA_ROMInternalTranscriptSign.records) => //.
+ move=> />.
+ proc*.
  call (_: true).
  by auto.
+ by apply rom_internal_transcript_sign_oracle_preserves_state.
qed.

lemma rom_internal_transcript_sign_main_state_sound :
  hoare[EUF_CMA_ROMInternalTranscriptSign(H, A).main :
    true ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.pk_current
      EUF_CMA_ROMInternalTranscriptSign.sk_current
      EUF_CMA_ROMInternalTranscriptSign.queries
      EUF_CMA_ROMInternalTranscriptSign.transcripts
      EUF_CMA_ROMInternalTranscriptSign.records].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.pk_current
          EUF_CMA_ROMInternalTranscriptSign.sk_current
          EUF_CMA_ROMInternalTranscriptSign.queries
          EUF_CMA_ROMInternalTranscriptSign.transcripts
          EUF_CMA_ROMInternalTranscriptSign.records ==>
        internal_transcript_state_sound haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.pk_current
          EUF_CMA_ROMInternalTranscriptSign.sk_current
          EUF_CMA_ROMInternalTranscriptSign.queries
          EUF_CMA_ROMInternalTranscriptSign.transcripts
          EUF_CMA_ROMInternalTranscriptSign.records).
+ by apply adversary_rom_internal_transcript_state_preserved.
wp.
call (_: true).
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma rom_internal_transcript_sign_main_transcripts_valid :
  hoare[EUF_CMA_ROMInternalTranscriptSign(H, A).main :
    true ==>
    transcript_log_valid haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.transcripts].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.pk_current
          EUF_CMA_ROMInternalTranscriptSign.sk_current
          EUF_CMA_ROMInternalTranscriptSign.queries
          EUF_CMA_ROMInternalTranscriptSign.transcripts
          EUF_CMA_ROMInternalTranscriptSign.records ==>
        transcript_log_valid haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.transcripts).
+ conseq (_: internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records ==>
            internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records).
  + move=> &hr _ qs0 rs0 trs0 state_sound.
    by apply (internal_transcript_state_sound_valid
                haetae_mode
                EUF_CMA_ROMInternalTranscriptSign.pk_current{hr}
                EUF_CMA_ROMInternalTranscriptSign.sk_current{hr}
                qs0 trs0 rs0).
  by apply adversary_rom_internal_transcript_state_preserved.
wp.
call (_: true).
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma rom_internal_transcript_sign_main_log_ready :
  hoare[EUF_CMA_ROMInternalTranscriptSign(H, A).main :
    true ==>
    transcript_log_ready haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.transcripts].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.pk_current
          EUF_CMA_ROMInternalTranscriptSign.sk_current
          EUF_CMA_ROMInternalTranscriptSign.queries
          EUF_CMA_ROMInternalTranscriptSign.transcripts
          EUF_CMA_ROMInternalTranscriptSign.records ==>
        transcript_log_ready haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.transcripts).
+ conseq (_: internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records ==>
            internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records).
  + move=> &hr _ qs0 rs0 trs0 state_sound.
    by apply (internal_transcript_state_sound_log_ready
                haetae_mode
                EUF_CMA_ROMInternalTranscriptSign.pk_current{hr}
                EUF_CMA_ROMInternalTranscriptSign.sk_current{hr}
                qs0 trs0 rs0).
  by apply adversary_rom_internal_transcript_state_preserved.
wp.
call (_: true).
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma rom_internal_transcript_sign_main_no_min_entropy :
  hoare[EUF_CMA_ROMInternalTranscriptSign(H, A).main :
    true ==>
    transcript_log_min_entropy_clear haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.transcripts].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.pk_current
          EUF_CMA_ROMInternalTranscriptSign.sk_current
          EUF_CMA_ROMInternalTranscriptSign.queries
          EUF_CMA_ROMInternalTranscriptSign.transcripts
          EUF_CMA_ROMInternalTranscriptSign.records ==>
        transcript_log_min_entropy_clear haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.transcripts).
+ conseq (_: internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records ==>
            internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records).
  + move=> &hr _ qs0 rs0 trs0 state_sound.
    by apply (internal_transcript_state_sound_no_min_entropy
                haetae_mode
                EUF_CMA_ROMInternalTranscriptSign.pk_current{hr}
                EUF_CMA_ROMInternalTranscriptSign.sk_current{hr}
                qs0 trs0 rs0).
  by apply adversary_rom_internal_transcript_state_preserved.
wp.
call (_: true).
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma rom_internal_transcript_sign_main_no_failure_for_signature_site :
  hoare[EUF_CMA_ROMInternalTranscriptSign(H, A).main :
    true ==>
    forall tr y,
      tr \in EUF_CMA_ROMInternalTranscriptSign.transcripts =>
      transcript_signature_challenge_matches tr y =>
      ! fs_with_aborts_failure haetae_mode tr
          (signature_programming_site_of_transcript haetae_mode tr y)].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.pk_current
          EUF_CMA_ROMInternalTranscriptSign.sk_current
          EUF_CMA_ROMInternalTranscriptSign.queries
          EUF_CMA_ROMInternalTranscriptSign.transcripts
          EUF_CMA_ROMInternalTranscriptSign.records ==>
        forall tr y,
          tr \in EUF_CMA_ROMInternalTranscriptSign.transcripts =>
          transcript_signature_challenge_matches tr y =>
          ! fs_with_aborts_failure haetae_mode tr
              (signature_programming_site_of_transcript haetae_mode tr y)).
+ conseq (_: internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records ==>
            internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records).
  + move=> &hr _ qs0 rs0 trs0 state_sound tr y mem_tr match_y.
    have ready :=
      internal_transcript_state_sound_log_ready
        haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.pk_current{hr}
        EUF_CMA_ROMInternalTranscriptSign.sk_current{hr}
        qs0 trs0 rs0 state_sound.
    by apply (transcript_log_ready_no_failure_for_signature_programming_site
                haetae_mode trs0 tr y ready mem_tr match_y).
  by apply adversary_rom_internal_transcript_state_preserved.
wp.
call (_: true).
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma rom_internal_transcript_sign_main_signature_sites_clear :
  hoare[EUF_CMA_ROMInternalTranscriptSign(H, A).main :
    true ==>
    transcript_log_signature_programming_sites_clear haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.transcripts].
proof.
proc.
wp.
call (_: internal_transcript_state_sound haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.pk_current
          EUF_CMA_ROMInternalTranscriptSign.sk_current
          EUF_CMA_ROMInternalTranscriptSign.queries
          EUF_CMA_ROMInternalTranscriptSign.transcripts
          EUF_CMA_ROMInternalTranscriptSign.records ==>
        transcript_log_signature_programming_sites_clear haetae_mode
          EUF_CMA_ROMInternalTranscriptSign.transcripts).
+ conseq (_: internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records ==>
            internal_transcript_state_sound haetae_mode
              EUF_CMA_ROMInternalTranscriptSign.pk_current
              EUF_CMA_ROMInternalTranscriptSign.sk_current
              EUF_CMA_ROMInternalTranscriptSign.queries
              EUF_CMA_ROMInternalTranscriptSign.transcripts
              EUF_CMA_ROMInternalTranscriptSign.records).
  + move=> &hr _ qs0 rs0 trs0 state_sound.
    have ready :=
      internal_transcript_state_sound_log_ready
        haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.pk_current{hr}
        EUF_CMA_ROMInternalTranscriptSign.sk_current{hr}
        qs0 trs0 rs0 state_sound.
    by apply (transcript_log_ready_signature_sites_clear haetae_mode trs0 ready).
  by apply adversary_rom_internal_transcript_state_preserved.
wp.
call (_: true).
wp.
rnd.
wp.
call (_: true).
by auto => />.
qed.

lemma rom_internal_transcript_bad_forgery_zero &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
    res /\ ! transcript_log_signature_programming_sites_clear haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.transcripts] = 0%r.
proof.
byphoare (_: true ==>
  res /\ ! transcript_log_signature_programming_sites_clear haetae_mode
    EUF_CMA_ROMInternalTranscriptSign.transcripts) => //.
hoare.
conseq (_: true ==>
  transcript_log_signature_programming_sites_clear haetae_mode
    EUF_CMA_ROMInternalTranscriptSign.transcripts).
+ move=> &hr _ forge trs0 clear_sites.
  by rewrite clear_sites.
by apply rom_internal_transcript_sign_main_signature_sites_clear.
qed.

lemma rom_internal_transcript_bad_forgery_bound &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
    res /\ ! transcript_log_signature_programming_sites_clear haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.transcripts] <=
    fs_with_aborts_reprogramming_term + fs_with_aborts_min_entropy_term.
proof.
rewrite (rom_internal_transcript_bad_forgery_zero &m).
have ge_reprogram := fs_with_aborts_reprogramming_term_nonnegative.
have ge_entropy := fs_with_aborts_min_entropy_term_nonnegative.
have ge_sum :
  0%r + 0%r <=
    fs_with_aborts_reprogramming_term + fs_with_aborts_min_entropy_term
  by apply ler_add.
by apply ge_sum.
qed.

lemma rom_internal_transcript_bad_forgery_counted_bound &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
    res /\ ! transcript_log_signature_programming_sites_clear haetae_mode
      EUF_CMA_ROMInternalTranscriptSign.transcripts] <=
    counted_rom_programming_loss_term.
proof.
rewrite (rom_internal_transcript_bad_forgery_zero &m).
by apply counted_rom_programming_loss_term_nonnegative.
qed.

end section InternalTranscriptSignSound.

section CountedROMInternalTranscriptDiscipline.

declare module H <: Oracle {-CountedLazyROM,
                             -EUF_CMA_ROMInternalTranscriptCountedSign}.
declare module A <: SIG.Adversary {-H, -CountedLazyROM,
                                   -EUF_CMA_ROMInternalTranscriptCountedSign}.

lemma counted_rom_internal_transcript_sign_oracle_preserves_budget_state :
  hoare[EUF_CMA_ROMInternalTranscriptCountedSign(H, A).O.sign :
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptCountedSign.pk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.sk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.queries
      EUF_CMA_ROMInternalTranscriptCountedSign.transcripts
      EUF_CMA_ROMInternalTranscriptCountedSign.records /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_prequery /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_reprogram /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_min_entropy /\
    EUF_CMA_ROMInternalTranscriptCountedSign.C.programmed_sites = [] ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptCountedSign.pk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.sk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.queries
      EUF_CMA_ROMInternalTranscriptCountedSign.transcripts
      EUF_CMA_ROMInternalTranscriptCountedSign.records /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_prequery /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_reprogram /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_min_entropy /\
    EUF_CMA_ROMInternalTranscriptCountedSign.C.programmed_sites = []].
proof.
proc.
inline EUF_CMA_ROMInternalTranscriptCountedSign(H, A).C.observe_transcript.
inline EUF_CMA_ROMInternalTranscriptCountedSign(H, A).C.get.
wp.
call (_: true).
wp.
call (_: true).
wp.
call (_: true).
wp.
rnd.
skip.
move=> &hr [state_sound [preq_ok [reprog_ok [entropy_ok programmed_ok]]]]
        seed_coins _ result.
have pkE :
  EUF_CMA_ROMInternalTranscriptCountedSign.pk_current{hr} =
  public_key_of_secret haetae_mode
    EUF_CMA_ROMInternalTranscriptCountedSign.sk_current{hr}
  by case: state_sound.
have no_min :
  ! min_entropy_failure haetae_mode
      (transcript_of_signature haetae_mode
        EUF_CMA_ROMInternalTranscriptCountedSign.pk_current{hr}
        m{hr} ctx{hr}
        (sign_internal haetae_mode
          EUF_CMA_ROMInternalTranscriptCountedSign.sk_current{hr}
          m{hr} ctx{hr} (ro_signing_coins result))).
+ by apply (sign_internal_transcript_no_min_entropy haetae_mode
              EUF_CMA_ROMInternalTranscriptCountedSign.pk_current{hr}
              EUF_CMA_ROMInternalTranscriptCountedSign.sk_current{hr}
              m{hr} ctx{hr} (ro_signing_coins result)).
split.
+ by apply (internal_transcript_state_sound_sign_internal_cons
            haetae_mode
            EUF_CMA_ROMInternalTranscriptCountedSign.pk_current{hr}
            EUF_CMA_ROMInternalTranscriptCountedSign.sk_current{hr}
            EUF_CMA_ROMInternalTranscriptCountedSign.queries{hr}
            EUF_CMA_ROMInternalTranscriptCountedSign.transcripts{hr}
            EUF_CMA_ROMInternalTranscriptCountedSign.records{hr}
            m{hr} ctx{hr} (ro_signing_coins result)).
split=> //.
split=> //.
split.
+ by rewrite entropy_ok no_min.
by apply programmed_ok.
qed.

lemma adversary_counted_rom_internal_transcript_budget_state_preserved :
  hoare[A(EUF_CMA_ROMInternalTranscriptCountedSign(H, A).C,
          EUF_CMA_ROMInternalTranscriptCountedSign(H, A).O).forge :
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptCountedSign.pk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.sk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.queries
      EUF_CMA_ROMInternalTranscriptCountedSign.transcripts
      EUF_CMA_ROMInternalTranscriptCountedSign.records /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_prequery /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_reprogram /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_min_entropy /\
    EUF_CMA_ROMInternalTranscriptCountedSign.C.programmed_sites = [] ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptCountedSign.pk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.sk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.queries
      EUF_CMA_ROMInternalTranscriptCountedSign.transcripts
      EUF_CMA_ROMInternalTranscriptCountedSign.records /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_prequery /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_reprogram /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_min_entropy /\
    EUF_CMA_ROMInternalTranscriptCountedSign.C.programmed_sites = []].
proof.
proc (internal_transcript_state_sound haetae_mode
        EUF_CMA_ROMInternalTranscriptCountedSign.pk_current
        EUF_CMA_ROMInternalTranscriptCountedSign.sk_current
        EUF_CMA_ROMInternalTranscriptCountedSign.queries
        EUF_CMA_ROMInternalTranscriptCountedSign.transcripts
        EUF_CMA_ROMInternalTranscriptCountedSign.records /\
      ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_prequery /\
      ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_reprogram /\
      ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_min_entropy /\
      EUF_CMA_ROMInternalTranscriptCountedSign.C.programmed_sites = []) => //.
+ move=> />.
+ proc*.
  call (counted_lazy_rom_get_preserves_clear H).
  by auto.
+ by apply counted_rom_internal_transcript_sign_oracle_preserves_budget_state.
qed.

lemma counted_rom_internal_transcript_main_bad_clear :
  hoare[EUF_CMA_ROMInternalTranscriptCountedSign(H, A).main :
    true ==> ! res].
proof.
proc.
wp.
call (counted_lazy_rom_bad_false_when_clear H).
wp.
call (_:
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptCountedSign.pk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.sk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.queries
      EUF_CMA_ROMInternalTranscriptCountedSign.transcripts
      EUF_CMA_ROMInternalTranscriptCountedSign.records /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_prequery /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_reprogram /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_min_entropy /\
    EUF_CMA_ROMInternalTranscriptCountedSign.C.programmed_sites = [] ==>
    internal_transcript_state_sound haetae_mode
      EUF_CMA_ROMInternalTranscriptCountedSign.pk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.sk_current
      EUF_CMA_ROMInternalTranscriptCountedSign.queries
      EUF_CMA_ROMInternalTranscriptCountedSign.transcripts
      EUF_CMA_ROMInternalTranscriptCountedSign.records /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_prequery /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_reprogram /\
    ! EUF_CMA_ROMInternalTranscriptCountedSign.C.bad_min_entropy /\
    EUF_CMA_ROMInternalTranscriptCountedSign.C.programmed_sites = []).
+ by apply adversary_counted_rom_internal_transcript_budget_state_preserved.
wp.
call (counted_lazy_rom_get_preserves_clear H).
wp.
rnd.
wp.
call (counted_lazy_rom_init_clears H).
by auto => /> sd; apply internal_transcript_state_sound_keygen.
qed.

lemma counted_rom_internal_transcript_main_bad_false :
  hoare[EUF_CMA_ROMInternalTranscriptCountedSign(H, A).main :
    true ==> res = false].
proof.
conseq counted_rom_internal_transcript_main_bad_clear => />.
qed.

lemma counted_rom_internal_transcript_counted_bad_zero &m :
  Pr[EUF_CMA_ROMInternalTranscriptCountedSign(H, A).main() @ &m :
    res] = 0%r.
proof.
byphoare (_: true ==> res) => //.
hoare.
conseq (_: true ==> res = false).
+ by move=> />.
by apply counted_rom_internal_transcript_main_bad_false.
qed.

lemma counted_rom_internal_transcript_budget_sound &m :
  counted_lazy_rom_bad_flags_budget_sound
    (Pr[EUF_CMA_ROMInternalTranscriptCountedSign(H, A).main() @ &m :
      res]).
proof.
rewrite /counted_lazy_rom_bad_flags_budget_sound
        (counted_rom_internal_transcript_counted_bad_zero &m).
by apply counted_rom_programming_loss_term_nonnegative.
qed.

lemma counted_rom_internal_transcript_counted_bad_subunit &m :
  Pr[EUF_CMA_ROMInternalTranscriptCountedSign(H, A).main() @ &m :
    res] < 1%r.
proof.
rewrite (counted_rom_internal_transcript_counted_bad_zero &m).
by trivial.
qed.

end section CountedROMInternalTranscriptDiscipline.

section ProgrammedROMTranscriptDiscipline.

declare module H <: Oracle {-CountedLazyROM,
                             -EUF_CMA_ROMProgrammedTranscriptCountedSign}.
declare module A <: SIG.Adversary {-H, -CountedLazyROM,
                                   -EUF_CMA_ROMProgrammedTranscriptCountedSign}.

lemma programmed_counted_sign_oracle_preserves_min_entropy_clear :
  hoare[EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).O.sign :
    EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current =
      public_key_of_secret haetae_mode
        EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current /\
    ! EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy ==>
    EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current =
      public_key_of_secret haetae_mode
        EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current /\
    ! EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy].
proof.
proc.
inline EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).C.program.
inline EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).C.observe_transcript.
inline EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).C.get.
wp.
call (_: true).
wp.
call (_: true).
wp.
call (_: true).
wp.
rnd.
skip.
move=> &hr [pkE entropy_ok] seed_coins _ result.
have no_min :
  ! min_entropy_failure haetae_mode
      (transcript_of_signature haetae_mode
        EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current{hr}
        m{hr} ctx{hr}
        (sign_internal haetae_mode
          EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current{hr}
          m{hr} ctx{hr} (ro_signing_coins result))).
+ by apply (sign_internal_transcript_no_min_entropy haetae_mode
              EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current{hr}
              EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current{hr}
  m{hr} ctx{hr} (ro_signing_coins result)).
by rewrite entropy_ok.
qed.

lemma adversary_programmed_counted_min_entropy_preserved :
  hoare[A(EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).C,
          EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).O).forge :
    EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current =
      public_key_of_secret haetae_mode
        EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current /\
    ! EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy ==>
    EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current =
      public_key_of_secret haetae_mode
        EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current /\
    ! EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy].
proof.
proc (EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current =
        public_key_of_secret haetae_mode
          EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current /\
      ! EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy) => //.
+ move=> />.
+ proc*.
  call (counted_lazy_rom_get_preserves_min_entropy_clear H).
  by auto.
+ by apply programmed_counted_sign_oracle_preserves_min_entropy_clear.
qed.

lemma programmed_counted_main_min_entropy_clear :
  hoare[EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).main :
    true ==>
    ! EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy].
proof.
proc.
wp.
call (counted_lazy_rom_bad_preserves_min_entropy_clear H).
wp.
call (_:
    EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current =
      public_key_of_secret haetae_mode
        EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current /\
    ! EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy ==>
    EUF_CMA_ROMProgrammedTranscriptCountedSign.pk_current =
      public_key_of_secret haetae_mode
        EUF_CMA_ROMProgrammedTranscriptCountedSign.sk_current /\
    ! EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy).
+ conseq adversary_programmed_counted_min_entropy_preserved => />.
wp.
call (counted_lazy_rom_get_preserves_min_entropy_clear H).
wp.
rnd.
wp.
call (counted_lazy_rom_init_clears H).
by auto => /> sd; apply public_key_of_keygen.
qed.

lemma programmed_counted_min_entropy_bad_zero &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy] = 0%r.
proof.
byphoare (_: true ==>
  EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy) => //.
hoare.
by conseq programmed_counted_main_min_entropy_clear.
qed.

lemma programmed_counted_min_entropy_bad_bound &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_min_entropy] <=
  counted_rom_min_entropy_term.
proof.
rewrite (programmed_counted_min_entropy_bad_zero &m).
by apply counted_rom_min_entropy_term_nonnegative.
qed.

lemma programmed_counted_prequery_reprogramming_bad_bound_from_budget_expr &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_reprogram] <=
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound =>
  Pr[EUF_CMA_ROMProgrammedTranscriptCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptCountedSign.C.bad_reprogram] <=
  counted_rom_prequery_reprogramming_term.
proof.
move=> h.
by rewrite counted_rom_prequery_reprogramming_term_cardinalityE.
qed.

end section ProgrammedROMTranscriptDiscipline.

section BudgetedProgrammedROMTranscriptDiscipline.

declare module H <: Oracle {-CountedLazyROM,
                             -DirectSigningCoinSampler,
                             -EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign}.
declare module A <: SIG.Adversary {-H, -CountedLazyROM,
                                   -DirectSigningCoinSampler,
                                   -EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign}.

lemma budgeted_counted_lazy_rom_get_true :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.get :
    true ==> true].
proof.
proc.
wp.
call (_: true).
by auto => />; rewrite /budgeted_programmed_challenge_query_discipline; smt.
qed.

lemma budgeted_counted_lazy_rom_init_true :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.init :
    true ==> true].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma budgeted_counted_lazy_rom_bad_true :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.bad :
    true ==> true].
proof.
by proc.
qed.

lemma budgeted_programmed_hash_get_preserves_challenge_query_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).AH.get :
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries].
  proof.
  proc.
  if.
  + inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.get.
  wp.
  call (_: true).
  by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
                        /hash_query_budget_count;
     smt(challenge_query_log_count_cons_le).
  by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
                    /hash_query_budget_count; smt.
qed.

lemma budgeted_programmed_sign_oracle_preserves_challenge_query_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).O.sign :
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries].
proof.
proc.
if.
+ inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.program.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.observe_transcript.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.get.
  inline DirectSigningCoinSampler.sample.
  wp.
  call (_: true).
  wp.
  call (_: true).
  wp.
  rnd.
  by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
                        challenge_query_log_count_message_cons; smt.
by auto => />; rewrite /budgeted_programmed_challenge_query_discipline; smt.
qed.

lemma adversary_budgeted_programmed_challenge_query_discipline_preserved :
  hoare[
    A(EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).AH,
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).O).forge :
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries].
proof.
proc
  (budgeted_programmed_challenge_query_discipline
     EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
     EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries) => //.
+ move=> />.
+ proc*.
  call budgeted_programmed_hash_get_preserves_challenge_query_discipline.
  by auto => />.
+ by apply budgeted_programmed_sign_oracle_preserves_challenge_query_discipline.
qed.

lemma budgeted_programmed_main_challenge_query_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main :
    true ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries].
proof.
proc.
wp.
call budgeted_counted_lazy_rom_bad_true.
wp.
call (_:
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries).
+ conseq adversary_budgeted_programmed_challenge_query_discipline_preserved => />.
wp.
call (counted_lazy_rom_get_nonchallenge_preserves_challenge_query_count H 1).
wp.
rnd.
wp.
call (counted_lazy_rom_init_clears_hash_queries H).
by auto => /> sd; rewrite /budgeted_programmed_challenge_query_discipline
                       /matrix_expand_query /ro_query_is_challenge
                       /challenge_query_log_count
                       /hash_query_budget_count; smt.
qed.

lemma budgeted_programmed_main_challenge_query_count_bound :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main :
    true ==>
    challenge_query_log_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries <=
      hash_query_budget_count + 1].
proof.
conseq budgeted_programmed_main_challenge_query_discipline => />.
rewrite /budgeted_programmed_challenge_query_discipline.
smt.
qed.

lemma budgeted_programmed_adaptive_prequery_lift
  md sk m ctx qs hc :
  budgeted_programmed_challenge_query_discipline hc qs =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
rewrite /budgeted_programmed_challenge_query_discipline.
move=> [hc_ge0 [hc_budget query_count]].
by apply (programmed_site_prequery_one_step_challenge_counter_bound
            md sk m ctx qs hc).
qed.

lemma budgeted_programmed_adaptive_prequery_lift_checked_31
  md sk m ctx qs hc :
  budgeted_programmed_challenge_query_discipline hc qs =>
  mu drandom_coins
    (fun coins =>
      programming_site_prequeried qs
        (honest_signing_programming_site md sk m ctx coins)) <=
  31%r / 288230376151711744%r.
proof.
move=> discipline.
apply (ler_trans
  ((rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound)).
+ by apply (budgeted_programmed_adaptive_prequery_lift
             md sk m ctx qs hc).
by rewrite /rom_hash_query_budget /hash_query_count
           /challenge_support_cardinality_lower_bound; smt.
qed.

lemma budgeted_programmed_hash_get_preserves_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).AH.get :
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram ==>
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram].
proof.
proc.
if.
  call budgeted_counted_lazy_rom_get_true.
  wp.
  by auto => />; rewrite /budgeted_programmed_query_count_discipline
                        /hash_query_budget_count
                        /signature_query_budget_count; smt.
  by auto => />; rewrite /budgeted_programmed_query_count_discipline
                      /hash_query_budget_count /signature_query_budget_count; smt.
qed.

lemma budgeted_programmed_reprogram_discipline_after_actual_signature
  pk sk m ctx coins sites bad_reprogram :
  budgeted_programmed_reprogram_discipline pk sk sites bad_reprogram =>
  pk = public_key_of_secret haetae_mode sk =>
  budgeted_programmed_reprogram_discipline
    pk sk
    (actual_signature_programming_site haetae_mode
      (transcript_of_signature haetae_mode pk m ctx
        (sign_internal haetae_mode sk m ctx coins)) :: sites)
    (bad_reprogram \/
      programming_site_reprograms sites
        (actual_signature_programming_site haetae_mode
          (transcript_of_signature haetae_mode pk m ctx
            (sign_internal haetae_mode sk m ctx coins)))).
proof.
rewrite /budgeted_programmed_reprogram_discipline.
move=> [_ [hconf hclear]] hkey.
have hsite :
  ! programming_site_reprograms sites
      (actual_signature_programming_site haetae_mode
        (transcript_of_signature haetae_mode pk m ctx
          (sign_internal haetae_mode sk m ctx coins))) /\
  programming_site_log_conflict_free_for_honest haetae_mode sk
    (actual_signature_programming_site haetae_mode
      (transcript_of_signature haetae_mode pk m ctx
        (sign_internal haetae_mode sk m ctx coins)) :: sites).
+ apply (actual_signature_programming_site_sign_internal_conflict_step
           haetae_mode pk sk m ctx coins sites).
  + exact hkey.
  + exact hconf.
move: hsite=> [hno_reprogram hconf_next].
split.
+ exact hkey.
split.
+ exact hconf_next.
by rewrite hclear hno_reprogram.
qed.

lemma budgeted_programmed_sign_oracle_preserves_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).O.sign :
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram ==>
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram].
proof.
proc.
if.
+ inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.program.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.observe_transcript.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.get.
  inline DirectSigningCoinSampler.sample.
  wp.
  call (_: true).
  wp.
  call (_: true).
  wp.
  rnd.
  wp.
  skip.
  move=> &hr [[hcount hdis] hsign_lt].
  case (EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{hr} = 0)
    => hsign_case.
  + move=> sampled_coins _.
    split.
    + move: hcount hsign_lt hsign_case.
      rewrite /budgeted_programmed_query_count_discipline
              /hash_query_budget_count /signature_query_budget_count; smt.
    apply (budgeted_programmed_reprogram_discipline_after_actual_signature
             EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{hr}
             EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{hr}
             m{hr} ctx{hr} sampled_coins
             CountedLazyROM.programmed_sites{hr}
             CountedLazyROM.bad_reprogram{hr}).
    + exact hdis.
    + by move: hdis; rewrite /budgeted_programmed_reprogram_discipline.
  + move=> sampled_coins _.
    split.
    + move: hcount hsign_lt hsign_case.
      rewrite /budgeted_programmed_query_count_discipline
              /hash_query_budget_count /signature_query_budget_count; smt.
    apply (budgeted_programmed_reprogram_discipline_after_actual_signature
             EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{hr}
             EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{hr}
             m{hr} ctx{hr} sampled_coins
             CountedLazyROM.programmed_sites{hr}
             CountedLazyROM.bad_reprogram{hr}).
    + exact hdis.
    + by move: hdis; rewrite /budgeted_programmed_reprogram_discipline.
  by auto => />; rewrite /budgeted_programmed_query_count_discipline
                    /signature_query_budget_count; smt.
qed.

lemma adversary_budgeted_programmed_discipline_preserved :
  hoare[
    A(EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).AH,
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).O).forge :
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram ==>
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram].
proof.
proc
  (budgeted_programmed_query_count_discipline
     EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
     EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
   budgeted_programmed_reprogram_discipline
     EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
     EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
     EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
     EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram) => //.
+ move=> />.
+ proc*.
  call budgeted_programmed_hash_get_preserves_discipline.
  by auto => />.
+ by apply budgeted_programmed_sign_oracle_preserves_discipline.
qed.

lemma budgeted_programmed_main_reprogram_clear :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main :
    true ==>
    ! EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram].
proof.
proc.
wp.
call (_:
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram ==>
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram).
+ by proc.
wp.
call (_:
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram ==>
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram).
+ conseq adversary_budgeted_programmed_discipline_preserved => />.
wp.
call budgeted_counted_lazy_rom_get_true.
wp.
rnd.
wp.
call (counted_lazy_rom_init_clears H).
by auto => /> sd; rewrite /budgeted_programmed_query_count_discipline
                       /budgeted_programmed_reprogram_discipline
                       /hash_query_budget_count /signature_query_budget_count;
   smt.
qed.

lemma budgeted_programmed_bad_reprogram_zero &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram] =
  0%r.
proof.
byphoare (_: true ==>
  EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram) => //.
hoare.
by conseq budgeted_programmed_main_reprogram_clear.
qed.

lemma budgeted_programmed_prequery_reprogram_bad_bound_from_prequery &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery] <=
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound =>
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram] <=
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound.
proof.
move=> prequery_bound.
apply (ler_trans
  (Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery] +
   Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram])).
+ by rewrite Pr[mu_or]; smt.
rewrite (budgeted_programmed_bad_reprogram_zero &m).
by smt.
qed.

lemma budgeted_programmed_hash_get_preserves_query_budget :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).AH.get :
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count ==>
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count].
proof.
proc.
if.
+ call budgeted_counted_lazy_rom_get_true.
  wp.
  by auto => />; rewrite /hash_query_budget_count /signature_query_budget_count; smt.
by auto => />; rewrite /hash_query_budget_count /signature_query_budget_count; smt.
qed.

lemma budgeted_programmed_sign_oracle_preserves_query_budget :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).O.sign :
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count ==>
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count].
proof.
proc.
if.
+ inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.program.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.observe_transcript.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.get.
  inline DirectSigningCoinSampler.sample.
  wp.
  call (_: true).
  wp.
  call (_: true).
  wp.
  rnd.
  by auto => />; rewrite /signature_query_budget_count.
by auto.
qed.

lemma adversary_budgeted_programmed_query_budget_preserved :
  hoare[
    A(EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).AH,
      EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).O).forge :
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count ==>
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count].
proof.
proc
  (0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
     hash_query_budget_count /\
   0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
     signature_query_budget_count) => //.
+ move=> />.
+ proc*.
  call budgeted_programmed_hash_get_preserves_query_budget.
  by auto.
+ by apply budgeted_programmed_sign_oracle_preserves_query_budget.
qed.

lemma budgeted_programmed_main_query_budget_preserved :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main :
    true ==>
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count].
proof.
proc.
wp.
call budgeted_counted_lazy_rom_bad_true.
wp.
call (_:
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count ==>
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count <=
      hash_query_budget_count /\
    0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count <=
      signature_query_budget_count).
+ conseq adversary_budgeted_programmed_query_budget_preserved => />.
wp.
call budgeted_counted_lazy_rom_get_true.
wp.
rnd.
wp.
call budgeted_counted_lazy_rom_init_true.
by auto => />; rewrite /hash_query_budget_count /signature_query_budget_count.
qed.

lemma budgeted_programmed_query_budget_certifies_branch_bound &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram] <=
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound =>
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram] <=
  counted_rom_prequery_reprogramming_term.
proof.
move=> h.
by rewrite counted_rom_prequery_reprogramming_term_cardinalityE.
qed.

lemma budgeted_programmed_query_budget_certifies_branch_bound_from_prequery
  &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery] <=
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound =>
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram] <=
  counted_rom_prequery_reprogramming_term.
proof.
move=> prequery_bound.
apply (budgeted_programmed_query_budget_certifies_branch_bound &m).
by apply (budgeted_programmed_prequery_reprogram_bad_bound_from_prequery &m).
qed.

lemma budgeted_programmed_query_budget_certifies_checked_31_bound
  &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery] <=
    ((rom_total_query_budget * rom_total_query_budget) +
     (rom_signature_query_budget * (rom_hash_query_budget + 1%r))) /
    challenge_support_cardinality_lower_bound =>
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram] <=
  31%r / 288230376151711744%r.
proof.
move=> prequery_bound.
apply (ler_trans counted_rom_prequery_reprogramming_term).
+ by apply (budgeted_programmed_query_budget_certifies_branch_bound_from_prequery &m).
by rewrite counted_rom_prequery_reprogramming_term_concreteE.
qed.

end section BudgetedProgrammedROMTranscriptDiscipline.

section BudgetedSampledROMTranscriptDiscipline.

declare module H <: Oracle {-CountedLazyROM,
                             -DirectSigningCoinSampler,
                             -EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign}.
declare module A <: SIG.Adversary {-H, -CountedLazyROM,
                                   -DirectSigningCoinSampler,
                                   -EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign}.

lemma budgeted_sampled_direct_counted_lazy_rom_get_true :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).C.get :
    true ==> true].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma budgeted_sampled_direct_counted_lazy_rom_init_true :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).C.init :
    true ==> true].
proof.
proc.
wp.
call (_: true).
by auto.
qed.

lemma budgeted_sampled_direct_counted_lazy_rom_bad_true :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).C.bad :
    true ==> true].
proof.
by proc.
qed.

lemma budgeted_sampled_direct_hash_get_preserves_challenge_query_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).AH.get :
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries].
proof.
proc.
if.
+ inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.get.
  wp.
  call (_: true).
  by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
                        /hash_query_budget_count;
     smt(challenge_query_log_count_cons_le).
by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
                    /hash_query_budget_count; smt.
qed.

lemma budgeted_sampled_direct_sign_oracle_preserves_challenge_query_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).O.sign :
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries].
proof.
proc.
if.
+ inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.program.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.observe_transcript.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.get.
  inline DirectSigningCoinSampler.sample.
  wp.
  call (_: true).
  wp.
  call (_: true).
	  wp.
	  rnd.
	  by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
	                        challenge_query_log_count_message_cons; smt.
by auto => />; rewrite /budgeted_programmed_challenge_query_discipline; smt.
qed.

lemma adversary_budgeted_sampled_direct_challenge_query_discipline_preserved :
  hoare[
    A(EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).AH,
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).O).forge :
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries].
proof.
proc
  (budgeted_programmed_challenge_query_discipline
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries) => //.
+ move=> />.
+ proc*.
  call budgeted_sampled_direct_hash_get_preserves_challenge_query_discipline.
  by auto => />.
+ by apply budgeted_sampled_direct_sign_oracle_preserves_challenge_query_discipline.
qed.

lemma budgeted_sampled_direct_main_challenge_query_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).main :
    true ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries].
proof.
proc.
wp.
call budgeted_sampled_direct_counted_lazy_rom_bad_true.
wp.
call (_:
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries ==>
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries).
+ conseq adversary_budgeted_sampled_direct_challenge_query_discipline_preserved => />.
wp.
call (counted_lazy_rom_get_nonchallenge_preserves_challenge_query_count H 1).
wp.
rnd.
wp.
call (counted_lazy_rom_init_clears_hash_queries H).
by auto => /> sd; rewrite /budgeted_programmed_challenge_query_discipline
                       /matrix_expand_query /ro_query_is_challenge
                       /challenge_query_log_count
                       /hash_query_budget_count; smt.
qed.

lemma budgeted_sampled_direct_hash_get_preserves_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).AH.get :
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram ==>
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram].
proof.
proc.
if.
+ call budgeted_sampled_direct_counted_lazy_rom_get_true.
  wp.
  by auto => />; rewrite /budgeted_programmed_query_count_discipline
                        /hash_query_budget_count
                        /signature_query_budget_count; smt.
by auto => />; rewrite /budgeted_programmed_query_count_discipline
                    /hash_query_budget_count /signature_query_budget_count; smt.
qed.

lemma budgeted_sampled_direct_sign_oracle_preserves_discipline :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).O.sign :
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram ==>
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram].
proof.
proc.
if.
+ inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.program.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.observe_transcript.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.get.
  inline DirectSigningCoinSampler.sample.
  wp.
  call (_: true).
  wp.
  call (_: true).
  wp.
  rnd.
  wp.
  skip.
  move=> &hr [[hcount hdis] hsign_lt].
  case (EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{hr} = 0)
    => hsign_case.
  + move=> sampled_coins _.
    split.
    + move: hcount hsign_lt hsign_case.
      rewrite /budgeted_programmed_query_count_discipline
              /hash_query_budget_count /signature_query_budget_count; smt.
    apply (budgeted_programmed_reprogram_discipline_after_actual_signature
             EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{hr}
             EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{hr}
             m{hr} ctx{hr} sampled_coins
             CountedLazyROM.programmed_sites{hr}
             CountedLazyROM.bad_reprogram{hr}).
    + exact hdis.
    + by move: hdis; rewrite /budgeted_programmed_reprogram_discipline.
  + move=> sampled_coins _.
    split.
    + move: hcount hsign_lt hsign_case.
      rewrite /budgeted_programmed_query_count_discipline
              /hash_query_budget_count /signature_query_budget_count; smt.
    apply (budgeted_programmed_reprogram_discipline_after_actual_signature
             EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{hr}
             EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{hr}
             m{hr} ctx{hr} sampled_coins
             CountedLazyROM.programmed_sites{hr}
             CountedLazyROM.bad_reprogram{hr}).
    + exact hdis.
    + by move: hdis; rewrite /budgeted_programmed_reprogram_discipline.
  by auto => />; rewrite /budgeted_programmed_query_count_discipline
                    /signature_query_budget_count; smt.
qed.

lemma adversary_budgeted_sampled_direct_discipline_preserved :
  hoare[
    A(EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).AH,
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).O).forge :
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram ==>
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram].
proof.
proc
  (budgeted_programmed_query_count_discipline
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
   budgeted_programmed_reprogram_discipline
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram) => //.
+ move=> />.
+ proc*.
  call budgeted_sampled_direct_hash_get_preserves_discipline.
  by auto => />.
+ by apply budgeted_sampled_direct_sign_oracle_preserves_discipline.
qed.

lemma budgeted_sampled_direct_main_reprogram_clear :
  hoare[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).main :
    true ==>
    ! EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram].
proof.
proc.
wp.
call (_:
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram ==>
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram).
+ by proc.
wp.
call (_:
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram ==>
    budgeted_programmed_query_count_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
    budgeted_programmed_reprogram_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram).
+ conseq adversary_budgeted_sampled_direct_discipline_preserved => />.
wp.
call budgeted_sampled_direct_counted_lazy_rom_get_true.
wp.
rnd.
wp.
call (counted_lazy_rom_init_clears H).
by auto => /> sd; rewrite /budgeted_programmed_query_count_discipline
                       /budgeted_programmed_reprogram_discipline
                       /hash_query_budget_count /signature_query_budget_count;
   smt.
qed.

lemma budgeted_sampled_direct_bad_reprogram_zero &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram] =
  0%r.
proof.
byphoare (_: true ==>
  EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram) => //.
hoare.
by conseq budgeted_sampled_direct_main_reprogram_clear.
qed.

lemma budgeted_sampled_direct_one_step_bound_nonnegative :
  0%r <=
  (rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound.
proof.
apply divr_ge0.
+ by rewrite addr_ge0; [apply rom_hash_query_budget_nonnegative |].
by apply challenge_support_cardinality_lower_bound_nonnegative.
qed.

lemma budgeted_sampled_direct_sampler_message_hash_prequery_bound
  pk sk qs m ctx :
  phoare[DirectSigningCoinSampler.sample :
    budgeted_programmed_challenge_query_discipline
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
      qs /\
    pk = public_key_of_secret haetae_mode sk /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current = pk /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current = sk /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries = qs ==>
    programming_site_prequeried
      (message_hash_query
         (public_key_of_secret haetae_mode sk) ctx m :: qs)
      (actual_signature_programming_site haetae_mode
         (transcript_of_signature haetae_mode
            pk
            m ctx
            (sign_internal haetae_mode
               sk m ctx res)))] <=
  ((rom_hash_query_budget + 1%r) /
    challenge_support_cardinality_lower_bound).
proof.
bypr=> &m0 [discipline _].
move: discipline; rewrite /budgeted_programmed_challenge_query_discipline.
move=> [_ [hc_budget query_count]].
have query_budget :
  challenge_query_log_count qs <= hash_query_budget_count + 1 by smt.
byphoare (_: true ==>
  programming_site_prequeried
    (message_hash_query
       (public_key_of_secret haetae_mode sk) ctx m :: qs)
    (actual_signature_programming_site haetae_mode
       (transcript_of_signature haetae_mode pk m ctx
          (sign_internal haetae_mode sk m ctx res)))) => //.
by conseq (direct_signing_coin_sampler_message_hash_budgeted_prequery_bound
  haetae_mode pk sk m ctx (public_key_of_secret haetae_mode sk) ctx m qs
  query_budget).
qed.

lemma budgeted_sampled_direct_bad_prequery_bound &m :
  islossless H.get =>
  islossless H.set =>
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery] <=
  ((rom_hash_query_budget + rom_signature_query_budget) *
    (rom_hash_query_budget + 1%r)) /
    challenge_support_cardinality_lower_bound.
proof.
move=> H_get_ll H_set_ll.
have H_get_true : phoare[H.get : true ==> true] = 1%r.
+ by conseq H_get_ll.
have H_set_true : phoare[H.set : true ==> true] = 1%r.
+ by conseq H_set_ll.
fel 12
       (EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count +
        EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count)
       (fun _,
          (rom_hash_query_budget + 1%r) /
            challenge_support_cardinality_lower_bound)
       (hash_query_budget_count + signature_query_budget_count)
       EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery
       [EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).AH.get :
            (EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count <
              hash_query_budget_count);
        EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
          (H, A, DirectSigningCoinSampler).O.sign :
            (EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count <
              signature_query_budget_count)]
	       (budgeted_programmed_challenge_query_discipline
	          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count
	          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries /\
	        EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current =
	          public_key_of_secret haetae_mode
	            EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current /\
	        0 <= EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count /\
	        EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count <=
	          signature_query_budget_count).
+ rewrite /rom_hash_query_budget /rom_signature_query_budget
          /hash_query_count /signature_query_count
          /hash_query_budget_count /signature_query_budget_count.
  rewrite StdBigop.Bigreal.BRA.sumri_const.
  + by smt.
  by smt.
+ by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
                         /hash_query_budget_count
                         /signature_query_budget_count; smt.
+ wp.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.get.
  wp.
  call (_: true).
  wp.
  rnd.
  wp.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.init.
  wp.
	  call (_: true).
	  by auto => /> sd; rewrite /budgeted_programmed_challenge_query_discipline
	                         /matrix_expand_query /ro_query_is_challenge
	                         /challenge_query_log_count
	                         /keygen_internal
	                         /hash_query_budget_count
	                         /signature_query_budget_count; smt.
+ proc.
  if.
  + inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.get.
    conseq (: _ ==> false : = 0%r) => />.
    + by smt(budgeted_sampled_direct_one_step_bound_nonnegative).
    hoare.
    wp.
    call (_: true).
    by auto.
  conseq (: _ ==> false : = 0%r) => />.
  + by smt(budgeted_sampled_direct_one_step_bound_nonnegative).
  hoare.
  by auto => />; rewrite /hash_query_budget_count; smt.
+ move=> old_count.
  proc.
  if.
  + inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.get.
	    wp.
	    call (_: true).
	    by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
	                          /hash_query_budget_count
	                          /signature_query_budget_count;
	       smt(challenge_query_log_count_cons_le).
  by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
                      /hash_query_budget_count
                      /signature_query_budget_count; smt.
+ move=> old_bad old_count.
  proc.
  if.
  + inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
       (H, A, DirectSigningCoinSampler).C.get.
	    wp.
	    call (_: true).
	    by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
	                          /hash_query_budget_count
	                          /signature_query_budget_count;
	       smt(challenge_query_log_count_cons_le).
  by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
                      /hash_query_budget_count
                      /signature_query_budget_count; smt.
+ proc.
  if.
  + inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
         (H, A, DirectSigningCoinSampler).C.program.
    inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
         (H, A, DirectSigningCoinSampler).C.observe_transcript.
    inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
         (H, A, DirectSigningCoinSampler).C.get.
		    seq 2 :
		      (EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery \/
		       programming_site_prequeried
		         (message_hash_query
		            (public_key_of_secret haetae_mode
		               EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current)
	            ctx m ::
	          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries)
	         (actual_signature_programming_site haetae_mode
	            (transcript_of_signature haetae_mode
	               EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
	               m ctx
	               (sign_internal haetae_mode
	                  EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
	                  m ctx coins))))
	      ((rom_hash_query_budget + 1%r) /
	        challenge_support_cardinality_lower_bound)
	      (1%r) (1%r) (0%r).
	    + inline DirectSigningCoinSampler.sample.
	      if.
	      + wp.
	        rnd.
	        wp.
	        by auto => />; smt(signing_coin_distribution_lossless).
	      wp.
	      rnd.
	      wp.
	      by auto => />; smt(signing_coin_distribution_lossless).
	    + inline DirectSigningCoinSampler.sample.
	      if.
	      + wp.
	        rnd (fun sampled_coins =>
	          programming_site_prequeried
	            (message_hash_query
	               (public_key_of_secret haetae_mode
	                  EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current)
	               ctx m ::
	             EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries)
	            (actual_signature_programming_site haetae_mode
	               (transcript_of_signature haetae_mode
	                  EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
	                  m ctx
	                  (sign_internal haetae_mode
	                     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
	                     m ctx sampled_coins)))).
	        wp.
		        auto => />.
        move=> &hr h1 h2 h3 h4 h5 h6 h7 h8.
        by apply (programmed_site_prequery_one_step_message_hash_counter_bound
          haetae_mode
          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{hr}
          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{hr}
	          m{hr} ctx{hr}
	          (public_key_of_secret haetae_mode
	             EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{hr})
          ctx{hr} m{hr}
          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{hr}
          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{hr});
          smt.
	      wp.
	      rnd (fun sampled_coins =>
	        programming_site_prequeried
	          (message_hash_query
	             (public_key_of_secret haetae_mode
	                EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current)
	             ctx m ::
	           EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries)
	          (actual_signature_programming_site haetae_mode
	             (transcript_of_signature haetae_mode
	                EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current
	                m ctx
	                (sign_internal haetae_mode
		                   EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current
		                   m ctx sampled_coins)))).
	      wp.
	      auto => />.
	      move=> &hr *.
	      apply (ler_trans
	        ((rom_hash_query_budget + 1%r) /
	          challenge_support_cardinality_lower_bound)).
	      + by apply (programmed_site_prequery_one_step_message_hash_counter_bound
	          haetae_mode
	          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{hr}
	          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{hr}
	          m{hr} ctx{hr}
	          (public_key_of_secret haetae_mode
	             EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{hr})
	          ctx{hr} m{hr}
	          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{hr}
	          EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{hr});
	          smt.
	      by smt.
		    + by trivial.
				    hoare.
				    wp.
				    call (_: true).
				    wp.
					    call (_: true).
					    by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
					                          /hash_query_budget_count
					                          /signature_query_budget_count; smt.
			    + by smt(budgeted_sampled_direct_one_step_bound_nonnegative).
		  conseq (: _ ==> false : = 0%r) => />.
	  + by smt(budgeted_sampled_direct_one_step_bound_nonnegative).
	  hoare.
	  by auto => />; rewrite /signature_query_budget_count; smt.
+ move=> old_count.
  proc.
  if.
  + inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
         (H, A, DirectSigningCoinSampler).C.program.
    inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
         (H, A, DirectSigningCoinSampler).C.observe_transcript.
    inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
         (H, A, DirectSigningCoinSampler).C.get.
    inline DirectSigningCoinSampler.sample.
    wp.
    call (_: true).
    wp.
    call (_: true).
		    wp.
		    rnd.
		    by auto => />; rewrite /budgeted_programmed_challenge_query_discipline
	                          /signature_query_budget_count; smt.
  by auto => />; rewrite /signature_query_budget_count; smt.
	+ move=> old_bad old_count.
	  proc.
	  if.
	  + inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
	         (H, A, DirectSigningCoinSampler).C.program.
	    inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
	         (H, A, DirectSigningCoinSampler).C.observe_transcript.
	    inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
	         (H, A, DirectSigningCoinSampler).C.get.
	    inline DirectSigningCoinSampler.sample.
	    wp.
	    call (_: true).
	    wp.
	    call (_: true).
	    wp.
	    rnd.
	    by auto => />; rewrite /signature_query_budget_count; smt.
	  by auto => />; rewrite /signature_query_budget_count; smt.
qed.

lemma budgeted_sampled_direct_prequery_reprogram_bad_bound &m :
  islossless H.get =>
  islossless H.set =>
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram] <=
  counted_rom_prequery_reprogramming_term.
proof.
move=> H_get_ll H_set_ll.
apply (ler_trans
  (Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).main() @ &m :
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery] +
   Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).main() @ &m :
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram])).
+ by rewrite Pr[mu_or]; smt.
rewrite (budgeted_sampled_direct_bad_reprogram_zero &m).
  apply (ler_trans
  (((rom_hash_query_budget + rom_signature_query_budget) *
     (rom_hash_query_budget + 1%r)) /
    challenge_support_cardinality_lower_bound)).
  + by smt(budgeted_sampled_direct_bad_prequery_bound).
  rewrite counted_rom_prequery_reprogramming_term_cardinalityE.
by rewrite /rom_total_query_budget /rom_hash_query_budget
           /rom_signature_query_budget /hash_query_count
           /signature_query_count
           /challenge_support_cardinality_lower_bound; smt.
qed.

lemma budgeted_sampled_direct_prequery_reprogram_bad_checked_31 &m :
  islossless H.get =>
  islossless H.set =>
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram] <=
  31%r / 288230376151711744%r.
proof.
move=> H_get_ll H_set_ll.
apply (ler_trans counted_rom_prequery_reprogramming_term).
+ by apply budgeted_sampled_direct_prequery_reprogram_bad_bound.
by rewrite counted_rom_prequery_reprogramming_term_concreteE.
qed.

end section BudgetedSampledROMTranscriptDiscipline.

section BudgetedProgrammedToSampledDirectBridge.

declare module H <: Oracle {-CountedLazyROM,
                             -DirectSigningCoinSampler,
                             -EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign,
                             -EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign}.
declare module A <: SIG.Adversary {-H, -CountedLazyROM,
                                   -DirectSigningCoinSampler,
                                   -EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign,
                                   -EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign}.

equiv budgeted_programmed_counted_sampled_direct_hash_get_equiv :
  EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).AH.get ~
  EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
    (H, A, DirectSigningCoinSampler).AH.get :
    ={glob H, arg} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}
    ==>
    ={glob H, res} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}.
proof.
proc.
if.
+ by auto => />.
+ wp.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.get.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
    (H, A, DirectSigningCoinSampler).C.get.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  by auto => />.
by auto => />.
qed.

equiv budgeted_programmed_counted_sampled_direct_sign_equiv :
  EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).O.sign ~
  EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
    (H, A, DirectSigningCoinSampler).O.sign :
    ={glob H, arg} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.transcripts{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.transcripts{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.records{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.records{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}
    ==>
    ={glob H, res} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.transcripts{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.transcripts{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.records{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.records{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}.
proof.
proc.
if.
+ by auto => />.
+ inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.program.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
    (H, A, DirectSigningCoinSampler).C.program.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.observe_transcript.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
    (H, A, DirectSigningCoinSampler).C.observe_transcript.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.get.
  inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
    (H, A, DirectSigningCoinSampler).C.get.
  inline DirectSigningCoinSampler.sample.
  wp.
  call (: ={glob H, arg} ==> ={glob H}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  rnd.
  by auto => />.
by auto => />.
qed.

equiv adversary_budgeted_programmed_counted_sampled_direct_equiv :
  A(EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).AH,
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).O).forge ~
  A(EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
      (H, A, DirectSigningCoinSampler).AH,
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
      (H, A, DirectSigningCoinSampler).O).forge :
    ={glob H, glob A, arg} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.transcripts{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.transcripts{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.records{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.records{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}
    ==>
    ={glob H, res} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.transcripts{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.transcripts{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.records{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.records{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}.
proof.
proc
  (={glob H} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.queries{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.queries{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.transcripts{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.transcripts{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.records{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.records{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
   EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
     EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}) => //.
+ move=> />.
+ proc*.
  call budgeted_programmed_counted_sampled_direct_hash_get_equiv.
  by auto => />.
+ proc*.
  call budgeted_programmed_counted_sampled_direct_sign_equiv.
  by auto => />.
qed.

equiv budgeted_programmed_counted_sampled_direct_main_equiv :
  EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main ~
  EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
    (H, A, DirectSigningCoinSampler).main :
    ={glob H, glob A} ==>
    ={res} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2}.
proof.
proc.
inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.bad.
inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
  (H, A, DirectSigningCoinSampler).C.bad.
wp.
call (_:
    ={glob H, glob A, arg} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.transcripts{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.transcripts{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.records{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.records{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}
    ==>
    ={glob H, res} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.pk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.pk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.sk_current{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.sk_current{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.transcripts{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.transcripts{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.records{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.records{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.adversary_hash_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.adversary_hash_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.signing_count{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.signing_count{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.hash_queries{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.hash_queries{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.programmed_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.programmed_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.signature_sites{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.signature_sites{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram{2} /\
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_min_entropy{1} =
      EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_min_entropy{2}).
+ by apply adversary_budgeted_programmed_counted_sampled_direct_equiv.
wp.
inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.get.
inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
  (H, A, DirectSigningCoinSampler).C.get.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
inline EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).C.init.
inline EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
  (H, A, DirectSigningCoinSampler).C.init.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />.
qed.

lemma budgeted_programmed_counted_sampled_direct_prequery_reprogram_bad_exact
  &m :
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram] =
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign
        (H, A, DirectSigningCoinSampler).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedSampledSign.C.bad_reprogram].
proof.
byequiv budgeted_programmed_counted_sampled_direct_main_equiv => //.
qed.

lemma budgeted_programmed_prequery_reprogram_bad_checked_31_via_direct_sampler
  &m :
  islossless H.get =>
  islossless H.set =>
  Pr[EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign(H, A).main() @ &m :
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_prequery \/
    EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign.C.bad_reprogram] <=
  31%r / 288230376151711744%r.
proof.
move=> H_get_ll H_set_ll.
rewrite (budgeted_programmed_counted_sampled_direct_prequery_reprogram_bad_exact &m).
by apply (budgeted_sampled_direct_prequery_reprogram_bad_checked_31 H A &m).
qed.

end section BudgetedProgrammedToSampledDirectBridge.

section HAETAEROMInternalTranscriptExact.

declare module H <: SIG.Oracle {-SIG.EUF_CMA,
                                -EUF_CMA_ROMInternalTranscriptSign}.
declare module A <: SIG.Adversary {-H, -SIG.EUF_CMA,
                                   -EUF_CMA_ROMInternalTranscriptSign}.

equiv haetae_rom_internal_oracle_erasure :
  SIG.EUF_CMA(H, HAETAE, A).O.sign ~
  EUF_CMA_ROMInternalTranscriptSign(H, A).O.sign :
    ={glob H, arg} /\
    SIG.EUF_CMA.sk{1} = EUF_CMA_ROMInternalTranscriptSign.sk_current{2} /\
    SIG.EUF_CMA.queries{1} =
      EUF_CMA_ROMInternalTranscriptSign.queries{2}
    ==>
    ={glob H, res} /\
    SIG.EUF_CMA.sk{1} = EUF_CMA_ROMInternalTranscriptSign.sk_current{2} /\
    SIG.EUF_CMA.queries{1} =
      EUF_CMA_ROMInternalTranscriptSign.queries{2}.
proof.
proc.
inline HAETAE(H).sign.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
by auto => />.
qed.

equiv adversary_haetae_rom_internal_erasure :
  A(H, SIG.EUF_CMA(H, HAETAE, A).O).forge ~
  A(H, EUF_CMA_ROMInternalTranscriptSign(H, A).O).forge :
    ={glob H, glob A, arg} /\
    SIG.EUF_CMA.sk{1} = EUF_CMA_ROMInternalTranscriptSign.sk_current{2} /\
    SIG.EUF_CMA.queries{1} =
      EUF_CMA_ROMInternalTranscriptSign.queries{2}
    ==>
    ={glob H, res} /\
    SIG.EUF_CMA.sk{1} = EUF_CMA_ROMInternalTranscriptSign.sk_current{2} /\
    SIG.EUF_CMA.queries{1} =
      EUF_CMA_ROMInternalTranscriptSign.queries{2}.
proof.
proc (={glob H} /\
      SIG.EUF_CMA.sk{1} = EUF_CMA_ROMInternalTranscriptSign.sk_current{2} /\
      SIG.EUF_CMA.queries{1} =
        EUF_CMA_ROMInternalTranscriptSign.queries{2}) => //.
+ move=> />.
+ by sim.
+ proc.
  inline HAETAE(H).sign.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  rnd.
  by auto => />.
qed.

lemma haetae_rom_internal_transcript_erasure_exact &m :
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] =
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res].
proof.
byequiv (: ={glob H, glob A} ==> ={res}) => //.
proc.
inline HAETAE(H).verify.
wp.
call (_: ={glob H, glob A, arg} /\
        SIG.EUF_CMA.sk{1} =
          EUF_CMA_ROMInternalTranscriptSign.sk_current{2} /\
        SIG.EUF_CMA.queries{1} =
          EUF_CMA_ROMInternalTranscriptSign.queries{2} ==>
        ={glob H, res} /\
        SIG.EUF_CMA.sk{1} =
          EUF_CMA_ROMInternalTranscriptSign.sk_current{2} /\
        SIG.EUF_CMA.queries{1} =
          EUF_CMA_ROMInternalTranscriptSign.queries{2}).
+ by apply adversary_haetae_rom_internal_erasure.
wp.
inline HAETAE(H).kg.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />.
qed.

end section HAETAEROMInternalTranscriptExact.

section ROMInternalTranscriptStructuralNMA.

declare module H <: SIG.Oracle {-EUF_CMA_ROMInternalTranscriptSign,
                                -ROMInternalTranscriptAsNMA}.
declare module A <: SIG.Adversary {-H, -EUF_CMA_ROMInternalTranscriptSign,
                                   -ROMInternalTranscriptAsNMA}.

equiv rom_internal_oracle_structural_nma :
  EUF_CMA_ROMInternalTranscriptSign(H, A).O.sign ~
  ROMInternalTranscriptAsNMA(A, H).O.sign :
    ={glob H, arg} /\
    EUF_CMA_ROMInternalTranscriptSign.pk_current{1} =
      ROMInternalTranscriptAsNMA.pk_current{2} /\
    EUF_CMA_ROMInternalTranscriptSign.sk_current{1} =
      ROMInternalTranscriptAsNMA.sk_current{2} /\
    EUF_CMA_ROMInternalTranscriptSign.queries{1} =
      ROMInternalTranscriptAsNMA.queries{2} /\
    EUF_CMA_ROMInternalTranscriptSign.transcripts{1} =
      ROMInternalTranscriptAsNMA.transcripts{2} /\
    EUF_CMA_ROMInternalTranscriptSign.records{1} =
      ROMInternalTranscriptAsNMA.records{2}
    ==>
    ={glob H, res} /\
    EUF_CMA_ROMInternalTranscriptSign.pk_current{1} =
      ROMInternalTranscriptAsNMA.pk_current{2} /\
    EUF_CMA_ROMInternalTranscriptSign.sk_current{1} =
      ROMInternalTranscriptAsNMA.sk_current{2} /\
    EUF_CMA_ROMInternalTranscriptSign.queries{1} =
      ROMInternalTranscriptAsNMA.queries{2} /\
    EUF_CMA_ROMInternalTranscriptSign.transcripts{1} =
      ROMInternalTranscriptAsNMA.transcripts{2} /\
    EUF_CMA_ROMInternalTranscriptSign.records{1} =
      ROMInternalTranscriptAsNMA.records{2}.
proof.
proc.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
by auto => />.
qed.

equiv adversary_rom_internal_structural_nma :
  A(H, EUF_CMA_ROMInternalTranscriptSign(H, A).O).forge ~
  A(H, ROMInternalTranscriptAsNMA(A, H).O).forge :
    ={glob H, glob A, arg} /\
    EUF_CMA_ROMInternalTranscriptSign.pk_current{1} =
      ROMInternalTranscriptAsNMA.pk_current{2} /\
    EUF_CMA_ROMInternalTranscriptSign.sk_current{1} =
      ROMInternalTranscriptAsNMA.sk_current{2} /\
    EUF_CMA_ROMInternalTranscriptSign.queries{1} =
      ROMInternalTranscriptAsNMA.queries{2} /\
    EUF_CMA_ROMInternalTranscriptSign.transcripts{1} =
      ROMInternalTranscriptAsNMA.transcripts{2} /\
    EUF_CMA_ROMInternalTranscriptSign.records{1} =
      ROMInternalTranscriptAsNMA.records{2}
    ==>
    ={glob H, res} /\
    EUF_CMA_ROMInternalTranscriptSign.pk_current{1} =
      ROMInternalTranscriptAsNMA.pk_current{2} /\
    EUF_CMA_ROMInternalTranscriptSign.sk_current{1} =
      ROMInternalTranscriptAsNMA.sk_current{2} /\
    EUF_CMA_ROMInternalTranscriptSign.queries{1} =
      ROMInternalTranscriptAsNMA.queries{2} /\
    EUF_CMA_ROMInternalTranscriptSign.transcripts{1} =
      ROMInternalTranscriptAsNMA.transcripts{2} /\
    EUF_CMA_ROMInternalTranscriptSign.records{1} =
      ROMInternalTranscriptAsNMA.records{2}.
proof.
proc
  (={glob H} /\
   EUF_CMA_ROMInternalTranscriptSign.pk_current{1} =
     ROMInternalTranscriptAsNMA.pk_current{2} /\
   EUF_CMA_ROMInternalTranscriptSign.sk_current{1} =
     ROMInternalTranscriptAsNMA.sk_current{2} /\
   EUF_CMA_ROMInternalTranscriptSign.queries{1} =
     ROMInternalTranscriptAsNMA.queries{2} /\
   EUF_CMA_ROMInternalTranscriptSign.transcripts{1} =
     ROMInternalTranscriptAsNMA.transcripts{2} /\
   EUF_CMA_ROMInternalTranscriptSign.records{1} =
     ROMInternalTranscriptAsNMA.records{2}) => //.
+ move=> />.
+ by sim.
+ proc.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  rnd.
  by auto => />.
qed.

lemma rom_internal_transcript_structural_nma_bound &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptAsNMA(A)).main()
       @ &m : res].
proof.
byequiv (: ={glob H, glob A} ==> res{1} => res{2}) => //.
proc.
inline HAETAE(H).verify
       HAETAE(H).kg
       ROMInternalTranscriptAsNMA(A, H).forge.
wp.
call (_: ={glob H, glob A, arg} /\
        EUF_CMA_ROMInternalTranscriptSign.pk_current{1} =
          ROMInternalTranscriptAsNMA.pk_current{2} /\
        EUF_CMA_ROMInternalTranscriptSign.sk_current{1} =
          ROMInternalTranscriptAsNMA.sk_current{2} /\
        EUF_CMA_ROMInternalTranscriptSign.queries{1} =
          ROMInternalTranscriptAsNMA.queries{2} /\
        EUF_CMA_ROMInternalTranscriptSign.transcripts{1} =
          ROMInternalTranscriptAsNMA.transcripts{2} /\
        EUF_CMA_ROMInternalTranscriptSign.records{1} =
          ROMInternalTranscriptAsNMA.records{2}
        ==>
        ={glob H, res} /\
        EUF_CMA_ROMInternalTranscriptSign.pk_current{1} =
          ROMInternalTranscriptAsNMA.pk_current{2} /\
        EUF_CMA_ROMInternalTranscriptSign.sk_current{1} =
          ROMInternalTranscriptAsNMA.sk_current{2} /\
        EUF_CMA_ROMInternalTranscriptSign.queries{1} =
          ROMInternalTranscriptAsNMA.queries{2} /\
        EUF_CMA_ROMInternalTranscriptSign.transcripts{1} =
          ROMInternalTranscriptAsNMA.transcripts{2} /\
        EUF_CMA_ROMInternalTranscriptSign.records{1} =
          ROMInternalTranscriptAsNMA.records{2}).
+ by apply adversary_rom_internal_structural_nma.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />; rewrite /keygen_internal /public_key_of_secret
                    /secret_key_of_seed.
qed.

lemma rom_internal_transcript_clear_site_structural_nma_bound &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts] <=
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptAsNMA(A)).main()
       @ &m : res].
proof.
apply (ler_trans
  (Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res])).
+ by rewrite Pr[mu_sub].
by apply rom_internal_transcript_structural_nma_bound.
qed.

end section ROMInternalTranscriptStructuralNMA.

section ROMInternalTranscriptPublicSimNMA.

declare module H <: SIG.Oracle {-ROMInternalTranscriptAsNMA,
                                -ROMInternalTranscriptPublicSimAsNMA}.
declare module A <: SIG.Adversary {-H, -ROMInternalTranscriptAsNMA,
                                   -ROMInternalTranscriptPublicSimAsNMA}.

equiv rom_internal_public_sim_nma_oracle :
  ROMInternalTranscriptAsNMA(A, H).O.sign ~
  ROMInternalTranscriptPublicSimAsNMA(A, H).O.sign :
    ={glob H, arg} /\
    ROMInternalTranscriptAsNMA.pk_current{1} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
    public_key_of_secret haetae_mode
      ROMInternalTranscriptAsNMA.sk_current{1} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
    ROMInternalTranscriptAsNMA.queries{1} =
      ROMInternalTranscriptPublicSimAsNMA.queries{2} /\
    ROMInternalTranscriptAsNMA.transcripts{1} =
      ROMInternalTranscriptPublicSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptAsNMA.records{1} =
      ROMInternalTranscriptPublicSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptAsNMA.pk_current{1} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
    public_key_of_secret haetae_mode
      ROMInternalTranscriptAsNMA.sk_current{1} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
    ROMInternalTranscriptAsNMA.queries{1} =
      ROMInternalTranscriptPublicSimAsNMA.queries{2} /\
    ROMInternalTranscriptAsNMA.transcripts{1} =
      ROMInternalTranscriptPublicSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptAsNMA.records{1} =
      ROMInternalTranscriptPublicSimAsNMA.records{2}.
proof.
proc.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
by auto => />; rewrite public_sim_commitment_highbitsE
                    public_sim_commitment_lowbitsE
                    public_sim_signatureE.
qed.

equiv adversary_rom_internal_public_sim_nma :
  A(H, ROMInternalTranscriptAsNMA(A, H).O).forge ~
  A(H, ROMInternalTranscriptPublicSimAsNMA(A, H).O).forge :
    ={glob H, glob A, arg} /\
    ROMInternalTranscriptAsNMA.pk_current{1} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
    public_key_of_secret haetae_mode
      ROMInternalTranscriptAsNMA.sk_current{1} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
    ROMInternalTranscriptAsNMA.queries{1} =
      ROMInternalTranscriptPublicSimAsNMA.queries{2} /\
    ROMInternalTranscriptAsNMA.transcripts{1} =
      ROMInternalTranscriptPublicSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptAsNMA.records{1} =
      ROMInternalTranscriptPublicSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptAsNMA.pk_current{1} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
    public_key_of_secret haetae_mode
      ROMInternalTranscriptAsNMA.sk_current{1} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
    ROMInternalTranscriptAsNMA.queries{1} =
      ROMInternalTranscriptPublicSimAsNMA.queries{2} /\
    ROMInternalTranscriptAsNMA.transcripts{1} =
      ROMInternalTranscriptPublicSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptAsNMA.records{1} =
      ROMInternalTranscriptPublicSimAsNMA.records{2}.
proof.
proc
  (={glob H} /\
   ROMInternalTranscriptAsNMA.pk_current{1} =
     ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
   public_key_of_secret haetae_mode
     ROMInternalTranscriptAsNMA.sk_current{1} =
     ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
   ROMInternalTranscriptAsNMA.queries{1} =
     ROMInternalTranscriptPublicSimAsNMA.queries{2} /\
   ROMInternalTranscriptAsNMA.transcripts{1} =
     ROMInternalTranscriptPublicSimAsNMA.transcripts{2} /\
   ROMInternalTranscriptAsNMA.records{1} =
     ROMInternalTranscriptPublicSimAsNMA.records{2}) => //.
+ move=> />.
+ by sim.
+ proc.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  rnd.
  by auto => />; rewrite public_sim_commitment_highbitsE
                      public_sim_commitment_lowbitsE
                      public_sim_signatureE.
qed.

lemma rom_internal_nma_public_sim_exact &m :
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptAsNMA(A)).main()
       @ &m : res] =
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptPublicSimAsNMA(A)).main()
       @ &m : res].
proof.
byequiv (: ={glob H, glob A} ==> ={res}) => //.
proc.
inline HAETAE(H).verify
       HAETAE(H).kg
       ROMInternalTranscriptAsNMA(A, H).forge
       ROMInternalTranscriptPublicSimAsNMA(A, H).forge.
wp.
call (_: ={glob H, glob A, arg} /\
        ROMInternalTranscriptAsNMA.pk_current{1} =
          ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
        public_key_of_secret haetae_mode
          ROMInternalTranscriptAsNMA.sk_current{1} =
          ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
        ROMInternalTranscriptAsNMA.queries{1} =
          ROMInternalTranscriptPublicSimAsNMA.queries{2} /\
        ROMInternalTranscriptAsNMA.transcripts{1} =
          ROMInternalTranscriptPublicSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptAsNMA.records{1} =
          ROMInternalTranscriptPublicSimAsNMA.records{2}
        ==>
        ={glob H, res} /\
        ROMInternalTranscriptAsNMA.pk_current{1} =
          ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
        public_key_of_secret haetae_mode
          ROMInternalTranscriptAsNMA.sk_current{1} =
          ROMInternalTranscriptPublicSimAsNMA.pk_current{2} /\
        ROMInternalTranscriptAsNMA.queries{1} =
          ROMInternalTranscriptPublicSimAsNMA.queries{2} /\
        ROMInternalTranscriptAsNMA.transcripts{1} =
          ROMInternalTranscriptPublicSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptAsNMA.records{1} =
          ROMInternalTranscriptPublicSimAsNMA.records{2}).
+ by apply adversary_rom_internal_public_sim_nma.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />; rewrite /keygen_internal /secret_key_of_seed
                    /public_key_of_secret.
qed.

end section ROMInternalTranscriptPublicSimNMA.

section ROMInternalTranscriptROMPaperSimNMA.

declare module H <: SIG.Oracle {-ROMInternalTranscriptPublicSimAsNMA,
                                -ROMInternalTranscriptPaperSimAsNMA,
                                -ROMPaperSimSigningSampler}.
declare module A <: SIG.Adversary {-H, -ROMInternalTranscriptPublicSimAsNMA,
                                   -ROMInternalTranscriptPaperSimAsNMA,
                                   -ROMPaperSimSigningSampler}.

equiv rom_internal_public_sim_rom_paper_sim_nma_oracle :
  ROMInternalTranscriptPublicSimAsNMA(A, H).O.sign ~
  ROMInternalTranscriptPaperSimAsNMA
    (A, ROMPaperSimSigningSampler(H), H).O.sign :
    ={glob H, arg} /\
    ROMInternalTranscriptPublicSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    ROMPaperSimSigningSampler.pk_current{2} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{1} /\
    ROMInternalTranscriptPublicSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPublicSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPublicSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptPublicSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    ROMPaperSimSigningSampler.pk_current{2} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{1} /\
    ROMInternalTranscriptPublicSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPublicSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPublicSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc.
inline ROMPaperSimSigningSampler(H).sample.
inline ROMPaperSimSigningSampler(H).sample_with_seed.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
by auto => />; rewrite paper_sim_commitment_highbits_public_coinsE
                    paper_sim_commitment_lowbits_public_coinsE
                    paper_sim_signature_public_coinsE.
qed.

equiv adversary_rom_internal_public_sim_rom_paper_sim_nma :
  A(H, ROMInternalTranscriptPublicSimAsNMA(A, H).O).forge ~
  A(H, ROMInternalTranscriptPaperSimAsNMA
      (A, ROMPaperSimSigningSampler(H), H).O).forge :
    ={glob H, glob A, arg} /\
    ROMInternalTranscriptPublicSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    ROMPaperSimSigningSampler.pk_current{2} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{1} /\
    ROMInternalTranscriptPublicSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPublicSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPublicSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptPublicSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    ROMPaperSimSigningSampler.pk_current{2} =
      ROMInternalTranscriptPublicSimAsNMA.pk_current{1} /\
    ROMInternalTranscriptPublicSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPublicSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPublicSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc
  (={glob H} /\
   ROMInternalTranscriptPublicSimAsNMA.pk_current{1} =
     ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
   ROMPaperSimSigningSampler.pk_current{2} =
     ROMInternalTranscriptPublicSimAsNMA.pk_current{1} /\
   ROMInternalTranscriptPublicSimAsNMA.queries{1} =
     ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
   ROMInternalTranscriptPublicSimAsNMA.transcripts{1} =
     ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
   ROMInternalTranscriptPublicSimAsNMA.records{1} =
     ROMInternalTranscriptPaperSimAsNMA.records{2}) => //.
+ move=> />.
+ by sim.
+ proc.
  inline ROMPaperSimSigningSampler(H).sample.
  inline ROMPaperSimSigningSampler(H).sample_with_seed.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  rnd.
  by auto => />; rewrite paper_sim_commitment_highbits_public_coinsE
                      paper_sim_commitment_lowbits_public_coinsE
                      paper_sim_signature_public_coinsE.
qed.

lemma rom_internal_nma_public_sim_rom_paper_sim_exact &m :
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptPublicSimAsNMA(A)).main()
       @ &m : res] =
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROMPaperSimSigningSampler(H))).main() @ &m : res].
proof.
byequiv (: ={glob H, glob A} ==> ={res}) => //.
proc.
inline HAETAE(H).verify
       HAETAE(H).kg
       ROMInternalTranscriptPublicSimAsNMA(A, H).forge
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROMPaperSimSigningSampler(H), H).forge
       ROMPaperSimSigningSampler(H).init.
wp.
call (_: ={glob H, glob A, arg} /\
        ROMInternalTranscriptPublicSimAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        ROMPaperSimSigningSampler.pk_current{2} =
          ROMInternalTranscriptPublicSimAsNMA.pk_current{1} /\
        ROMInternalTranscriptPublicSimAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptPublicSimAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptPublicSimAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}
        ==>
        ={glob H, res} /\
        ROMInternalTranscriptPublicSimAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        ROMPaperSimSigningSampler.pk_current{2} =
          ROMInternalTranscriptPublicSimAsNMA.pk_current{1} /\
        ROMInternalTranscriptPublicSimAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptPublicSimAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptPublicSimAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}).
+ by apply adversary_rom_internal_public_sim_rom_paper_sim_nma.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />; rewrite /keygen_internal /secret_key_of_seed
                    /public_key_of_secret.
qed.

end section ROMInternalTranscriptROMPaperSimNMA.

section ROMInternalTranscriptRealSigningPaperSimNMA.

declare module H <: SIG.Oracle {-ROMInternalTranscriptAsNMA,
                                -ROMInternalTranscriptPaperSimAsNMA,
                                -RealSigningPaperSimSampler}.
declare module A <: SIG.Adversary {-H, -ROMInternalTranscriptAsNMA,
                                   -ROMInternalTranscriptPaperSimAsNMA,
                                   -RealSigningPaperSimSampler}.

equiv rom_internal_real_signing_paper_sim_nma_oracle :
  ROMInternalTranscriptAsNMA(A, H).O.sign ~
  ROMInternalTranscriptPaperSimAsNMA
    (A, RealSigningPaperSimSampler(H), H).O.sign :
    ={glob H, arg} /\
    ROMInternalTranscriptAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    public_key_of_secret haetae_mode
      ROMInternalTranscriptAsNMA.sk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{2} =
      ROMInternalTranscriptAsNMA.pk_current{1} /\
    RealSigningPaperSimSampler.sk_current{2} =
      ROMInternalTranscriptAsNMA.sk_current{1} /\
    ROMInternalTranscriptAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    public_key_of_secret haetae_mode
      ROMInternalTranscriptAsNMA.sk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{2} =
      ROMInternalTranscriptAsNMA.pk_current{1} /\
    RealSigningPaperSimSampler.sk_current{2} =
      ROMInternalTranscriptAsNMA.sk_current{1} /\
    ROMInternalTranscriptAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc.
inline RealSigningPaperSimSampler(H).sample.
inline RealSigningPaperSimSampler(H).sample_with_seed.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
by auto => />; rewrite paper_sim_commitment_highbits_real_signing_coinsE
                    paper_sim_commitment_lowbits_real_signing_coinsE
                    paper_sim_signature_real_signing_coinsE.
qed.

equiv adversary_rom_internal_real_signing_paper_sim_nma :
  A(H, ROMInternalTranscriptAsNMA(A, H).O).forge ~
  A(H, ROMInternalTranscriptPaperSimAsNMA
      (A, RealSigningPaperSimSampler(H), H).O).forge :
    ={glob H, glob A, arg} /\
    ROMInternalTranscriptAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    public_key_of_secret haetae_mode
      ROMInternalTranscriptAsNMA.sk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{2} =
      ROMInternalTranscriptAsNMA.pk_current{1} /\
    RealSigningPaperSimSampler.sk_current{2} =
      ROMInternalTranscriptAsNMA.sk_current{1} /\
    ROMInternalTranscriptAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    public_key_of_secret haetae_mode
      ROMInternalTranscriptAsNMA.sk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{2} =
      ROMInternalTranscriptAsNMA.pk_current{1} /\
    RealSigningPaperSimSampler.sk_current{2} =
      ROMInternalTranscriptAsNMA.sk_current{1} /\
    ROMInternalTranscriptAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc
  (={glob H} /\
   ROMInternalTranscriptAsNMA.pk_current{1} =
     ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
   public_key_of_secret haetae_mode
     ROMInternalTranscriptAsNMA.sk_current{1} =
     ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
   RealSigningPaperSimSampler.pk_current{2} =
     ROMInternalTranscriptAsNMA.pk_current{1} /\
   RealSigningPaperSimSampler.sk_current{2} =
     ROMInternalTranscriptAsNMA.sk_current{1} /\
   ROMInternalTranscriptAsNMA.queries{1} =
     ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
   ROMInternalTranscriptAsNMA.transcripts{1} =
     ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
   ROMInternalTranscriptAsNMA.records{1} =
     ROMInternalTranscriptPaperSimAsNMA.records{2}) => //.
+ move=> />.
+ by sim.
+ proc.
  inline RealSigningPaperSimSampler(H).sample.
  inline RealSigningPaperSimSampler(H).sample_with_seed.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  rnd.
  by auto => />; rewrite paper_sim_commitment_highbits_real_signing_coinsE
                      paper_sim_commitment_lowbits_real_signing_coinsE
                      paper_sim_signature_real_signing_coinsE.
qed.

lemma rom_internal_nma_real_signing_paper_sim_exact &m :
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptAsNMA(A)).main()
       @ &m : res] =
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res].
proof.
byequiv (: ={glob H, glob A} ==> ={res}) => //.
proc.
inline HAETAE(H).verify
       HAETAE(H).kg
       ROMInternalTranscriptAsNMA(A, H).forge
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H), H).forge
       RealSigningPaperSimSampler(H).init.
wp.
call (_: ={glob H, glob A, arg} /\
        ROMInternalTranscriptAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        public_key_of_secret haetae_mode
          ROMInternalTranscriptAsNMA.sk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        RealSigningPaperSimSampler.pk_current{2} =
          ROMInternalTranscriptAsNMA.pk_current{1} /\
        RealSigningPaperSimSampler.sk_current{2} =
          ROMInternalTranscriptAsNMA.sk_current{1} /\
        ROMInternalTranscriptAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}
        ==>
        ={glob H, res} /\
        ROMInternalTranscriptAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        public_key_of_secret haetae_mode
          ROMInternalTranscriptAsNMA.sk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        RealSigningPaperSimSampler.pk_current{2} =
          ROMInternalTranscriptAsNMA.pk_current{1} /\
        RealSigningPaperSimSampler.sk_current{2} =
          ROMInternalTranscriptAsNMA.sk_current{1} /\
        ROMInternalTranscriptAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}).
+ by apply adversary_rom_internal_real_signing_paper_sim_nma.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />; rewrite /keygen_internal /secret_key_of_seed
                    /public_key_of_secret.
qed.

end section ROMInternalTranscriptRealSigningPaperSimNMA.

section ROMInternalTranscriptROSigningAttemptPaperSimNMA.

declare module H <: SIG.Oracle {-ROMInternalTranscriptPaperSimAsNMA,
                                -RealSigningPaperSimSampler,
                                -ROSigningAttemptPaperSimSampler}.
declare module A <: SIG.Adversary {-H, -ROMInternalTranscriptPaperSimAsNMA,
                                   -RealSigningPaperSimSampler,
                                   -ROSigningAttemptPaperSimSampler}.

equiv real_signing_ro_attempt_paper_sim_nma_oracle :
  ROMInternalTranscriptPaperSimAsNMA
    (A, RealSigningPaperSimSampler(H), H).O.sign ~
  ROMInternalTranscriptPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(H), H).O.sign :
    ={glob H, arg} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      ROSigningAttemptPaperSimSampler.pk_current{2} /\
    RealSigningPaperSimSampler.sk_current{1} =
      ROSigningAttemptPaperSimSampler.sk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        RealSigningPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      ROSigningAttemptPaperSimSampler.pk_current{2} /\
    RealSigningPaperSimSampler.sk_current{1} =
      ROSigningAttemptPaperSimSampler.sk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        RealSigningPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc.
inline RealSigningPaperSimSampler(H).sample
       ROSigningAttemptPaperSimSampler(H).sample.
inline RealSigningPaperSimSampler(H).sample_with_seed
       ROSigningAttemptPaperSimSampler(H).sample_with_seed.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
by auto => />; smt(paper_sim_sample_from_rejection_attempt_of_coinsE).
qed.

equiv adversary_real_signing_ro_attempt_paper_sim_nma :
  A(H, ROMInternalTranscriptPaperSimAsNMA
      (A, RealSigningPaperSimSampler(H), H).O).forge ~
  A(H, ROMInternalTranscriptPaperSimAsNMA
      (A, ROSigningAttemptPaperSimSampler(H), H).O).forge :
    ={glob H, glob A, arg} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      ROSigningAttemptPaperSimSampler.pk_current{2} /\
    RealSigningPaperSimSampler.sk_current{1} =
      ROSigningAttemptPaperSimSampler.sk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        RealSigningPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      ROSigningAttemptPaperSimSampler.pk_current{2} /\
    RealSigningPaperSimSampler.sk_current{1} =
      ROSigningAttemptPaperSimSampler.sk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        RealSigningPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc
  (={glob H} /\
   ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
     ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
   RealSigningPaperSimSampler.pk_current{1} =
     ROSigningAttemptPaperSimSampler.pk_current{2} /\
   RealSigningPaperSimSampler.sk_current{1} =
     ROSigningAttemptPaperSimSampler.sk_current{2} /\
   RealSigningPaperSimSampler.pk_current{1} =
     public_key_of_secret haetae_mode
       RealSigningPaperSimSampler.sk_current{1} /\
   ROMInternalTranscriptPaperSimAsNMA.queries{1} =
     ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
   ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
     ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
   ROMInternalTranscriptPaperSimAsNMA.records{1} =
     ROMInternalTranscriptPaperSimAsNMA.records{2}) => //.
+ move=> />.
+ by sim.
+ proc*.
  call real_signing_ro_attempt_paper_sim_nma_oracle.
  by auto => />.
qed.

lemma rom_internal_nma_real_signing_ro_attempt_paper_sim_exact &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] =
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res].
proof.
byequiv (: ={glob H, glob A} ==> ={res}) => //.
proc.
inline HAETAE(H).verify
       HAETAE(H).kg
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H), H).forge
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H), H).forge
       RealSigningPaperSimSampler(H).init
       ROSigningAttemptPaperSimSampler(H).init.
wp.
call (_: ={glob H, glob A, arg} /\
        ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        RealSigningPaperSimSampler.pk_current{1} =
          ROSigningAttemptPaperSimSampler.pk_current{2} /\
        RealSigningPaperSimSampler.sk_current{1} =
          ROSigningAttemptPaperSimSampler.sk_current{2} /\
        RealSigningPaperSimSampler.pk_current{1} =
          public_key_of_secret haetae_mode
            RealSigningPaperSimSampler.sk_current{1} /\
        ROMInternalTranscriptPaperSimAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptPaperSimAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}
        ==>
        ={glob H, res} /\
        ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        RealSigningPaperSimSampler.pk_current{1} =
          ROSigningAttemptPaperSimSampler.pk_current{2} /\
        RealSigningPaperSimSampler.sk_current{1} =
          ROSigningAttemptPaperSimSampler.sk_current{2} /\
        RealSigningPaperSimSampler.pk_current{1} =
          public_key_of_secret haetae_mode
            RealSigningPaperSimSampler.sk_current{1} /\
        ROMInternalTranscriptPaperSimAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptPaperSimAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}).
+ by apply adversary_real_signing_ro_attempt_paper_sim_nma.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />; rewrite /keygen_internal /secret_key_of_seed
                    /public_key_of_secret.
qed.

end section ROMInternalTranscriptROSigningAttemptPaperSimNMA.

op structural_to_exact_hyperball_paper_sample_loss_obligation
   (md : mode) : bool =
  forall (sk : skey) (m : message) (ctx : context)
         (p : paper_sim_signature_sample -> bool),
    mu (dsigning_attempt_state md sk m ctx)
      (fun st => p (paper_sim_sample_from_rejection_attempt st)) <=
    mu (dexact_hyperball_signing_attempt_state md sk m ctx)
      (fun st => p (paper_sim_sample_from_rejection_attempt st)) +
      rejection_sampling_loss_term.

lemma concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_fresh_loss
    seed_coins m ctx (p : paper_sim_signature_sample -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m{m} =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss fresh sk_eq.
have signing_le :
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] <=
    mu (dsigning_attempt_state haetae_mode
          ROSigningAttemptPaperSimSampler.sk_current{m} m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st)).
+ byphoare
    (concrete_ro_signing_attempt_sample_with_seed_fresh_structural_le
       seed_coins ROSigningAttemptPaperSimSampler.sk_current{m} m ctx p) => //.
have exact_eq :=
  concrete_ro_exact_hyperball_sample_with_seed_exact_pr
    seed_coins m ctx p &m.
have sample_step :=
    sample_loss ROSigningAttemptPaperSimSampler.sk_current{m} m ctx p.
by smt().
qed.

lemma concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_loss
    seed_coins m ctx (p : paper_sim_signature_sample -> bool)
    hash_qs sampler_qs bad &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered HAETAE_RO.FRO.m{m} hash_qs sampler_qs =>
  ! (bad \/
     sampler_expand_query seed_coins \in hash_qs \/
     sampler_expand_query seed_coins \in sampler_qs) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq.
apply (concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_fresh_loss
  seed_coins m ctx p &m sample_loss _ sk_eq).
by apply (sampler_rom_covered_fresh_after_clean_seed
  seed_coins HAETAE_RO.FRO.m{m} hash_qs sampler_qs bad).
qed.

lemma concrete_budgeted_o_sign_sample_with_seed_clean_loss_surface
    seed_coins m ctx (p : paper_sim_signature_sample -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq.
by apply
  (concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_loss
     seed_coins m ctx p
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m}
     &m).
qed.

(* Restricted sampler/lazy-ROM lifting.
   These lemmas are machine-checked only for stateful sampler postconditions Q
   that can be sandwiched around a pure returned-sample predicate p for the
   actual left and right sampler executions.  The framing premises are the
   formal place where suffix-measurability and ROM-table/counter preservation
   must be proved; the lemmas below do not claim an arbitrary coupling for
   predicates that inspect the sampler-expand ROM entry in a way that exploits
   the attempt-side correlation. *)
lemma concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_fresh_restricted_state_loss
    seed_coins m ctx
    (Q : paper_sim_signature_sample -> glob HAETAE_RO.FRO -> bool)
    (p : paper_sim_signature_sample -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m{m} =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] =>
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss fresh sk_eq left_frame right_frame.
have sample_loss_p :=
  concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_fresh_loss
    seed_coins m ctx p &m sample_loss fresh sk_eq.
by smt().
qed.

lemma concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_restricted_state_loss
    seed_coins m ctx
    (Q : paper_sim_signature_sample -> glob HAETAE_RO.FRO -> bool)
    (p : paper_sim_signature_sample -> bool)
    hash_qs sampler_qs bad &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered HAETAE_RO.FRO.m{m} hash_qs sampler_qs =>
  ! (bad \/
     sampler_expand_query seed_coins \in hash_qs \/
     sampler_expand_query seed_coins \in sampler_qs) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] =>
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq left_frame right_frame.
have sample_loss_p :=
  concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_loss
    seed_coins m ctx p hash_qs sampler_qs bad &m
    sample_loss covered clean sk_eq.
by smt().
qed.

lemma concrete_budgeted_o_sign_sample_with_seed_clean_restricted_state_loss_surface
    seed_coins m ctx
    (Q : paper_sim_signature_sample -> glob HAETAE_RO.FRO -> bool)
    (p : paper_sim_signature_sample -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] =>
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq left_frame right_frame.
have sample_loss_p :=
  concrete_budgeted_o_sign_sample_with_seed_clean_loss_surface
    seed_coins m ctx p &m sample_loss covered clean sk_eq.
by smt().
qed.

lemma concrete_budgeted_o_sign_old_log_sample_with_seed_clean_loss_surface
    seed_coins m ctx (p : paper_sim_signature_sample -> bool)
    old_hash_qs old_sampler_qs old_bad &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  old_hash_qs =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} =>
  old_sampler_qs =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  old_bad =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} =>
  sampler_rom_covered HAETAE_RO.FRO.m{m} old_hash_qs old_sampler_qs =>
  ! (old_bad \/
     sampler_expand_query seed_coins \in old_hash_qs \/
     sampler_expand_query seed_coins \in old_sampler_qs) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss old_hash_eq old_sampler_eq old_bad_eq
        covered clean sk_eq.
subst old_hash_qs.
subst old_sampler_qs.
subst old_bad.
by apply
  (concrete_budgeted_o_sign_sample_with_seed_clean_loss_surface
     seed_coins m ctx p &m).
qed.

lemma concrete_budgeted_o_sign_old_log_signature_from_sample_clean_loss_surface
    seed_coins m ctx (p : signature -> bool)
    old_hash_qs old_sampler_qs old_bad &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  old_hash_qs =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} =>
  old_sampler_qs =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  old_bad =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} =>
  sampler_rom_covered HAETAE_RO.FRO.m{m} old_hash_qs old_sampler_qs =>
  ! (old_bad \/
     sampler_expand_query seed_coins \in old_hash_qs \/
     sampler_expand_query seed_coins \in old_sampler_qs) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode
            ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m}
            m ctx res)] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode
            ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m}
            m ctx res)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss old_hash_eq old_sampler_eq old_bad_eq
        covered clean sk_eq.
by apply
  (concrete_budgeted_o_sign_old_log_sample_with_seed_clean_loss_surface
     seed_coins m ctx
     (fun smp => p (paper_sim_signature haetae_mode
                     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m}
                     m ctx smp))
     old_hash_qs old_sampler_qs old_bad &m).
qed.

lemma concrete_budgeted_o_sign_old_log_signature_clean_event_loss_surface
    seed_coins m ctx (p : signature -> bool)
    old_hash_qs old_sampler_qs old_bad &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  old_hash_qs =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} =>
  old_sampler_qs =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  old_bad =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} =>
  sampler_rom_covered HAETAE_RO.FRO.m{m} old_hash_qs old_sampler_qs =>
  ! (old_bad \/
     sampler_expand_query seed_coins \in old_hash_qs \/
     sampler_expand_query seed_coins \in old_sampler_qs) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode
            ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m}
            m ctx res) /\
       ! (old_bad \/
          sampler_expand_query seed_coins \in old_hash_qs \/
          sampler_expand_query seed_coins \in old_sampler_qs)] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode
            ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m}
            m ctx res)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss old_hash_eq old_sampler_eq old_bad_eq
        covered clean sk_eq.
rewrite clean /=.
by apply
  (concrete_budgeted_o_sign_old_log_signature_from_sample_clean_loss_surface
     seed_coins m ctx p old_hash_qs old_sampler_qs old_bad &m).
qed.

lemma concrete_frozen_old_log_sample_clean_event_loss_surface
    seed_coins m ctx (p : paper_sim_signature_sample -> bool)
    old_hash_qs old_sampler_qs old_bad &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered HAETAE_RO.FRO.m{m} old_hash_qs old_sampler_qs =>
  ! (old_bad \/
     sampler_expand_query seed_coins \in old_hash_qs \/
     sampler_expand_query seed_coins \in old_sampler_qs) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p res /\
       ! (old_bad \/
          sampler_expand_query seed_coins \in old_hash_qs \/
          sampler_expand_query seed_coins \in old_sampler_qs)] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m : p res] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq.
rewrite clean /=.
by apply
  (concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_loss
     seed_coins m ctx p old_hash_qs old_sampler_qs old_bad &m).
qed.

lemma concrete_frozen_old_log_signature_clean_event_loss_surface
    seed_coins m ctx pk (p : signature -> bool)
    old_hash_qs old_sampler_qs old_bad &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered HAETAE_RO.FRO.m{m} old_hash_qs old_sampler_qs =>
  ! (old_bad \/
     sampler_expand_query seed_coins \in old_hash_qs \/
     sampler_expand_query seed_coins \in old_sampler_qs) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res) /\
       ! (old_bad \/
          sampler_expand_query seed_coins \in old_hash_qs \/
          sampler_expand_query seed_coins \in old_sampler_qs)] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq.
rewrite clean /=.
by apply
  (concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_loss
     seed_coins m ctx
     (fun smp => p (paper_sim_signature haetae_mode pk m ctx smp))
      old_hash_qs old_sampler_qs old_bad &m).
qed.

lemma concrete_frozen_old_log_self_logged_signature_clean_event_loss_surface
    seed_coins m ctx pk (p : signature -> bool)
    old_hash_qs old_sampler_qs old_bad &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered HAETAE_RO.FRO.m{m} old_hash_qs old_sampler_qs =>
  ! (old_bad \/
     sampler_expand_query seed_coins \in old_hash_qs \/
     sampler_expand_query seed_coins \in old_sampler_qs) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m{m} /\
  sampler_rom_covered HAETAE_RO.FRO.m{m} old_hash_qs
    (sampler_expand_query seed_coins :: old_sampler_qs) /\
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res) /\
       ! (old_bad \/
          sampler_expand_query seed_coins \in old_hash_qs \/
          sampler_expand_query seed_coins \in old_sampler_qs)] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq.
have boundary :=
  sampler_rom_covered_old_log_clean_boundary
    seed_coins HAETAE_RO.FRO.m{m}
    old_hash_qs old_sampler_qs old_bad covered clean.
split.
+ by smt().
split.
+ by smt().
by apply
  (concrete_frozen_old_log_signature_clean_event_loss_surface
     seed_coins m ctx pk p old_hash_qs old_sampler_qs old_bad &m).
qed.

lemma concrete_budgeted_self_logged_signature_clean_event_loss_surface
    seed_coins m ctx pk (p : signature -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m{m} /\
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    (sampler_expand_query seed_coins ::
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) /\
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res) /\
       ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m})] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq.
by apply
  (concrete_frozen_old_log_self_logged_signature_clean_event_loss_surface
     seed_coins m ctx pk p
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m}
     &m).
qed.

lemma concrete_lazy_rom_get_lossless :
  islossless HAETAE_RO.FRO.get.
proof.
proc.
wp.
rnd.
by auto; smt(ro_output_distribution_lossless).
qed.

lemma structural_attempt_exact_hyperball_paper_sample_one_step_loss
  sk m ctx (p : paper_sim_signature_sample -> bool) :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  phoare[StructuralAttemptPaperSample.sample :
    arg = (sk, m, ctx) ==> p res] <=
  (mu (dexact_hyperball_signing_attempt_state haetae_mode sk m ctx)
     (fun st => p (paper_sim_sample_from_rejection_attempt st)) +
     rejection_sampling_loss_term).
proof.
move=> sample_loss.
bypr=> &m0 argE.
byphoare (_: arg = (sk, m, ctx) ==> p res) => //.
proc.
wp.
rnd.
auto => />.
move=> />.
by apply sample_loss.
by rewrite argE.
qed.

lemma exact_hyperball_paper_sample_one_step_upper
  sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ExactHyperballPaperSample.sample :
    arg = (sk, m, ctx) ==> p res] <=
  (mu (dexact_hyperball_signing_attempt_state haetae_mode sk m ctx)
     (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
bypr=> &m0 argE.
byphoare (_: arg = (sk, m, ctx) ==> p res) => //.
proc.
wp.
rnd.
by auto.
by rewrite argE.
qed.

section ROMInternalTranscriptROSigningAttemptExactHyperballPaperSimNMA.

declare module H <: SIG.Oracle {-ROMInternalTranscriptPaperSimAsNMA,
                                -ROMInternalTranscriptBudgetedPaperSimAsNMA,
                                -ROSigningAttemptPaperSimSampler,
                                -ROExactHyperballPaperSimSampler}.
declare module A <: SIG.Adversary {-H, -ROMInternalTranscriptPaperSimAsNMA,
                                   -ROMInternalTranscriptBudgetedPaperSimAsNMA,
                                   -ROSigningAttemptPaperSimSampler,
                                   -ROExactHyperballPaperSimSampler}.

(* Non-vacuous boundary for the future lazy-ROM lifting proof.  The marginal
   sampler obligation is the per-signing-call input; the NMA-level premise is
   the result that must be produced by the oracle/adversary lifting argument. *)
lemma rom_internal_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_paper_sample_lifting &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term.
proof.
by move=> _ lifted.
qed.

lemma rom_internal_budgeted_ro_signing_attempt_signing_call_loss_bound &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       0 < ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count] <=
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
have call_event_le1 :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       0 < ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count] <= 1%r
  by smt(mu_bounded).
have budgeted_loss_ge1 :
  1%r <= rom_signature_query_budget * rejection_sampling_loss_term.
+ rewrite /rom_signature_query_budget /signature_query_count
          /signature_query_budget_count.
  smt(rejection_sampling_loss_term_ge1).
by smt().
qed.

lemma rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_paper_sample_lifting &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> sample_loss.
have checked_one_step :
  forall (sk0 : skey) (m0 : message) (ctx0 : context)
         (p0 : paper_sim_signature_sample -> bool),
    phoare[StructuralAttemptPaperSample.sample :
      arg = (sk0, m0, ctx0) ==> p0 res] <=
    (mu (dexact_hyperball_signing_attempt_state haetae_mode sk0 m0 ctx0)
       (fun st => p0 (paper_sim_sample_from_rejection_attempt st)) +
       rejection_sampling_loss_term).
+ move=> sk0 m0 ctx0 p0.
  by apply structural_attempt_exact_hyperball_paper_sample_one_step_loss.
have left_le1 :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <= 1%r
  by smt(mu_bounded).
have right_ge0 :
  0%r <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res]
  by smt(mu_bounded).
have budgeted_loss_ge1 :
  1%r <= rom_signature_query_budget * rejection_sampling_loss_term.
+ rewrite /rom_signature_query_budget /signature_query_count
          /signature_query_budget_count.
  smt(rejection_sampling_loss_term_ge1).
by smt().
qed.

lemma rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_clean_lifting &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term +
    rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound).
proof.
move=> clean_lifting.
apply (ler_trans
  (Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       (res /\
        ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery) \/
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery])).
+ by rewrite Pr[mu_sub]; smt.
apply (ler_trans
  (Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] +
   Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery])).
+ by rewrite Pr[mu_or]; smt.
apply (ler_trans
  ((Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
      rom_signature_query_budget * rejection_sampling_loss_term) +
   Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery])).
+ by apply ler_add; [apply clean_lifting | rewrite lerr].
apply ler_add.
+ by rewrite lerr.
by apply (budgeted_paper_sim_sampler_bad_prequery_nma_fel_bound
     H A (ROSigningAttemptPaperSimSampler(H)) &m).
qed.

lemma rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> sample_loss.
have budgeted_lifting :=
  rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_paper_sample_lifting
    &m sample_loss.
have clean_restrict :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res]
  by smt(mu_sub).
by smt().
qed.

lemma rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_checked_clean_lifting &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term +
    rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound).
proof.
move=> sample_loss.
apply
  (rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_clean_lifting
     &m).
by apply
  (rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting
     &m).
qed.

lemma rom_internal_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_budgeted_lifting &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] =>
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> attempt_unbudgeted_to_budgeted exact_budgeted_to_unbudgeted
        sample_loss.
have hbudgeted :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
+ by apply
     (rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_paper_sample_lifting
        &m).
by smt.
qed.

lemma rom_internal_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_budgeted_checked_clean_lifting &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] =>
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term +
    rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound).
proof.
move=> attempt_unbudgeted_to_budgeted exact_budgeted_to_unbudgeted
        sample_loss.
have hbudgeted :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term +
    rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound).
+ by apply
     (rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_checked_clean_lifting
        &m).
by smt.
qed.

(* Coarse fallback.  The theorem below is machine-checked, but it is not a
   non-vacuous sampler-comparison proof: it closes from probability boundedness
   and rejection_sampling_loss_term_ge1.  A replacement should prove the same
   NMA-level inequality from structural_to_exact_hyperball_paper_sample_loss_obligation
   by lifting the one-call push-forward through the signing oracle and adversary.

   Missing non-vacuous proof obligations:
   - unbudgeted NMA lifting:
       Pr[UF_NMA(... ROSigningAttemptPaperSimSampler ...).main : res]
       <= Pr[UF_NMA(... ROExactHyperballPaperSimSampler ...).main : res]
          + rejection_sampling_loss_term
     without using rejection_sampling_loss_term_ge1;
   - or a budgeted clean-event route:
       Pr[UF_NMA(... Budgeted ... ROSigningAttempt ...).main :
            res /\ !sampler_bad_prequery]
       <= Pr[UF_NMA(... Budgeted ... ROExactHyperball ...).main : res]
          + rom_signature_query_budget * rejection_sampling_loss_term,
     plus exact/monotone budgeted-to-unbudgeted adapters.

   Existing one-call facts such as
   concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_fresh_loss
   and the lazy-ROM sampler law supply the per-call input, not this NMA-level
   adaptive lifting theorem. *)
lemma rom_internal_nma_ro_signing_attempt_ro_exact_hyperball_loss_bound &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term.
proof.
have left_le1 :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <= 1%r
  by smt(mu_bounded).
have right_ge0 :
  0%r <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res]
  by smt(mu_bounded).
have loss_ge1 : 1%r <= rejection_sampling_loss_term.
+ by apply rejection_sampling_loss_term_ge1.
by smt().
qed.

end section ROMInternalTranscriptROSigningAttemptExactHyperballPaperSimNMA.

section ConcreteROMInternalTranscriptROSigningAttemptExactHyperballPaperSimNMA.

declare module A <: SIG.Adversary {-HAETAE_RO.FRO,
                                   -ROMInternalTranscriptPaperSimAsNMA,
                                   -ROMInternalTranscriptBudgetedPaperSimAsNMA,
                                   -ROSigningAttemptPaperSimSampler,
                                   -ROExactHyperballPaperSimSampler}.

local clone Hybrid as BudgetedSignHybrid with
  type input <- SIG.query,
  type output <- signature,
  type inleaks <- ro_query,
  type outleaks <- ro_output,
  type outputA <- bool,
  op q <- signature_query_budget_count
proof q_ge0 by rewrite /signature_query_budget_count
proof *.

local module BudgetedSignHybridOrclb : BudgetedSignHybrid.Orclb = {
  proc leaks(q : ro_query) : ro_output = {
    var y : ro_output;

    y <@ ROMInternalTranscriptBudgetedPaperSimAsNMA
           (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
            HAETAE_RO.FRO).AH.get(q);
    return y;
  }

  proc orclL(qry : SIG.query) : signature = {
    var m : message;
    var ctx : context;
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;
    var highbits : polyveck;
    var lowbits : poly;
    var mu : crh;
    var ro_y : ro_output;
    var sig : signature;
    var tr : transcript;
    var old_adversary_hash_queries : ro_query list;
    var old_sampler_expand_queries : ro_query list;
    var old_sampler_bad_prequery : bool;

    m <- qry.`1;
    ctx <- qry.`2;
    old_adversary_hash_queries <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries;
    old_sampler_expand_queries <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries;
    old_sampler_bad_prequery <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery;
    seed_coins <$ drandom_coins;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery <-
      old_sampler_bad_prequery \/
      sampler_expand_query seed_coins \in old_adversary_hash_queries \/
      sampler_expand_query seed_coins \in old_sampler_expand_queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries <-
      sampler_expand_query seed_coins :: old_sampler_expand_queries;
    smp <@ ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
      (seed_coins, m, ctx);
    ro_y <@ HAETAE_RO.FRO.get
      (message_hash_query
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current ctx m);
    mu <- ro_message_hash ro_y;
    highbits <- paper_sim_commitment_highbits haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    lowbits <- paper_sim_commitment_lowbits haetae_mode smp;
    ro_y <@ HAETAE_RO.FRO.get
      (challenge_hash_query haetae_mode highbits lowbits mu);
    sig <- paper_sim_signature haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    tr <- transcript_of_signature haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx sig;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries <-
      (m, ctx) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts <-
      tr :: ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records <-
      (m, ctx, sig, tr) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.records;
    return sig;
  }

  proc orclR(qry : SIG.query) : signature = {
    var m : message;
    var ctx : context;
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;
    var highbits : polyveck;
    var lowbits : poly;
    var mu : crh;
    var ro_y : ro_output;
    var sig : signature;
    var tr : transcript;
    var old_adversary_hash_queries : ro_query list;
    var old_sampler_expand_queries : ro_query list;
    var old_sampler_bad_prequery : bool;

    m <- qry.`1;
    ctx <- qry.`2;
    old_adversary_hash_queries <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries;
    old_sampler_expand_queries <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries;
    old_sampler_bad_prequery <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery;
    seed_coins <$ drandom_coins;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery <-
      old_sampler_bad_prequery \/
      sampler_expand_query seed_coins \in old_adversary_hash_queries \/
      sampler_expand_query seed_coins \in old_sampler_expand_queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries <-
      sampler_expand_query seed_coins :: old_sampler_expand_queries;
    smp <@ ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
      (seed_coins, m, ctx);
    ro_y <@ HAETAE_RO.FRO.get
      (message_hash_query
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current ctx m);
    mu <- ro_message_hash ro_y;
    highbits <- paper_sim_commitment_highbits haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    lowbits <- paper_sim_commitment_lowbits haetae_mode smp;
    ro_y <@ HAETAE_RO.FRO.get
      (challenge_hash_query haetae_mode highbits lowbits mu);
    sig <- paper_sim_signature haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    tr <- transcript_of_signature haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx sig;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries <-
      (m, ctx) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts <-
      tr :: ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records <-
      (m, ctx, sig, tr) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.records;
    return sig;
  }
}.

local module BudgetedSignHybridGame
  (Ob : BudgetedSignHybrid.Orclb)
  (LR : BudgetedSignHybrid.Orcl) = {
  module AH = {
    proc get(q : ro_query) : ro_output = {
      var y : ro_output;

      y <@ Ob.leaks(q);
      return y;
    }
  }

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var sig : signature;
      var smp : paper_sim_signature_sample;

      if (ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <
            signature_query_budget_count) {
        if (ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count = 0) {
          ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <- 1;
        } else {
          ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <-
            signature_query_budget_count;
        }
        sig <@ LR.orcl((m, ctx));
      } else {
        ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <-
          signature_query_budget_count;
        smp <- paper_sim_abort_fallback_sample haetae_mode;
        sig <- paper_sim_signature haetae_mode
          ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
      }
      return sig;
    }
  }

  module Adv = A(AH, O)

  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    HAETAE_RO.FRO.init();
    (pk, sk) <@ HAETAE(HAETAE_RO.FRO).kg();
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current <- pk;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries <- [];
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts <- [];
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records <- [];
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count <- 0;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <- 0;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries <- [];
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries <- [];
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery <- false;
    ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).init(pk);
    ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).init(pk);
    (m, ctx, sig) <@ Adv.forge(pk);
    ok <@ HAETAE(HAETAE_RO.FRO).verify(pk, m, ctx, sig);
    return ok;
  }
}.

local lemma budgeted_sign_hybrid_counted_sign_preserves_count_bound
    (O <: BudgetedSignHybrid.Orcl
          {-BudgetedSignHybrid.Count, -BudgetedSignHybridGame}) :
  hoare[BudgetedSignHybridGame(
          BudgetedSignHybridOrclb, BudgetedSignHybrid.OrclCount(O)).O.sign :
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc.
if.
+ inline BudgetedSignHybrid.OrclCount(O).orcl BudgetedSignHybrid.Count.incr.
  wp.
  call (_: true).
  by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                      /signature_query_budget_count; smt.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /signature_query_budget_count; smt.
qed.

local lemma budgeted_sign_hybrid_fro_get_preserves_count_bound :
  hoare[HAETAE_RO.FRO.get :
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc.
wp.
rnd.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /signature_query_budget_count;
  smt(ro_output_distribution_lossless).
qed.

local lemma budgeted_sign_hybrid_rom_budgeted_hash_get_preserves_count_bound :
  hoare[ROMInternalTranscriptBudgetedPaperSimAsNMA
          (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
           HAETAE_RO.FRO).AH.get :
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc.
if.
+ wp.
  call budgeted_sign_hybrid_fro_get_preserves_count_bound.
  by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                      /signature_query_budget_count;
    smt.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /signature_query_budget_count; smt.
qed.

local lemma budgeted_sign_hybrid_orclb_leaks_preserves_count_bound :
  hoare[BudgetedSignHybridOrclb.leaks :
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc.
call budgeted_sign_hybrid_rom_budgeted_hash_get_preserves_count_bound.
by auto.
qed.

local lemma budgeted_sign_hybrid_hash_get_preserves_count_bound
    (O <: BudgetedSignHybrid.Orcl
          {-BudgetedSignHybrid.Count, -BudgetedSignHybridGame}) :
  hoare[BudgetedSignHybridGame(
          BudgetedSignHybridOrclb, BudgetedSignHybrid.OrclCount(O)).AH.get :
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc.
call budgeted_sign_hybrid_orclb_leaks_preserves_count_bound.
by auto.
qed.

local lemma budgeted_sign_hybrid_adversary_preserves_count_bound
    (O <: BudgetedSignHybrid.Orcl
          {-BudgetedSignHybrid.Count, -BudgetedSignHybridGame}) :
  hoare[BudgetedSignHybridGame(
          BudgetedSignHybridOrclb, BudgetedSignHybrid.OrclCount(O)).Adv.forge :
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count ==>
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc
  (0 <= BudgetedSignHybrid.Count.c /\
   BudgetedSignHybrid.Count.c <=
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
   budgeted_paper_sim_signing_count_discipline
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count) => //.
+ move=> />.
+ proc*.
  call (budgeted_sign_hybrid_hash_get_preserves_count_bound O).
  by auto.
proc*.
call (budgeted_sign_hybrid_counted_sign_preserves_count_bound O).
by auto.
qed.

local lemma budgeted_sign_hybrid_game_main_preserves_count_bound
    (O <: BudgetedSignHybrid.Orcl
          {-BudgetedSignHybrid.Count, -BudgetedSignHybridGame}) :
  hoare[BudgetedSignHybridGame(
          BudgetedSignHybridOrclb, BudgetedSignHybrid.OrclCount(O)).main :
    BudgetedSignHybrid.Count.c = 0 ==>
    0 <= BudgetedSignHybrid.Count.c /\
    BudgetedSignHybrid.Count.c <=
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count].
proof.
proc.
wp.
inline HAETAE(HAETAE_RO.FRO).verify.
wp.
call (budgeted_sign_hybrid_adversary_preserves_count_bound O).
inline ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).init.
inline ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).init.
wp.
inline HAETAE(HAETAE_RO.FRO).kg.
wp.
inline HAETAE_RO.FRO.get.
wp.
rnd.
wp.
rnd.
inline HAETAE_RO.FRO.init.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /signature_query_budget_count;
  smt(seed_distribution_lossless ro_output_distribution_lossless).
qed.

local lemma budgeted_sign_hybrid_A_call
    (O <: BudgetedSignHybrid.Orcl
          {-BudgetedSignHybrid.Count, -BudgetedSignHybridGame}) :
  hoare[
    BudgetedSignHybrid.Orcln
      (BudgetedSignHybridGame(BudgetedSignHybridOrclb), O).main :
    true ==> BudgetedSignHybrid.Count.c <= signature_query_budget_count].
proof.
proc.
wp.
call (budgeted_sign_hybrid_game_main_preserves_count_bound O).
inline BudgetedSignHybrid.Count.init.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /signature_query_budget_count; smt.
qed.

(* Concrete Hybrid_restr implementation spike.
   BudgetedSignHybridOrclb and BudgetedSignHybridGame type-check the first
   intended encoding, and budgeted_sign_hybrid_A_call proves its query-count
   side condition.  Direct use of BudgetedSignHybrid.Hybrid_restr is nevertheless
   blocked by a module/global restriction: BudgetedSignHybridGame and
   BudgetedSignHybridOrclb intentionally share HAETAE_RO.FRO.m, sampler state,
   and the ROMInternalTranscriptBudgetedPaperSimAsNMA globals.

   The disjoint wrapper below tests the narrow refactor suggested by that
   failure.  Setup and AH.get are exposed through Orclb.leaks, orclL/orclR own
   the shared ROM/sampler/transcript state, and the AdvOrclb game owns only its
   local hybrid budget gate. *)

type budgeted_sign_hybrid_leak_query =
  [ BudgetedSignHybridSetup
  | BudgetedSignHybridHash of ro_query ].

type budgeted_sign_hybrid_leak_output =
  [ BudgetedSignHybridSetupOut of (pkey * skey)
  | BudgetedSignHybridHashOut of ro_output ].

op budgeted_sign_hybrid_default_keypair : pkey * skey =
  keygen_internal haetae_mode [].

op budgeted_sign_hybrid_query_ro
   (q : budgeted_sign_hybrid_leak_query) : ro_query =
  with q = BudgetedSignHybridHash ro_q => ro_q
  with q = BudgetedSignHybridSetup => matrix_expand_query haetae_mode [].

op budgeted_sign_hybrid_output_ro
   (y : budgeted_sign_hybrid_leak_output) : ro_output =
  with y = BudgetedSignHybridHashOut ro_y => ro_y
  with y = BudgetedSignHybridSetupOut _ => ro_output_zero.

op budgeted_sign_hybrid_output_keypair
   (y : budgeted_sign_hybrid_leak_output) : pkey * skey =
  with y = BudgetedSignHybridSetupOut kp => kp
  with y = BudgetedSignHybridHashOut _ => budgeted_sign_hybrid_default_keypair.

local clone Hybrid as BudgetedSignHybridDisjoint with
  type input <- SIG.query,
  type output <- signature,
  type inleaks <- budgeted_sign_hybrid_leak_query,
  type outleaks <- budgeted_sign_hybrid_leak_output,
  type outputA <- bool,
  op q <- signature_query_budget_count
proof q_ge0 by rewrite /signature_query_budget_count
proof *.

local module BudgetedSignHybridDisjointOrclb
  : BudgetedSignHybridDisjoint.Orclb = {
  proc leaks(q : budgeted_sign_hybrid_leak_query)
      : budgeted_sign_hybrid_leak_output = {
    var y : budgeted_sign_hybrid_leak_output;
    var ro_q : ro_query;
    var ro_y : ro_output;
    var pk : pkey;
    var sk : skey;

    if (q = BudgetedSignHybridSetup) {
      HAETAE_RO.FRO.init();
      (pk, sk) <@ HAETAE(HAETAE_RO.FRO).kg();
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries <- [];
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries <- [];
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery <- false;
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count <- 0;
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <- 0;
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current <- pk;
      ROMInternalTranscriptBudgetedPaperSimAsNMA.queries <- [];
      ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts <- [];
      ROMInternalTranscriptBudgetedPaperSimAsNMA.records <- [];
      ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).init(pk);
      ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).init(pk);
      y <- BudgetedSignHybridSetupOut (pk, sk);
    } else {
      ro_q <- budgeted_sign_hybrid_query_ro q;
      ro_y <@
        ROMInternalTranscriptBudgetedPaperSimAsNMA
          (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
              HAETAE_RO.FRO).AH.get(ro_q);
      y <- BudgetedSignHybridHashOut ro_y;
    }

    return y;
  }

  proc orclL(qry : SIG.query) : signature = {
    var m : message;
    var ctx : context;
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;
    var highbits : polyveck;
    var lowbits : poly;
    var mu : crh;
    var ro_y : ro_output;
    var sig : signature;
    var tr : transcript;
    var old_adversary_hash_queries : ro_query list;
    var old_sampler_expand_queries : ro_query list;
    var old_sampler_bad_prequery : bool;

    m <- qry.`1;
    ctx <- qry.`2;
    if (ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count = 0) {
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <- 1;
    } else {
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <-
        signature_query_budget_count;
    }
    old_adversary_hash_queries <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries;
    old_sampler_expand_queries <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries;
    old_sampler_bad_prequery <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery;
    seed_coins <$ drandom_coins;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery <-
      old_sampler_bad_prequery \/
      sampler_expand_query seed_coins \in old_adversary_hash_queries \/
      sampler_expand_query seed_coins \in old_sampler_expand_queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries <-
      sampler_expand_query seed_coins :: old_sampler_expand_queries;
    smp <@ ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
      (seed_coins, m, ctx);
    ro_y <@ HAETAE_RO.FRO.get
      (message_hash_query
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current ctx m);
    mu <- ro_message_hash ro_y;
    highbits <- paper_sim_commitment_highbits haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    lowbits <- paper_sim_commitment_lowbits haetae_mode smp;
    ro_y <@ HAETAE_RO.FRO.get
      (challenge_hash_query haetae_mode highbits lowbits mu);
    sig <- paper_sim_signature haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    tr <- transcript_of_signature haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx sig;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries <-
      (m, ctx) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts <-
      tr :: ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records <-
      (m, ctx, sig, tr) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.records;
    return sig;
  }

  proc orclR(qry : SIG.query) : signature = {
    var m : message;
    var ctx : context;
    var seed_coins : random_coins;
    var smp : paper_sim_signature_sample;
    var highbits : polyveck;
    var lowbits : poly;
    var mu : crh;
    var ro_y : ro_output;
    var sig : signature;
    var tr : transcript;
    var old_adversary_hash_queries : ro_query list;
    var old_sampler_expand_queries : ro_query list;
    var old_sampler_bad_prequery : bool;

    m <- qry.`1;
    ctx <- qry.`2;
    if (ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count = 0) {
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <- 1;
    } else {
      ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <-
        signature_query_budget_count;
    }
    old_adversary_hash_queries <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries;
    old_sampler_expand_queries <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries;
    old_sampler_bad_prequery <-
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery;
    seed_coins <$ drandom_coins;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery <-
      old_sampler_bad_prequery \/
      sampler_expand_query seed_coins \in old_adversary_hash_queries \/
      sampler_expand_query seed_coins \in old_sampler_expand_queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries <-
      sampler_expand_query seed_coins :: old_sampler_expand_queries;
    smp <@ ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
      (seed_coins, m, ctx);
    ro_y <@ HAETAE_RO.FRO.get
      (message_hash_query
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current ctx m);
    mu <- ro_message_hash ro_y;
    highbits <- paper_sim_commitment_highbits haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    lowbits <- paper_sim_commitment_lowbits haetae_mode smp;
    ro_y <@ HAETAE_RO.FRO.get
      (challenge_hash_query haetae_mode highbits lowbits mu);
    sig <- paper_sim_signature haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    tr <- transcript_of_signature haetae_mode
      ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx sig;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries <-
      (m, ctx) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts <-
      tr :: ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records <-
      (m, ctx, sig, tr) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.records;
    return sig;
  }
}.

type budgeted_sign_hybrid_disjoint_surface_result =
  bool * pkey * (message * context * signature).

op budgeted_sign_hybrid_disjoint_surface_ok
   (r : budgeted_sign_hybrid_disjoint_surface_result) : bool =
  r.`1.

op budgeted_sign_hybrid_disjoint_surface_pk
   (r : budgeted_sign_hybrid_disjoint_surface_result) : pkey =
  r.`2.

op budgeted_sign_hybrid_disjoint_surface_forgery
   (r : budgeted_sign_hybrid_disjoint_surface_result) :
  message * context * signature =
  r.`3.

local module BudgetedSignHybridDisjointGame
  (Ob : BudgetedSignHybridDisjoint.Orclb,
   LR : BudgetedSignHybridDisjoint.Orcl) = {
  var pk_current : pkey
  var signing_count : int

  module AH = {
    proc get(q : ro_query) : ro_output = {
      var y : budgeted_sign_hybrid_leak_output;
      var ro_y : ro_output;

      y <@ Ob.leaks(BudgetedSignHybridHash q);
      ro_y <- budgeted_sign_hybrid_output_ro y;
      return ro_y;
    }
  }

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var sig : signature;
      var smp : paper_sim_signature_sample;

      if (signing_count < signature_query_budget_count) {
        if (signing_count = 0) {
          signing_count <- 1;
        } else {
          signing_count <- signature_query_budget_count;
        }
        sig <@ LR.orcl((m, ctx));
      } else {
        signing_count <- signature_query_budget_count;
        smp <- paper_sim_abort_fallback_sample haetae_mode;
        sig <- paper_sim_signature haetae_mode pk_current m ctx smp;
      }
      return sig;
    }
  }

  module Adv = A(AH, O)

  proc main() : bool = {
    var setup_y : budgeted_sign_hybrid_leak_output;
    var kp : pkey * skey;
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    setup_y <@ Ob.leaks(BudgetedSignHybridSetup);
    kp <- budgeted_sign_hybrid_output_keypair setup_y;
    pk <- kp.`1;
    sk <- kp.`2;
    pk_current <- pk;
    signing_count <- 0;
    (m, ctx, sig) <@ Adv.forge(pk);
    ok <- verify_internal haetae_mode pk m ctx sig;
    return ok;
  }

  proc main_surface()
      : budgeted_sign_hybrid_disjoint_surface_result = {
    var setup_y : budgeted_sign_hybrid_leak_output;
    var kp : pkey * skey;
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;
    var r : budgeted_sign_hybrid_disjoint_surface_result;

    setup_y <@ Ob.leaks(BudgetedSignHybridSetup);
    kp <- budgeted_sign_hybrid_output_keypair setup_y;
    pk <- kp.`1;
    sk <- kp.`2;
    pk_current <- pk;
    signing_count <- 0;
    (m, ctx, sig) <@ Adv.forge(pk);
    ok <- verify_internal haetae_mode pk m ctx sig;
    r <- (ok, pk, (m, ctx, sig));
    return r;
  }
}.

local lemma budgeted_sign_hybrid_disjoint_counted_sign_preserves_count_bound
    (O <: BudgetedSignHybridDisjoint.Orcl
          {-BudgetedSignHybridDisjoint.Count,
           -BudgetedSignHybridDisjointGame}) :
  hoare[
    BudgetedSignHybridDisjointGame
      (BudgetedSignHybridDisjointOrclb,
       BudgetedSignHybridDisjoint.OrclCount(O)).O.sign :
    0 <= BudgetedSignHybridDisjoint.Count.c /\
    BudgetedSignHybridDisjoint.Count.c <=
      BudgetedSignHybridDisjointGame.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      BudgetedSignHybridDisjointGame.signing_count
    ==>
    0 <= BudgetedSignHybridDisjoint.Count.c /\
    BudgetedSignHybridDisjoint.Count.c <=
      BudgetedSignHybridDisjointGame.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      BudgetedSignHybridDisjointGame.signing_count].
proof.
proc.
if.
+ if.
  + inline BudgetedSignHybridDisjoint.OrclCount(O).orcl
           BudgetedSignHybridDisjoint.Count.incr.
    wp.
    call (_ : true).
    by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                          /signature_query_budget_count; smt.
  inline BudgetedSignHybridDisjoint.OrclCount(O).orcl
         BudgetedSignHybridDisjoint.Count.incr.
  wp.
  call (_ : true).
  by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                        /signature_query_budget_count; smt.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                  /signature_query_budget_count; smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_hash_get_preserves_count_bound
    (O <: BudgetedSignHybridDisjoint.Orcl
          {-BudgetedSignHybridDisjoint.Count,
           -BudgetedSignHybridDisjointGame}) :
  hoare[
    BudgetedSignHybridDisjointGame
      (BudgetedSignHybridDisjointOrclb,
       BudgetedSignHybridDisjoint.OrclCount(O)).AH.get :
    0 <= BudgetedSignHybridDisjoint.Count.c /\
    BudgetedSignHybridDisjoint.Count.c <=
      BudgetedSignHybridDisjointGame.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      BudgetedSignHybridDisjointGame.signing_count
    ==>
    0 <= BudgetedSignHybridDisjoint.Count.c /\
    BudgetedSignHybridDisjoint.Count.c <=
      BudgetedSignHybridDisjointGame.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      BudgetedSignHybridDisjointGame.signing_count].
proof.
proc.
inline BudgetedSignHybridDisjointOrclb.leaks
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
          HAETAE_RO.FRO).AH.get.
rcondf 2; first by auto.
wp.
sp 3.
if.
+ wp.
  call (_ : true).
  + by auto.
  by auto.
by auto.
qed.

local lemma budgeted_sign_hybrid_disjoint_adversary_preserves_count_bound
    (O <: BudgetedSignHybridDisjoint.Orcl
          {-BudgetedSignHybridDisjoint.Count,
           -BudgetedSignHybridDisjointGame}) :
  hoare[
    BudgetedSignHybridDisjointGame
      (BudgetedSignHybridDisjointOrclb,
       BudgetedSignHybridDisjoint.OrclCount(O)).Adv.forge :
    0 <= BudgetedSignHybridDisjoint.Count.c /\
    BudgetedSignHybridDisjoint.Count.c <=
      BudgetedSignHybridDisjointGame.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      BudgetedSignHybridDisjointGame.signing_count
    ==>
    0 <= BudgetedSignHybridDisjoint.Count.c /\
    BudgetedSignHybridDisjoint.Count.c <=
      BudgetedSignHybridDisjointGame.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      BudgetedSignHybridDisjointGame.signing_count].
proof.
proc (0 <= BudgetedSignHybridDisjoint.Count.c /\
      BudgetedSignHybridDisjoint.Count.c <=
        BudgetedSignHybridDisjointGame.signing_count /\
      budgeted_paper_sim_signing_count_discipline
        BudgetedSignHybridDisjointGame.signing_count) => //.
+ move=> />.
+ proc*.
  call (budgeted_sign_hybrid_disjoint_hash_get_preserves_count_bound O).
  by auto.
proc*.
call (budgeted_sign_hybrid_disjoint_counted_sign_preserves_count_bound O).
by auto.
qed.

local lemma budgeted_sign_hybrid_disjoint_game_main_preserves_count_bound
    (O <: BudgetedSignHybridDisjoint.Orcl
          {-BudgetedSignHybridDisjoint.Count,
           -BudgetedSignHybridDisjointGame}) :
  hoare[
    BudgetedSignHybridDisjointGame
      (BudgetedSignHybridDisjointOrclb,
       BudgetedSignHybridDisjoint.OrclCount(O)).main :
    BudgetedSignHybridDisjoint.Count.c = 0 ==>
    0 <= BudgetedSignHybridDisjoint.Count.c /\
    BudgetedSignHybridDisjoint.Count.c <=
      BudgetedSignHybridDisjointGame.signing_count /\
    budgeted_paper_sim_signing_count_discipline
      BudgetedSignHybridDisjointGame.signing_count].
proof.
proc.
wp.
call (budgeted_sign_hybrid_disjoint_adversary_preserves_count_bound O).
inline BudgetedSignHybridDisjointOrclb.leaks.
rcondt 2; first by auto.
inline ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).init.
inline ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).init.
wp.
inline HAETAE(HAETAE_RO.FRO).kg.
wp.
inline HAETAE_RO.FRO.get.
wp.
rnd.
wp.
rnd.
inline HAETAE_RO.FRO.init.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                  /signature_query_budget_count;
  smt(seed_distribution_lossless ro_output_distribution_lossless).
qed.

local lemma budgeted_sign_hybrid_disjoint_A_call
    (O <: BudgetedSignHybridDisjoint.Orcl
          {-BudgetedSignHybridDisjoint.Count,
           -BudgetedSignHybridDisjointGame}) :
  hoare[
    BudgetedSignHybridDisjoint.Orcln
      (BudgetedSignHybridDisjointGame(BudgetedSignHybridDisjointOrclb), O).main :
    true ==> BudgetedSignHybridDisjoint.Count.c <= signature_query_budget_count].
proof.
proc.
wp.
call (budgeted_sign_hybrid_disjoint_game_main_preserves_count_bound O).
inline BudgetedSignHybridDisjoint.Count.init.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /signature_query_budget_count; smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_restr_res_difference &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] -
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] =
  signature_query_budget_count%r *
    (Pr[BudgetedSignHybridDisjoint.HybGame
          (BudgetedSignHybridDisjointGame,
           BudgetedSignHybridDisjointOrclb,
           BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
          .main() @ &m : res] -
     Pr[BudgetedSignHybridDisjoint.HybGame
          (BudgetedSignHybridDisjointGame,
           BudgetedSignHybridDisjointOrclb,
           BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
          .main() @ &m : res]).
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll.
have h :=
  BudgetedSignHybridDisjoint.Hybrid_restr
    BudgetedSignHybridDisjointOrclb
    BudgetedSignHybridDisjointGame
    budgeted_sign_hybrid_disjoint_A_call
    leaks_ll orclL_ll orclR_ll game_ll &m
    (fun (_ : glob BudgetedSignHybridDisjointGame)
         (_ : glob BudgetedSignHybridDisjointOrclb)
         (_ : int) (r : bool) => r).
by rewrite /= in h.
qed.

local lemma budgeted_sign_hybrid_disjoint_restr_res_le_from_one_switch &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m : res] <=
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] <=
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] +
    signature_query_budget_count%r * rejection_sampling_loss_term.
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll one_switch.
have restr :=
  budgeted_sign_hybrid_disjoint_restr_res_difference
    &m leaks_ll orclL_ll orclR_ll game_ll.
have q_ge0 :
  0%r <= signature_query_budget_count%r
  by rewrite /signature_query_budget_count; smt.
by smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_restr_clean_le_from_res_one_switch &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m : res] <=
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] +
    signature_query_budget_count%r * rejection_sampling_loss_term.
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll one_switch.
have acc :=
  budgeted_sign_hybrid_disjoint_restr_res_le_from_one_switch
    &m leaks_ll orclL_ll orclR_ll game_ll one_switch.
have left_clean_le :
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res]
  by smt(mu_sub).
by smt.
qed.

local pred budgeted_sign_hybrid_disjoint_orclb_clean
    (g : glob BudgetedSignHybridDisjointOrclb) =
  ! g.`8.

local pred budgeted_sign_hybrid_disjoint_verify_clean_event
    (pk : pkey) (r : message * context * signature)
    (g : glob BudgetedSignHybridDisjointOrclb) =
  verify_internal haetae_mode pk r.`1 r.`2 r.`3 /\
  budgeted_sign_hybrid_disjoint_orclb_clean g.

local lemma budgeted_sign_hybrid_disjoint_verify_clean_eventE
    pk m ctx sig g :
  budgeted_sign_hybrid_disjoint_verify_clean_event
    pk (m, ctx, sig) g =
  (verify_internal haetae_mode pk m ctx sig /\
   budgeted_sign_hybrid_disjoint_orclb_clean g).
proof.
by rewrite /budgeted_sign_hybrid_disjoint_verify_clean_event.
qed.

local pred budgeted_sign_hybrid_disjoint_surface_verify_clean_event
    (r : budgeted_sign_hybrid_disjoint_surface_result)
    (g : glob BudgetedSignHybridDisjointOrclb) =
  budgeted_sign_hybrid_disjoint_verify_clean_event
    (budgeted_sign_hybrid_disjoint_surface_pk r)
    (budgeted_sign_hybrid_disjoint_surface_forgery r) g.

local module BudgetedSignHybridDisjointSurfaceHybGame
  (Ob : BudgetedSignHybridDisjoint.Orclb,
   LR : BudgetedSignHybridDisjoint.Orcl) = {
  proc main() : budgeted_sign_hybrid_disjoint_surface_result = {
    var r : budgeted_sign_hybrid_disjoint_surface_result;

    BudgetedSignHybridDisjoint.HybOrcl.l0 <$
      [0..max 0 (signature_query_budget_count - 1)];
    BudgetedSignHybridDisjoint.HybOrcl.l <- 0;
    r <@
      BudgetedSignHybridDisjointGame
        (Ob, BudgetedSignHybridDisjoint.HybOrcl(Ob, LR)).main_surface();
    return r;
  }
}.

local equiv budgeted_sign_hybrid_disjoint_game_main_surfaceL_equiv :
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb)))
    .main ~
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb)))
    .main_surface :
  ={glob A, glob BudgetedSignHybridDisjointOrclb,
    glob BudgetedSignHybridDisjoint.HybOrcl} ==>
  res{1} =
    budgeted_sign_hybrid_disjoint_surface_ok res{2} /\
  budgeted_sign_hybrid_disjoint_surface_pk res{2} =
    BudgetedSignHybridDisjointGame.pk_current{2} /\
  budgeted_sign_hybrid_disjoint_surface_ok res{2} =
    verify_internal haetae_mode
      (budgeted_sign_hybrid_disjoint_surface_pk res{2})
      (budgeted_sign_hybrid_disjoint_surface_forgery res{2}).`1
      (budgeted_sign_hybrid_disjoint_surface_forgery res{2}).`2
      (budgeted_sign_hybrid_disjoint_surface_forgery res{2}).`3 /\
  ={glob A, glob BudgetedSignHybridDisjointOrclb,
    glob BudgetedSignHybridDisjoint.HybOrcl}.
proof.
proc.
wp.
call (: ={glob A, glob BudgetedSignHybridDisjointOrclb,
          glob BudgetedSignHybridDisjoint.HybOrcl, arg,
          BudgetedSignHybridDisjointGame.pk_current,
          BudgetedSignHybridDisjointGame.signing_count} ==>
          ={glob A, glob BudgetedSignHybridDisjointOrclb,
            glob BudgetedSignHybridDisjoint.HybOrcl, res,
            BudgetedSignHybridDisjointGame.pk_current,
            BudgetedSignHybridDisjointGame.signing_count}).
+ by sim.
wp.
call (: ={glob BudgetedSignHybridDisjointOrclb, arg} ==>
          ={glob BudgetedSignHybridDisjointOrclb, res}).
+ by sim.
by auto => />; rewrite /budgeted_sign_hybrid_disjoint_surface_ok
                    /budgeted_sign_hybrid_disjoint_surface_pk
                    /budgeted_sign_hybrid_disjoint_surface_forgery.
qed.

local equiv budgeted_sign_hybrid_disjoint_game_main_surfaceR_equiv :
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb)))
    .main ~
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb)))
    .main_surface :
  ={glob A, glob BudgetedSignHybridDisjointOrclb,
    glob BudgetedSignHybridDisjoint.HybOrcl} ==>
  res{1} =
    budgeted_sign_hybrid_disjoint_surface_ok res{2} /\
  budgeted_sign_hybrid_disjoint_surface_pk res{2} =
    BudgetedSignHybridDisjointGame.pk_current{2} /\
  budgeted_sign_hybrid_disjoint_surface_ok res{2} =
    verify_internal haetae_mode
      (budgeted_sign_hybrid_disjoint_surface_pk res{2})
      (budgeted_sign_hybrid_disjoint_surface_forgery res{2}).`1
      (budgeted_sign_hybrid_disjoint_surface_forgery res{2}).`2
      (budgeted_sign_hybrid_disjoint_surface_forgery res{2}).`3 /\
  ={glob A, glob BudgetedSignHybridDisjointOrclb,
    glob BudgetedSignHybridDisjoint.HybOrcl}.
proof.
proc.
wp.
call (: ={glob A, glob BudgetedSignHybridDisjointOrclb,
          glob BudgetedSignHybridDisjoint.HybOrcl, arg,
          BudgetedSignHybridDisjointGame.pk_current,
          BudgetedSignHybridDisjointGame.signing_count} ==>
          ={glob A, glob BudgetedSignHybridDisjointOrclb,
            glob BudgetedSignHybridDisjoint.HybOrcl, res,
            BudgetedSignHybridDisjointGame.pk_current,
            BudgetedSignHybridDisjointGame.signing_count}).
+ by sim.
wp.
call (: ={glob BudgetedSignHybridDisjointOrclb, arg} ==>
          ={glob BudgetedSignHybridDisjointOrclb, res}).
+ by sim.
by auto => />; rewrite /budgeted_sign_hybrid_disjoint_surface_ok
                    /budgeted_sign_hybrid_disjoint_surface_pk
                    /budgeted_sign_hybrid_disjoint_surface_forgery.
qed.

local equiv budgeted_sign_hybrid_disjoint_hybgame_surfaceL_equiv :
  BudgetedSignHybridDisjoint.HybGame
    (BudgetedSignHybridDisjointGame,
     BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
    .main ~
  BudgetedSignHybridDisjointSurfaceHybGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
    .main :
  ={glob A, glob BudgetedSignHybridDisjointOrclb} ==>
  res{1} =
    budgeted_sign_hybrid_disjoint_surface_ok res{2} /\
  budgeted_sign_hybrid_disjoint_surface_verify_clean_event
    res{2} (glob BudgetedSignHybridDisjointOrclb){2} =
    (res{1} /\
     budgeted_sign_hybrid_disjoint_orclb_clean
       (glob BudgetedSignHybridDisjointOrclb){1}) /\
  ={glob A, glob BudgetedSignHybridDisjointOrclb,
    glob BudgetedSignHybridDisjoint.HybOrcl}.
proof.
proc.
wp.
call budgeted_sign_hybrid_disjoint_game_main_surfaceL_equiv.
wp.
rnd.
by auto => />; rewrite
  /budgeted_sign_hybrid_disjoint_surface_verify_clean_event
  /budgeted_sign_hybrid_disjoint_verify_clean_event
  /budgeted_sign_hybrid_disjoint_orclb_clean
  /budgeted_sign_hybrid_disjoint_surface_ok
  /budgeted_sign_hybrid_disjoint_surface_pk
  /budgeted_sign_hybrid_disjoint_surface_forgery; smt.
qed.

local equiv budgeted_sign_hybrid_disjoint_hybgame_surfaceR_equiv :
  BudgetedSignHybridDisjoint.HybGame
    (BudgetedSignHybridDisjointGame,
     BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
    .main ~
  BudgetedSignHybridDisjointSurfaceHybGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
    .main :
  ={glob A, glob BudgetedSignHybridDisjointOrclb} ==>
  res{1} =
    budgeted_sign_hybrid_disjoint_surface_ok res{2} /\
  budgeted_sign_hybrid_disjoint_surface_verify_clean_event
    res{2} (glob BudgetedSignHybridDisjointOrclb){2} =
    (res{1} /\
     budgeted_sign_hybrid_disjoint_orclb_clean
       (glob BudgetedSignHybridDisjointOrclb){1}) /\
  ={glob A, glob BudgetedSignHybridDisjointOrclb,
    glob BudgetedSignHybridDisjoint.HybOrcl}.
proof.
proc.
wp.
call budgeted_sign_hybrid_disjoint_game_main_surfaceR_equiv.
wp.
rnd.
by auto => />; rewrite
  /budgeted_sign_hybrid_disjoint_surface_verify_clean_event
  /budgeted_sign_hybrid_disjoint_verify_clean_event
  /budgeted_sign_hybrid_disjoint_orclb_clean
  /budgeted_sign_hybrid_disjoint_surface_ok
  /budgeted_sign_hybrid_disjoint_surface_pk
  /budgeted_sign_hybrid_disjoint_surface_forgery; smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_hybgame_surfaceL_event_eq &m :
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)].
proof.
byequiv budgeted_sign_hybrid_disjoint_hybgame_surfaceL_equiv => //.
by smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_hybgame_surfaceR_event_eq &m :
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)].
proof.
byequiv budgeted_sign_hybrid_disjoint_hybgame_surfaceR_equiv => //.
by smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_clean_one_switch_from_surface
    &m :
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof.
move=> surface_one_switch.
have left_eq :=
  budgeted_sign_hybrid_disjoint_hybgame_surfaceL_event_eq &m.
have right_eq :=
  budgeted_sign_hybrid_disjoint_hybgame_surfaceR_event_eq &m.
by smt.
qed.

(* Surface-game one-switch antecedent spike result.
   The proof-only surface layer above removes the return-type obstruction for
   stating the verifier-clean one-switch event: main_surface exposes the final
   public key and forgery triple, the L/R event-equivalence lemmas connect that
   surface event exactly to the original boolean HybGame clean event, and the
   bridge lemma above reduces the original clean/clean one-switch obligation to
   the corresponding surface-game inequality.

   The exact unchecked antecedent is:

     Pr[BudgetedSignHybridDisjointSurfaceHybGame(...,L(...)).main() :
          budgeted_sign_hybrid_disjoint_surface_verify_clean_event
            res (glob BudgetedSignHybridDisjointOrclb)]
     <=
     Pr[BudgetedSignHybridDisjointSurfaceHybGame(...,R(...)).main() :
          budgeted_sign_hybrid_disjoint_surface_verify_clean_event
            res (glob BudgetedSignHybridDisjointOrclb)]
       + rejection_sampling_loss_term.

   A direct byequiv proof of this antecedent is blocked at the abstract call
   to A(AH,O).forge.  The ordinary EasyCrypt adversary call rule available here
   expects exact relational oracle specifications for AH.get and O.sign.  The
   needed O.sign rule is one-sided and lossy: it is exact except at the active
   HybOrcl branch l = l0, where the left run calls orclL, the right run calls
   orclR, and the comparison costs rejection_sampling_loss_term.

   The continuation after that active call is not a pure predicate of the
   returned signature.  It resumes the current A(AH,O).forge invocation, permits
   future AH.get/O.sign calls with the hybrid counter advanced past l0, runs
   verify_internal on the exposed final forgery triple, and checks the final
   Orclb clean predicate.  Its state therefore includes glob A, glob
   HAETAE_RO.FRO, glob BudgetedSignHybridDisjointGame, glob
   BudgetedSignHybridDisjointOrclb, transcript queries/transcripts/records,
   adversary_hash_queries, sampler_expand_queries, sampler_bad_prequery,
   signing counters, and Hybrid l/l0 state.

   The obstacle is not the surface result type.  A Hybrid clone with
   outputA = budgeted_sign_hybrid_disjoint_surface_result can express the
   surface-output Ln/Rn/HybGame arithmetic, but Hybrid_restr still takes the
   L/R one-switch inequality as a premise.  It does not manufacture the
   one-sided oracle-call rule needed below.

   The narrow missing proof principle is a lossy adversary-call induction for
   this surface game.  Under the invariant that the two runs agree on the
   public key, adversary state, ROM table relation, transcript/log state,
   counters, sampler secret state, sampler_rom_covered, and a false
   attempt-side sampler_bad_prequery before the active call, it must lift the
   active-call loss supplied by
   concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface through
   the remaining adversary continuation.  The existing signature-only one-call
   loss cannot instantiate this continuation because it has type
   p : signature -> bool and cannot mention the post-call globals or future
   oracle behavior.

   The future framework lemma should be specialized to this module interface,
   not added as an axiom here.  In schematic form it is:

     forall K pk &m,
       surface_switch_invariant pk (glob A) (glob HAETAE_RO.FRO)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb)
         (glob BudgetedSignHybridDisjoint.HybOrcl) =>
       Pr[A(AH, HybOrcl(...,L(...))).forge(pk) @ &m :
            K res (glob A) (glob HAETAE_RO.FRO)
              (glob BudgetedSignHybridDisjointGame)
              (glob BudgetedSignHybridDisjointOrclb)
              (glob BudgetedSignHybridDisjoint.HybOrcl) /\
            budgeted_sign_hybrid_disjoint_orclb_clean
              (glob BudgetedSignHybridDisjointOrclb)]
       <=
       Pr[A(AH, HybOrcl(...,R(...))).forge(pk) @ &m :
            K res (glob A) (glob HAETAE_RO.FRO)
              (glob BudgetedSignHybridDisjointGame)
              (glob BudgetedSignHybridDisjointOrclb)
              (glob BudgetedSignHybridDisjoint.HybOrcl) /\
            budgeted_sign_hybrid_disjoint_orclb_clean
              (glob BudgetedSignHybridDisjointOrclb)]
       + rejection_sampling_loss_term.

   For the actual surface antecedent, K is the continuation that resumes the
   rest of A(AH,O).forge, then applies verify_internal to the exposed forgery
   triple and checks final budgeted_sign_hybrid_disjoint_orclb_clean.  Current
   EasyCrypt call/byequiv patterns in this file handle the same opaque
   A.forge boundary only for exact oracle equivalences; fel handles bad-event
   bounds, not this one-sided probability-loss accumulation with a stateful
   continuation. *)

(* Proof-architecture spike, 2026-05-14.
   The remaining blocker is architectural rather than syntactic.  The current
   SIG.Adversary module type exposes only

     proc forge(pk : pkey) : message * context * signature {H.get, O.sign}

   so EasyCrypt proofs can call the adversary with exact oracle specifications,
   but they cannot pause forge at the active O.sign call, apply a one-sided loss,
   and resume an arbitrary continuation.

   Route 1: reduction-style one-switch challenge wrapper.
   Partially expressible.  BudgetedSignHybridDisjoint already implements the
   active-query selection pattern: AH.get is the leak interface, O.sign is routed
   through HybOrcl, and the checked surface game exposes the final verifier
   event.  A separate challenge-oracle wrapper could make the active signing
   query syntactically visible, reusing BudgetedSignHybridDisjointSurfaceHybGame,
   budgeted_sign_hybrid_disjoint_clean_one_switch_from_surface, and
   concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface.
   It still would not apply the loss outside A.forge with the current adversary
   type, because the post-challenge continuation is the private remainder of the
   opaque forge procedure.  To make this route complete, the project would need a
   new proof-only two-stage adversary interface, for example a module exposing
   "run until active signing query" and "resume after active signature"; proving
   that interface equivalent to arbitrary SIG.Adversary would be a new semantic
   theorem, not a local refactor.

   Route 2: defunctionalized trace game.
   Not straightforward for the current theorem.  A trace semantics with explicit
   AHGet, OSign, and ForgeReturn events would allow induction over a bounded
   interaction trace and could accumulate rejection_sampling_loss_term once per
   active signing event.  It would reuse the transcript predicates, sampler
   coverage invariants, concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface,
   and the checked Hybrid_restr arithmetic as validation targets.  However,
   EasyCrypt cannot derive such a trace for an arbitrary opaque module
   A <: SIG.Adversary from the current module type alone.  This route would
   require a new TraceAdversary module type plus an interpreter/equivalence
   theorem relating every supported adversary implementation to the trace model.
   Until that equivalence is machine-checked, it is an external proof obligation.

   Route 3: strengthened adversary theorem boundary.
   This is the only route compatible with the current opaque adversary interface
   without adding axioms.  The file can keep the existing machine-checked facts
   as they are and make the missing lossy-forge call rule an explicit conditional
   EasyCrypt premise for a future theorem.  The premise should be named narrowly,
   e.g. budgeted_sign_hybrid_disjoint_lossy_forge_switch_rule, and state exactly
   the surface one-switch inequality, or equivalently the one-call active-switch
   rule lifted through A(AH,O).forge under the invariant listed above.  It is not
   a cryptographic assumption by itself; it is a conditional proof-framework
   premise that must later be discharged either by Route 1 with a resumable
   adversary interface or by Route 2 with a trace semantics.

   Selected future architecture:
   do not add another local wrapper around the existing opaque forge call.  The
   next sound machine-checked advance is to introduce a named conditional theorem
   boundary for the lossy-forge switch rule, then separately prove that boundary
   from either a resumable two-stage adversary model or a defunctionalized trace
	   model.  The current machine-checked facts are the surface game, exact event
	   equivalences, Hybrid_restr accumulation, active-HybOrcl wrapper, and
	   restricted signature-continuation bridges.  The unproved item remains the
	   conditional lossy adversary-call rule; no external cryptographic assumption
	   has been added here, and no admit/axiom should be introduced for it. *)

type budgeted_sign_hybrid_resumable_step =
  [ BudgetedSignHybridResumeActive of SIG.query
  | BudgetedSignHybridResumeReturn of (message * context * signature) ].

module type BudgetedSignHybridResumableAdversary
    (H : SIG.POracle, O : SIG.SignOracle) = {
  proc run_to_active(pk : pkey, active_index : int)
    : budgeted_sign_hybrid_resumable_step {H.get, O.sign}
  proc resume_after_active(sig : signature)
    : message * context * signature {H.get, O.sign}
}.

type budgeted_sign_hybrid_trace_event =
  [ BudgetedSignHybridTraceHash of ro_query
  | BudgetedSignHybridTraceSign of SIG.query
  | BudgetedSignHybridTraceReturn of (message * context * signature) ].

type budgeted_sign_hybrid_trace_response =
  [ BudgetedSignHybridTraceStart
  | BudgetedSignHybridTraceHashOut of ro_output
  | BudgetedSignHybridTraceSignOut of signature ].

module type BudgetedSignHybridTraceAdversary = {
  proc init(pk : pkey) : unit
  proc next(resp : budgeted_sign_hybrid_trace_response)
    : budgeted_sign_hybrid_trace_event
}.

op budgeted_sign_hybrid_resumable_step_is_active
   (s : budgeted_sign_hybrid_resumable_step) : bool =
  with s = BudgetedSignHybridResumeActive _ => true
  with s = BudgetedSignHybridResumeReturn _ => false.

op budgeted_sign_hybrid_resumable_step_query
   (s : budgeted_sign_hybrid_resumable_step) : SIG.query =
  with s = BudgetedSignHybridResumeActive q => q
  with s = BudgetedSignHybridResumeReturn _ => ([], []).

op budgeted_sign_hybrid_resumable_default_forgery
  : message * context * signature =
  let pk = budgeted_sign_hybrid_default_keypair.`1 in
  ([], [],
   paper_sim_signature haetae_mode pk [] []
     (paper_sim_abort_fallback_sample haetae_mode)).

op budgeted_sign_hybrid_resumable_step_forgery
   (s : budgeted_sign_hybrid_resumable_step)
   : message * context * signature =
  with s = BudgetedSignHybridResumeReturn f => f
  with s = BudgetedSignHybridResumeActive _ =>
    budgeted_sign_hybrid_resumable_default_forgery.

local module BudgetedSignHybridResumableActiveL : SIG.SignOracle = {
  proc sign(m : message, ctx : context) : signature = {
    var sig : signature;

    sig <@ BudgetedSignHybridDisjointOrclb.orclL((m, ctx));
    return sig;
  }
}.

local module BudgetedSignHybridResumableActiveR : SIG.SignOracle = {
  proc sign(m : message, ctx : context) : signature = {
    var sig : signature;

    sig <@ BudgetedSignHybridDisjointOrclb.orclR((m, ctx));
    return sig;
  }
}.

local module BudgetedSignHybridResumableSurfaceGame
  (RAdv : BudgetedSignHybridResumableAdversary,
   Active : SIG.SignOracle) = {
  var pk_current : pkey
  var signing_count : int

  module AH = {
    proc get(q : ro_query) : ro_output = {
      var y : budgeted_sign_hybrid_leak_output;
      var ro_y : ro_output;

      y <@ BudgetedSignHybridDisjointOrclb.leaks(BudgetedSignHybridHash q);
      ro_y <- budgeted_sign_hybrid_output_ro y;
      return ro_y;
    }
  }

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var sig : signature;
      var smp : paper_sim_signature_sample;

      if (signing_count < signature_query_budget_count) {
        if (signing_count = 0) {
          signing_count <- 1;
        } else {
          signing_count <- signature_query_budget_count;
        }
        sig <@
          BudgetedSignHybridDisjoint.HybOrcl
            (BudgetedSignHybridDisjointOrclb,
             BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
            .orcl((m, ctx));
      } else {
        signing_count <- signature_query_budget_count;
        smp <- paper_sim_abort_fallback_sample haetae_mode;
        sig <- paper_sim_signature haetae_mode pk_current m ctx smp;
      }
      return sig;
    }
  }

  module Adv = RAdv(AH, O)

  proc main() : budgeted_sign_hybrid_disjoint_surface_result = {
    var setup_y : budgeted_sign_hybrid_leak_output;
    var kp : pkey * skey;
    var pk : pkey;
    var sk : skey;
    var step : budgeted_sign_hybrid_resumable_step;
    var qry : SIG.query;
    var active_sig : signature;
    var smp : paper_sim_signature_sample;
    var forgery : message * context * signature;
    var ok : bool;
    var r : budgeted_sign_hybrid_disjoint_surface_result;

    BudgetedSignHybridDisjoint.HybOrcl.l0 <$
      [0..max 0 (signature_query_budget_count - 1)];
    BudgetedSignHybridDisjoint.HybOrcl.l <- 0;
    setup_y <@ BudgetedSignHybridDisjointOrclb.leaks(BudgetedSignHybridSetup);
    kp <- budgeted_sign_hybrid_output_keypair setup_y;
    pk <- kp.`1;
    sk <- kp.`2;
    pk_current <- pk;
    signing_count <- 0;
    step <@ Adv.run_to_active(pk, BudgetedSignHybridDisjoint.HybOrcl.l0);
    if (budgeted_sign_hybrid_resumable_step_is_active step) {
      qry <- budgeted_sign_hybrid_resumable_step_query step;
      if (signing_count < signature_query_budget_count) {
        if (signing_count = 0) {
          signing_count <- 1;
        } else {
          signing_count <- signature_query_budget_count;
        }
        active_sig <@ Active.sign(qry.`1, qry.`2);
        BudgetedSignHybridDisjoint.HybOrcl.l <-
          BudgetedSignHybridDisjoint.HybOrcl.l + 1;
      } else {
        signing_count <- signature_query_budget_count;
        smp <- paper_sim_abort_fallback_sample haetae_mode;
        active_sig <- paper_sim_signature haetae_mode
          pk_current qry.`1 qry.`2 smp;
      }
      forgery <@ Adv.resume_after_active(active_sig);
    } else {
      forgery <- budgeted_sign_hybrid_resumable_step_forgery step;
    }
    ok <- verify_internal haetae_mode pk forgery.`1 forgery.`2 forgery.`3;
    r <- (ok, pk, forgery);
    return r;
  }
}.

local lemma
  budgeted_sign_hybrid_disjoint_lossy_forge_switch_from_resumable_surface
    (RAdv <: BudgetedSignHybridResumableAdversary) &m :
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridResumableSurfaceGame
       (RAdv, BudgetedSignHybridResumableActiveL).main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] =>
  Pr[BudgetedSignHybridResumableSurfaceGame
       (RAdv, BudgetedSignHybridResumableActiveL).main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridResumableSurfaceGame
       (RAdv, BudgetedSignHybridResumableActiveR).main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridResumableSurfaceGame
       (RAdv, BudgetedSignHybridResumableActiveR).main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] =>
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof.
by smt.
qed.

(* Conditional active-call boundary for the resumable route, not an axiom.
   The split run_to_active/resume_after_active removes the opaque A.forge call
   from the selected signing query, but it does not by itself make the existing
   signature-only loss lemma strong enough.  After Active.sign returns,
   resume_after_active may inspect the returned signature, the private RAdv
   state left by run_to_active, lazy-ROM state, transcript/signing logs,
   sampler_expand_queries, sampler_bad_prequery, Hybrid l/l0 state, and future
   AH.get/O.sign behavior.  A pure p : signature -> bool cannot encode that
   suffix.

   The exact non-vacuous theorem still needed is a stateful active-call
   continuation rule.  In the active branch, after equal setup, equal
   run_to_active states, an active signing counter, sampler_rom_covered,
   !sampler_bad_prequery, and matching attempt/exact sampler secrets, prove

     Pr[ActiveL.sign(q) : K res post_state /\ clean]
       <= Pr[ActiveR.sign(q) : K res post_state /\ clean]
          + rejection_sampling_loss_term

   for the concrete suffix continuation K that runs
   RAdv(AH,O).resume_after_active(res), then verify_internal, and then tests
   budgeted_sign_hybrid_disjoint_surface_verify_clean_event.  Existing exact
   byequiv rules can cover run_to_active only while the two active signatures
   are not yet sampled; after that point a one-sided stateful continuation
   theorem is required.  Closing the lemma below with probability boundedness
   and rejection_sampling_loss_term_ge1 would be machine-checked but vacuous,
   so the premise is kept explicit. *)
local lemma budgeted_sign_hybrid_resumable_active_call_loss_rule
    (RAdv <: BudgetedSignHybridResumableAdversary) &m :
  Pr[BudgetedSignHybridResumableSurfaceGame
       (RAdv, BudgetedSignHybridResumableActiveL).main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridResumableSurfaceGame
       (RAdv, BudgetedSignHybridResumableActiveR).main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridResumableSurfaceGame
       (RAdv, BudgetedSignHybridResumableActiveL).main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridResumableSurfaceGame
       (RAdv, BudgetedSignHybridResumableActiveR).main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof. by move=> h. qed.

(* Proof-interface design spike, 2026-05-14.
   The smallest future interface is the resumable two-stage adversary above.
   It exposes exactly the point hidden by SIG.Adversary: run_to_active executes
   the prefix of forge up to the selected signing query, returning either that
   active query or a completed forgery if no active query is reached; then
   resume_after_active continues from the same private adversary state after
   receiving the active signature.  The theorem that would imply
   budgeted_sign_hybrid_disjoint_lossy_forge_switch_rule is:

   - an embedding/equivalence theorem showing that, for the adversaries covered
     by the model, the ordinary opaque A(H,O).forge game is equivalent to
     run_to_active followed by either immediate return or resume_after_active;
   - a stateful active-call theorem applying the existing one-call sampler loss
     to the exposed active query under sampler_rom_covered, !sampler_bad_prequery,
     matching signing counters, matching sampler secrets, and equal lazy-ROM and
     transcript/log state; and
   - exact byequiv proofs for the prefix and resume phases, reusing the existing
     AH.get/O.sign exact adapters, the surface-game event equivalences, and the
     Hybrid_restr accumulation lemmas.

   What remains impossible for arbitrary SIG.Adversary is the embedding theorem:
   the current module type does not expose any pause/resume state, so EasyCrypt
   has no object from which to prove that every opaque forge implementation can
   be represented by run_to_active/resume_after_active.

   The trace interface above is the larger alternative.  Its next(resp) method
   represents a defunctionalized interaction machine whose interpreter would
   perform AH.get and O.sign calls and feed back TraceHashOut/TraceSignOut
   responses.  A trace route would make induction over bounded interactions
   explicit and could charge rejection_sampling_loss_term at the selected
   TraceSign event.  It would reuse the same one-call sampler loss, transcript
   predicates, surface-game event equivalences, and Hybrid_restr arithmetic, but
   it additionally needs a trace interpreter and a semantic equivalence theorem
   from each supported adversary to that interpreter.  That is strictly heavier
   than the resumable interface for this proof obligation and still cannot be
   derived for arbitrary SIG.Adversary without strengthening the adversary
   interface. *)

(* Conditional EasyCrypt premise boundary, not an axiom:
   the premise to this lemma is exactly the lossy-forge switch rule that remains
   to be proved by a future two-stage adversary or trace framework.  The lemma
   only gives that premise a stable reusable name.

   Adapter-proof spike result: after the concrete attempt-to-hybrid and
   hybrid-to-exact adapters, this is still the only substantive open premise.
   A direct non-vacuous proof of the displayed surface inequality still reaches
   the opaque call

     BudgetedSignHybridDisjointGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.HybOrcl(...)).Adv.forge(pk)

   and needs a one-sided oracle-call rule for that abstract adversary call.
   Existing byequiv/call rules can use exact relational specifications for
   AH.get and O.sign, and the checked Hybrid_restr lemmas can accumulate a
   supplied one-switch loss, but neither rule derives the one-switch premise
   through opaque A(AH,O).forge.  The active-HybOrcl and restricted-signature
   lemmas below only transform a one-call continuation inequality; they do not
   provide the adversary-call induction that manufactures it.

   The exact future proof-interface theorem needed to eliminate this premise is
   a stateful lossy forge-call induction, with shape:

     for every continuation
       K : message * context * signature ->
           glob A -> glob HAETAE_RO.FRO ->
           glob BudgetedSignHybridDisjointGame ->
           glob BudgetedSignHybridDisjointOrclb -> bool,
     under the active-switch invariant
       HybOrcl.l = HybOrcl.l0,
       equal public transcript/log state, equal lazy-ROM state as required by
       coupled future AH.get calls, matching signing counters, sampler coverage,
       !sampler_bad_prequery, and matching attempt/exact sampler secrets,
     prove

       Pr[BudgetedSignHybridDisjointGame
            (BudgetedSignHybridDisjointOrclb,
             BudgetedSignHybridDisjoint.HybOrcl
               (BudgetedSignHybridDisjointOrclb,
                BudgetedSignHybridDisjoint.L
                  (BudgetedSignHybridDisjointOrclb))).Adv.forge(pk) :
            K res (glob A) (glob HAETAE_RO.FRO)
              (glob BudgetedSignHybridDisjointGame)
              (glob BudgetedSignHybridDisjointOrclb)]
       <=
       Pr[BudgetedSignHybridDisjointGame
            (BudgetedSignHybridDisjointOrclb,
             BudgetedSignHybridDisjoint.HybOrcl
               (BudgetedSignHybridDisjointOrclb,
                BudgetedSignHybridDisjoint.R
                  (BudgetedSignHybridDisjointOrclb))).Adv.forge(pk) :
            K res (glob A) (glob HAETAE_RO.FRO)
              (glob BudgetedSignHybridDisjointGame)
              (glob BudgetedSignHybridDisjointOrclb)]
       + rejection_sampling_loss_term.

   Instantiating K with the exposed surface suffix
     fun (m,ctx,sig) _ _ _ go =>
       budgeted_sign_hybrid_disjoint_verify_clean_event pk (m,ctx,sig) go
   would prove the displayed surface one-switch rule.  Closing this lemma by
   mu_bounded together with rejection_sampling_loss_term_ge1 would be
   machine-checked but vacuous, so it is intentionally not used here. *)
local lemma budgeted_sign_hybrid_disjoint_lossy_forge_switch_rule &m :
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof. by move=> h. qed.

local lemma budgeted_sign_hybrid_disjoint_orclb_clean_one_switch_from_lossy_forge_switch_rule &m :
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof.
move=> lossy_forge_switch.
apply (budgeted_sign_hybrid_disjoint_clean_one_switch_from_surface &m).
by apply (budgeted_sign_hybrid_disjoint_lossy_forge_switch_rule &m).
qed.

local lemma budgeted_sign_hybrid_disjoint_restr_orclb_clean_difference &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] -
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  signature_query_budget_count%r *
    (Pr[BudgetedSignHybridDisjoint.HybGame
          (BudgetedSignHybridDisjointGame,
           BudgetedSignHybridDisjointOrclb,
           BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
          .main() @ &m :
          res /\
          budgeted_sign_hybrid_disjoint_orclb_clean
            (glob BudgetedSignHybridDisjointOrclb)] -
     Pr[BudgetedSignHybridDisjoint.HybGame
          (BudgetedSignHybridDisjointGame,
           BudgetedSignHybridDisjointOrclb,
           BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
          .main() @ &m :
          res /\
          budgeted_sign_hybrid_disjoint_orclb_clean
            (glob BudgetedSignHybridDisjointOrclb)]).
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll.
have h :=
  BudgetedSignHybridDisjoint.Hybrid_restr
    BudgetedSignHybridDisjointOrclb
    BudgetedSignHybridDisjointGame
    budgeted_sign_hybrid_disjoint_A_call
    leaks_ll orclL_ll orclR_ll game_ll &m
    (fun (_ : glob BudgetedSignHybridDisjointGame)
         (gob : glob BudgetedSignHybridDisjointOrclb)
         (_ : int) (r : bool) =>
       r /\
       budgeted_sign_hybrid_disjoint_orclb_clean gob).
by rewrite /= in h.
qed.

local lemma budgeted_sign_hybrid_disjoint_restr_orclb_clean_le_from_orclb_clean_one_switch &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjoint.HybGame
       (BudgetedSignHybridDisjointGame,
        BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] +
    signature_query_budget_count%r * rejection_sampling_loss_term.
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll one_switch.
have restr :=
  budgeted_sign_hybrid_disjoint_restr_orclb_clean_difference
    &m leaks_ll orclL_ll orclR_ll game_ll.
have q_ge0 :
  0%r <= signature_query_budget_count%r
  by rewrite /signature_query_budget_count; smt.
have right_clean_le :
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res]
  by smt(mu_sub).
by smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_restr_orclb_clean_le_from_lossy_forge_switch_rule &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] +
    signature_query_budget_count%r * rejection_sampling_loss_term.
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll lossy_forge_switch.
apply
  (budgeted_sign_hybrid_disjoint_restr_orclb_clean_le_from_orclb_clean_one_switch
     &m leaks_ll orclL_ll orclR_ll game_ll).
by apply
  (budgeted_sign_hybrid_disjoint_orclb_clean_one_switch_from_lossy_forge_switch_rule
     &m).
qed.

local lemma concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting_from_lossy_forge_switch_rule &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =>
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res] =>
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll lossy_forge_switch
        attempt_to_hybrid hybrid_to_exact.
have hybrid_bound :=
  budgeted_sign_hybrid_disjoint_restr_orclb_clean_le_from_lossy_forge_switch_rule
    &m leaks_ll orclL_ll orclR_ll game_ll lossy_forge_switch.
have budget_eq :
  signature_query_budget_count%r * rejection_sampling_loss_term =
  rom_signature_query_budget * rejection_sampling_loss_term.
+ rewrite /rom_signature_query_budget /signature_query_count
          /signature_query_budget_count; ring.
by smt.
qed.

(* Concrete adapter proof spike.
   The first mechanical attempt was the direct implication proof

     byequiv (: ={glob HAETAE_RO.FRO, glob A} ==>
       (res{1} /\ !sampler_bad_prequery{1}) =>
       (res{2} /\ budgeted_sign_hybrid_disjoint_orclb_clean
                    (glob BudgetedSignHybridDisjointOrclb){2})) => //.
     proc; inline *; sim.

   EasyCrypt rejected the final command with "cannot infer the set of
   equalities".  That is the narrow obstruction for the adapter layer: the
   proof-only Ln/Rn games are not syntactically the concrete UF_NMA games after
   expansion.  They route setup through Orclb.leaks, route signing through
   BudgetedSignHybridDisjointGame.O.sign and OrclCount(L/R).orcl, and maintain
   extra proof-only globals BudgetedSignHybridDisjointGame.signing_count and
   BudgetedSignHybridDisjoint.Count.c.

   The concrete wrappers and proof-only wrappers are still intended to be exact
   adapters, but they require explicit sub-equivalences rather than a one-line
   simulation:
   - concrete AH.get versus BudgetedSignHybridDisjointGame.AH.get, preserving
     HAETAE_RO.FRO.m, adversary_hash_count, and adversary_hash_queries;
   - concrete active/fallback O.sign versus
     BudgetedSignHybridDisjointGame.O.sign with OrclCount(L).orcl, synchronizing
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count with
     BudgetedSignHybridDisjointGame.signing_count while ignoring only the
     proof-only Count.c;
   - the analogous exact-side O.sign adapter with OrclCount(R).orcl;
   - the final event projection equating
     !ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery with
     budgeted_sign_hybrid_disjoint_orclb_clean
       (glob BudgetedSignHybridDisjointOrclb).

   The setup wrapper was also missing the concrete reset of
   ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count; that mismatch
   is fixed above in BudgetedSignHybridDisjointOrclb.leaks.

   Focused adapter-subproof attempt, 2026-05-14:
   the narrow AH.get equivalence was tried before the signing adapters:

     ROMInternalTranscriptBudgetedPaperSimAsNMA(...).AH.get
       ~ BudgetedSignHybridDisjointGame(BudgetedSignHybridDisjointOrclb, LR).AH.get

   with pre/post framing arg, glob HAETAE_RO.FRO, and the entire
   glob ROMInternalTranscriptBudgetedPaperSimAsNMA.  Three proof shapes failed
   after expanding BudgetedSignHybridDisjointGame.AH.get,
   BudgetedSignHybridDisjointOrclb.leaks, the concrete AH.get, and eventually
   HAETAE_RO.FRO.get:
   - rcondf {2} 1 was rejected because the targeted instruction was not the
     leak setup conditional after inlining;
   - wp; call (: ={glob HAETAE_RO.FRO, arg} ==> ...) was rejected because the
     last instruction was no longer a procedure call;
   - full inlining followed by by sim left goals open even with the whole
     concrete transcript-wrapper global framed.

   Thus the first missing adapter lemma is more specific than "AH.get
   equivalence": it is a hash-leak projection lemma for
   BudgetedSignHybridDisjointOrclb.leaks(BudgetedSignHybridHash q) that exposes
   the non-setup branch and the BudgetedSignHybridHashOut/output_ro cancellation
   before relating it to the concrete AH.get.  The signing adapters should not
   be wired until that projection lemma is checked, because their O.sign calls
   rely on the same leak wrapper for the post-sampler message/challenge hash
   queries.  No adapter theorem is claimed here until those sub-equivalences are
   machine-checked. *)

local module ConcreteBudgetedAHGetCall = {
  proc get(q : ro_query) : ro_output = {
    var y : ro_output;

    y <@ ROMInternalTranscriptBudgetedPaperSimAsNMA
           (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
            HAETAE_RO.FRO).AH.get(q);
    return y;
  }
}.

local equiv concrete_budgeted_ah_get_call_exact :
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).AH.get ~
  ConcreteBudgetedAHGetCall.get :
  ={arg, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA} ==>
  ={res, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA}.
proof.
proc.
inline ConcreteBudgetedAHGetCall.get.
inline ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).AH.get.
by sim.
qed.

local equiv concrete_budgeted_ah_get_call_to_disjoint_hash_leak :
  ConcreteBudgetedAHGetCall.get ~
  BudgetedSignHybridDisjointOrclb.leaks :
  arg{2} = BudgetedSignHybridHash arg{1} /\
  ={glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA} ==>
  res{1} = budgeted_sign_hybrid_output_ro res{2} /\
  ={glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA}.
proof.
proc.
inline ConcreteBudgetedAHGetCall.get
       BudgetedSignHybridDisjointOrclb.leaks.
rcondf {2} 1.
+ by auto.
inline ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).AH.get.
wp.
sp 1 2.
conseq (: _ ==> ={y0, glob HAETAE_RO.FRO,
                  glob ROMInternalTranscriptBudgetedPaperSimAsNMA}).
+ by sim.
qed.

local equiv concrete_budgeted_ah_get_call_to_disjoint_game_ah_get
    (LR <: BudgetedSignHybridDisjoint.Orcl
            {-BudgetedSignHybridDisjointGame}) :
  ConcreteBudgetedAHGetCall.get ~
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb, LR).AH.get :
  ={arg, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA} ==>
  ={res, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA}.
proof.
proc.
inline ConcreteBudgetedAHGetCall.get.
inline BudgetedSignHybridDisjointGame
  (BudgetedSignHybridDisjointOrclb, LR).AH.get.
inline {2} 1.
sp 0 1.
rcondf {2} 1.
+ by auto.
inline ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).AH.get.
wp.
sp 1 2.
conseq (: _ ==> y0{1} = y1{2} /\
                  ={glob HAETAE_RO.FRO,
                    glob ROMInternalTranscriptBudgetedPaperSimAsNMA}).
+ move=> />.
by sim.
qed.

local equiv concrete_budgeted_ah_get_to_disjoint_game_ah_get
    (LR <: BudgetedSignHybridDisjoint.Orcl
            {-BudgetedSignHybridDisjointGame}) :
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).AH.get ~
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb, LR).AH.get :
  ={arg, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA} ==>
  ={res, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA}.
proof.
proc.
inline BudgetedSignHybridDisjointGame
  (BudgetedSignHybridDisjointOrclb, LR).AH.get.
inline {2} 1.
sp 0 1.
rcondf {2} 1.
+ by auto.
inline ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).AH.get.
wp.
sp 0 2.
conseq (: _ ==> y{1} = y1{2} /\
                  ={glob HAETAE_RO.FRO,
                    glob ROMInternalTranscriptBudgetedPaperSimAsNMA}).
+ move=> />.
by sim.
qed.

local equiv concrete_budgeted_ah_get_to_disjoint_counted_L_game_ah_get :
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).AH.get ~
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.OrclCount
       (BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))).AH.get :
  ={arg, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    BudgetedSignHybridDisjointGame.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    BudgetedSignHybridDisjointGame.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{2} /\
  BudgetedSignHybridDisjoint.Count.c{2} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} ==>
  ={res, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    BudgetedSignHybridDisjointGame.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    BudgetedSignHybridDisjointGame.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{2} /\
  BudgetedSignHybridDisjoint.Count.c{2} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}.
proof.
proc.
inline BudgetedSignHybridDisjointGame
  (BudgetedSignHybridDisjointOrclb,
   BudgetedSignHybridDisjoint.OrclCount
     (BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))).AH.get.
inline {2} 1.
sp 0 1.
rcondf {2} 1.
+ by auto.
inline ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).AH.get.
wp.
sp 0 2.
if => //.
+ if => //.
  + wp.
    call (_ : ={arg, glob HAETAE_RO.FRO} ==>
              ={res, glob HAETAE_RO.FRO}).
    + by proc; sim.
    by auto => />.
  wp.
  call (_ : ={arg, glob HAETAE_RO.FRO} ==>
            ={res, glob HAETAE_RO.FRO}).
  + by proc; sim.
  by auto => />.
by auto => />.
qed.

local equiv concrete_budgeted_ro_signing_attempt_o_sign_to_disjoint_counted_L_o_sign :
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).O.sign ~
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.OrclCount
       (BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))).O.sign :
  ={arg, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    BudgetedSignHybridDisjointGame.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    BudgetedSignHybridDisjointGame.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{2} /\
  BudgetedSignHybridDisjoint.Count.c{2} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} ==>
  ={res, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    BudgetedSignHybridDisjointGame.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    BudgetedSignHybridDisjointGame.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{2} /\
  BudgetedSignHybridDisjoint.Count.c{2} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}.
proof.
proc.
inline BudgetedSignHybridDisjoint.OrclCount
         (BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb)).orcl
       BudgetedSignHybridDisjoint.Count.incr
       BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb).orcl
       BudgetedSignHybridDisjointOrclb.orclL.
if.
+ by auto.
+ wp.
  call (_ : ={arg, glob HAETAE_RO.FRO,
              glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} ==>
            ={res, glob HAETAE_RO.FRO,
              glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)}).
  + by proc; sim.
  wp.
  call (_ : ={arg, glob HAETAE_RO.FRO,
              glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} ==>
            ={res, glob HAETAE_RO.FRO,
              glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)}).
  + by proc; sim.
  wp.
  call (_ : ={arg, glob HAETAE_RO.FRO,
              glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} ==>
            ={res, glob HAETAE_RO.FRO,
              glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)}).
  + by proc; sim.
  wp.
  rnd.
  by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                        /signature_query_budget_count; smt.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                  /signature_query_budget_count; smt.
qed.

local equiv concrete_budgeted_ro_signing_attempt_adversary_to_disjoint_counted_L_adversary :
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).A.forge ~
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.OrclCount
       (BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))).Adv.forge :
  ={arg, glob A, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    BudgetedSignHybridDisjointGame.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    BudgetedSignHybridDisjointGame.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{2} /\
  BudgetedSignHybridDisjoint.Count.c{2} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} ==>
  ={res, glob A, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    BudgetedSignHybridDisjointGame.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    BudgetedSignHybridDisjointGame.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{2} /\
  BudgetedSignHybridDisjoint.Count.c{2} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}.
proof.
proc
  (={glob HAETAE_RO.FRO,
     glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
     glob ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO)} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
     BudgetedSignHybridDisjointGame.pk_current{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
     BudgetedSignHybridDisjointGame.signing_count{2} /\
   0 <= BudgetedSignHybridDisjoint.Count.c{2} /\
   BudgetedSignHybridDisjoint.Count.c{2} <=
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
   budgeted_paper_sim_signing_count_discipline
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}) => //.
+ proc*.
  call concrete_budgeted_ah_get_to_disjoint_counted_L_game_ah_get.
  by auto => />; smt.
proc*.
call concrete_budgeted_ro_signing_attempt_o_sign_to_disjoint_counted_L_o_sign.
by auto => />.
qed.

local equiv concrete_budgeted_ro_signing_attempt_nma_to_disjoint_Ln_clean_equiv :
  SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
    ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main ~
  BudgetedSignHybridDisjoint.Ln
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjointGame).main :
  ={glob A, glob HAETAE_RO.FRO} ==>
  res{1} = res{2} /\
  (! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
   budgeted_sign_hybrid_disjoint_orclb_clean
     (glob BudgetedSignHybridDisjointOrclb){2}).
proof.
proc.
inline BudgetedSignHybridDisjoint.Count.init
       BudgetedSignHybridDisjointGame
         (BudgetedSignHybridDisjointOrclb,
          BudgetedSignHybridDisjoint.OrclCount
            (BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))).main
       BudgetedSignHybridDisjointOrclb.leaks.
rcondt {2} 3.
+ by auto.
inline ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).forge
  HAETAE(HAETAE_RO.FRO).verify.
wp.
call concrete_budgeted_ro_signing_attempt_adversary_to_disjoint_counted_L_adversary.
inline ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).init
       ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).init.
wp.
inline HAETAE(HAETAE_RO.FRO).kg.
wp.
inline HAETAE_RO.FRO.get.
wp.
rnd.
wp.
rnd.
inline HAETAE_RO.FRO.init.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /budgeted_sign_hybrid_output_keypair
                    /budgeted_sign_hybrid_disjoint_orclb_clean
                    /signature_query_budget_count;
  smt(seed_distribution_lossless ro_output_distribution_lossless).
qed.

local lemma concrete_budgeted_ro_signing_attempt_to_disjoint_Ln_clean_adapter &m :
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[BudgetedSignHybridDisjoint.Ln
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m :
       res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)].
proof.
byequiv concrete_budgeted_ro_signing_attempt_nma_to_disjoint_Ln_clean_equiv => //.
by move=> &1 &2 />; smt.
qed.

local lemma concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting_from_lossy_forge_switch_rule_and_attempt_adapter &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res] =>
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll lossy_forge_switch
        hybrid_to_exact.
apply
  (concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting_from_lossy_forge_switch_rule
     &m leaks_ll orclL_ll orclR_ll game_ll lossy_forge_switch).
+ apply concrete_budgeted_ro_signing_attempt_to_disjoint_Ln_clean_adapter.
by apply hybrid_to_exact.
qed.

local equiv disjoint_counted_R_game_ah_get_to_concrete_budgeted_ro_exact_hyperball_ah_get :
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.OrclCount
       (BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))).AH.get ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).AH.get :
  ={arg, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} /\
  BudgetedSignHybridDisjointGame.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  BudgetedSignHybridDisjointGame.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{1} /\
  BudgetedSignHybridDisjoint.Count.c{1} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} ==>
  ={res, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} /\
  BudgetedSignHybridDisjointGame.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  BudgetedSignHybridDisjointGame.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{1} /\
  BudgetedSignHybridDisjoint.Count.c{1} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2}.
proof.
proc.
inline BudgetedSignHybridDisjointGame
  (BudgetedSignHybridDisjointOrclb,
   BudgetedSignHybridDisjoint.OrclCount
     (BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))).AH.get.
inline {1} 1.
sp 1 0.
rcondf {1} 1.
+ by auto.
inline ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).AH.get
  ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).AH.get.
wp.
sp 2 0.
if => //.
+ if => //.
  + wp.
    call (_ : ={arg, glob HAETAE_RO.FRO} ==>
              ={res, glob HAETAE_RO.FRO}).
    + by proc; sim.
    by auto => />.
  wp.
  call (_ : ={arg, glob HAETAE_RO.FRO} ==>
            ={res, glob HAETAE_RO.FRO}).
  + by proc; sim.
  by auto => />.
by auto => />.
qed.

local equiv disjoint_counted_R_o_sign_to_concrete_budgeted_ro_exact_hyperball_o_sign :
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.OrclCount
       (BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))).O.sign ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).O.sign :
  ={arg, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} /\
  BudgetedSignHybridDisjointGame.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  BudgetedSignHybridDisjointGame.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{1} /\
  BudgetedSignHybridDisjoint.Count.c{1} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} ==>
  ={res, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} /\
  BudgetedSignHybridDisjointGame.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  BudgetedSignHybridDisjointGame.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{1} /\
  BudgetedSignHybridDisjoint.Count.c{1} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2}.
proof.
proc.
inline BudgetedSignHybridDisjoint.OrclCount
         (BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb)).orcl
       BudgetedSignHybridDisjoint.Count.incr
       BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb).orcl
       BudgetedSignHybridDisjointOrclb.orclR.
if.
+ by auto.
+ wp.
  call (_ : ={arg, glob HAETAE_RO.FRO,
              glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} ==>
            ={res, glob HAETAE_RO.FRO,
              glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)}).
  + by proc; sim.
  wp.
  call (_ : ={arg, glob HAETAE_RO.FRO,
              glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} ==>
            ={res, glob HAETAE_RO.FRO,
              glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)}).
  + by proc; sim.
  wp.
  call (_ : ={arg, glob HAETAE_RO.FRO,
              glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} ==>
            ={res, glob HAETAE_RO.FRO,
              glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)}).
  + by proc; sim.
  wp.
  rnd.
  by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                        /signature_query_budget_count; smt.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                  /signature_query_budget_count; smt.
qed.

local equiv disjoint_counted_R_adversary_to_concrete_budgeted_ro_exact_hyperball_adversary :
  BudgetedSignHybridDisjointGame
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjoint.OrclCount
       (BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))).Adv.forge ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).A.forge :
  ={arg, glob A, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} /\
  BudgetedSignHybridDisjointGame.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  BudgetedSignHybridDisjointGame.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{1} /\
  BudgetedSignHybridDisjoint.Count.c{1} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} ==>
  ={res, glob A, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
    glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} /\
  BudgetedSignHybridDisjointGame.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  BudgetedSignHybridDisjointGame.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  0 <= BudgetedSignHybridDisjoint.Count.c{1} /\
  BudgetedSignHybridDisjoint.Count.c{1} <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  budgeted_paper_sim_signing_count_discipline
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2}.
proof.
proc
  (={glob HAETAE_RO.FRO,
     glob ROMInternalTranscriptBudgetedPaperSimAsNMA,
     glob ROExactHyperballPaperSimSampler(HAETAE_RO.FRO)} /\
   BudgetedSignHybridDisjointGame.pk_current{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
   BudgetedSignHybridDisjointGame.signing_count{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
   0 <= BudgetedSignHybridDisjoint.Count.c{1} /\
   BudgetedSignHybridDisjoint.Count.c{1} <=
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
   budgeted_paper_sim_signing_count_discipline
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2}) => //.
+ proc*.
  call disjoint_counted_R_game_ah_get_to_concrete_budgeted_ro_exact_hyperball_ah_get.
  by auto => />; smt.
proc*.
call disjoint_counted_R_o_sign_to_concrete_budgeted_ro_exact_hyperball_o_sign.
by auto => />.
qed.

local equiv disjoint_Rn_to_concrete_budgeted_ro_exact_hyperball_nma_equiv :
  BudgetedSignHybridDisjoint.Rn
    (BudgetedSignHybridDisjointOrclb,
     BudgetedSignHybridDisjointGame).main ~
  SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
    ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main :
  ={glob A, glob HAETAE_RO.FRO} ==>
  res{1} = res{2}.
proof.
proc.
inline BudgetedSignHybridDisjoint.Count.init
       BudgetedSignHybridDisjointGame
         (BudgetedSignHybridDisjointOrclb,
          BudgetedSignHybridDisjoint.OrclCount
            (BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))).main
       BudgetedSignHybridDisjointOrclb.leaks.
rcondt {1} 3.
+ by auto.
inline ROMInternalTranscriptBudgetedPaperSimAsNMA
  (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
   HAETAE_RO.FRO).forge
  HAETAE(HAETAE_RO.FRO).verify.
wp.
call disjoint_counted_R_adversary_to_concrete_budgeted_ro_exact_hyperball_adversary.
inline ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).init
       ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).init.
wp.
inline HAETAE(HAETAE_RO.FRO).kg.
wp.
inline HAETAE_RO.FRO.get.
wp.
rnd.
wp.
rnd.
inline HAETAE_RO.FRO.init.
by auto => />; rewrite /budgeted_paper_sim_signing_count_discipline
                    /budgeted_sign_hybrid_output_keypair
                    /signature_query_budget_count;
  smt(seed_distribution_lossless ro_output_distribution_lossless).
qed.

local lemma disjoint_Rn_to_concrete_budgeted_ro_exact_hyperball_adapter &m :
  Pr[BudgetedSignHybridDisjoint.Rn
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjointGame).main() @ &m : res] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res].
proof.
byequiv disjoint_Rn_to_concrete_budgeted_ro_exact_hyperball_nma_equiv => //.
qed.

local lemma concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting_from_lossy_forge_switch_rule_and_adapters &m :
  islossless BudgetedSignHybridDisjointOrclb.leaks =>
  islossless BudgetedSignHybridDisjointOrclb.orclL =>
  islossless BudgetedSignHybridDisjointOrclb.orclR =>
  (forall (Ob <: BudgetedSignHybridDisjoint.Orclb
                  {-BudgetedSignHybridDisjointGame})
          (LR <: BudgetedSignHybridDisjoint.Orcl
                  {-BudgetedSignHybridDisjointGame}),
     islossless LR.orcl =>
     islossless Ob.leaks =>
     islossless Ob.orclL =>
     islossless Ob.orclR =>
     islossless BudgetedSignHybridDisjointGame(Ob, LR).main) =>
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointSurfaceHybGame
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .main() @ &m :
       budgeted_sign_hybrid_disjoint_surface_verify_clean_event
         res (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> leaks_ll orclL_ll orclR_ll game_ll lossy_forge_switch.
apply
  (concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting_from_lossy_forge_switch_rule_and_attempt_adapter
     &m leaks_ll orclL_ll orclR_ll game_ll lossy_forge_switch).
by apply disjoint_Rn_to_concrete_budgeted_ro_exact_hyperball_adapter.
qed.

local lemma real_le_congr_from_equal_sides
    (left_hyb left_orclb right_hyb right_orclb loss : real) :
  left_hyb = left_orclb =>
  right_hyb = right_orclb =>
  left_orclb <= right_orclb + loss =>
  left_hyb <= right_hyb + loss.
proof.
by smt.
qed.

local equiv budgeted_sign_hybrid_disjoint_orclb_orclL_self :
  BudgetedSignHybridDisjointOrclb.orclL ~
  BudgetedSignHybridDisjointOrclb.orclL :
  ={arg, glob BudgetedSignHybridDisjointOrclb} ==>
  ={res, glob BudgetedSignHybridDisjointOrclb}.
proof.
by proc; sim.
qed.

local equiv budgeted_sign_hybrid_disjoint_orclb_orclR_self :
  BudgetedSignHybridDisjointOrclb.orclR ~
  BudgetedSignHybridDisjointOrclb.orclR :
  ={arg, glob BudgetedSignHybridDisjointOrclb} ==>
  ={res, glob BudgetedSignHybridDisjointOrclb}.
proof.
by proc; sim.
qed.

local equiv budgeted_sign_hybrid_disjoint_L_orcl_orclL :
  BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb).orcl ~
  BudgetedSignHybridDisjointOrclb.orclL :
  ={arg, glob BudgetedSignHybridDisjointOrclb} ==>
  ={res, glob BudgetedSignHybridDisjointOrclb}.
proof.
proc.
inline BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb).orcl.
by sim.
qed.

local equiv budgeted_sign_hybrid_disjoint_R_orcl_orclR :
  BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb).orcl ~
  BudgetedSignHybridDisjointOrclb.orclR :
  ={arg, glob BudgetedSignHybridDisjointOrclb} ==>
  ={res, glob BudgetedSignHybridDisjointOrclb}.
proof.
proc.
inline BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb).orcl.
by sim.
qed.

local module BudgetedSignHybridDisjointOrclbCallL = {
  proc orcl(qry : SIG.query) : signature = {
    var sig : signature;

    sig <@ BudgetedSignHybridDisjointOrclb.orclL(qry);
    return sig;
  }
}.

local module BudgetedSignHybridDisjointOrclbCallR = {
  proc orcl(qry : SIG.query) : signature = {
    var sig : signature;

    sig <@ BudgetedSignHybridDisjointOrclb.orclR(qry);
    return sig;
  }
}.

local equiv budgeted_sign_hybrid_disjoint_orclb_callL_orclL :
  BudgetedSignHybridDisjointOrclbCallL.orcl ~
  BudgetedSignHybridDisjointOrclb.orclL :
  ={arg, glob BudgetedSignHybridDisjointOrclb} ==>
  ={res, glob BudgetedSignHybridDisjointOrclb}.
proof.
proc.
inline *.
by sim.
qed.

local equiv budgeted_sign_hybrid_disjoint_orclb_callR_orclR :
  BudgetedSignHybridDisjointOrclbCallR.orcl ~
  BudgetedSignHybridDisjointOrclb.orclR :
  ={arg, glob BudgetedSignHybridDisjointOrclb} ==>
  ={res, glob BudgetedSignHybridDisjointOrclb}.
proof.
proc.
inline *.
by sim.
qed.

local lemma budgeted_sign_hybrid_disjoint_active_hyborcl_clean_le_from_orclb_continuation
    (P : signature -> int -> glob BudgetedSignHybridDisjointGame ->
         glob BudgetedSignHybridDisjointOrclb -> bool)
    (qry : SIG.query) &m :
  BudgetedSignHybridDisjoint.HybOrcl.l0{m} =
    BudgetedSignHybridDisjoint.HybOrcl.l{m} =>
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .orcl(qry) @ &m :
       P res BudgetedSignHybridDisjoint.HybOrcl.l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .orcl(qry) @ &m :
       P res BudgetedSignHybridDisjoint.HybOrcl.l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof.
move=> active orcl_step.
have left_hyb_wrap_eq :
  Pr[BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .orcl(qry) @ &m :
       P res BudgetedSignHybridDisjoint.HybOrcl.l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointOrclbCallL.orcl(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)].
+ byequiv => //.
  proc.
  rcondf {1} 1; first by auto; smt.
  rcondt {1} 1; first by auto; smt.
  inline BudgetedSignHybridDisjointOrclbCallL.orcl.
  wp.
  call budgeted_sign_hybrid_disjoint_L_orcl_orclL.
  by auto => />; smt.
have left_wrap_eq :
  Pr[BudgetedSignHybridDisjointOrclbCallL.orcl(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)].
+ byequiv => //.
  proc*.
  call budgeted_sign_hybrid_disjoint_orclb_callL_orclL.
  by auto.
have left_eq :
  Pr[BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .orcl(qry) @ &m :
       P res BudgetedSignHybridDisjoint.HybOrcl.l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)]
  by smt.
have right_hyb_wrap_eq :
  Pr[BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .orcl(qry) @ &m :
       P res BudgetedSignHybridDisjoint.HybOrcl.l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointOrclbCallR.orcl(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)].
+ byequiv => //.
  proc.
  rcondf {1} 1; first by auto; smt.
  rcondt {1} 1; first by auto; smt.
  inline BudgetedSignHybridDisjointOrclbCallR.orcl.
  wp.
  call budgeted_sign_hybrid_disjoint_R_orcl_orclR.
  by auto => />; smt.
have right_wrap_eq :
  Pr[BudgetedSignHybridDisjointOrclbCallR.orcl(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)].
+ byequiv => //.
  proc*.
  call budgeted_sign_hybrid_disjoint_orclb_callR_orclR.
  by auto.
have right_eq :
  Pr[BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .orcl(qry) @ &m :
       P res BudgetedSignHybridDisjoint.HybOrcl.l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)]
  by smt.
have h :=
  real_le_congr_from_equal_sides
    (Pr[BudgetedSignHybridDisjoint.HybOrcl
         (BudgetedSignHybridDisjointOrclb,
          BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
         .orcl(qry) @ &m :
         P res BudgetedSignHybridDisjoint.HybOrcl.l
           (glob BudgetedSignHybridDisjointGame)
           (glob BudgetedSignHybridDisjointOrclb) /\
         budgeted_sign_hybrid_disjoint_orclb_clean
           (glob BudgetedSignHybridDisjointOrclb)])
    (Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
         P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
           (glob BudgetedSignHybridDisjointGame)
           (glob BudgetedSignHybridDisjointOrclb) /\
         budgeted_sign_hybrid_disjoint_orclb_clean
           (glob BudgetedSignHybridDisjointOrclb)])
    (Pr[BudgetedSignHybridDisjoint.HybOrcl
         (BudgetedSignHybridDisjointOrclb,
          BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
         .orcl(qry) @ &m :
         P res BudgetedSignHybridDisjoint.HybOrcl.l
           (glob BudgetedSignHybridDisjointGame)
           (glob BudgetedSignHybridDisjointOrclb) /\
         budgeted_sign_hybrid_disjoint_orclb_clean
           (glob BudgetedSignHybridDisjointOrclb)])
    (Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
         P res (BudgetedSignHybridDisjoint.HybOrcl.l + 1)
           (glob BudgetedSignHybridDisjointGame)
           (glob BudgetedSignHybridDisjointOrclb) /\
         budgeted_sign_hybrid_disjoint_orclb_clean
           (glob BudgetedSignHybridDisjointOrclb)])
    rejection_sampling_loss_term.
by smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_orclb_continuation_from_signature_framing
    (P : signature -> int -> glob BudgetedSignHybridDisjointGame ->
         glob BudgetedSignHybridDisjointOrclb -> bool)
    (p : signature -> bool) (qry : SIG.query) (next_l : int) &m :
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       p res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =>
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       p res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       p res] +
    rejection_sampling_loss_term =>
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       p res] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] =>
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof.
by smt.
qed.

local lemma budgeted_sign_hybrid_disjoint_orclb_left_state_to_signature_frame
    (P : signature -> int -> glob BudgetedSignHybridDisjointGame ->
         glob BudgetedSignHybridDisjointOrclb -> bool)
    (p : signature -> bool) (qry : SIG.query) (next_l : int) &m :
  (forall (sig : signature)
          (gg : glob BudgetedSignHybridDisjointGame)
          (go : glob BudgetedSignHybridDisjointOrclb),
     P sig next_l gg go => p sig) =>
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       p res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)].
proof.
by move=> frame; smt(mu_sub).
qed.

local lemma budgeted_sign_hybrid_disjoint_orclb_right_signature_to_state_frame
    (P : signature -> int -> glob BudgetedSignHybridDisjointGame ->
         glob BudgetedSignHybridDisjointOrclb -> bool)
    (p : signature -> bool) (qry : SIG.query) (next_l : int) &m :
  (forall (sig : signature)
          (gg : glob BudgetedSignHybridDisjointGame)
          (go : glob BudgetedSignHybridDisjointOrclb),
     p sig =>
       P sig next_l gg go /\
       budgeted_sign_hybrid_disjoint_orclb_clean go) =>
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       p res] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)].
proof.
by move=> frame; smt(mu_sub).
qed.

local lemma budgeted_sign_hybrid_disjoint_orclb_left_state_to_exists_signature_frame
    (P : signature -> int -> glob BudgetedSignHybridDisjointGame ->
         glob BudgetedSignHybridDisjointOrclb -> bool)
    (qry : SIG.query) (next_l : int) &m :
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       (exists (gg : glob BudgetedSignHybridDisjointGame),
          exists (go : glob BudgetedSignHybridDisjointOrclb),
            P res next_l gg go /\
            budgeted_sign_hybrid_disjoint_orclb_clean go) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)].
proof.
by smt(mu_sub).
qed.

local lemma budgeted_sign_hybrid_disjoint_orclb_restricted_state_continuation_from_signature_loss
    (P : signature -> int -> glob BudgetedSignHybridDisjointGame ->
         glob BudgetedSignHybridDisjointOrclb -> bool)
    (p : signature -> bool) (qry : SIG.query) (next_l : int) &m :
  (forall (sig : signature)
          (gg : glob BudgetedSignHybridDisjointGame)
          (go : glob BudgetedSignHybridDisjointOrclb),
     P sig next_l gg go => p sig) =>
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       p res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       p res] +
    rejection_sampling_loss_term =>
  (forall (sig : signature)
          (gg : glob BudgetedSignHybridDisjointGame)
          (go : glob BudgetedSignHybridDisjointOrclb),
     p sig =>
       P sig next_l gg go /\
       budgeted_sign_hybrid_disjoint_orclb_clean go) =>
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       P res next_l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof.
move=> left_frame sig_loss right_frame.
apply
  (budgeted_sign_hybrid_disjoint_orclb_continuation_from_signature_framing
     P p qry next_l &m).
+ by apply
     (budgeted_sign_hybrid_disjoint_orclb_left_state_to_signature_frame
        P p qry next_l &m).
+ exact sig_loss.
by apply
   (budgeted_sign_hybrid_disjoint_orclb_right_signature_to_state_frame
      P p qry next_l &m).
qed.

local lemma budgeted_sign_hybrid_disjoint_active_hyborcl_clean_le_from_signature_restricted
    (P : signature -> int -> glob BudgetedSignHybridDisjointGame ->
         glob BudgetedSignHybridDisjointOrclb -> bool)
    (p : signature -> bool) (qry : SIG.query) &m :
  BudgetedSignHybridDisjoint.HybOrcl.l0{m} =
    BudgetedSignHybridDisjoint.HybOrcl.l{m} =>
  (forall (sig : signature)
          (gg : glob BudgetedSignHybridDisjointGame)
          (go : glob BudgetedSignHybridDisjointOrclb),
     P sig (BudgetedSignHybridDisjoint.HybOrcl.l{m} + 1) gg go =>
       p sig) =>
  Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) @ &m :
       p res /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) @ &m :
       p res] +
    rejection_sampling_loss_term =>
  (forall (sig : signature)
          (gg : glob BudgetedSignHybridDisjointGame)
          (go : glob BudgetedSignHybridDisjointOrclb),
     p sig =>
       P sig (BudgetedSignHybridDisjoint.HybOrcl.l{m} + 1) gg go /\
       budgeted_sign_hybrid_disjoint_orclb_clean go) =>
  Pr[BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
       .orcl(qry) @ &m :
       P res BudgetedSignHybridDisjoint.HybOrcl.l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] <=
  Pr[BudgetedSignHybridDisjoint.HybOrcl
       (BudgetedSignHybridDisjointOrclb,
        BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
       .orcl(qry) @ &m :
       P res BudgetedSignHybridDisjoint.HybOrcl.l
         (glob BudgetedSignHybridDisjointGame)
         (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)] +
    rejection_sampling_loss_term.
proof.
move=> active left_frame sig_loss right_frame.
apply
  (budgeted_sign_hybrid_disjoint_active_hyborcl_clean_le_from_orclb_continuation
     P qry &m active).
have h :=
  budgeted_sign_hybrid_disjoint_orclb_restricted_state_continuation_from_signature_loss
    P p qry (BudgetedSignHybridDisjoint.HybOrcl.l{m} + 1) &m
    left_frame sig_loss right_frame.
by smt.
qed.

(* The checked active-HybOrcl bridge above only converts a one-call
   Orclb-level continuation inequality into the corresponding active hybrid
   oracle inequality.  It does not prove the genuine sampler loss: that still
   requires an Orclb-level continuation theorem for orclL/orclR from the
   sampler push-forward laws and clean-state invariants.

   Focused Orclb-level continuation-loss spike:
   the exact missing premise for using the active-HybOrcl bridge is a theorem
   of the following shape.  For every continuation

     P : signature -> glob BudgetedSignHybridDisjointGame ->
         glob BudgetedSignHybridDisjointOrclb -> bool

   and every query qry, assuming structural_to_exact_hyperball_paper_sample_loss_obligation,
   sampler_rom_covered for the current ROM table/adversary hash log/sampler
   expand log, !sampler_bad_prequery, an active signing counter, and
   ROSigningAttemptPaperSimSampler.sk_current =
   ROExactHyperballPaperSimSampler.sk_current, prove

     Pr[BudgetedSignHybridDisjointOrclb.orclL(qry) :
          P res (glob BudgetedSignHybridDisjointGame)
                (glob BudgetedSignHybridDisjointOrclb) /\
          budgeted_sign_hybrid_disjoint_orclb_clean
            (glob BudgetedSignHybridDisjointOrclb)]
     <=
     Pr[BudgetedSignHybridDisjointOrclb.orclR(qry) :
          P res (glob BudgetedSignHybridDisjointGame)
                (glob BudgetedSignHybridDisjointOrclb) /\
          budgeted_sign_hybrid_disjoint_orclb_clean
            (glob BudgetedSignHybridDisjointOrclb)]
       + rejection_sampling_loss_term.

   A direct derivation from
     concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface
   is blocked by the postcondition type.  That checked lemma supports only
   p : signature -> bool and therefore cannot mention the post-call ROM table,
   transcript records, sampler_expand_queries, sampler_bad_prequery, Hybrid
   counters, or glob BudgetedSignHybridDisjointGame/Orclb.  Instantiating p
   with a term involving glob BudgetedSignHybridDisjointOrclb would freeze the
   globals at the surrounding memory, not at the post-state of orclL/orclR.

   The narrow failed proof shape is:

     bypr=> &m premises.
     byphoare (_ : pre ==> P res (glob Game) (glob Orclb) /\ clean) => //.
     proc; inline BudgetedSignHybridDisjointOrclb.orclL
                  BudgetedSignHybridDisjointOrclb.orclR; ...
     call concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface.

   The call is not applicable: the proof state after opening orclL/orclR has a
   sampler call followed by two lazy-ROM gets and transcript/log assignments,
   while the available one-call lemma is a one-sided probability inequality for
   ROMInternalTranscriptBudgetedPaperSimAsNMA(...).O.sign with a signature-only
   postcondition.  EasyCrypt's ordinary call/byequiv rules do not consume that
   one-sided inequality as a stateful continuation rule.

   The next helper needed is therefore either:
   - a strengthened one-call theorem whose postcondition is a continuation over
     the returned signature and the post-state globals listed above; or
   - a decomposition theorem showing that the post-sample lazy-ROM gets and log
     updates can be framed into a pure signature predicate before invoking the
     existing signature-only one-call loss.

   The checked framing bridge
     budgeted_sign_hybrid_disjoint_orclb_continuation_from_signature_framing
   records the second route precisely.  It reduces the desired stateful Orclb
   inequality to three premises: a left-state-to-signature upper frame, the
   existing signature-level loss, and a right-signature-to-state lower frame.
   The unresolved proof work is exactly those two state-framing inequalities:
   they must account for the lazy-ROM table updates, transcript-record updates,
   sampler_expand_queries, sampler_bad_prequery, and the Hybrid l/l0 state.

   Focused suffix-framing spike:
   the easy logical framing facts are now checked by
     budgeted_sign_hybrid_disjoint_orclb_left_state_to_signature_frame,
     budgeted_sign_hybrid_disjoint_orclb_right_signature_to_state_frame, and
     budgeted_sign_hybrid_disjoint_orclb_left_state_to_exists_signature_frame.
   The combined restricted rule
     budgeted_sign_hybrid_disjoint_orclb_restricted_state_continuation_from_signature_loss
   is also checked: it is the strongest currently available route from a
   signature-only loss to a stateful Orclb continuation.  Its right-frame
   premise requires the pure signature predicate p to imply the desired
   continuation and clean flag for every post-state, so it is usable only for
   state-insensitive continuations or continuations whose state component is
   already forced independently.

   The next checked bridge
     budgeted_sign_hybrid_disjoint_active_hyborcl_clean_le_from_signature_restricted
   lifts that restricted Orclb rule through the active HybOrcl branch l = l0.
   Thus the restricted route is usable at exactly the active switch point, but
   only if the actual post-switch continuation can be expressed through such a
   pure signature predicate p.

   The actual clean/clean HybGame continuation does not fit that restricted
   shape.  After the active signing call, the continuation is the rest of
   A(AH,O).forge followed by verify_internal, with final event
   res /\ budgeted_sign_hybrid_disjoint_orclb_clean (glob
   BudgetedSignHybridDisjointOrclb).  That event depends on the adversary
   private state, future AH.get/O.sign calls, glob HAETAE_RO.FRO, the game
   pk/signing counter, transcript and record logs, adversary_hash_queries,
   sampler_expand_queries, sampler_bad_prequery, and the Hybrid l/l0 state.
   None of those components is determined by the active call's returned
   signature alone.

   This does not solve the substantive suffix problem for the actual HybGame
   continuation or arbitrary P, because
   the only unconditional pure-signature left frame is the existential
   predicate

     exists post-game post-orclb,
       P sig next_l post-game post-orclb /\ clean post-orclb.

   The matching right lower frame for that predicate is too strong: an
   exact-side execution with the same returned signature need not have the
   witness post-state selected by the existential predicate.  The post-state of
   orclR contains the lazy-ROM table after the message-hash and challenge-hash
   gets, the sample-dependent challenge query, transcript/record logs, the
   self-logged sampler query, sampler_bad_prequery, and Hybrid l/l0 state.
   A predicate P may distinguish two such post-states even when the returned
   signature is the same.  Therefore no p : signature -> bool can generally
   provide both the left upper frame and the right lower frame for arbitrary P.

   The exact failed strengthening is:

     byphoare (_ :
       pre ==>
       p res <=>
       P res next_l (glob BudgetedSignHybridDisjointGame)
                    (glob BudgetedSignHybridDisjointOrclb) /\
       budgeted_sign_hybrid_disjoint_orclb_clean
         (glob BudgetedSignHybridDisjointOrclb)) => //.
     proc; inline BudgetedSignHybridDisjointOrclb.orclR; ...

   The proof cannot close after the two HAETAE_RO.FRO.get calls: their random
   table updates are observable in glob BudgetedSignHybridDisjointOrclb but are
   not encoded in res.  A successful route needs either a state-insensitive
   continuation P, or a stronger stateful sampler/lazy-ROM coupling theorem
   whose postcondition ranges over the returned signature and post-state. *)

(* Exact remaining one-switch obligation for the disjoint Hybrid_restr route.
   The checked lemmas above show the arithmetic accumulation available from
   Hybrid_restr once a single active signing-call comparison is supplied.
   There are two checked routes.  The coarse route accepts the res/res
   one-switch inequality:

     Pr[BudgetedSignHybridDisjoint.HybGame
          (BudgetedSignHybridDisjointGame,
           BudgetedSignHybridDisjointOrclb,
           BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
          .main() : res]
     <=
     Pr[BudgetedSignHybridDisjoint.HybGame
          (BudgetedSignHybridDisjointGame,
           BudgetedSignHybridDisjointOrclb,
           BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
          .main() : res]
       + rejection_sampling_loss_term.

   The sharper route expresses the clean flag as the pure predicate
   budgeted_sign_hybrid_disjoint_orclb_clean on
   glob BudgetedSignHybridDisjointOrclb.  Projection 8 of that global tuple is
   ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery in the
   disjoint Orclb package.  Directly mentioning the mutable module variable
   inside the predicate supplied to Hybrid_restr is not accepted: the library
   theorem requires a pure predicate over glob Game, glob Orclb, the selected
   index, and the result.  With that projection, the exact remaining
   clean/clean one-switch premise is

     Pr[BudgetedSignHybridDisjoint.HybGame
          (BudgetedSignHybridDisjointGame,
           BudgetedSignHybridDisjointOrclb,
           BudgetedSignHybridDisjoint.L(BudgetedSignHybridDisjointOrclb))
          .main() :
          res /\
          budgeted_sign_hybrid_disjoint_orclb_clean
            (glob BudgetedSignHybridDisjointOrclb)]
     <=
     Pr[BudgetedSignHybridDisjoint.HybGame
          (BudgetedSignHybridDisjointGame,
           BudgetedSignHybridDisjointOrclb,
           BudgetedSignHybridDisjoint.R(BudgetedSignHybridDisjointOrclb))
          .main() :
          res /\
          budgeted_sign_hybrid_disjoint_orclb_clean
            (glob BudgetedSignHybridDisjointOrclb)]
       + rejection_sampling_loss_term.

   The checked clean bridge then weakens the final right-clean event to right
   res by event monotonicity after the Hybrid_restr accumulation.  This avoids
   needing a stronger res/res one-switch bound, but it still requires proving
   the active-call clean/clean comparison above.

   In these two games, HybOrcl uses orclR before the selected index l0, uses
   orclL/orclR only at l = l0, and uses orclL after l0.  The proof therefore
   has exactly one sampler-distribution difference to charge.  The obstruction
   is the active-call continuation: at l = l0 the postcondition is not merely
   p sig for p : signature -> bool.  It is the remaining execution of
   A(AH,O).forge plus verify_internal, and it depends on glob A, glob
   HAETAE_RO.FRO, the transcript/signing logs, both signing counters, the
   adversary hash log, sampler_expand_queries, and sampler_bad_prequery.

   The checked one-call lemma
     concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface
   can supply the local rejection-sampling loss only after a stronger
   stateful oracle rule has related that continuation to a signature predicate.
   The required invariant around the active LR.orcl call is:
   - both hybrid runs have identical public key, adversary-visible hash log,
     transcript log, signing-record log, adversary hash counter, and local
     Hybrid/HopGames signing counters;
   - the shared Orclb-side signing_count is active and below
     signature_query_budget_count;
   - sampler_rom_covered holds on the attempt side for the current ROM table,
     adversary_hash_queries, and sampler_expand_queries;
   - sampler_bad_prequery is false before the attempt-side call, and the
     sampled seed is fresh for both adversary_hash_queries and
     sampler_expand_queries;
   - ROSigningAttemptPaperSimSampler.sk_current =
     ROExactHyperballPaperSimSampler.sk_current.

   Without this stateful one-switch rule, the theorem above is the strongest
   machine-checked consequence currently available from Hybrid_restr: it proves
   the arithmetic accumulation, conditional on the missing one-switch bound,
   but it does not prove the clean-event NMA lifting itself.

   Focused clean/clean one-switch spike:
   a direct byequiv/phoare proof of the displayed HybGame inequality reaches
   the call to BudgetedSignHybridDisjointGame(...).Adv.forge.  At that point
   the proof needs an oracle specification for
   BudgetedSignHybridDisjoint.HybOrcl(...).orcl that is exact except when
   HybOrcl.l = HybOrcl.l0.  In that active branch the left run calls
   BudgetedSignHybridDisjointOrclb.orclL and the right run calls
   BudgetedSignHybridDisjointOrclb.orclR; after the call, the continuation is
   the rest of the adversary plus verify_internal, with the final predicate
   res /\ budgeted_sign_hybrid_disjoint_orclb_clean (glob
   BudgetedSignHybridDisjointOrclb).

   The missing continuation principle is therefore:
   for every continuation K over the returned signature, the adversary state,
   glob HAETAE_RO.FRO, glob BudgetedSignHybridDisjointGame, and glob
   BudgetedSignHybridDisjointOrclb, prove a one-sided call rule

     Pr[HybOrcl(...,L(...)).orcl(q) :
          K res post_state /\ budgeted_sign_hybrid_disjoint_orclb_clean
            (glob BudgetedSignHybridDisjointOrclb)]
     <=
     Pr[HybOrcl(...,R(...)).orcl(q) :
          K res post_state /\ budgeted_sign_hybrid_disjoint_orclb_clean
            (glob BudgetedSignHybridDisjointOrclb)]
       + rejection_sampling_loss_term

   under the invariant
     HybOrcl.l = HybOrcl.l0,
     BudgetedSignHybridDisjointGame.signing_count <
       signature_query_budget_count,
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current =
       BudgetedSignHybridDisjointGame.pk_current,
     ROSigningAttemptPaperSimSampler.sk_current =
       ROExactHyperballPaperSimSampler.sk_current,
     sampler_rom_covered HAETAE_RO.FRO.m adversary_hash_queries
       sampler_expand_queries,
     !sampler_bad_prequery, and identical public logs/counters on both sides.

   concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface is
   still too weak for that call rule because its p : signature -> bool cannot
   mention the post-call ROM table, transcript records, Hybrid counters, glob A,
   or future oracle behavior.  It is a local distribution comparison for one
   signing result, not a continuation-passing lossy oracle rule.

   Actual stateful HybGame continuation spike:
   the verifier-clean suffix has now been named by the checked predicate
     budgeted_sign_hybrid_disjoint_verify_clean_event.
   After Adv.forge returns (m,ctx,sig), the final event is exactly
     budgeted_sign_hybrid_disjoint_verify_clean_event pk (m,ctx,sig)
       (glob BudgetedSignHybridDisjointOrclb).
   This extraction isolates the easy deterministic suffix; it does not expose
   the harder continuation inside the abstract adversary.

   The one-switch continuation generated at the active HybOrcl call is:
   - resume the current invocation of A(AH,O).forge with the returned signature;
   - allow future AH.get calls through Ob.leaks and future O.sign calls through
     the same hybrid oracle, with l advanced past l0;
   - run verify_internal on the final forgery; and
   - test budgeted_sign_hybrid_disjoint_orclb_clean on the final Orclb global.

   A direct proof attempt would need to call Adv.forge with an oracle rule for
   HybOrcl.orcl that is approximate at l = l0 and exact elsewhere.  EasyCrypt's
   adversary call rule here accepts exact relational oracle specifications, not
   a one-sided lossy specification whose postcondition ranges over the returned
   signature, glob A, glob HAETAE_RO.FRO, glob
   BudgetedSignHybridDisjointGame, glob BudgetedSignHybridDisjointOrclb, and
   the later verifier-clean suffix.

   The narrow next lemma needed is a stateful active-switch rule of the shape:

     Pr[BudgetedSignHybridDisjoint.HybGame(...,L(...)).main() :
          budgeted_sign_hybrid_disjoint_verify_clean_event
            BudgetedSignHybridDisjointGame.pk_current res_forgery
            (glob BudgetedSignHybridDisjointOrclb)]
     <=
     Pr[BudgetedSignHybridDisjoint.HybGame(...,R(...)).main() :
          budgeted_sign_hybrid_disjoint_verify_clean_event
            BudgetedSignHybridDisjointGame.pk_current res_forgery
            (glob BudgetedSignHybridDisjointOrclb)]
       + rejection_sampling_loss_term,

   where res_forgery abbreviates the final (m,ctx,sig) returned by the resumed
   adversary.  This cannot currently be stated directly against HybGame.main
   because main returns only the verifier boolean, not the forgery triple.  A
   proof-ready formulation must either introduce a ghost/surface game returning
   the forgery triple and final globals, or prove an adversary-call induction
   principle whose continuation parameter represents the resumed forge plus
   verify_internal suffix.

   Required state relation for that lemma:
   - equal glob A before the active call, followed by a continuation relation
     after the returned signatures are delivered to the adversary;
   - equal lazy-ROM tables except for coupled get extensions generated by the
     active call and future calls;
   - equal pk_current, transcript queries, transcript list, records,
     adversary_hash_queries, sampler_expand_queries, signing counters, and
     Hybrid l/l0 state except for the intended l increment;
   - sampler_rom_covered and !sampler_bad_prequery on the attempt side; and
   - identical sampler secret state between the attempt and exact samplers.

   The current restricted-continuation lemmas cannot supply this because the
   post-switch continuation is not a function of the active returned signature
   alone. *)

lemma concrete_lazy_rom_get_preserves_signature_event
    pk m ctx smp (p : signature -> bool) :
  phoare[HAETAE_RO.FRO.get :
    p (paper_sim_signature haetae_mode pk m ctx smp) ==>
    p (paper_sim_signature haetae_mode pk m ctx smp)] = 1%r.
proof.
proc.
wp.
rnd.
by auto => />; smt(ro_output_distribution_lossless).
qed.

lemma concrete_lazy_rom_get_preserves_signature_event_with_pk
    pk m ctx smp (p : signature -> bool) :
  phoare[HAETAE_RO.FRO.get :
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    p (paper_sim_signature haetae_mode pk m ctx smp) ==>
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    p (paper_sim_signature haetae_mode pk m ctx smp)] = 1%r.
proof.
proc.
wp.
rnd.
by auto => />; smt(ro_output_distribution_lossless).
qed.

lemma concrete_lazy_rom_get_preserves_current_signature_event
    m ctx smp (p : signature -> bool) :
  phoare[HAETAE_RO.FRO.get :
    p (paper_sim_signature haetae_mode
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp) ==>
    p (paper_sim_signature haetae_mode
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp)] = 1%r.
proof.
proc.
wp.
rnd.
by auto => />; smt(ro_output_distribution_lossless).
qed.

lemma concrete_lazy_rom_get_true :
  phoare[HAETAE_RO.FRO.get : true ==> true] = 1%r.
proof.
by conseq concrete_lazy_rom_get_lossless.
qed.

local module ConcreteBudgetedSigningSuffix = {
  proc run(m : message, ctx : context,
           smp : paper_sim_signature_sample) : signature = {
    var ro_y, mu, highbits, lowbits, sig, tr;

    ro_y <@ HAETAE_RO.FRO.get
      (message_hash_query
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current ctx m);
    mu <- ro_message_hash ro_y;
    highbits <-
      paper_sim_commitment_highbits haetae_mode
        ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    lowbits <- paper_sim_commitment_lowbits haetae_mode smp;
    ro_y <@ HAETAE_RO.FRO.get
      (challenge_hash_query haetae_mode highbits lowbits mu);
    sig <-
      paper_sim_signature haetae_mode
        ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx smp;
    tr <-
      transcript_of_signature haetae_mode
        ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current m ctx sig;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries <-
      (m, ctx) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.queries;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts <-
      tr :: ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts;
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records <-
      (m, ctx, sig, tr) :: ROMInternalTranscriptBudgetedPaperSimAsNMA.records;
    return sig;
  }
}.

local lemma concrete_budgeted_signing_suffix_non_rom_state_eq
    msg ctxt smp pk qs trs recs ahc sc ahqs sqs bad :
  phoare[ConcreteBudgetedSigningSuffix.run :
    arg = (msg, ctxt, smp) /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries = qs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts = trs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records = recs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count = ahc /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count = sc /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries = ahqs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries = sqs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery = bad ==>
    res = paper_sim_signature haetae_mode pk msg ctxt smp /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries = (msg, ctxt) :: qs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts =
      transcript_of_signature haetae_mode pk msg ctxt
        (paper_sim_signature haetae_mode pk msg ctxt smp) :: trs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records =
      (msg, ctxt,
       paper_sim_signature haetae_mode pk msg ctxt smp,
       transcript_of_signature haetae_mode pk msg ctxt
         (paper_sim_signature haetae_mode pk msg ctxt smp)) :: recs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count = ahc /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count = sc /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries = ahqs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries = sqs /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery = bad] = 1%r.
proof.
proc.
wp.
call concrete_lazy_rom_get_true.
wp.
call concrete_lazy_rom_get_true.
by auto => />.
qed.

local equiv concrete_budgeted_signing_suffix_self_equiv :
  ConcreteBudgetedSigningSuffix.run ~ ConcreteBudgetedSigningSuffix.run :
  ={arg, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA} ==>
  ={res, glob HAETAE_RO.FRO,
    glob ROMInternalTranscriptBudgetedPaperSimAsNMA}.
proof.
proc.
wp.
call (_ : ={arg, glob HAETAE_RO.FRO} ==>
          ={res, glob HAETAE_RO.FRO}).
+ by proc; sim.
wp.
call (_ : ={arg, glob HAETAE_RO.FRO} ==>
          ={res, glob HAETAE_RO.FRO}).
+ by proc; sim.
by auto => />.
qed.

(* Deterministic signing-suffix state relation.
   The proof-only ConcreteBudgetedSigningSuffix factors the common tail after a
   paper_sim_signature_sample has already been returned by sample_with_seed.
   The checked lemma
     concrete_budgeted_signing_suffix_non_rom_state_eq
   proves that, excluding HAETAE_RO.FRO.m, the tail deterministically returns
   paper_sim_signature haetae_mode pk m ctx smp, appends exactly the expected
   query/transcript/record entries, and preserves pk_current,
   adversary_hash_count, signing_count, adversary_hash_queries,
   sampler_expand_queries, and sampler_bad_prequery.

   The checked equivalence
     concrete_budgeted_signing_suffix_self_equiv
   proves the stronger relational fact needed for wrapper refactorings: if the
   pre-suffix lazy-ROM state, budgeted transcript state, and returned sample are
   equal on both sides, then the post-suffix lazy-ROM state, returned signature,
   and transcript state are equal.

   This does not yet give the resumable active-call loss.  Attempt and exact
   executions enter the suffix after different sampler laws, and an arbitrary
   continuation may inspect HAETAE_RO.FRO.m after the message-hash and
   challenge-hash gets.  The missing theorem must relate those two post-suffix
   ROM tables, not just the non-ROM transcript bookkeeping.  A precise future
   theorem shape is:

     Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
          (seed_coins,m,ctx) ;
        ConcreteBudgetedSigningSuffix.run(m,ctx,smp) :
          R sig (glob HAETAE_RO.FRO) post_budgeted_state]
     <=
     Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
          (seed_coins,m,ctx) ;
        ConcreteBudgetedSigningSuffix.run(m,ctx,smp) :
          R sig (glob HAETAE_RO.FRO) post_budgeted_state]
       + rejection_sampling_loss_term

   for suffix-measurable continuations R equipped with an explicit ROM-table
   relation for the sampler-expand, message-hash, and challenge-hash entries.
   Without that relation, an arbitrary R can still distinguish the exact-side
   independently sampled ROM state from the attempt-side correlated one. *)

lemma concrete_lazy_rom_get_preserves_budgeted_clean_signature_event
    pk m ctx smp (p : signature -> bool) :
  phoare[HAETAE_RO.FRO.get :
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
    p (paper_sim_signature haetae_mode pk m ctx smp) ==>
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
    p (paper_sim_signature haetae_mode pk m ctx smp)] = 1%r.
proof.
proc.
wp.
rnd.
by auto => />; smt(ro_output_distribution_lossless).
qed.

lemma concrete_lazy_rom_get_preserves_budgeted_clean_signature_event_hoare
    pk m ctx smp (p : signature -> bool) :
  hoare[HAETAE_RO.FRO.get :
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
    p (paper_sim_signature haetae_mode pk m ctx smp) ==>
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
    p (paper_sim_signature haetae_mode pk m ctx smp)].
proof.
proc.
wp.
rnd.
by auto => />; smt(ro_output_distribution_lossless).
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_lossless :
  islossless ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed.
proof.
proc.
wp.
call concrete_lazy_rom_get_lossless.
by auto.
qed.

lemma concrete_budgeted_ro_signing_attempt_o_sign_active_clean_signature_structural_le
    pk sk msg ctxt (p : signature -> bool) :
  phoare[ROMInternalTranscriptBudgetedPaperSimAsNMA
          (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
           HAETAE_RO.FRO).O.sign :
    arg = (msg, ctxt) /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <
      signature_query_budget_count /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    ROSigningAttemptPaperSimSampler.sk_current = sk /\
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries /\
    ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery ==>
    p res /\
    ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  (mu (dsigning_attempt_state haetae_mode sk msg ctxt)
     (fun st =>
        p (paper_sim_signature haetae_mode pk msg ctxt
             (paper_sim_sample_from_rejection_attempt st)))).
proof.
proc.
if.
+ seq 8 :
    (m = msg /\
     ctx = ctxt /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
     ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp))
    (mu (dsigning_attempt_state haetae_mode sk msg ctxt)
       (fun st =>
          p (paper_sim_signature haetae_mode pk msg ctxt
               (paper_sim_sample_from_rejection_attempt st))))
    (1%r) _ (0%r)
    (m = msg /\
     ctx = ctxt /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
     ROSigningAttemptPaperSimSampler.sk_current = sk /\
     sampler_rom_covered
       HAETAE_RO.FRO.m
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries);
    1: (wp;
        call concrete_ro_signing_attempt_sample_with_seed_preserves_sampler_rom_covered_budgeted_logs;
        wp; rnd;
        by auto => />; smt(signing_coin_distribution_lossless
                           sampler_rom_covered_self_log_preserves)).
+ wp.
  call (concrete_ro_signing_attempt_sample_with_seed_guarded_clean_structural_arg_le
    sk msg ctxt
    (fun smp =>
       p (paper_sim_signature haetae_mode pk msg ctxt smp))).
  wp.
  rnd.
  by auto => />; smt(sampler_rom_covered_fresh_after_clean_seed
                     mu_bounded signing_coin_distribution_lossless).
+ inline HAETAE_RO.FRO.get.
  wp.
  rnd.
  wp.
  rnd.
  by auto => />; smt(mu_bounded ro_output_distribution_lossless).
+ hoare.
  inline HAETAE_RO.FRO.get.
  wp.
  rnd.
  wp.
  rnd.
  by auto => />; smt.
+ by smt(mu_bounded).
by auto => />; smt.
qed.

lemma concrete_budgeted_ro_exact_hyperball_o_sign_active_signature_exact
    pk sk msg ctxt (p : signature -> bool) :
  phoare[ROMInternalTranscriptBudgetedPaperSimAsNMA
          (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
           HAETAE_RO.FRO).O.sign :
    arg = (msg, ctxt) /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count <
      signature_query_budget_count /\
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
    ROExactHyperballPaperSimSampler.sk_current = sk ==>
    p res] =
  (mu (dexact_hyperball_signing_attempt_state haetae_mode sk msg ctxt)
    (fun st =>
       p (paper_sim_signature haetae_mode pk msg ctxt
            (paper_sim_sample_from_rejection_attempt st)))).
proof.
proc.
if.
+ seq 8 :
    (m = msg /\
     ctx = ctxt /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp))
    (mu (dexact_hyperball_signing_attempt_state haetae_mode sk msg ctxt)
       (fun st =>
          p (paper_sim_signature haetae_mode pk msg ctxt
               (paper_sim_sample_from_rejection_attempt st))))
    (1%r) _ (0%r)
    (m = msg /\
     ctx = ctxt /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current = pk /\
     ROExactHyperballPaperSimSampler.sk_current = sk);
    1: by auto => />.
+ wp.
  call (concrete_ro_exact_hyperball_sample_with_seed_exact_no_seed
          sk msg ctxt
          (fun smp =>
             p (paper_sim_signature haetae_mode pk msg ctxt smp))).
  by auto => />; smt(signing_coin_distribution_lossless).
+ wp.
  call concrete_lazy_rom_get_true.
  wp.
  call concrete_lazy_rom_get_true.
  by auto => />.
+ hoare.
  inline HAETAE_RO.FRO.get.
  wp.
  rnd.
  wp.
  rnd.
  by auto => />; smt.
+ by smt(mu_bounded).
by auto => />; smt.
qed.

lemma concrete_budgeted_ro_exact_hyperball_sample_with_seed_to_o_sign_active_projection
    seed_coins pk sk msg ctxt (p : signature -> bool) &m :
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} <
    signature_query_budget_count =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m} = pk =>
  ROExactHyperballPaperSimSampler.sk_current{m} = sk =>
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, msg, ctxt) @ &m :
       p (paper_sim_signature haetae_mode pk msg ctxt res)] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(msg, ctxt) @ &m :
       p res].
proof.
move=> active pk_eq sk_eq.
have sample_eq :
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, msg, ctxt) @ &m :
       p (paper_sim_signature haetae_mode pk msg ctxt res)] =
  mu (dexact_hyperball_signing_attempt_state haetae_mode sk msg ctxt)
    (fun st =>
       p (paper_sim_signature haetae_mode pk msg ctxt
            (paper_sim_sample_from_rejection_attempt st))).
+ rewrite
    (concrete_ro_exact_hyperball_sample_with_seed_exact_pr
       seed_coins msg ctxt
       (fun smp =>
          p (paper_sim_signature haetae_mode pk msg ctxt smp)) &m).
  by rewrite sk_eq.
have osign_eq :
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(msg, ctxt) @ &m :
       p res] =
  mu (dexact_hyperball_signing_attempt_state haetae_mode sk msg ctxt)
    (fun st =>
       p (paper_sim_signature haetae_mode pk msg ctxt
            (paper_sim_sample_from_rejection_attempt st))).
+ byphoare
    (concrete_budgeted_ro_exact_hyperball_o_sign_active_signature_exact
       pk sk msg ctxt p) => //.
  by auto => />; smt.
qed.

lemma concrete_budgeted_ro_signing_attempt_o_sign_to_self_logged_sample_active_projection
    seed_coins pk sk msg ctxt (p : signature -> bool) &m :
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} <
    signature_query_budget_count =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m} = pk =>
  ROSigningAttemptPaperSimSampler.sk_current{m} = sk =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(msg, ctxt) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, msg, ctxt) @ &m :
       p (paper_sim_signature haetae_mode pk msg ctxt res) /\
       ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m})].
proof.
move=> covered clean active pk_eq sk_eq.
have osign_le :
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(msg, ctxt) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  mu (dsigning_attempt_state haetae_mode sk msg ctxt)
     (fun st =>
        p (paper_sim_signature haetae_mode pk msg ctxt
             (paper_sim_sample_from_rejection_attempt st))).
+ byphoare
    (concrete_budgeted_ro_signing_attempt_o_sign_active_clean_signature_structural_le
       pk sk msg ctxt p) => //.
  by auto => />; smt.
have sample_eq :
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, msg, ctxt) @ &m :
       p (paper_sim_signature haetae_mode pk msg ctxt res) /\
       ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m})] =
  mu (dsigning_attempt_state haetae_mode sk msg ctxt)
     (fun st =>
        p (paper_sim_signature haetae_mode pk msg ctxt
             (paper_sim_sample_from_rejection_attempt st))).
+ have clean_eq :
    ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
       sampler_expand_query seed_coins \in
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
       sampler_expand_query seed_coins \in
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =
    true by smt.
  rewrite (mu_eq _ _
    (fun st =>
       p (paper_sim_signature haetae_mode pk msg ctxt
            (paper_sim_sample_from_rejection_attempt st)) /\
       ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}))).
  + by move=> st; smt.
  byphoare
    (concrete_ro_signing_attempt_sample_with_seed_fresh_structural_eq
       seed_coins sk msg ctxt
       (fun smp =>
          p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
          ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
             sampler_expand_query seed_coins \in
               ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
             sampler_expand_query seed_coins \in
               ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}))) => //.
  by auto => />; smt(sampler_rom_covered_fresh_after_clean_seed).
by smt().
qed.

lemma concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface
    seed_coins m ctx pk (p : signature -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} <
    signature_query_budget_count =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m} = pk =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res) /\
       ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m})] =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean active pk_eq sk_eq attempt_project.
have surface :=
  concrete_budgeted_self_logged_signature_clean_event_loss_surface
    seed_coins m ctx pk p &m sample_loss covered clean sk_eq.
have exact_project :
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res)] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res].
+ by apply
    (concrete_budgeted_ro_exact_hyperball_sample_with_seed_to_o_sign_active_projection
       seed_coins pk ROExactHyperballPaperSimSampler.sk_current{m}
       m ctx p &m).
by smt().
qed.

lemma concrete_budgeted_o_sign_clean_one_call_restricted_state_loss_from_sampler_framing
    seed_coins m ctx pk
    (R : signature -> glob HAETAE_RO.FRO -> pkey ->
         SIG.query list -> transcript list -> signing_transcript_record list ->
         int -> int -> ro_query list -> ro_query list -> bool -> bool)
    (Q : paper_sim_signature_sample -> glob HAETAE_RO.FRO -> bool)
    (p : paper_sim_signature_sample -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} <
    signature_query_budget_count =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m} = pk =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] =>
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p res] =>
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p res] <=
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] =>
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean active pk_eq sk_eq
        attempt_suffix_frame sample_left_frame sample_right_frame
        exact_suffix_frame.
have sampler_state_loss :=
  concrete_budgeted_o_sign_sample_with_seed_clean_restricted_state_loss_surface
    seed_coins m ctx Q p &m sample_loss covered clean sk_eq
    sample_left_frame sample_right_frame.
by smt().
qed.

lemma concrete_budgeted_o_sign_attempt_signature_suffix_frame
    seed_coins m ctx pk
    (R : signature -> glob HAETAE_RO.FRO -> pkey ->
         SIG.query list -> transcript list -> signing_transcript_record list ->
         int -> int -> ro_query list -> ro_query list -> bool -> bool)
    (p : signature -> bool) &m :
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} <
    signature_query_budget_count =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m} = pk =>
  (forall (sig : signature) (fro : glob HAETAE_RO.FRO) (pk0 : pkey)
          (qs : SIG.query list) (trs : transcript list)
          (recs : signing_transcript_record list) (ahc sc : int)
          (ahqs sqs : ro_query list) (bad : bool),
     R sig fro pk0 qs trs recs ahc sc ahqs sqs bad => p sig) =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res)].
proof.
move=> covered clean active pk_eq frame.
have left_sub :
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery].
+ by smt(mu_sub).
have project :=
  concrete_budgeted_ro_signing_attempt_o_sign_to_self_logged_sample_active_projection
    seed_coins pk ROSigningAttemptPaperSimSampler.sk_current{m}
    m ctx p &m covered clean active pk_eq _.
+ by smt().
have clean_true :
  (fun smp =>
     p (paper_sim_signature haetae_mode pk m ctx smp) /\
     ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
        sampler_expand_query seed_coins \in
          ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
        sampler_expand_query seed_coins \in
          ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}))
  =
  (fun smp =>
     p (paper_sim_signature haetae_mode pk m ctx smp)).
+ by apply fun_ext; move=> smp; smt().
by smt().
qed.

lemma concrete_budgeted_o_sign_exact_signature_suffix_frame
    seed_coins m ctx pk
    (R : signature -> glob HAETAE_RO.FRO -> pkey ->
         SIG.query list -> transcript list -> signing_transcript_record list ->
         int -> int -> ro_query list -> ro_query list -> bool -> bool)
    (p : signature -> bool) &m :
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} <
    signature_query_budget_count =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m} = pk =>
  (forall (sig : signature) (fro : glob HAETAE_RO.FRO) (pk0 : pkey)
          (qs : SIG.query list) (trs : transcript list)
          (recs : signing_transcript_record list) (ahc sc : int)
          (ahqs sqs : ro_query list) (bad : bool),
     p sig => R sig fro pk0 qs trs recs ahc sc ahqs sqs bad) =>
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       p (paper_sim_signature haetae_mode pk m ctx res)] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery].
proof.
move=> active pk_eq frame.
have project :=
  concrete_budgeted_ro_exact_hyperball_sample_with_seed_to_o_sign_active_projection
    seed_coins pk ROExactHyperballPaperSimSampler.sk_current{m}
    m ctx p &m active pk_eq _.
+ by smt().
have right_sub :
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery].
+ by smt(mu_sub).
by smt().
qed.

lemma concrete_budgeted_o_sign_clean_one_call_restricted_state_loss_from_signature_suffix_frames
    seed_coins m ctx pk
    (R : signature -> glob HAETAE_RO.FRO -> pkey ->
         SIG.query list -> transcript list -> signing_transcript_record list ->
         int -> int -> ro_query list -> ro_query list -> bool -> bool)
    (p : signature -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}) =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} <
    signature_query_budget_count =>
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{m} = pk =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  (forall (sig : signature) (fro : glob HAETAE_RO.FRO) (pk0 : pkey)
          (qs : SIG.query list) (trs : transcript list)
          (recs : signing_transcript_record list) (ahc sc : int)
          (ahqs sqs : ro_query list) (bad : bool),
     R sig fro pk0 qs trs recs ahc sc ahqs sqs bad => p sig) =>
  (forall (sig : signature) (fro : glob HAETAE_RO.FRO) (pk0 : pkey)
          (qs : SIG.query list) (trs : transcript list)
          (recs : signing_transcript_record list) (ahc sc : int)
          (ahqs sqs : ro_query list) (bad : bool),
     p sig => R sig fro pk0 qs trs recs ahc sc ahqs sqs bad) =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean active pk_eq sk_eq left_frame right_frame.
have left_sub :
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery].
+ by smt(mu_sub).
have attempt_project :=
  concrete_budgeted_ro_signing_attempt_o_sign_to_self_logged_sample_active_projection
    seed_coins pk ROSigningAttemptPaperSimSampler.sk_current{m}
    m ctx p &m covered clean active pk_eq _.
+ by smt().
have sig_loss :=
  concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface
    seed_coins m ctx pk p &m sample_loss covered clean active pk_eq sk_eq
    attempt_project.
have right_sub :
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)
         ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current
         ROMInternalTranscriptBudgetedPaperSimAsNMA.queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts
         ROMInternalTranscriptBudgetedPaperSimAsNMA.records
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count
         ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery].
+ by smt(mu_sub).
by smt().
qed.

(* Checked O.sign stateful bridge status.
   concrete_budgeted_o_sign_clean_one_call_restricted_state_loss_from_sampler_framing
   is the current non-vacuous O.sign-level consequence of the restricted
   sampler/lazy-ROM lifting lemmas.  It is machine-checked by implication, and
   its four framing premises are the exact remaining proof obligations:
   - attempt O.sign stateful event <= attempt sample_with_seed stateful sample
     event, after exposing the active branch, self-logged seed, sampler log
     update, message-hash get, challenge-hash get, signature construction, and
     transcript/record updates;
   - attempt sample stateful event <= pure returned-sample predicate p;
   - pure returned-sample predicate p <= exact sample stateful event; and
   - exact sample stateful event <= exact O.sign stateful event after the same
     deterministic signing suffix.

   The last two suffix obligations are the hard ones.  They require a ROM-table
   relation for the two post-sample HAETAE_RO.FRO.get calls and a statement
   that the resulting transcript/log state is either determined by the returned
   sample and preserved globals or is intentionally hidden from R.  Without that
   relation, an arbitrary R can distinguish post-call lazy-ROM tables,
   challenge queries, records, sampler_expand_queries, or sampler_bad_prequery
   values that are not encoded by the pure sample predicate p.

   The checked suffix-frame lemmas above prove the only local frame available
   from the current projection facts: if the stateful postcondition R is
   equivalent, for all relevant post-states, to a pure returned-signature
   predicate p, then the signature-only one-call loss yields the restricted
   stateful O.sign theorem
     concrete_budgeted_o_sign_clean_one_call_restricted_state_loss_from_signature_suffix_frames.
   That is useful for state-insensitive continuations, but it still does not
   cover the resumable active-call continuation, whose truth can depend on the
   concrete post-call ROM table, transcript records, sampler log, and future
   oracle behavior.  The more general sampler/lazy-ROM bridge remains the
   conditional interface for future suffix-measurable Q predicates once their
   four framing premises are proved. *)

(* Stateful one-call strengthening spike.
   A direct strengthening of
     concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface
   from p : signature -> bool to an arbitrary post-state predicate is not a
   local generalization of the checked proof above.  The proof above uses the
   marginal sampler obligation

     forall p : paper_sim_signature_sample -> bool,
       mu dsigning_attempt_state p <=
       mu dexact_hyperball_signing_attempt_state p
         + rejection_sampling_loss_term.

   A stateful postcondition over the returned signature, glob HAETAE_RO.FRO,
   transcript/signing logs, sampler_expand_queries, sampler_bad_prequery, and
   signing counters needs a joint sampler/lazy-ROM statement instead.  The
   attempt sampler correlates the returned sample with the sampler-expand ROM
   entry, while the exact-hyperball sampler still performs the ROM get but
   samples the attempt state independently.  An arbitrary post-state predicate
   can observe that joint state through the lazy-ROM table or through later
   adversary calls, so it cannot be encoded by freezing a pure p on the
   returned signature.

   The next non-vacuous theorem needed before the resumable active-call loss
   can be proved is therefore a restricted stateful sampler/lazy-ROM lifting
   lemma, not the vacuous O.sign bound:

     Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
          (seed_coins,m,ctx) :
          Q res (glob HAETAE_RO.FRO)]
     <=
     Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
          (seed_coins,m,ctx) :
          Q res (glob HAETAE_RO.FRO)]
       + rejection_sampling_loss_term

   for the specific suffix-measurable predicates Q generated by the signing
   suffix and resumable resume_after_active continuation, under freshness,
   sampler_rom_covered, matching sampler secrets, and a relation saying that Q
   does not exploit any correlation between the sampler-expand ROM output and
   the exact-side independently sampled state beyond the information present in
   the returned signature.  The checked O.sign bridge above shows how to lift
   such a sampler statement through the deterministic signing suffix once the
   suffix-framing premises are proved.  Without those frames, the theorem is
   still conditional; using mu_bounded plus rejection_sampling_loss_term_ge1
   here would again be a vacuous proof and is intentionally not done. *)

(* Focused proof-obligation note for the budgeted clean-event route.
   The desired non-vacuous proof of
   concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting
   requires an adaptive loss-lifting rule over A.forge.  The checked one-call
   ingredients above are not enough by themselves: they must be applied to the
   continuation success predicate induced by the adversary after each active
   signing-oracle call.

   Exact missing induction principle:
   for every adversary-continuation postcondition C over the final forge result
   and the public final state visible to the later verifier
     C r (glob A) (glob HAETAE_RO.FRO)
       pk_current queries transcripts records
       adversary_hash_count signing_count
       adversary_hash_queries sampler_expand_queries,
   and for related attempt/exact memories satisfying the invariant below with
     k = signature_query_budget_count - signing_count{attempt},
   prove
     Pr[A(AH_attempt,O_attempt).forge(pk) @ attempt :
          C res ... /\ !sampler_bad_prequery]
     <=
     Pr[A(AH_exact,O_exact).forge(pk) @ exact :
          C res ...]
     + (k)%r * rejection_sampling_loss_term.
   The NMA clean-event theorem is the instance where C is the rest of
   UF_NMA.main after A.forge returns, including HAETAE.verify.

   This is not expressible by the current one-call lemma alone.  The current
   lemma quantifies over p : signature -> bool.  The continuation needed here
   is stateful: after O.sign returns, it depends on the adversary private
   state, the lazy-ROM table, the public transcript/signing logs, the query
   counters, and future oracle calls.  A usable active-call premise therefore
   has to be a stateful oracle rule:
     Pr[O_attempt.sign(m,ctx) @ attempt :
          R res post_state_attempt /\ !sampler_bad_prequery]
     <=
     Pr[O_exact.sign(m,ctx) @ exact :
          R res post_state_exact]
     + rejection_sampling_loss_term,
   where R includes the post-call relation required by the recursive
   continuation.  The existing signature-only one-call lemma should be one
   component of that stateful rule, not the induction rule itself.

   Invariant needed before and after every active O.sign in the attempt and
   exact-hyperball games:
   - the two executions expose the same public key, adversary-visible hash
     log, transcript log, signing-record log, adversary hash counter, and
     signing counter;
   - ROSigningAttemptPaperSimSampler.sk_current =
     ROExactHyperballPaperSimSampler.sk_current;
   - sampler_rom_covered HAETAE_RO.FRO.m adversary_hash_queries
     sampler_expand_queries holds on the attempt side;
   - the attempt side is on the clean branch
     !ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery, and
     the seed about to be used is absent from both adversary_hash_queries and
     sampler_expand_queries;
   - signing_count <= signature_query_budget_count, with the per-call loss
     charged only when signing_count < signature_query_budget_count.

   Per-call step that the lifting theorem must invoke:
   concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface, with
   p instantiated to the adversary-continuation success predicate after the
   current O.sign.  Its premises should be discharged by the invariant, the
   fresh self-logged seed condition, and
   concrete_budgeted_ro_signing_attempt_o_sign_to_self_logged_sample_active_projection.
   The exact sampler side is connected by
   concrete_budgeted_ro_exact_hyperball_sample_with_seed_to_o_sign_active_projection.

   Accumulation target:
   the active branch is entered at most signature_query_budget_count times, so a
   custom lossy-oracle/fel rule should sum the constant per-call charge
   rejection_sampling_loss_term to
   rom_signature_query_budget * rejection_sampling_loss_term.

   Why the current EasyCrypt patterns are insufficient:
   existing equiv/byequiv calls can traverse A.forge only when AH.get and
   O.sign satisfy exact relational postconditions; existing fel uses in this
   file bound one bad flag in one execution and have no right-side probability
   term; existing phoare lemmas prove local one-procedure inequalities but do
   not provide an adversary-call rule for one-sided lossy oracles.  Therefore
   none of the current patterns can directly consume the one-call lossy
   comparison and sum the loss through A.forge.

   Focused proof-engineering spike, 2026-05-13:
   EasyCrypt's library Hybrid_restr theorem is the closest reusable shape.  A
   plausible instantiation would package AH.get as the Hybrid Orclb.leaks
   procedure, package attempt/exact O.sign as Orclb.orclL/orclR, and take
   AdvOrclb.main to be A(AH,O).forge with q = signature_query_budget_count.
   That route still leaves the same local one-switch obligation: after the
   hybrid chooses the active signing call, the proof must compare the attempt
   and exact sign oracles under the continuation consisting of the remaining
   adversary execution plus the final UF_NMA verifier.  The available
   concrete_budgeted_o_sign_clean_one_call_loss_from_self_logged_surface cannot
   discharge that obligation because its postcondition is only p res for
   p : signature -> bool.

   SDist.sdist_oracleN is not a replacement: it proves a symmetric statistical
   distance bound for simple sampling oracles from an sdist premise.  The
   present premise is one-sided,
     mu attempt P <= mu exact P + rejection_sampling_loss_term,
   and the oracle state includes the lazy ROM map, transcript/signing logs,
   counters, sampler coverage, and the clean flag.

   Narrow failed direct proof shape:
     byequiv (: ={glob HAETAE_RO.FRO, glob A, arg} /\ Inv ==>
               C res{1} ... /\ !sampler_bad_prequery{1} => C res{2} ...).
     proc; inline ...; call (_: Inv ==> ?).
   The proof stops at the A.forge call because the EasyCrypt call rule at that
   point accepts exact relational oracle specifications or fundamental-lemma
   bad-event specifications, but not an oracle premise of the form
     Pr[O_attempt.sign(m,ctx) @ &1 :
          R res post_state_attempt /\ !sampler_bad_prequery]
     <=
     Pr[O_exact.sign(m,ctx) @ &2 :
          R res post_state_exact]
       + rejection_sampling_loss_term
   together with an instruction to add this charge to the enclosing adversary
   judgement for each active O.sign call.  Thus the missing construct is an
   approximate/lossy call rule, or an explicit hybrid wrapper plus a stateful
   one-switch lemma, whose continuation predicate R ranges over res, glob A,
   glob HAETAE_RO.FRO, pk_current, queries, transcripts, records,
   adversary_hash_count, signing_count, adversary_hash_queries,
   sampler_expand_queries, and sampler_bad_prequery. *)
lemma concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> sample_loss.
have left_le1 :
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <= 1%r
  by smt(mu_bounded).
have right_ge0 :
  0%r <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m : res]
  by smt(mu_bounded).
have budgeted_loss_ge1 :
  1%r <= rom_signature_query_budget * rejection_sampling_loss_term.
+ rewrite /rom_signature_query_budget /signature_query_count
          /signature_query_budget_count.
  smt(rejection_sampling_loss_term_ge1).
by smt().
qed.

lemma concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_clean_lifting &m :
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m :
       res /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term +
    rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound).
proof.
move=> clean_lifting.
apply
  (rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_clean_lifting
     HAETAE_RO.FRO A &m).
by apply clean_lifting.
qed.

lemma concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_paper_sample_lifting &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term +
    rom_signature_query_budget *
      ((rom_hash_query_budget + rom_signature_query_budget) /
       challenge_support_cardinality_lower_bound).
proof.
move=> sample_loss.
apply
  (concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_clean_lifting
     &m).
by apply
  (concrete_rom_internal_budgeted_nma_ro_signing_attempt_ro_exact_hyperball_clean_conditioned_lifting
     &m).
qed.

end section ConcreteROMInternalTranscriptROSigningAttemptExactHyperballPaperSimNMA.

section ROMInternalTranscriptHAETAERejectionPaperSimNMA.

declare module H <: SIG.Oracle {-ROMInternalTranscriptPaperSimAsNMA,
                                 -RealSigningPaperSimSampler,
                                -HAETAERejectionPaperSimSampler}.
declare module A <: SIG.Adversary {-H, -ROMInternalTranscriptPaperSimAsNMA,
                                   -RealSigningPaperSimSampler,
                                   -HAETAERejectionPaperSimSampler}.

equiv real_signing_rejection_paper_sim_nma_oracle :
  ROMInternalTranscriptPaperSimAsNMA
    (A, RealSigningPaperSimSampler(H), H).O.sign ~
  ROMInternalTranscriptPaperSimAsNMA
    (A, HAETAERejectionPaperSimSampler(H), H).O.sign :
    ={glob H, arg} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      HAETAERejectionPaperSimSampler.pk_current{2} /\
    RealSigningPaperSimSampler.sk_current{1} =
      HAETAERejectionPaperSimSampler.sk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        RealSigningPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      HAETAERejectionPaperSimSampler.pk_current{2} /\
    RealSigningPaperSimSampler.sk_current{1} =
      HAETAERejectionPaperSimSampler.sk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        RealSigningPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc.
inline RealSigningPaperSimSampler(H).sample
       HAETAERejectionPaperSimSampler(H).sample.
inline RealSigningPaperSimSampler(H).sample_with_seed
       HAETAERejectionPaperSimSampler(H).sample_with_seed.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
by auto => />; smt(haetae_rejection_sample_from_attempt_of_coinsE).
qed.

equiv adversary_real_signing_rejection_paper_sim_nma :
  A(H, ROMInternalTranscriptPaperSimAsNMA
      (A, RealSigningPaperSimSampler(H), H).O).forge ~
  A(H, ROMInternalTranscriptPaperSimAsNMA
      (A, HAETAERejectionPaperSimSampler(H), H).O).forge :
    ={glob H, glob A, arg} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      HAETAERejectionPaperSimSampler.pk_current{2} /\
    RealSigningPaperSimSampler.sk_current{1} =
      HAETAERejectionPaperSimSampler.sk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        RealSigningPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      HAETAERejectionPaperSimSampler.pk_current{2} /\
    RealSigningPaperSimSampler.sk_current{1} =
      HAETAERejectionPaperSimSampler.sk_current{2} /\
    RealSigningPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        RealSigningPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc
  (={glob H} /\
   ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
     ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
   RealSigningPaperSimSampler.pk_current{1} =
     HAETAERejectionPaperSimSampler.pk_current{2} /\
   RealSigningPaperSimSampler.sk_current{1} =
     HAETAERejectionPaperSimSampler.sk_current{2} /\
   RealSigningPaperSimSampler.pk_current{1} =
     public_key_of_secret haetae_mode
       RealSigningPaperSimSampler.sk_current{1} /\
   ROMInternalTranscriptPaperSimAsNMA.queries{1} =
     ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
   ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
     ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
   ROMInternalTranscriptPaperSimAsNMA.records{1} =
     ROMInternalTranscriptPaperSimAsNMA.records{2}) => //.
+ move=> />.
+ by sim.
+ proc.
  inline RealSigningPaperSimSampler(H).sample
         HAETAERejectionPaperSimSampler(H).sample.
  inline RealSigningPaperSimSampler(H).sample_with_seed
         HAETAERejectionPaperSimSampler(H).sample_with_seed.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  call (: ={glob H, arg} ==> ={glob H, res}).
  + by sim.
  wp.
  rnd.
  by auto => />; smt(haetae_rejection_sample_from_attempt_of_coinsE).
qed.

lemma rom_internal_nma_real_signing_haetae_rejection_paper_sim_exact &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] =
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res].
proof.
byequiv (: ={glob H, glob A} ==> ={res}) => //.
proc.
inline HAETAE(H).verify
       HAETAE(H).kg
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H), H).forge
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H), H).forge
       RealSigningPaperSimSampler(H).init
       HAETAERejectionPaperSimSampler(H).init.
wp.
call (_: ={glob H, glob A, arg} /\
        ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        RealSigningPaperSimSampler.pk_current{1} =
          HAETAERejectionPaperSimSampler.pk_current{2} /\
        RealSigningPaperSimSampler.sk_current{1} =
          HAETAERejectionPaperSimSampler.sk_current{2} /\
        RealSigningPaperSimSampler.pk_current{1} =
          public_key_of_secret haetae_mode
            RealSigningPaperSimSampler.sk_current{1} /\
        ROMInternalTranscriptPaperSimAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptPaperSimAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}
        ==>
        ={glob H, res} /\
        ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        RealSigningPaperSimSampler.pk_current{1} =
          HAETAERejectionPaperSimSampler.pk_current{2} /\
        RealSigningPaperSimSampler.sk_current{1} =
          HAETAERejectionPaperSimSampler.sk_current{2} /\
        RealSigningPaperSimSampler.pk_current{1} =
          public_key_of_secret haetae_mode
            RealSigningPaperSimSampler.sk_current{1} /\
        ROMInternalTranscriptPaperSimAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptPaperSimAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}).
+ by apply adversary_real_signing_rejection_paper_sim_nma.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />; rewrite /keygen_internal /secret_key_of_seed
                    /public_key_of_secret.
qed.

end section ROMInternalTranscriptHAETAERejectionPaperSimNMA.

section ROMInternalTranscriptExactHyperballPaperSimNMA.

declare module H <: SIG.Oracle {-ROMInternalTranscriptPaperSimAsNMA,
                                 -ExactHyperballHAETAERejectionPaperSimSampler,
                                 -ExactHyperballPaperSimSampler}.
declare module A <: SIG.Adversary {-H, -ROMInternalTranscriptPaperSimAsNMA,
                                   -ExactHyperballHAETAERejectionPaperSimSampler,
                                   -ExactHyperballPaperSimSampler}.

equiv exact_hyperball_haetae_rejection_paper_sim_nma_oracle :
  ROMInternalTranscriptPaperSimAsNMA
    (A, ExactHyperballHAETAERejectionPaperSimSampler(H), H).O.sign ~
  ROMInternalTranscriptPaperSimAsNMA
    (A, ExactHyperballPaperSimSampler(H), H).O.sign :
    ={glob H, arg} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
      ExactHyperballPaperSimSampler.pk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
      ExactHyperballPaperSimSampler.sk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
      ExactHyperballPaperSimSampler.pk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
      ExactHyperballPaperSimSampler.sk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
call (: ={glob H, arg} /\
        ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
          ExactHyperballPaperSimSampler.pk_current{2} /\
        ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
          ExactHyperballPaperSimSampler.sk_current{2}
        ==>
        ={glob H, res} /\
        ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
          ExactHyperballPaperSimSampler.pk_current{2} /\
        ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
          ExactHyperballPaperSimSampler.sk_current{2}).
+ by proc; sim.
by auto => />.
qed.

equiv adversary_exact_hyperball_haetae_rejection_paper_sim_nma :
  A(H, ROMInternalTranscriptPaperSimAsNMA
      (A, ExactHyperballHAETAERejectionPaperSimSampler(H), H).O).forge ~
  A(H, ROMInternalTranscriptPaperSimAsNMA
      (A, ExactHyperballPaperSimSampler(H), H).O).forge :
    ={glob H, glob A, arg} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
      ExactHyperballPaperSimSampler.pk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
      ExactHyperballPaperSimSampler.sk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}
    ==>
    ={glob H, res} /\
    ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
      ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
      ExactHyperballPaperSimSampler.pk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
      ExactHyperballPaperSimSampler.sk_current{2} /\
    ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
      public_key_of_secret haetae_mode
        ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} /\
    ROMInternalTranscriptPaperSimAsNMA.queries{1} =
      ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
    ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
      ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
    ROMInternalTranscriptPaperSimAsNMA.records{1} =
      ROMInternalTranscriptPaperSimAsNMA.records{2}.
proof.
proc
  (={glob H} /\
   ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
     ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
   ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
     ExactHyperballPaperSimSampler.pk_current{2} /\
   ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
     ExactHyperballPaperSimSampler.sk_current{2} /\
   ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
     public_key_of_secret haetae_mode
       ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} /\
   ROMInternalTranscriptPaperSimAsNMA.queries{1} =
     ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
   ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
     ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
   ROMInternalTranscriptPaperSimAsNMA.records{1} =
     ROMInternalTranscriptPaperSimAsNMA.records{2}) => //.
+ move=> />.
+ by sim.
+ proc*.
  call exact_hyperball_haetae_rejection_paper_sim_nma_oracle.
  by auto => />.
qed.

lemma rom_internal_nma_exact_hyperball_rejection_paper_sim_no_fallback_exact &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H))).main()
       @ &m : res] =
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H))).main() @ &m : res].
proof.
byequiv (: ={glob H, glob A} ==> ={res}) => //.
proc.
inline HAETAE(H).verify
       HAETAE(H).kg
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H), H).forge
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H), H).forge
       ExactHyperballHAETAERejectionPaperSimSampler(H).init
       ExactHyperballPaperSimSampler(H).init.
wp.
call (_: ={glob H, glob A, arg} /\
        ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
          ExactHyperballPaperSimSampler.pk_current{2} /\
        ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
          ExactHyperballPaperSimSampler.sk_current{2} /\
        ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
          public_key_of_secret haetae_mode
            ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} /\
        ROMInternalTranscriptPaperSimAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptPaperSimAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}
        ==>
        ={glob H, res} /\
        ROMInternalTranscriptPaperSimAsNMA.pk_current{1} =
          ROMInternalTranscriptPaperSimAsNMA.pk_current{2} /\
        ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
          ExactHyperballPaperSimSampler.pk_current{2} /\
        ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} =
          ExactHyperballPaperSimSampler.sk_current{2} /\
        ExactHyperballHAETAERejectionPaperSimSampler.pk_current{1} =
          public_key_of_secret haetae_mode
            ExactHyperballHAETAERejectionPaperSimSampler.sk_current{1} /\
        ROMInternalTranscriptPaperSimAsNMA.queries{1} =
          ROMInternalTranscriptPaperSimAsNMA.queries{2} /\
        ROMInternalTranscriptPaperSimAsNMA.transcripts{1} =
          ROMInternalTranscriptPaperSimAsNMA.transcripts{2} /\
        ROMInternalTranscriptPaperSimAsNMA.records{1} =
          ROMInternalTranscriptPaperSimAsNMA.records{2}).
+ by apply adversary_exact_hyperball_haetae_rejection_paper_sim_nma.
wp.
call (: ={glob H, arg} ==> ={glob H, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />; rewrite /keygen_internal /secret_key_of_seed
                    /public_key_of_secret.
qed.

end section ROMInternalTranscriptExactHyperballPaperSimNMA.

section ROMInternalTranscriptPaperSimHop.

declare module H <: SIG.Oracle {-ROMInternalTranscriptPublicSimAsNMA,
                                -ROMInternalTranscriptPaperSimAsNMA}.
declare module A <: SIG.Adversary {-H, -ROMInternalTranscriptPublicSimAsNMA,
                                   -ROMInternalTranscriptPaperSimAsNMA}.
declare module Samp <: PaperSimSigningSampler {-H, -A,
                                               -ROMInternalTranscriptPaperSimAsNMA}.

lemma public_sim_to_paper_sim_nma_hop_from_sampling_hop &m :
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptPublicSimAsNMA(A)).main()
       @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA(A, Samp)).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptPublicSimAsNMA(A)).main()
       @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA(A, Samp)).main() @ &m : res] +
    rejection_sampling_loss_term.
proof. by move=> h. qed.

end section ROMInternalTranscriptPaperSimHop.

section TranscriptLoggingErasure.

declare module H <: SIG.Oracle {-EUF_CMA_SimulatedSign,
                                 -EUF_CMA_TranscriptSimulatedSign}.
declare module S <: SIG.Scheme {-H, -EUF_CMA_SimulatedSign,
                                 -EUF_CMA_TranscriptSimulatedSign}.
declare module A <: SIG.Adversary {-H, -S, -EUF_CMA_SimulatedSign,
                                    -EUF_CMA_TranscriptSimulatedSign}.
declare module Sim <: SigningSimulator {-H, -S, -A,
                                         -EUF_CMA_SimulatedSign,
                                         -EUF_CMA_TranscriptSimulatedSign}.

equiv transcript_logging_oracle_erasure :
  EUF_CMA_SimulatedSign(H, S, A, Sim).O.sign ~
  EUF_CMA_TranscriptSimulatedSign(H, S, A, Sim).O.sign :
    ={glob H, glob S, glob Sim, arg} /\
    EUF_CMA_SimulatedSign.queries{1} =
      EUF_CMA_TranscriptSimulatedSign.queries{2}
    ==>
    ={glob H, glob S, glob Sim, res} /\
    EUF_CMA_SimulatedSign.queries{1} =
      EUF_CMA_TranscriptSimulatedSign.queries{2}.
proof.
proc.
wp.
call (: ={glob H, glob Sim, arg} ==> ={glob H, glob Sim, res}).
+ by sim.
by auto.
qed.

equiv adversary_transcript_logging_erasure :
  A(H, EUF_CMA_SimulatedSign(H, S, A, Sim).O).forge ~
  A(H, EUF_CMA_TranscriptSimulatedSign(H, S, A, Sim).O).forge :
    ={glob H, glob S, glob A, glob Sim, arg} /\
    EUF_CMA_SimulatedSign.queries{1} =
      EUF_CMA_TranscriptSimulatedSign.queries{2}
    ==>
    ={glob H, glob S, glob Sim, res} /\
    EUF_CMA_SimulatedSign.queries{1} =
      EUF_CMA_TranscriptSimulatedSign.queries{2}.
proof.
proc (={glob H, glob S, glob Sim} /\
      EUF_CMA_SimulatedSign.queries{1} =
        EUF_CMA_TranscriptSimulatedSign.queries{2}) => //.
+ move=> />.
+ by sim.
+ proc.
  wp.
  call (: ={glob H, glob Sim, arg} ==> ={glob H, glob Sim, res}).
  + by sim.
  by auto.
qed.

lemma transcript_logging_erasure_exact &m :
  Pr[EUF_CMA_SimulatedSign(H, S, A, Sim).main() @ &m : res] =
  Pr[EUF_CMA_TranscriptSimulatedSign(H, S, A, Sim).main() @ &m : res].
proof.
byequiv (: ={glob H, glob S, glob A, glob Sim} ==> ={res}) => //.
proc.
wp.
call (: ={glob H, glob S, arg} ==> ={glob H, glob S, res}).
+ by sim.
wp.
call (_: ={glob H, glob S, glob A, glob Sim, arg} /\
        EUF_CMA_SimulatedSign.queries{1} =
        EUF_CMA_TranscriptSimulatedSign.queries{2} ==>
        ={glob H, glob S, glob Sim, res} /\
        EUF_CMA_SimulatedSign.queries{1} =
        EUF_CMA_TranscriptSimulatedSign.queries{2}).
+ by apply adversary_transcript_logging_erasure.
wp.
call (: ={glob H, glob Sim, arg} ==> ={glob H, glob Sim}).
+ by sim.
wp.
call (: ={glob H, glob S} ==> ={glob H, glob S, res}).
+ by sim.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />.
qed.

end section TranscriptLoggingErasure.

section RealSigningSimulatorExact.

declare module H <: SIG.Oracle {-SIG.EUF_CMA, -EUF_CMA_SimulatedSign,
                                 -RealSigningSimulator}.
declare module S <: SIG.Scheme {-H, -SIG.EUF_CMA, -EUF_CMA_SimulatedSign,
                                 -RealSigningSimulator}.
declare module A <: SIG.Adversary {-H, -S, -SIG.EUF_CMA,
                                    -EUF_CMA_SimulatedSign,
                                    -RealSigningSimulator}.

equiv real_signing_oracle_equiv :
  SIG.EUF_CMA(H, S, A).O.sign ~
  EUF_CMA_SimulatedSign(H, S, A, RealSigningSimulator(S)).O.sign :
    ={glob H, glob S, arg} /\
    SIG.EUF_CMA.sk{1} = RealSigningSimulator.sk{2} /\
    SIG.EUF_CMA.queries{1} = EUF_CMA_SimulatedSign.queries{2}
    ==>
    ={glob H, glob S, res} /\
    SIG.EUF_CMA.sk{1} = RealSigningSimulator.sk{2} /\
    SIG.EUF_CMA.queries{1} = EUF_CMA_SimulatedSign.queries{2}.
proof.
proc.
inline RealSigningSimulator(S, H).sign.
wp.
call (: ={glob H, glob S, arg} ==> ={glob H, glob S, res}).
+ by sim.
by auto.
qed.

equiv adversary_real_signing_equiv :
  A(H, SIG.EUF_CMA(H, S, A).O).forge ~
  A(H, EUF_CMA_SimulatedSign(H, S, A, RealSigningSimulator(S)).O).forge :
    ={glob H, glob S, glob A, arg} /\
    SIG.EUF_CMA.sk{1} = RealSigningSimulator.sk{2} /\
    SIG.EUF_CMA.queries{1} = EUF_CMA_SimulatedSign.queries{2}
    ==>
    ={glob H, glob S, res} /\
    SIG.EUF_CMA.sk{1} = RealSigningSimulator.sk{2} /\
    SIG.EUF_CMA.queries{1} = EUF_CMA_SimulatedSign.queries{2}.
proof.
proc (={glob H, glob S} /\
      SIG.EUF_CMA.sk{1} = RealSigningSimulator.sk{2} /\
      SIG.EUF_CMA.queries{1} = EUF_CMA_SimulatedSign.queries{2}) => //.
+ move=> />.
+ by sim.
+ proc.
  inline RealSigningSimulator(S, H).sign.
  wp.
  call (: ={glob H, glob S, arg} ==> ={glob H, glob S, res}).
  + by sim.
  by auto.
qed.

lemma real_signing_simulator_exact &m :
  Pr[SIG.EUF_CMA(H, S, A).main() @ &m : res] =
  Pr[EUF_CMA_SimulatedSign(H, S, A, RealSigningSimulator(S)).main() @ &m : res].
proof.
byequiv (: ={glob H, glob S, glob A} ==> ={res}) => //.
proc.
inline RealSigningSimulator(S, H).init.
wp.
call (: ={glob H, glob S, arg} ==> ={glob H, glob S, res}).
+ by sim.
wp.
call (_: ={glob H, glob S, glob A, arg} /\
        SIG.EUF_CMA.sk{1} = RealSigningSimulator.sk{2} /\
        SIG.EUF_CMA.queries{1} =
        EUF_CMA_SimulatedSign.queries{2} ==>
        ={glob H, glob S, res} /\
        SIG.EUF_CMA.sk{1} = RealSigningSimulator.sk{2} /\
        SIG.EUF_CMA.queries{1} =
        EUF_CMA_SimulatedSign.queries{2}).
+ by apply adversary_real_signing_equiv.
wp.
call (: ={glob H, glob S} ==> ={glob H, glob S, res}).
+ by sim.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />.
qed.

end section RealSigningSimulatorExact.

module type ForkingAdversary(H : SIG.POracle) = {
  proc fork(pk : pkey) : transcript * transcript
}.

module type TranscriptExtractor = {
  proc extract(tr1 : transcript, tr2 : transcript) :
    module_sis_solution option
}.

module type BimodalTranscriptExtractor = {
  proc extract(tr1 : transcript, tr2 : transcript) :
    bimodal_selftarget_msis_solution option
}.

module BimodalSpecialSoundness_Game(
  H : SIG.Oracle,
  S : SIG.Scheme,
  F : ForkingAdversary,
  X : BimodalTranscriptExtractor
) = {
  proc main(md : mode) : bool = {
    var pk : pkey;
    var sk : skey;
    var tr1 : transcript;
    var tr2 : transcript;
    var sol : bimodal_selftarget_msis_solution option;

    H.init();
    (pk, sk) <@ S(H).kg();
    (tr1, tr2) <@ F(H).fork(pk);
    sol <@ X.extract(tr1, tr2);
    return valid_forking_pair md tr1 tr2 /\
      sol <> None /\
      bimodal_selftarget_msis_valid md
        (bimodal_selftarget_msis_instance_of_fork md tr1 tr2)
        (oget sol);
  }
}.

module SpecialSoundness_Game(
  H : SIG.Oracle,
  S : SIG.Scheme,
  F : ForkingAdversary,
  X : TranscriptExtractor
) = {
  proc main(md : mode) : bool = {
    var pk : pkey;
    var sk : skey;
    var tr1 : transcript;
    var tr2 : transcript;
    var sol : module_sis_solution option;

    H.init();
    (pk, sk) <@ S(H).kg();
    (tr1, tr2) <@ F(H).fork(pk);
    sol <@ X.extract(tr1, tr2);
    return valid_forking_pair md tr1 tr2 /\
      sol <> None /\
      module_sis_valid md
        (module_sis_instance_of_fork md tr1 tr2)
        (oget sol);
  }
}.

module BimodalTranscriptExtractor_As_ModuleSIS(
  X : BimodalTranscriptExtractor
) = {
  proc extract(tr1 : transcript, tr2 : transcript) :
    module_sis_solution option = {
    var sol : bimodal_selftarget_msis_solution option;

    sol <@ X.extract(tr1, tr2);
    return sol;
  }
}.

section BimodalSpecialSoundnessLift.

declare module H <: SIG.Oracle.
declare module S <: SIG.Scheme {-H}.
declare module F <: ForkingAdversary {-H, -S}.
declare module X <: BimodalTranscriptExtractor {-H, -S, -F}.

lemma bimodal_special_soundness_lift_exact &m md :
  Pr[BimodalSpecialSoundness_Game(H, S, F, X).main(md) @ &m : res] =
  Pr[SpecialSoundness_Game(
       H, S, F, BimodalTranscriptExtractor_As_ModuleSIS(X)).main(md)
       @ &m : res].
proof.
byequiv (: ={glob H, glob S, glob F, glob X} ==> ={res}) => //.
proc.
inline BimodalTranscriptExtractor_As_ModuleSIS(X).extract.
wp.
call (: ={glob X, arg} ==> ={glob X, res}).
+ by sim.
wp.
call (: ={glob H, glob F, arg} ==> ={glob H, glob F, res}).
+ by sim.
wp.
call (: ={glob H, glob S} ==> ={glob H, glob S, res}).
+ by sim.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />; rewrite /module_sis_instance_of_fork
                  /bimodal_to_module_sis_instance
                  /bimodal_selftarget_msis_valid; smt.
qed.

end section BimodalSpecialSoundnessLift.

module type BimodalToModuleSIS = {
  proc lift(x : bimodal_selftarget_msis_instance,
            sol : bimodal_selftarget_msis_solution) :
    module_sis_solution
}.

op special_soundness_interfaces_ready (md : mode) : bool =
  fork_public_reconstruction_obligation md /\
  forking_extraction_obligation md /\
  bimodal_to_module_sis_lift_obligation md.

lemma special_soundness_interfaces_ready_from_forking md :
  forking_extraction_obligation md =>
  special_soundness_interfaces_ready md.
proof.
move=> hfork.
rewrite /special_soundness_interfaces_ready.
split.
 + exact (fork_public_reconstruction_obligation_holds md).
split.
 + exact hfork.
 + exact (bimodal_to_module_sis_lift_obligation_holds md).
qed.

lemma special_soundness_interfaces_public_reconstruction md :
  special_soundness_interfaces_ready md =>
  fork_public_reconstruction_obligation md.
proof.
rewrite /special_soundness_interfaces_ready.
move=> [hpublic _].
exact hpublic.
qed.

lemma special_soundness_interfaces_ready_sound md :
  special_soundness_interfaces_ready md =>
  special_soundness_obligation md.
proof.
rewrite /special_soundness_interfaces_ready.
move=> [_ [hfork hlift]].
exact (special_soundness_from_bimodal_lift md hfork hlift).
qed.

lemma special_soundness_interfaces_ready_sound_with_public_reconstruction md :
  special_soundness_interfaces_ready md =>
  special_soundness_with_public_reconstruction_obligation md.
proof.
rewrite /special_soundness_interfaces_ready.
move=> [hpublic [hfork hlift]].
exact (special_soundness_with_public_reconstruction_from_bimodal_lift
          md hpublic hfork hlift).
qed.

op signing_simulator_sound (md : mode) : bool =
  forall (pk : pkey) (m : message) (ctx : context) (sig : signature),
    signing_simulation_relation md pk m ctx sig =>
    verify_internal md pk m ctx sig.

lemma signing_simulator_sound_current md :
  signing_simulator_sound md.
proof.
rewrite /signing_simulator_sound.
move=> pk m ctx sig h.
exact (signing_simulation_verifies md pk m ctx sig h).
qed.

lemma rejection_sampling_bound_from_fs_bound :
  fs_with_aborts_bound_obligation =>
  rejection_sampling_bound_obligation.
proof.
rewrite /fs_with_aborts_bound_obligation
        /rejection_sampling_bound_obligation
        /rejection_sampling_loss_term.
move=> [ge_reprogram ge_entropy].
split.
+ by apply addr_ge0.
split.
 + exact ge_reprogram.
 + exact ge_entropy.
qed.

op fs_with_aborts_interfaces_ready (md : mode) : bool =
  signing_simulator_sound md /\
  special_soundness_interfaces_ready md /\
  fs_with_aborts_bound_obligation.

lemma fs_with_aborts_interfaces_ready_from_parts md :
  special_soundness_interfaces_ready md =>
  fs_with_aborts_bound_obligation =>
  fs_with_aborts_interfaces_ready md.
proof.
move=> hspecial hfs_bound.
rewrite /fs_with_aborts_interfaces_ready.
split.
 + exact (signing_simulator_sound_current md).
split.
 + exact hspecial.
 + exact hfs_bound.
qed.

lemma fs_with_aborts_interfaces_ready_from_forking md :
  forking_extraction_obligation md =>
  fs_with_aborts_interfaces_ready md.
proof.
move=> fork.
exact (fs_with_aborts_interfaces_ready_from_parts md
         (special_soundness_interfaces_ready_from_forking md fork)
         fs_with_aborts_bound_obligation_holds).
qed.

lemma fs_with_aborts_interfaces_ready_holds md :
  fs_with_aborts_interfaces_ready md.
proof.
exact (fs_with_aborts_interfaces_ready_from_forking md
       (forking_extraction_obligation_holds md)).
qed.

lemma structural_to_exact_hyperball_paper_sample_loss_from_obligation
   (md : mode) :
  structural_to_exact_hyperball_paper_sample_loss_obligation md =>
  forall (sk : skey) (m : message) (ctx : context)
         (p : paper_sim_signature_sample -> bool),
    mu (dsigning_attempt_state md sk m ctx)
      (fun st => p (paper_sim_sample_from_rejection_attempt st)) <=
    mu (dexact_hyperball_signing_attempt_state md sk m ctx)
      (fun st => p (paper_sim_sample_from_rejection_attempt st)) +
      rejection_sampling_loss_term.
proof.
rewrite /structural_to_exact_hyperball_paper_sample_loss_obligation.
move=> hop sk m ctx p.
exact (hop sk m ctx p).
qed.

lemma structural_to_exact_hyperball_paper_sample_loss_from_attempt_loss
   (md : mode) :
  structural_to_exact_hyperball_attempt_loss_obligation =>
  forall (sk : skey) (m : message) (ctx : context)
         (p : paper_sim_signature_sample -> bool),
    mu (dsigning_attempt_state md sk m ctx)
      (fun st => p (paper_sim_sample_from_rejection_attempt st)) <=
    mu (dexact_hyperball_signing_attempt_state md sk m ctx)
      (fun st => p (paper_sim_sample_from_rejection_attempt st)) +
      rejection_sampling_loss_term.
proof.
rewrite /structural_to_exact_hyperball_attempt_loss_obligation.
move=> hop sk m ctx p.
exact (hop md sk m ctx
  (fun st => p (paper_sim_sample_from_rejection_attempt st))).
qed.

lemma structural_to_exact_hyperball_paper_sample_loss_obligation_from_attempt_loss
   (md : mode) :
  structural_to_exact_hyperball_attempt_loss_obligation =>
  structural_to_exact_hyperball_paper_sample_loss_obligation md.
proof.
rewrite /structural_to_exact_hyperball_paper_sample_loss_obligation.
move=> hop sk m ctx p.
exact
  (structural_to_exact_hyperball_paper_sample_loss_from_attempt_loss
     md hop sk m ctx p).
qed.

lemma structural_to_exact_hyperball_paper_sample_loss_from_coin_sample_pair_loss
   (md : mode) :
  structural_to_exact_hyperball_coin_sample_pair_loss_obligation =>
  forall (sk : skey) (m : message) (ctx : context)
         (p : paper_sim_signature_sample -> bool),
    mu (dsigning_attempt_state md sk m ctx)
      (fun st => p (paper_sim_sample_from_rejection_attempt st)) <=
    mu (dexact_hyperball_signing_attempt_state md sk m ctx)
      (fun st => p (paper_sim_sample_from_rejection_attempt st)) +
      rejection_sampling_loss_term.
proof.
move=> hop.
apply structural_to_exact_hyperball_paper_sample_loss_from_attempt_loss.
by apply structural_to_exact_hyperball_attempt_loss_from_coin_sample_pair_loss.
qed.

lemma structural_to_exact_hyperball_paper_sample_loss_obligation_from_coin_sample_pair_loss
   (md : mode) :
  structural_to_exact_hyperball_coin_sample_pair_loss_obligation =>
  structural_to_exact_hyperball_paper_sample_loss_obligation md.
proof.
rewrite /structural_to_exact_hyperball_paper_sample_loss_obligation.
move=> hop sk m ctx p.
exact
  (structural_to_exact_hyperball_paper_sample_loss_from_coin_sample_pair_loss
     md hop sk m ctx p).
qed.

lemma dexact_hyperball_reference_paper_sim_attempt_boundary_ready
   (md : mode) (sk : skey) (m : message) (ctx : context) :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reference_rejection_aborts md) = 0%r.
proof.
by apply dexact_hyperball_signing_attempt_state_reference_rejection_abort_zero.
qed.

lemma dexact_hyperball_full_rejection_paper_sim_attempt_boundary_ready
   (md : mode) (sk : skey) (m : message) (ctx : context) :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_rejection_aborts md
       (public_key_of_secret md sk) m ctx) = 0%r.
proof.
by apply dexact_hyperball_signing_attempt_state_rejection_abort_zero.
qed.

lemma dexact_hyperball_haetae_rejection_sample_no_fallback_mu
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (p : paper_sim_signature_sample -> bool) :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (fun st =>
       p (haetae_rejection_sample_from_attempt md
            (public_key_of_secret md sk) m ctx st)) =
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (fun st => p (paper_sim_sample_from_rejection_attempt st)).
proof.
  apply Distr.mu_eq_support => st st_supp.
  rewrite /= /haetae_rejection_sample_from_attempt.
  rewrite (dexact_hyperball_signing_attempt_state_rejection_accepts
             md sk m ctx st st_supp).
  by [].
qed.

lemma dexact_hyperball_haetae_rejection_sample_signature_no_fallback_mu
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (p : signature -> bool) :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (fun st =>
       p (paper_sim_signature md (public_key_of_secret md sk) m ctx
            (haetae_rejection_sample_from_attempt md
               (public_key_of_secret md sk) m ctx st))) =
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (fun st =>
       p (paper_sim_signature md (public_key_of_secret md sk) m ctx
            (paper_sim_sample_from_rejection_attempt st))).
proof.
exact (dexact_hyperball_haetae_rejection_sample_no_fallback_mu
         md sk m ctx
         (fun s =>
            p (paper_sim_signature md (public_key_of_secret md sk) m ctx s))).
qed.

lemma dexact_hyperball_paper_sim_rejection_attempt_signature_mu
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (p : signature -> bool) :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (fun st =>
       p (paper_sim_signature md (public_key_of_secret md sk) m ctx
            (paper_sim_sample_from_rejection_attempt st))) =
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (fun st => p (signing_attempt_state_signature st)).
proof.
apply Distr.mu_eq_support => st st_supp.
have field_ok :
  signing_attempt_state_field_accepts md
    (public_key_of_secret md sk) m ctx st.
+ move: (dexact_hyperball_signing_attempt_state_rejection_accepts
           md sk m ctx st st_supp).
  rewrite /signing_attempt_state_rejection_accepts
          /signing_attempt_state_verification_accepts.
  by move=> [[field_ok _] _].
by rewrite /= (paper_sim_signature_rejection_attempt_matches_state
                 md (public_key_of_secret md sk) m ctx st field_ok).
qed.

lemma dexact_hyperball_haetae_rejection_sample_signature_mu
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (p : signature -> bool) :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (fun st =>
       p (paper_sim_signature md (public_key_of_secret md sk) m ctx
            (haetae_rejection_sample_from_attempt md
               (public_key_of_secret md sk) m ctx st))) =
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (fun st => p (signing_attempt_state_signature st)).
proof.
rewrite (dexact_hyperball_haetae_rejection_sample_signature_no_fallback_mu
           md sk m ctx p).
exact (dexact_hyperball_paper_sim_rejection_attempt_signature_mu
         md sk m ctx p).
qed.

end HAETAE_HopGames.
