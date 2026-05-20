require import AllCore Distr List Real RealSeries FSet FMap StdOrder FelTactic Mu_mem.
require import Sig_ROM HAETAE_Scheme HAETAE_Params HAETAE_Algebra.
require import HAETAE_Distributions.
require import HAETAE_Assumptions.
require import HAETAE_Transcript.
require import HAETAE_Reductions.
require import HAETAE_Rejection HAETAE_ROM HAETAE_ROM_Programming.

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

module ROMInternalTranscriptBudgetedTwoCallHybridAsNMA(
  A : SIG.Adversary,
  First : PaperSimSigningSampler,
  Second : PaperSimSigningSampler
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
      var old_signing_count : int;
      var old_adversary_hash_queries : ro_query list;
      var old_sampler_expand_queries : ro_query list;
      var old_sampler_bad_prequery : bool;

      if (signing_count < signature_query_budget_count) {
        old_signing_count <- signing_count;
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
        if (old_signing_count = 0) {
          smp <@ First.sample_with_seed(seed_coins, m, ctx);
        } else {
          smp <@ Second.sample_with_seed(seed_coins, m, ctx);
        }
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
    First.init(pk);
    Second.init(pk);
    r <@ A.forge(pk);
    return r;
  }
}.

module ROMInternalTranscriptBudgetedTwoCallG0AsNMA
  (A : SIG.Adversary) (H : SIG.POracle) =
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA
    (A, ROSigningAttemptPaperSimSampler(H),
     ROSigningAttemptPaperSimSampler(H), H).

module ROMInternalTranscriptBudgetedTwoCallG1AsNMA
  (A : SIG.Adversary) (H : SIG.POracle) =
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA
    (A, ROExactHyperballPaperSimSampler(H),
     ROSigningAttemptPaperSimSampler(H), H).

module ROMInternalTranscriptBudgetedTwoCallG2AsNMA
  (A : SIG.Adversary) (H : SIG.POracle) =
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA
    (A, ROExactHyperballPaperSimSampler(H),
     ROExactHyperballPaperSimSampler(H), H).

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

lemma budgeted_paper_sim_sign_oracle_first_active_sets_one :
  hoare[ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).O.sign :
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count = 0 ==>
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count = 1].
proof.
proc.
rcondt 1; first by auto => />; rewrite /signature_query_budget_count.
rcondt 1; first by auto.
wp.
call (_: true).
wp.
call (_: true).
wp.
call (_: true).
by auto.
qed.

lemma budgeted_paper_sim_sign_oracle_second_active_saturates :
  hoare[ROMInternalTranscriptBudgetedPaperSimAsNMA(A, Samp, H).O.sign :
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count = 1 ==>
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count =
      signature_query_budget_count].
proof.
proc.
rcondt 1; first by auto => />; rewrite /signature_query_budget_count.
rcondf 1; first by auto.
wp.
call (_: true).
wp.
call (_: true).
wp.
call (_: true).
by auto => />; rewrite /signature_query_budget_count.
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
by auto => />;
  smt(ge0_mu mu_le_weight is_losslessP signing_attempt_state_distribution_lossless).
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

lemma concrete_ro_exact_hyperball_sample_with_seed_preserves_sk sk :
  hoare[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
    ROExactHyperballPaperSimSampler.sk_current = sk ==>
    ROExactHyperballPaperSimSampler.sk_current = sk].
proof.
proc.
wp.
rnd.
wp.
call (_: ROExactHyperballPaperSimSampler.sk_current = sk).
wp; rnd; auto; smt(ro_output_distribution_lossless).
by auto.
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

lemma concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_state_loss
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

lemma concrete_budgeted_o_sign_sample_with_seed_clean_state_loss_surface
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
by apply
  (concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_state_loss
     seed_coins m ctx Q p
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{m}
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{m}
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{m}
     &m).
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

(* Coarse fallback. The intended non-vacuous replacement is the
   push-forward of structural_to_exact_hyperball_attempt_loss_obligation
   through paper_sim_sample_from_rejection_attempt, lifted across the NMA
   wrapper once the lazy-ROM sampler law is exposed. *)
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
                                   -ROMInternalTranscriptBudgetedTwoCallHybridAsNMA,
                                   -ROSigningAttemptPaperSimSampler,
                                   -ROExactHyperballPaperSimSampler}.

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

lemma concrete_lazy_rom_get_true_le :
  phoare[HAETAE_RO.FRO.get : true ==> true] <= 1%r.
proof.
proc.
wp.
rnd.
by auto => />; smt(ro_output_distribution_lossless).
qed.

lemma concrete_signing_attempt_state_mu_lossless_bound
    md sk m ctx (p : signing_attempt_state -> bool) :
  0%r <= mu (dsigning_attempt_state md sk m ctx) p <= 1%r.
proof.
split.
+ by apply ge0_mu.
have hle := mu_le_weight (dsigning_attempt_state md sk m ctx) p.
have hwt : weight (dsigning_attempt_state md sk m ctx) = 1%r.
+ by apply is_losslessP; apply signing_attempt_state_distribution_lossless.
by smt.
qed.

lemma concrete_exact_hyperball_signing_attempt_state_mu_lossless_bound
    md sk m ctx (p : signing_attempt_state -> bool) :
  0%r <= mu (dexact_hyperball_signing_attempt_state md sk m ctx) p <= 1%r.
proof.
split.
+ by apply ge0_mu.
have hle :=
  mu_le_weight (dexact_hyperball_signing_attempt_state md sk m ctx) p.
have hwt :
  weight (dexact_hyperball_signing_attempt_state md sk m ctx) = 1%r.
+ by apply is_losslessP;
     apply dexact_hyperball_signing_attempt_state_lossless.
by smt.
qed.

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

lemma concrete_budgeted_o_sign_clean_stateful_loss_from_sample_frames
    seed_coins m ctx
    (R : signature -> glob HAETAE_RO.FRO -> bool)
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
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO) /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] =>
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
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)] =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO) /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean sk_eq attempt_frame left_frame
        right_frame exact_frame.
have sample_bridge :=
  concrete_budgeted_o_sign_sample_with_seed_clean_state_loss_surface
    seed_coins m ctx Q p &m
    sample_loss covered clean sk_eq left_frame right_frame.
by smt().
qed.

lemma concrete_lazy_rom_get_preserves_sampler_rom_covered_two_call_logs :
  hoare[HAETAE_RO.FRO.get :
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries /\
    (forall seed_coins,
       arg = sampler_expand_query seed_coins =>
       arg \in
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries \/
       arg \in
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries) ==>
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries].
proof.
proc.
wp.
rnd.
auto => />.
rewrite /sampler_rom_covered.
smt(mem_set).
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_preserves_sampler_rom_covered_two_call_logs :
  hoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries /\
    sampler_expand_query arg.`1 \in
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries ==>
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries].
proof.
proc.
wp.
call concrete_lazy_rom_get_preserves_sampler_rom_covered_two_call_logs.
by auto => />; smt.
qed.

lemma concrete_lazy_rom_sampler_expand_query_fresh_arg_two_call_clean_phoare
    (p : random_coins -> bool) :
  phoare[HAETAE_RO.FRO.get :
      (exists seed_coins,
         arg = sampler_expand_query seed_coins /\
         sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m) /\
      ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery
      ==> p (ro_signing_coins res) /\
          ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery] <=
    (mu drandom_coins p).
proof.
proc.
wp.
rnd.
auto => /> &hr seed_coins arg_eq fresh.
rewrite sampler_expand_query_dro_output_ro_signing_coins.
by rewrite lerr.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_fresh_structural_arg_two_call_clean_le
    sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg.`2 = m /\
      arg.`3 = ctx /\
      ROSigningAttemptPaperSimSampler.sk_current = sk /\
      ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
      sampler_expand_query arg.`1 \notin HAETAE_RO.FRO.m
      ==> p res /\
          ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery] <=
    (mu (dsigning_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
rewrite /dsigning_attempt_state dmapE /=.
proc.
wp.
call (concrete_lazy_rom_sampler_expand_query_fresh_arg_two_call_clean_phoare
  (fun coins =>
     p (paper_sim_sample_from_rejection_attempt
          (signing_attempt_state_of_coins haetae_mode
             sk m ctx coins)))).
by auto => />; smt.
qed.

lemma concrete_lazy_rom_sampler_expand_query_guarded_two_call_clean_phoare
    (p : random_coins -> bool) :
  phoare[HAETAE_RO.FRO.get :
      (! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery =>
       exists seed_coins,
         arg = sampler_expand_query seed_coins /\
         sampler_expand_query seed_coins \notin HAETAE_RO.FRO.m)
      ==> p (ro_signing_coins res) /\
          ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery] <=
    (mu drandom_coins p).
proof.
proc.
wp.
rnd.
auto => /> &hr guarded.
case (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{hr}).
+ move=> bad.
  rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
  + by move=> y; case (x{hr} \in HAETAE_RO.FRO.m{hr}).
  by rewrite mu0; smt.
+ move=> clean.
  elim (guarded clean) => seed_coins [arg_eq fresh].
  rewrite arg_eq fresh /=.
  rewrite sampler_expand_query_dro_output_ro_signing_coins.
  by rewrite lerr.
qed.

lemma concrete_ro_signing_attempt_sample_with_seed_guarded_two_call_clean_structural_arg_le
    sk m ctx (p : paper_sim_signature_sample -> bool) :
  phoare[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed :
      arg.`2 = m /\
      arg.`3 = ctx /\
      ROSigningAttemptPaperSimSampler.sk_current = sk /\
      (! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery =>
       sampler_expand_query arg.`1 \notin HAETAE_RO.FRO.m)
      ==> p res /\
          ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery] <=
    (mu (dsigning_attempt_state haetae_mode
          sk m ctx)
       (fun st => p (paper_sim_sample_from_rejection_attempt st))).
proof.
rewrite /dsigning_attempt_state dmapE /=.
proc.
wp.
call (concrete_lazy_rom_sampler_expand_query_guarded_two_call_clean_phoare
  (fun coins =>
     p (paper_sim_sample_from_rejection_attempt
          (signing_attempt_state_of_coins haetae_mode
             sk m ctx coins)))).
by auto => />; smt.
qed.

lemma concrete_two_call_g0_first_active_o_sign_active_clean_signature_structural_le
    pk sk msg ctxt (p : signature -> bool) :
  phoare[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
          (A, HAETAE_RO.FRO).O.sign :
    arg = (msg, ctxt) /\
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count = 0 /\
	    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current = pk /\
    ROSigningAttemptPaperSimSampler.sk_current = sk /\
    sampler_rom_covered
      HAETAE_RO.FRO.m
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
      ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries /\
    ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery ==>
    p res /\
    ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
    1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  (mu (dsigning_attempt_state haetae_mode sk msg ctxt)
     (fun st =>
        p (paper_sim_signature haetae_mode pk msg ctxt
             (paper_sim_sample_from_rejection_attempt st)))).
proof.
proc.
rcondt 1; first by auto => />; rewrite /signature_query_budget_count.
rcondt 2; first by auto.
rcondt 9; first by auto.
seq 9 :
  (m = msg /\
   ctx = ctxt /\
	   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current = pk /\
   ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
   1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count /\
   p (paper_sim_signature haetae_mode pk msg ctxt smp))
  (mu (dsigning_attempt_state haetae_mode sk msg ctxt)
     (fun st =>
        p (paper_sim_signature haetae_mode pk msg ctxt
             (paper_sim_sample_from_rejection_attempt st))))
  (1%r) _ (0%r)
  (m = msg /\
   ctx = ctxt /\
	   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current = pk /\
   ROSigningAttemptPaperSimSampler.sk_current = sk /\
   sampler_rom_covered
     HAETAE_RO.FRO.m
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries);
  1: (wp;
      call concrete_ro_signing_attempt_sample_with_seed_preserves_sampler_rom_covered_two_call_logs;
      wp; rnd;
      by auto => />; rewrite /signature_query_budget_count;
        smt(signing_coin_distribution_lossless
            sampler_rom_covered_self_log_preserves)).
+ wp.
  call (concrete_ro_signing_attempt_sample_with_seed_guarded_two_call_clean_structural_arg_le
    sk msg ctxt
    (fun smp =>
       p (paper_sim_signature haetae_mode pk msg ctxt smp))).
  wp; rnd.
  by auto => />; rewrite /signature_query_budget_count;
    smt(sampler_rom_covered_fresh_after_clean_seed
        signing_coin_distribution_lossless).
+ inline HAETAE_RO.FRO.get.
  wp.
  rnd.
  wp.
  rnd.
  by auto => />; smt(ro_output_distribution_lossless).
+ hoare.
  inline HAETAE_RO.FRO.get.
  wp.
  rnd.
  wp.
  rnd.
  by auto => />; smt.
+ have hbound :
    0%r <=
    mu (dsigning_attempt_state haetae_mode sk msg ctxt)
       (fun st =>
          p (paper_sim_signature haetae_mode pk msg ctxt
               (paper_sim_sample_from_rejection_attempt st))) <= 1%r.
  + by apply concrete_signing_attempt_state_mu_lossless_bound.
  by smt.
qed.

lemma concrete_two_call_g1_first_active_o_sign_active_signature_exact
    pk sk msg ctxt (p : signature -> bool) :
  phoare[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
          (A, HAETAE_RO.FRO).O.sign :
    arg = (msg, ctxt) /\
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count = 0 /\
	    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current = pk /\
    ROExactHyperballPaperSimSampler.sk_current = sk ==>
    p res /\
    1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] =
  (mu (dexact_hyperball_signing_attempt_state haetae_mode sk msg ctxt)
    (fun st =>
       p (paper_sim_signature haetae_mode pk msg ctxt
            (paper_sim_sample_from_rejection_attempt st)))).
proof.
proc.
rcondt 1; first by auto => />; rewrite /signature_query_budget_count.
rcondt 2; first by auto.
rcondt 9; first by auto.
seq 9 :
  (m = msg /\
   ctx = ctxt /\
	   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current = pk /\
   1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count /\
   p (paper_sim_signature haetae_mode pk msg ctxt smp))
  (mu (dexact_hyperball_signing_attempt_state haetae_mode sk msg ctxt)
     (fun st =>
        p (paper_sim_signature haetae_mode pk msg ctxt
             (paper_sim_sample_from_rejection_attempt st))))
  (1%r) _ (0%r)
  (m = msg /\
   ctx = ctxt /\
	   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current = pk /\
   ROExactHyperballPaperSimSampler.sk_current = sk);
  1: (wp;
      call (concrete_ro_exact_hyperball_sample_with_seed_preserves_sk sk);
      wp; rnd;
      by auto => />; rewrite /signature_query_budget_count;
        smt(signing_coin_distribution_lossless)).
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
+ have hbound :
    0%r <=
    mu (dexact_hyperball_signing_attempt_state haetae_mode sk msg ctxt)
       (fun st =>
          p (paper_sim_signature haetae_mode pk msg ctxt
               (paper_sim_sample_from_rejection_attempt st))) <= 1%r.
  + by apply concrete_exact_hyperball_signing_attempt_state_mu_lossless_bound.
  by smt.
qed.

lemma concrete_two_call_g0_first_active_o_sign_to_self_logged_sample_active_projection
    seed_coins pk sk msg ctxt (p : signature -> bool) &m :
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m}) =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{m} = 0 =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{m} = pk =>
  ROSigningAttemptPaperSimSampler.sk_current{m} = sk =>
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
       (A, HAETAE_RO.FRO).O.sign(msg, ctxt) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, msg, ctxt) @ &m :
       p (paper_sim_signature haetae_mode pk msg ctxt res) /\
       ! (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m})].
proof.
move=> covered clean first_active pk_eq sk_eq.
have osign_le :
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
       (A, HAETAE_RO.FRO).O.sign(msg, ctxt) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  mu (dsigning_attempt_state haetae_mode sk msg ctxt)
     (fun st =>
        p (paper_sim_signature haetae_mode pk msg ctxt
             (paper_sim_sample_from_rejection_attempt st))).
+ byphoare
    (concrete_two_call_g0_first_active_o_sign_active_clean_signature_structural_le
       pk sk msg ctxt p) => //.
  by auto => />; smt.
have sample_eq :
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, msg, ctxt) @ &m :
       p (paper_sim_signature haetae_mode pk msg ctxt res) /\
       ! (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m})] =
  mu (dsigning_attempt_state haetae_mode sk msg ctxt)
     (fun st =>
        p (paper_sim_signature haetae_mode pk msg ctxt
             (paper_sim_sample_from_rejection_attempt st))).
+ rewrite (mu_eq _ _
    (fun st =>
       p (paper_sim_signature haetae_mode pk msg ctxt
            (paper_sim_sample_from_rejection_attempt st)) /\
       ! (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m} \/
          sampler_expand_query seed_coins \in
            ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m}))).
  + by move=> st; smt.
  byphoare
    (concrete_ro_signing_attempt_sample_with_seed_fresh_structural_eq
       seed_coins sk msg ctxt
       (fun smp =>
          p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
          ! (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m} \/
             sampler_expand_query seed_coins \in
               ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m} \/
             sampler_expand_query seed_coins \in
               ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m}))) => //.
  by auto => />; smt(sampler_rom_covered_fresh_after_clean_seed).
by smt().
qed.

lemma concrete_two_call_g1_exact_sample_with_seed_to_first_active_o_sign_projection
    seed_coins pk sk msg ctxt (p : signature -> bool) &m :
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{m} = 0 =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{m} = pk =>
  ROExactHyperballPaperSimSampler.sk_current{m} = sk =>
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, msg, ctxt) @ &m :
       p (paper_sim_signature haetae_mode pk msg ctxt res)] <=
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
       (A, HAETAE_RO.FRO).O.sign(msg, ctxt) @ &m :
       p res /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count].
proof.
move=> first_active pk_eq sk_eq.
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
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
       (A, HAETAE_RO.FRO).O.sign(msg, ctxt) @ &m :
       p res /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] =
  mu (dexact_hyperball_signing_attempt_state haetae_mode sk msg ctxt)
    (fun st =>
       p (paper_sim_signature haetae_mode pk msg ctxt
            (paper_sim_sample_from_rejection_attempt st))).
  + byphoare
    (concrete_two_call_g1_first_active_o_sign_active_signature_exact
       pk sk msg ctxt p) => //.
  by auto => />; smt.
qed.

lemma concrete_two_call_g0_g1_first_active_o_sign_clean_stateful_loss_from_sample_frames
    seed_coins m ctx
    (R :
      signature -> glob HAETAE_RO.FRO -> pkey -> SIG.query list ->
      transcript list -> signing_transcript_record list -> int -> int ->
      ro_query list -> ro_query list -> bool -> bool)
    (Q : paper_sim_signature_sample -> glob HAETAE_RO.FRO -> bool)
    (p : paper_sim_signature_sample -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m}) =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{m} = 0 =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  Pr[ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] =>
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
  Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
       (seed_coins, m, ctx) @ &m :
       Q res (glob HAETAE_RO.FRO)] <=
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] =>
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean _first_active sk_eq attempt_frame
        left_frame right_frame exact_frame.
have sample_bridge :=
  concrete_ro_signing_attempt_to_exact_hyperball_sample_with_seed_clean_state_loss
    seed_coins m ctx Q p
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m}
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m}
    &m sample_loss covered clean sk_eq left_frame right_frame.
by smt().
qed.

lemma concrete_two_call_g0_g1_first_active_o_sign_clean_signature_loss
    seed_coins pk m ctx (p : signature -> bool) &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  sampler_rom_covered
    HAETAE_RO.FRO.m{m}
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m}
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m} =>
  ! (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m} \/
     sampler_expand_query seed_coins \in
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m}) =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{m} = 0 =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{m} = pk =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       p res /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss covered clean first_active pk_eq sk_eq.
apply
  (concrete_two_call_g0_g1_first_active_o_sign_clean_stateful_loss_from_sample_frames
     seed_coins m ctx
     (fun sig _ _ _ _ _ _ _ _ _ _ => p sig)
     (fun smp _ =>
        p (paper_sim_signature haetae_mode pk m ctx smp) /\
        ! (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{m} \/
           sampler_expand_query seed_coins \in
             ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{m} \/
           sampler_expand_query seed_coins \in
             ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{m}))
     (fun smp => p (paper_sim_signature haetae_mode pk m ctx smp))
     &m) => //.
+ by apply
    (concrete_two_call_g0_first_active_o_sign_to_self_logged_sample_active_projection
       seed_coins pk ROSigningAttemptPaperSimSampler.sk_current{m} m ctx p
       &m).
+ by rewrite Pr[mu_sub]; smt.
+ by rewrite Pr[mu_sub]; smt.
+ apply (ler_trans
     (Pr[ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).sample_with_seed
          (seed_coins, m, ctx) @ &m :
          p (paper_sim_signature haetae_mode pk m ctx res)])).
  + by rewrite Pr[mu_sub]; smt.
  by apply
    (concrete_two_call_g1_exact_sample_with_seed_to_first_active_o_sign_projection
       seed_coins pk ROExactHyperballPaperSimSampler.sk_current{m} m ctx p
       &m).
qed.

lemma concrete_mu_dlet_ge_point ['a 'b]
    (d : 'a distr) (K : 'a -> 'b distr) (E : 'b -> bool) x :
  mu1 d x * mu (K x) E <= mu (dlet d K) E.
proof.
rewrite dletE (@sumD1 _ x) /=.
+ apply summable_mu1_wght => y; smt(mu_bounded).
apply ler_addl.
apply ge0_sum => y /=.
by smt(ge0_mu1 ge0_mu).
qed.

lemma structural_to_exact_hyperball_coin_sample_pair_suffix_loss_from_point_loss
    ['a] md sk m ctx
    (K : signing_attempt_coin_sample_pair -> 'a distr) (E : 'a -> bool) :
  structural_to_exact_hyperball_sample_pair_point_loss_obligation =>
  mu (dlet (dstructural_signing_attempt_coin_sample_pair md sk m ctx) K) E <=
  mu (dlet (dexact_hyperball_signing_attempt_coin_sample_pair md sk m ctx) K) E +
    rejection_sampling_loss_term.
proof.
move=> point_loss.
rewrite /dstructural_signing_attempt_coin_sample_pair
        /dexact_hyperball_signing_attempt_coin_sample_pair.
have -> :
  dlet
    (dlet drandom_coins
       (fun coins =>
          dmap (dstructural_signing_sample_pair md sk m ctx coins)
            (fun sample => (coins, sample))))
    K =
  dlet drandom_coins
    (fun coins =>
       dlet
         (dmap (dstructural_signing_sample_pair md sk m ctx coins)
            (fun sample => (coins, sample)))
         K).
+ by rewrite dlet_dlet.
have -> :
  dlet
    (dlet drandom_coins
       (fun coins =>
          dmap (dexact_hyperball_signing_sample_pair md)
            (fun sample => (coins, sample))))
    K =
  dlet drandom_coins
    (fun coins =>
       dlet
         (dmap (dexact_hyperball_signing_sample_pair md)
            (fun sample => (coins, sample)))
         K).
+ by rewrite dlet_dlet.
apply mu_dlet_le_add_all.
+ apply rejection_sampling_loss_term_nonnegative.
move=> coins.
pose s0 := signing_sample_pair_of_coins md sk m ctx coins.
have hpoint := point_loss md sk m ctx coins.
have hge :=
  concrete_mu_dlet_ge_point
    (dexact_hyperball_signing_sample_pair md)
    (fun sample => K (coins, sample)) E s0.
have hstep :
  mu (K (coins, s0)) E <=
  mu1 (dexact_hyperball_signing_sample_pair md) s0 *
    mu (K (coins, s0)) E + rejection_sampling_loss_term.
+ have hb : 0%r <= mu (K (coins, s0)) E <= 1%r by smt(mu_bounded).
  have ha :
    0%r <= mu1 (dexact_hyperball_signing_sample_pair md) s0 <= 1%r
    by smt(mu_bounded).
  by smt.
by smt.
qed.

lemma structural_to_exact_hyperball_seeded_coin_sample_pair_suffix_loss_from_point_loss
    ['a] md sk m ctx
    (K : random_coins -> signing_attempt_coin_sample_pair -> 'a distr)
    (E : 'a -> bool) :
  structural_to_exact_hyperball_sample_pair_point_loss_obligation =>
  mu (dlet drandom_coins
        (fun seed_coins =>
           dlet (dstructural_signing_attempt_coin_sample_pair md sk m ctx)
             (K seed_coins))) E <=
  mu (dlet drandom_coins
        (fun seed_coins =>
           dlet (dexact_hyperball_signing_attempt_coin_sample_pair md sk m ctx)
             (K seed_coins))) E +
    rejection_sampling_loss_term.
proof.
move=> point_loss.
apply mu_dlet_le_add_all.
+ apply rejection_sampling_loss_term_nonnegative.
move=> seed_coins.
by apply
  (structural_to_exact_hyperball_coin_sample_pair_suffix_loss_from_point_loss
     md sk m ctx (K seed_coins) E point_loss).
qed.

op concrete_fro_get_step
   (rom : glob HAETAE_RO.FRO) (q : ro_query) :
   (ro_output * glob HAETAE_RO.FRO) distr =
  if q \in rom then
    let y = (oget rom.[q]).`1 in
    dunit (y, rom.[q <- (y, PROM.Known)])
  else
    dmap (dro_output q)
      (fun y => (y, rom.[q <- (y, PROM.Known)])).

op concrete_two_call_first_active_o_sign_suffix_kernel
   (R :
      signature -> glob HAETAE_RO.FRO -> pkey -> SIG.query list ->
      transcript list -> signing_transcript_record list -> int -> int ->
      ro_query list -> ro_query list -> bool -> bool)
   (rom0 : glob HAETAE_RO.FRO) (pk : pkey)
   (queries : SIG.query list) (transcripts : transcript list)
   (records : signing_transcript_record list)
   (adversary_hash_count signing_count : int)
   (adversary_hash_queries sampler_expand_queries : ro_query list)
   (sampler_bad_prequery : bool)
   (m : message) (ctx : context) (sk : skey)
   (seed_coins : random_coins)
   (cs : signing_attempt_coin_sample_pair) : bool distr =
  let sampler_q = sampler_expand_query seed_coins in
  let sampler_bad =
    sampler_bad_prequery \/
    sampler_q \in adversary_hash_queries \/
    sampler_q \in sampler_expand_queries in
  let sampler_queries' = sampler_q :: sampler_expand_queries in
  let rom_sampler =
    rom0.[sampler_q <- (ro_output_of_random_coins cs.`1, PROM.Known)] in
  let st =
    signing_attempt_state_of_coin_sample_pair haetae_mode sk m ctx cs in
  let smp = paper_sim_sample_from_rejection_attempt st in
  dlet (concrete_fro_get_step rom_sampler (message_hash_query pk ctx m))
    (fun (msg_step : ro_output * glob HAETAE_RO.FRO) =>
       let ro_y = msg_step.`1 in
       let rom_msg = msg_step.`2 in
       let mu = ro_message_hash ro_y in
       let highbits =
         paper_sim_commitment_highbits haetae_mode pk m ctx smp in
       let lowbits = paper_sim_commitment_lowbits haetae_mode smp in
       dmap
         (concrete_fro_get_step rom_msg
            (challenge_hash_query haetae_mode highbits lowbits mu))
         (fun (challenge_step : ro_output * glob HAETAE_RO.FRO) =>
            let rom_challenge = challenge_step.`2 in
            let sig = paper_sim_signature haetae_mode pk m ctx smp in
            let tr = transcript_of_signature haetae_mode pk m ctx sig in
            R sig rom_challenge pk
              ((m, ctx) :: queries)
              (tr :: transcripts)
              ((m, ctx, sig, tr) :: records)
              adversary_hash_count 1
              adversary_hash_queries sampler_queries' sampler_bad /\
            ! sampler_bad)).

lemma concrete_two_call_g0_g1_first_active_o_sign_clean_full_state_loss_from_coin_sample_suffix_frames
    pk m ctx
    (R :
      signature -> glob HAETAE_RO.FRO -> pkey -> SIG.query list ->
      transcript list -> signing_transcript_record list -> int -> int ->
      ro_query list -> ro_query list -> bool -> bool)
    (K : signing_attempt_coin_sample_pair -> signature distr)
    (P : signature -> bool) &m :
  structural_to_exact_hyperball_sample_pair_point_loss_obligation =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{m} = 0 =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{m} = pk =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  mu (dlet
        (dstructural_signing_attempt_coin_sample_pair haetae_mode
           ROSigningAttemptPaperSimSampler.sk_current{m} m ctx)
        K) P =>
  mu (dlet
        (dexact_hyperball_signing_attempt_coin_sample_pair haetae_mode
           ROExactHyperballPaperSimSampler.sk_current{m} m ctx)
        K) P <=
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] =>
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] +
    rejection_sampling_loss_term.
proof.
move=> point_loss _first_active _pk_eq sk_eq left_frame right_frame.
have hsuffix :=
  structural_to_exact_hyperball_coin_sample_pair_suffix_loss_from_point_loss
    haetae_mode ROSigningAttemptPaperSimSampler.sk_current{m} m ctx K P
    point_loss.
by smt.
qed.

lemma concrete_two_call_g0_g1_first_active_o_sign_clean_full_state_loss_from_seeded_coin_sample_suffix_frames
    pk m ctx
    (R :
      signature -> glob HAETAE_RO.FRO -> pkey -> SIG.query list ->
      transcript list -> signing_transcript_record list -> int -> int ->
      ro_query list -> ro_query list -> bool -> bool)
    (K : random_coins -> signing_attempt_coin_sample_pair -> bool distr)
    (P : bool -> bool) &m :
  structural_to_exact_hyperball_sample_pair_point_loss_obligation =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{m} = 0 =>
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{m} = pk =>
  ROSigningAttemptPaperSimSampler.sk_current{m} =
    ROExactHyperballPaperSimSampler.sk_current{m} =>
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  mu (dlet drandom_coins
        (fun seed_coins =>
           dlet
             (dstructural_signing_attempt_coin_sample_pair haetae_mode
                ROSigningAttemptPaperSimSampler.sk_current{m} m ctx)
             (K seed_coins))) P =>
  mu (dlet drandom_coins
        (fun seed_coins =>
           dlet
             (dexact_hyperball_signing_attempt_coin_sample_pair haetae_mode
                ROExactHyperballPaperSimSampler.sk_current{m} m ctx)
             (K seed_coins))) P <=
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] =>
  Pr[ROMInternalTranscriptBudgetedTwoCallG0AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] <=
  Pr[ROMInternalTranscriptBudgetedTwoCallG1AsNMA
	       (A, HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
	       R res (glob HAETAE_RO.FRO)
	         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries
         ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery /\
       1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count] +
    rejection_sampling_loss_term.
proof.
move=> point_loss _first_active _pk_eq sk_eq left_frame right_frame.
have hsuffix :=
  structural_to_exact_hyperball_seeded_coin_sample_pair_suffix_loss_from_point_loss
    haetae_mode ROSigningAttemptPaperSimSampler.sk_current{m} m ctx K P
    point_loss.
by smt.
qed.

lemma mu_ro_output_false_le0 (d : ro_output distr) (P : ro_output -> bool) :
  (forall y, P y = false) =>
  Pervasive.mu d P <= 0%r.
proof.
move=> P_false.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y; rewrite P_false.
by rewrite mu0.
qed.

lemma mu_ro_output_pointwise_not_le0
    (d : ro_output distr) (P : ro_output -> bool) :
  (forall y, ! P y) =>
  Pervasive.mu d P <= 0%r.
proof.
move=> P_false.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma mu_ro_output_pointwise_not_le_nonneg
    (d : ro_output distr) (P : ro_output -> bool) (z : real) :
  (forall y, ! P y) =>
  0%r <= z =>
  Pervasive.mu d P <= z.
proof.
move=> P_false z_ge0.
by smt(mu_ro_output_pointwise_not_le0 ler_trans).
qed.

lemma mu_ro_output_implies_rejected_state_le0
    (d : ro_output distr) (P : ro_output -> bool)
    (b sampler_bad : bool) (signing_count : int) :
  (forall y, P y => b /\ !sampler_bad /\ 1 <= signing_count) =>
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  mu d P <= 0%r.
proof.
move=> P_implies rejected.
apply (mu_ro_output_pointwise_not_le0 d P).
by move=> y; smt.
qed.

lemma mu_ro_output_implies_rejected_state_le_nonneg
    (d : ro_output distr) (P : ro_output -> bool)
    (b sampler_bad : bool) (signing_count : int) (z : real) :
  (forall y, P y => b /\ !sampler_bad /\ 1 <= signing_count) =>
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  0%r <= z =>
  mu d P <= z.
proof.
move=> P_implies rejected z_ge0.
by smt(mu_ro_output_implies_rejected_state_le0 ler_trans).
qed.

lemma mu_ro_output_false_self_support
    (d : ro_output distr) (P : ro_output -> bool) :
  (forall y, ! P y) =>
  (mu d P <= 0%r) &&
  (forall v, v \in d => P v => P v).
proof.
move=> P_false.
by smt(mu_ro_output_pointwise_not_le0).
qed.

lemma mu_ro_output_with_support_le1
    (x : ro_query) (P Q : ro_output -> bool) :
  (forall v, v \in dro_output x => P v => Q v) =>
  (mu (dro_output x) P <= 1%r) &&
  (forall v, v \in dro_output x => P v => Q v).
proof.
move=> HQ.
split.
+ have hle := mu_le_weight (dro_output x) P.
  have hwt : weight (dro_output x) = 1%r.
  + by apply is_losslessP; apply ro_output_distribution_lossless.
  by smt.
by smt.
qed.

lemma mu_ro_output_with_support_notnot_le1
    (x : ro_query) (P Q : ro_output -> bool) :
  (forall v, v \in dro_output x => P v => Q v) =>
  ! (! ((mu (dro_output x) P <= 1%r) &&
        (forall v, v \in dro_output x => P v => Q v))).
proof.
move=> HQ.
have H := mu_ro_output_with_support_le1 x P Q HQ.
by smt.
qed.

lemma mu_ro_output_with_support_neg_false
    (x : ro_query) (P Q : ro_output -> bool) :
  (forall v, v \in dro_output x => P v => Q v) =>
  (! ((mu (dro_output x) P <= 1%r) &&
      (forall v, v \in dro_output x => P v => Q v))) =
  false.
proof.
move=> HQ.
have H := mu_ro_output_with_support_le1 x P Q HQ.
by smt.
qed.

lemma not_bool_and_false (a b : bool) :
  a => b => (! (a && b)) = false.
proof. by smt. qed.

lemma not_prop_and_false (a b : bool) :
  a => b => (! (a /\ b)) = false.
proof. by smt. qed.

lemma if_bool_four_branches_false
    (c1 c2 c3 b1 b2 b3 b4 : bool) :
  !b1 =>
  !b2 =>
  !b3 =>
  !b4 =>
  (if c1 then (if c2 then b1 else b2)
   else (if c3 then b3 else b4)) = false.
proof.
by smt.
qed.

lemma if_bool_two_branches_false
    (c b1 b2 : bool) :
  !b1 =>
  !b2 =>
  (if c then b1 else b2) = false.
proof.
by smt.
qed.

lemma mu_ro_output_with_support_notnot_eq0
    (x : ro_query) (P Q : ro_output -> bool) :
  (forall v, v \in dro_output x => P v => Q v) =>
  mu (dro_output x)
    (fun (_ : ro_output) =>
       ! ((mu (dro_output x) P <= 1%r) &&
          (forall v, v \in dro_output x => P v => Q v))) = 0%r.
proof.
move=> HQ.
have H := mu_ro_output_with_support_le1 x P Q HQ.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma mu_ro_output_self_support_not_not_le1
    (x : ro_query) (P : ro_output -> bool) :
  ! (! ((mu (dro_output x) P <= 1%r) &&
        (forall v, v \in dro_output x => P v => P v))).
proof.
have H := mu_ro_output_with_support_le1 x P P _.
+ by smt.
by smt.
qed.

lemma mu_ro_output_beta_self_support_not_not_le1
    (x : ro_query) (P : ro_output -> bool) :
  ! (! ((mu (dro_output x) P <= 1%r) &&
        (forall v, v \in dro_output x => P v => (fun x2 => P x2) v))).
proof.
have H := mu_ro_output_with_support_le1 x P (fun x2 => P x2) _.
+ by smt.
by smt.
qed.

lemma mu_ro_output_beta_self_support_neg_false
    (x : ro_query) (P : ro_output -> bool) :
  (! ((mu (dro_output x) P <= 1%r) &&
      (forall v, v \in dro_output x => P v => (fun x2 => P x2) v))) =
  false.
proof.
have H := mu_ro_output_beta_self_support_not_not_le1 x P.
by smt.
qed.

lemma bool_and3_rejected_rot_eq_false (a b c : bool) :
  ! (b /\ c /\ a) => (a /\ b /\ c) = false.
proof. by smt. qed.

lemma bool_bool_count_rejected_rot_eq_false (a b : bool) (n : int) :
  ! (b /\ 1 <= n /\ a) => (a /\ b /\ 1 <= n) = false.
proof. by smt. qed.

lemma bool_nested_if_same_false (b1 b2 b3 a : bool) :
  ! a =>
  (if b1 then (if b2 then a else a) else (if b3 then a else a)) = false.
proof. by smt. qed.

lemma bool_nested_if_four_false (b1 b2 b3 a11 a12 a21 a22 : bool) :
  ! a11 =>
  ! a12 =>
  ! a21 =>
  ! a22 =>
  (if b1 then (if b2 then a11 else a12) else (if b3 then a21 else a22)) =
  false.
proof. by smt. qed.

lemma mu_pointwise_not_le0 ['a] (d : 'a distr) (P : 'a -> bool) :
  (forall y, ! P y) =>
  Pervasive.mu d P <= 0%r.
proof.
move=> P_false.
rewrite (mu_eq _ _ (fun (_ : 'a) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma mu_ro_output_const_false_le0 (d : ro_output distr) (b : bool) :
  ! b =>
  mu d (fun (_ : ro_output) => b) <= 0%r.
proof.
move=> b_false.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma mu_ro_output_const_false_and3_le0
    (d : ro_output distr) (b1 b2 b3 : bool) :
  ! (b1 /\ b2 /\ b3) =>
  mu d (fun (_ : ro_output) => b1 /\ b2 /\ b3) <= 0%r.
proof.
move=> b_false.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_const_false_and3_cycled_le0
    (d : ro_output distr) (b1 b2 b3 : bool) :
  ! (b2 /\ b3 /\ b1) =>
  mu d (fun (_ : ro_output) => b1 /\ b2 /\ b3) <= 0%r.
proof.
move=> b_false.
apply (mu_ro_output_const_false_and3_le0 d b1 b2 b3).
by smt(andbA andbC).
qed.

lemma mu_ro_output_paper_sim_signature_clean_rejected_le0
    pk msg ctxt (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  ! (! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output (message_hash_query pk ctxt msg))
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
       ! sampler_bad /\ 1 <= signing_count) <= 0%r.
proof.
move=> rejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_paper_sim_signature_clean_rejected_covered_le0
    (covered : bool) pk msg ctxt (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  covered =>
  ! (! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output (message_hash_query pk ctxt msg))
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
       ! sampler_bad /\ 1 <= signing_count) <= 0%r.
proof.
move=> _ rejected.
by apply (mu_ro_output_paper_sim_signature_clean_rejected_le0
            pk msg ctxt p smp sampler_bad signing_count).
qed.

lemma mu_ro_output_paper_sim_signature_clean_rejected_sampler_rom_covered_le0
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (adversary_hash_queries sampler_expand_queries : ro_query list)
    pk msg ctxt (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  sampler_rom_covered rom adversary_hash_queries sampler_expand_queries =>
  ! (! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output (message_hash_query pk ctxt msg))
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
       ! sampler_bad /\ 1 <= signing_count) <= 0%r.
proof.
move=> _ rejected.
by apply (mu_ro_output_paper_sim_signature_clean_rejected_le0
            pk msg ctxt p smp sampler_bad signing_count).
qed.

lemma mu_ro_output_paper_sim_signature_clean_rejected_equalized_le0
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     ! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output (message_hash_query pk_current ctx m))
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       ! sampler_bad /\ 1 <= signing_count) <= 0%r.
proof.
move=> -> -> -> rejected.
by apply (mu_ro_output_paper_sim_signature_clean_rejected_le0
            pk msg ctxt p smp sampler_bad signing_count); smt().
qed.

lemma mu_ro_output_paper_sim_signature_clean_rejected_any_equalized_le0
    (d : ro_output distr)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     ! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu d
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       ! sampler_bad /\ 1 <= signing_count) <= 0%r.
proof.
move=> -> -> -> rejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma paper_sim_signature_clean_count_rejected_rot_eq_false
    pk msg ctxt (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  ! (! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
   ! sampler_bad /\ 1 <= signing_count) = false.
proof. by smt(andbA andbC). qed.

lemma paper_sim_signature_transcript_clean_count_rejected_rot_eq_false
    pk msg ctxt (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  ! (! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
   let tr0 = transcript_of_signature haetae_mode pk msg ctxt sig0 in
   p sig0 /\ ! sampler_bad /\ 1 <= signing_count) = false.
proof. by smt(andbA andbC). qed.

lemma mu_ro_output_paper_sim_signature_clean_rejected_any_le0
    (d : ro_output distr) pk msg ctxt (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  ! (! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu d
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
       ! sampler_bad /\ 1 <= signing_count) <= 0%r.
proof.
move=> rejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_paper_sim_signature_clean_rejected_with_state_equalities
    (pk_ref pk_cur : pkey) (msg_ref msg_cur : message)
    (ctxt_ref ctxt_cur : context) (p : signature -> bool)
    (smp : paper_sim_signature_sample)
    (sampler_bad : bool) (signing_count : int) :
  msg_cur = msg_ref =>
  ctxt_cur = ctxt_ref =>
  pk_cur = pk_ref =>
  ! (msg_cur = msg_ref /\ ctxt_cur = ctxt_ref /\ pk_cur = pk_ref /\
     ! sampler_bad /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk_ref msg_ref ctxt_ref smp)) =>
  mu (dro_output (message_hash_query pk_cur ctxt_cur msg_cur))
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk_cur msg_cur ctxt_cur smp) /\
       ! sampler_bad /\ 1 <= signing_count) <= 0%r.
proof.
move=> msg_eq ctxt_eq pk_eq rejected.
rewrite msg_eq ctxt_eq pk_eq.
apply (mu_ro_output_paper_sim_signature_clean_rejected_le0
         pk_ref msg_ref ctxt_ref p smp sampler_bad signing_count).
by smt(andbA andbC).
qed.

lemma mu_ro_output_bad_middle_true_le0
    (d : ro_output distr) (b1 b3 : bool) :
  mu d (fun (_ : ro_output) => b1 /\ !true /\ b3) <= 0%r.
proof.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=.
by rewrite mu0.
qed.

lemma mu_ro_output_count_false_right_le0
    (d : ro_output distr) (b1 : bool) :
  mu d (fun (_ : ro_output) => b1 /\ !false /\ false) <= 0%r.
proof.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma mu_ro_output_middle_false_le0
    (d : ro_output distr) (b1 b3 : bool) :
  mu d (fun (_ : ro_output) => b1 /\ false /\ b3) <= 0%r.
proof.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=.
by rewrite mu0.
qed.

lemma mu_ro_output_right_false_le0
    (d : ro_output distr) (b1 b2 : bool) :
  mu d (fun (_ : ro_output) => b1 /\ b2 /\ false) <= 0%r.
proof.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma mu_ro_output_middle_false_rassoc_le0
    (d : ro_output distr) (b1 b3 : bool) :
  mu d (fun (_ : ro_output) => b1 /\ (false /\ b3)) <= 0%r.
proof.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=.
by rewrite mu0.
qed.

lemma mu_ro_output_right_false_rassoc_le0
    (d : ro_output distr) (b1 b2 : bool) :
  mu d (fun (_ : ro_output) => b1 /\ (b2 /\ false)) <= 0%r.
proof.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma mu_ro_output_middle_false_fun_rassoc_le0
    (d : ro_output distr) (P Q : ro_output -> bool) :
  mu d (fun y => P y /\ (false /\ Q y)) <= 0%r.
proof.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=.
by rewrite mu0.
qed.

lemma mu_ro_output_right_false_fun_rassoc_le0
    (d : ro_output distr) (P Q : ro_output -> bool) :
  mu d (fun y => P y /\ (Q y /\ false)) <= 0%r.
proof.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma mu_ro_output_clean_count_rejected_le0
    (d : ro_output distr) (b : bool) :
  ! (!false /\ true /\ b) =>
  mu d (fun (_ : ro_output) => b /\ !false /\ true) <= 0%r.
proof.
move=> rejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_clean_count_rejected_from_state_le0
    (d : ro_output distr) (b sampler_bad : bool) (signing_count : int) :
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  ! sampler_bad =>
  1 <= signing_count =>
  mu d (fun (_ : ro_output) => b /\ !false /\ true) <= 0%r.
proof.
move=> rejected clean count_ge1.
apply (mu_ro_output_clean_count_rejected_le0 d b).
by smt(andbA andbC).
qed.

lemma mu_ro_output_clean_count_rejected_from_state_rassoc_le0
    (d : ro_output distr) (b sampler_bad : bool) (signing_count : int) :
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  ! sampler_bad =>
  1 <= signing_count =>
  mu d (fun (_ : ro_output) => b /\ (!false /\ true)) <= 0%r.
proof.
move=> rejected clean count_ge1.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_clean_count_rejected_from_state_commuted_le0
    (d : ro_output distr) (b sampler_bad : bool) (signing_count : int) :
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  ! sampler_bad =>
  1 <= signing_count =>
  mu d (fun (_ : ro_output) => !false /\ true /\ b) <= 0%r.
proof.
move=> rejected clean count_ge1.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_clean_count_rejected_from_state_commuted_rassoc_le0
    (d : ro_output distr) (b sampler_bad : bool) (signing_count : int) :
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  ! sampler_bad =>
  1 <= signing_count =>
  mu d (fun (_ : ro_output) => !false /\ (true /\ b)) <= 0%r.
proof.
move=> rejected clean count_ge1.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_clean_count_rejected_from_state_count_le0
    (d : ro_output distr) (b sampler_bad : bool) (signing_count : int) :
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  ! sampler_bad =>
  mu d (fun (_ : ro_output) => b /\ !false /\ 1 <= signing_count) <= 0%r.
proof.
move=> rejected clean.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_clean_count_rejected_from_state_count_rassoc_le0
    (d : ro_output distr) (b sampler_bad : bool) (signing_count : int) :
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  ! sampler_bad =>
  mu d (fun (_ : ro_output) => b /\ (!false /\ 1 <= signing_count)) <= 0%r.
proof.
move=> rejected clean.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_clean_count_rejected_from_state_count_commuted_le0
    (d : ro_output distr) (b sampler_bad : bool) (signing_count : int) :
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  ! sampler_bad =>
  mu d (fun (_ : ro_output) => !false /\ 1 <= signing_count /\ b) <= 0%r.
proof.
move=> rejected clean.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_clean_count_rejected_from_state_count_commuted_rassoc_le0
    (d : ro_output distr) (b sampler_bad : bool) (signing_count : int) :
  ! (!sampler_bad /\ 1 <= signing_count /\ b) =>
  ! sampler_bad =>
  mu d (fun (_ : ro_output) => !false /\ (1 <= signing_count /\ b)) <= 0%r.
proof.
move=> rejected clean.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(andbA andbC).
by rewrite mu0.
qed.

lemma mu_ro_output_rejected_clean_signature_event_le0
    (d : ro_output distr) (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu d (fun (_ : ro_output) =>
      p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
      !sampler_bad_prequery /\
      1 <= signing_count) <= 0%r.
proof.
move=> Hm Hctx Hpk Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0.
qed.

lemma rejected_clean_signature_event_false
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  ! (p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
     !sampler_bad_prequery /\
     1 <= signing_count).
proof.
by smt.
qed.

lemma rejected_clean_signature_event_leaf_false
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery clean leaf : bool) (signing_count : int) :
  (leaf =>
     p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
     clean /\
     1 <= signing_count) =>
  (clean => !sampler_bad_prequery) =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  !leaf.
proof.
by smt.
qed.

lemma rejected_clean_signature_event_leaf_direct_not
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery leaf : bool) (signing_count : int) :
  (leaf =>
     p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
     !sampler_bad_prequery /\
     1 <= signing_count) =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  !leaf.
proof.
by smt.
qed.

lemma rejected_clean_signature_event_predicate_false
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int) :
  !sampler_bad_prequery =>
  1 <= signing_count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  ! p (paper_sim_signature haetae_mode pk_current m ctx smp).
proof.
by smt.
qed.

lemma rejected_guarded_leaf_false (guard b leaf : bool) :
  (leaf => guard) =>
  (leaf => b) =>
  ! (guard /\ b) =>
  ! leaf.
proof.
by smt.
qed.

lemma rejected_known_clean_count_leaf_false
    (g1 g2 g3 clean count b leaf : bool) :
  g1 =>
  g2 =>
  g3 =>
  clean =>
  count =>
  (leaf => b) =>
  ! (g1 /\ g2 /\ g3 /\ clean /\ count /\ b) =>
  ! leaf.
proof.
by smt.
qed.

lemma rejected_clean_signature_event_three_if_false
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (b0 b1 b2 : bool) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (if b0 then
     if b1 then
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       !sampler_bad_prequery /\ 1 <= signing_count
     else
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       !sampler_bad_prequery /\ 1 <= signing_count
   else
     if b2 then
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       !sampler_bad_prequery /\ 1 <= signing_count
     else
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       !sampler_bad_prequery /\ 1 <= signing_count) = false.
proof.
by move=> Hm Hctx Hpk Hrej;
   case: b0; case: b1; case: b2 => /=;
     smt(rejected_clean_signature_event_false).
qed.

lemma rejected_clean_signature_event_three_if_not
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (b0 b1 b2 : bool) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  ! (if b0 then
       if b1 then
         p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
         !sampler_bad_prequery /\ 1 <= signing_count
       else
         p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
         !sampler_bad_prequery /\ 1 <= signing_count
     else
       if b2 then
         p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
         !sampler_bad_prequery /\ 1 <= signing_count
       else
         p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
         !sampler_bad_prequery /\ 1 <= signing_count).
proof.
by move=> Hm Hctx Hpk Hrej;
   case: b0; case: b1; case: b2 => /=;
     smt(rejected_clean_signature_event_false).
qed.

lemma rejected_clean_signature_event_three_if_transcript_not
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (b0 b1 b2 : bool)
    (ignored0 ignored1 ignored2 ignored3 : ro_output) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  ! (if b0 then
       if b1 then
         let r0 = ignored0 in
         let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
         let tr0 = transcript_of_signature haetae_mode pk_current m ctx sig0 in
         p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
       else
         let r0 = ignored1 in
         let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
         let tr0 = transcript_of_signature haetae_mode pk_current m ctx sig0 in
         p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
     else
       if b2 then
         let r0 = ignored2 in
         let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
         let tr0 = transcript_of_signature haetae_mode pk_current m ctx sig0 in
         p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
       else
         let r0 = ignored3 in
         let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
         let tr0 = transcript_of_signature haetae_mode pk_current m ctx sig0 in
         p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count).
proof.
by move=> Hm Hctx Hpk Hrej;
   case: b0; case: b1; case: b2 => /=;
     smt(rejected_clean_signature_event_false).
qed.

lemma rejected_clean_signature_event_one_if_not
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (b : bool) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  ! (if b then
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       !sampler_bad_prequery /\ 1 <= signing_count
     else
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       !sampler_bad_prequery /\ 1 <= signing_count).
proof.
by move=> Hm Hctx Hpk Hrej;
   case: b => /=; smt(rejected_clean_signature_event_false).
qed.

lemma rejected_clean_signature_event_one_if_transcript_not
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (b : bool) (ignored : ro_output) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  ! (if b then
       let r0 = ignored in
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 = transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
     else
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 = transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count).
proof.
by move=> Hm Hctx Hpk Hrej;
   case: b => /=; smt(rejected_clean_signature_event_false).
qed.

lemma rejected_clean_signature_event_one_if_two_ignored_not
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (b : bool) (ignored_then ignored_else : ro_output) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  ! (if b then
       let r0 = ignored_then in
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 = transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
     else
       let r0 = ignored_else in
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 = transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count).
proof.
by move=> Hm Hctx Hpk Hrej;
   case: b => /=; smt(rejected_clean_signature_event_false).
qed.

lemma rejected_clean_signature_event_two_fro_get_suffix_false
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) (x2 : ro_output) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (if x1 \in rom then
     let r1 = (oget rom.[x1]).`1 in
     let m0 = rom.[x1 <- (r1, PROM.Known)] in
     let x0_0 =
       challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash r1) in
     if x0_0 \in m0 then
       let r0 = (oget m0.[x0_0]).`1 in
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 =
         transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
     else
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 =
         transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
   else
     let m0 = rom.[x1 <- (x2, PROM.Known)] in
     let x0_0 =
       challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash x2) in
     if x0_0 \in m0 then
       let r0 = (oget m0.[x0_0]).`1 in
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 =
         transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
     else
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 =
         transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) = false.
proof.
move=> Hm Hctx Hpk Hrejected.
case: (x1 \in rom) => Hx1 /=.
+ case:
    (challenge_hash_query haetae_mode
       (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
       (paper_sim_commitment_lowbits haetae_mode smp)
       (ro_message_hash (oget rom.[x1]).`1) \in
     rom.[x1 <- ((oget rom.[x1]).`1, PROM.Known)]) => Hx0 /=;
  smt(rejected_clean_signature_event_false).
case:
  (challenge_hash_query haetae_mode
     (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
     (paper_sim_commitment_lowbits haetae_mode smp)
     (ro_message_hash x2) \in
   rom.[x1 <- (x2, PROM.Known)]) => Hx0 /=;
smt(rejected_clean_signature_event_false).
qed.

lemma mu_ro_output_rejected_clean_signature_event_two_fro_get_suffix_le0
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (x2 : ro_output) =>
       if x1 \in rom then
         let r1 = (oget rom.[x1]).`1 in
         let m0 = rom.[x1 <- (r1, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash r1) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
         else
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
       else
         let m0 = rom.[x1 <- (x2, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash x2) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
         else
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) <= 0%r.
proof.
move=> Hm Hctx Hpk Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(rejected_clean_signature_event_two_fro_get_suffix_false).
by rewrite mu0.
qed.

lemma mu_ro_output_rejected_clean_signature_event_two_fro_get_simplified_suffix_le0
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk : pkey) (msg : message) (ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  ! (!sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (x2 : ro_output) =>
       if x1 \in rom then
         let r1 = (oget rom.[x1]).`1 in
         let m0 = rom.[x1 <- (r1, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash r1) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
         else
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
       else
         let m0 = rom.[x1 <- (x2, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash x2) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
         else
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) <= 0%r.
proof.
move=> Hrejected.
apply (mu_ro_output_rejected_clean_signature_event_two_fro_get_suffix_le0
         rom p pk pk msg msg ctxt ctxt smp sampler_bad_prequery
         signing_count x1); smt().
qed.

lemma rejected_clean_event_bool_drop_count_suffix_false_base
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  ! (!bad /\ 1 <= count /\ b) =>
  (b /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_signature_event_two_fro_get_guarded_drop_count_suffix_false
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) (x2 : ro_output) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  1 <= signing_count =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (if x1 \in rom then
     let r1 = (oget rom.[x1]).`1 in
     let m0 = rom.[x1 <- (r1, PROM.Known)] in
     let x0_0 =
       challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash r1) in
     if x0_0 \in m0 then
       let r0 = (oget m0.[x0_0]).`1 in
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 =
         transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery
     else
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 =
         transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery
   else
     let m0 = rom.[x1 <- (x2, PROM.Known)] in
     let x0_0 =
       challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash x2) in
     if x0_0 \in m0 then
       let r0 = (oget m0.[x0_0]).`1 in
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 =
         transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery
     else
       let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
       let tr0 =
         transcript_of_signature haetae_mode pk_current m ctx sig0 in
       p sig0 /\ !sampler_bad_prequery) = false.
proof.
move=> Hm Hctx Hpk Hcount Hrejected.
case: (x1 \in rom) => Hx1 /=.
+ case:
    (challenge_hash_query haetae_mode
       (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
       (paper_sim_commitment_lowbits haetae_mode smp)
       (ro_message_hash (oget rom.[x1]).`1) \in
     rom.[x1 <- ((oget rom.[x1]).`1, PROM.Known)]) => Hx0 /=;
  smt(rejected_clean_signature_event_predicate_false).
case:
  (challenge_hash_query haetae_mode
     (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
     (paper_sim_commitment_lowbits haetae_mode smp)
     (ro_message_hash x2) \in
   rom.[x1 <- (x2, PROM.Known)]) => Hx0 /=;
smt(rejected_clean_signature_event_predicate_false).
qed.

lemma mu_ro_output_rejected_clean_signature_event_two_fro_get_guarded_drop_count_suffix_le0
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  1 <= signing_count =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (x2 : ro_output) =>
       if x1 \in rom then
         let r1 = (oget rom.[x1]).`1 in
         let m0 = rom.[x1 <- (r1, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash r1) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ !sampler_bad_prequery
         else
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ !sampler_bad_prequery
       else
         let m0 = rom.[x1 <- (x2, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash x2) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ !sampler_bad_prequery
         else
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ !sampler_bad_prequery) <= 0%r.
proof.
move=> Hm Hctx Hpk Hcount Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(rejected_clean_signature_event_two_fro_get_guarded_drop_count_suffix_false).
by rewrite mu0.
qed.

lemma rejected_clean_signature_event_two_fro_get_target_guarded_drop_count_suffix_false
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) (x2 : ro_output) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  1 <= signing_count =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (if x1 \in rom then
     let r1 = (oget rom.[x1]).`1 in
     let m0 = rom.[x1 <- (r1, PROM.Known)] in
     let x0_0 =
       challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash r1) in
     if x0_0 \in m0 then
       let r0 = (oget m0.[x0_0]).`1 in
       let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
       let tr0 =
         transcript_of_signature haetae_mode pk msg ctxt sig0 in
       p sig0 /\ !sampler_bad_prequery
     else
       let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
       let tr0 =
         transcript_of_signature haetae_mode pk msg ctxt sig0 in
       p sig0 /\ !sampler_bad_prequery
   else
     let m0 = rom.[x1 <- (x2, PROM.Known)] in
     let x0_0 =
       challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash x2) in
     if x0_0 \in m0 then
       let r0 = (oget m0.[x0_0]).`1 in
       let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
       let tr0 =
         transcript_of_signature haetae_mode pk msg ctxt sig0 in
       p sig0 /\ !sampler_bad_prequery
     else
       let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
       let tr0 =
         transcript_of_signature haetae_mode pk msg ctxt sig0 in
       p sig0 /\ !sampler_bad_prequery) = false.
proof.
move=> Hm Hctx Hpk Hcount Hrejected.
case: (x1 \in rom) => Hx1 /=.
+ case:
    (challenge_hash_query haetae_mode
       (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
       (paper_sim_commitment_lowbits haetae_mode smp)
       (ro_message_hash (oget rom.[x1]).`1) \in
     rom.[x1 <- ((oget rom.[x1]).`1, PROM.Known)]) => Hx0 /=;
  smt(rejected_clean_event_bool_drop_count_suffix_false_base).
case:
  (challenge_hash_query haetae_mode
     (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
     (paper_sim_commitment_lowbits haetae_mode smp)
     (ro_message_hash x2) \in
   rom.[x1 <- (x2, PROM.Known)]) => Hx0 /=;
smt(rejected_clean_event_bool_drop_count_suffix_false_base).
qed.

lemma mu_ro_output_rejected_clean_signature_event_two_fro_get_target_guarded_drop_count_suffix_le0
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  1 <= signing_count =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (x2 : ro_output) =>
       if x1 \in rom then
         let r1 = (oget rom.[x1]).`1 in
         let m0 = rom.[x1 <- (r1, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash r1) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery
         else
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery
       else
         let m0 = rom.[x1 <- (x2, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash x2) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery
         else
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery) <= 0%r.
proof.
move=> Hm Hctx Hpk Hcount Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt(rejected_clean_signature_event_two_fro_get_target_guarded_drop_count_suffix_false).
by rewrite mu0.
qed.

lemma rejected_clean_signature_event_two_fro_get_drop_count_suffix_false
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk : pkey) (msg : message) (ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) (x2 : ro_output) :
  1 <= signing_count =>
  ! (!sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (if x1 \in rom then
     let r1 = (oget rom.[x1]).`1 in
     let m0 = rom.[x1 <- (r1, PROM.Known)] in
     let x0_0 =
       challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash r1) in
     if x0_0 \in m0 then
       let r0 = (oget m0.[x0_0]).`1 in
       let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
       let tr0 =
         transcript_of_signature haetae_mode pk msg ctxt sig0 in
       p sig0 /\ !sampler_bad_prequery
     else
       let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
       let tr0 =
         transcript_of_signature haetae_mode pk msg ctxt sig0 in
       p sig0 /\ !sampler_bad_prequery
   else
     let m0 = rom.[x1 <- (x2, PROM.Known)] in
     let x0_0 =
       challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash x2) in
     if x0_0 \in m0 then
       let r0 = (oget m0.[x0_0]).`1 in
       let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
       let tr0 =
         transcript_of_signature haetae_mode pk msg ctxt sig0 in
       p sig0 /\ !sampler_bad_prequery
     else
       let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
       let tr0 =
         transcript_of_signature haetae_mode pk msg ctxt sig0 in
       p sig0 /\ !sampler_bad_prequery) = false.
proof.
move=> Hcount Hrejected.
case: (x1 \in rom) => Hx1 /=.
+ case:
    (challenge_hash_query haetae_mode
       (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
       (paper_sim_commitment_lowbits haetae_mode smp)
       (ro_message_hash (oget rom.[x1]).`1) \in
     rom.[x1 <- ((oget rom.[x1]).`1, PROM.Known)]) => Hx0 /=;
  smt(rejected_clean_event_bool_drop_count_suffix_false_base).
case:
  (challenge_hash_query haetae_mode
     (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
     (paper_sim_commitment_lowbits haetae_mode smp)
     (ro_message_hash x2) \in
   rom.[x1 <- (x2, PROM.Known)]) => Hx0 /=;
smt(rejected_clean_event_bool_drop_count_suffix_false_base).
qed.

lemma mu_ro_output_rejected_clean_signature_event_two_fro_get_simplified_drop_count_suffix_le0
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk : pkey) (msg : message) (ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  1 <= signing_count =>
  ! (!sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (x2 : ro_output) =>
       if x1 \in rom then
         let r1 = (oget rom.[x1]).`1 in
         let m0 = rom.[x1 <- (r1, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash r1) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery
         else
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery
       else
         let m0 = rom.[x1 <- (x2, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk msg ctxt smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash x2) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery
         else
           let sig0 = paper_sim_signature haetae_mode pk msg ctxt smp in
           let tr0 =
             transcript_of_signature haetae_mode pk msg ctxt sig0 in
           p sig0 /\ !sampler_bad_prequery) <= 0%r.
proof.
  move=> Hcount Hrejected.
  rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
  + move=> y /=.
    by smt(rejected_clean_signature_event_two_fro_get_drop_count_suffix_false).
by rewrite mu0.
qed.

lemma mu_ro_output_rejected_clean_signature_event_two_fro_get_suffix_clean_le0
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery clean : bool) (signing_count : int)
    (x1 : ro_query) :
  (clean => !sampler_bad_prequery) =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (x2 : ro_output) =>
       if x1 \in rom then
         let r1 = (oget rom.[x1]).`1 in
         let m0 = rom.[x1 <- (r1, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash r1) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ clean /\ 1 <= signing_count
         else
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ clean /\ 1 <= signing_count
       else
         let m0 = rom.[x1 <- (x2, PROM.Known)] in
         let x0_0 =
           challenge_hash_query haetae_mode
             (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
             (paper_sim_commitment_lowbits haetae_mode smp)
             (ro_message_hash x2) in
         if x0_0 \in m0 then
           let r0 = (oget m0.[x0_0]).`1 in
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ clean /\ 1 <= signing_count
         else
           let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
           let tr0 =
             transcript_of_signature haetae_mode pk_current m ctx sig0 in
           p sig0 /\ clean /\ 1 <= signing_count) <= 0%r.
proof.
move=> Hclean Hm Hctx Hpk Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ move=> y /=.
  case: (x1 \in rom) => Hx1 /=.
  + case:
      (challenge_hash_query haetae_mode
         (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
         (paper_sim_commitment_lowbits haetae_mode smp)
         (ro_message_hash (oget rom.[x1]).`1) \in
       rom.[x1 <- ((oget rom.[x1]).`1, PROM.Known)]) => Hx0 /=;
    smt(rejected_clean_signature_event_false).
  case:
    (challenge_hash_query haetae_mode
       (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
       (paper_sim_commitment_lowbits haetae_mode smp)
       (ro_message_hash y) \in
     rom.[x1 <- (y, PROM.Known)]) => Hx0 /=;
  smt(rejected_clean_signature_event_false).
by rewrite mu0.
qed.

lemma mu_ro_output_rejected_clean_signature_event_two_fro_get_suffix_with_support
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (Q : ro_output -> bool)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (forall v,
     v \in dro_output x1 =>
     (if x1 \in rom then
        let r1 = (oget rom.[x1]).`1 in
        let m0 = rom.[x1 <- (r1, PROM.Known)] in
        let x0_0 =
          challenge_hash_query haetae_mode
            (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
            (paper_sim_commitment_lowbits haetae_mode smp)
            (ro_message_hash r1) in
        if x0_0 \in m0 then
          let r0 = (oget m0.[x0_0]).`1 in
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
      else
        let m0 = rom.[x1 <- (v, PROM.Known)] in
        let x0_0 =
          challenge_hash_query haetae_mode
            (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
            (paper_sim_commitment_lowbits haetae_mode smp)
            (ro_message_hash v) in
        if x0_0 \in m0 then
          let r0 = (oget m0.[x0_0]).`1 in
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) =>
     Q v) =>
  (mu (dro_output x1)
     (fun (x2 : ro_output) =>
        if x1 \in rom then
          let r1 = (oget rom.[x1]).`1 in
          let m0 = rom.[x1 <- (r1, PROM.Known)] in
          let x0_0 =
            challenge_hash_query haetae_mode
              (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
              (paper_sim_commitment_lowbits haetae_mode smp)
              (ro_message_hash r1) in
          if x0_0 \in m0 then
            let r0 = (oget m0.[x0_0]).`1 in
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
          else
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let m0 = rom.[x1 <- (x2, PROM.Known)] in
          let x0_0 =
            challenge_hash_query haetae_mode
              (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
              (paper_sim_commitment_lowbits haetae_mode smp)
              (ro_message_hash x2) in
          if x0_0 \in m0 then
            let r0 = (oget m0.[x0_0]).`1 in
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
          else
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) <= 0%r) &&
  (forall v,
     v \in dro_output x1 =>
     (if x1 \in rom then
        let r1 = (oget rom.[x1]).`1 in
        let m0 = rom.[x1 <- (r1, PROM.Known)] in
        let x0_0 =
          challenge_hash_query haetae_mode
            (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
            (paper_sim_commitment_lowbits haetae_mode smp)
            (ro_message_hash r1) in
        if x0_0 \in m0 then
          let r0 = (oget m0.[x0_0]).`1 in
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
      else
        let m0 = rom.[x1 <- (v, PROM.Known)] in
        let x0_0 =
          challenge_hash_query haetae_mode
            (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
            (paper_sim_commitment_lowbits haetae_mode smp)
            (ro_message_hash v) in
        if x0_0 \in m0 then
          let r0 = (oget m0.[x0_0]).`1 in
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) =>
     Q v).
proof.
move=> Hm Hctx Hpk Hrejected HQ.
split.
+ rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
  + by move=> y /=; smt(rejected_clean_signature_event_two_fro_get_suffix_false).
  by rewrite mu0.
by smt.
qed.

lemma mu_ro_output_rejected_clean_signature_event_two_fro_get_suffix_self_with_support
    (rom : (ro_query, ro_output * PROM.flag) fmap)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (mu (dro_output x1)
     (fun (x2 : ro_output) =>
        if x1 \in rom then
          let r1 = (oget rom.[x1]).`1 in
          let m0 = rom.[x1 <- (r1, PROM.Known)] in
          let x0_0 =
            challenge_hash_query haetae_mode
              (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
              (paper_sim_commitment_lowbits haetae_mode smp)
              (ro_message_hash r1) in
          if x0_0 \in m0 then
            let r0 = (oget m0.[x0_0]).`1 in
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
          else
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let m0 = rom.[x1 <- (x2, PROM.Known)] in
          let x0_0 =
            challenge_hash_query haetae_mode
              (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
              (paper_sim_commitment_lowbits haetae_mode smp)
              (ro_message_hash x2) in
          if x0_0 \in m0 then
            let r0 = (oget m0.[x0_0]).`1 in
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
          else
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) <= 0%r) &&
  (forall v,
     v \in dro_output x1 =>
     (if x1 \in rom then
        let r1 = (oget rom.[x1]).`1 in
        let m0 = rom.[x1 <- (r1, PROM.Known)] in
        let x0_0 =
          challenge_hash_query haetae_mode
            (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
            (paper_sim_commitment_lowbits haetae_mode smp)
            (ro_message_hash r1) in
        if x0_0 \in m0 then
          let r0 = (oget m0.[x0_0]).`1 in
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
      else
        let m0 = rom.[x1 <- (v, PROM.Known)] in
        let x0_0 =
          challenge_hash_query haetae_mode
            (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
            (paper_sim_commitment_lowbits haetae_mode smp)
            (ro_message_hash v) in
        if x0_0 \in m0 then
          let r0 = (oget m0.[x0_0]).`1 in
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
          let tr0 =
            transcript_of_signature haetae_mode pk_current m ctx sig0 in
          p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) =>
     (fun (x2 : ro_output) =>
        if x1 \in rom then
          let r1 = (oget rom.[x1]).`1 in
          let m0 = rom.[x1 <- (r1, PROM.Known)] in
          let x0_0 =
            challenge_hash_query haetae_mode
              (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
              (paper_sim_commitment_lowbits haetae_mode smp)
              (ro_message_hash r1) in
          if x0_0 \in m0 then
            let r0 = (oget m0.[x0_0]).`1 in
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
          else
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
        else
          let m0 = rom.[x1 <- (x2, PROM.Known)] in
          let x0_0 =
            challenge_hash_query haetae_mode
              (paper_sim_commitment_highbits haetae_mode pk_current m ctx smp)
              (paper_sim_commitment_lowbits haetae_mode smp)
              (ro_message_hash x2) in
          if x0_0 \in m0 then
            let r0 = (oget m0.[x0_0]).`1 in
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count
          else
            let sig0 = paper_sim_signature haetae_mode pk_current m ctx smp in
            let tr0 =
              transcript_of_signature haetae_mode pk_current m ctx sig0 in
            p sig0 /\ !sampler_bad_prequery /\ 1 <= signing_count) v).
proof.
move=> Hm Hctx Hpk Hrejected.
split.
+ apply (mu_ro_output_rejected_clean_signature_event_two_fro_get_suffix_le0
           rom p pk_current pk m msg ctx ctxt smp sampler_bad_prequery
           signing_count x1); smt().
by smt().
qed.

lemma mu_ro_output_rejected_clean_signature_event_with_support
    (d : ro_output distr) (P Q : ro_output -> bool)
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  (forall y, P y =>
     p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
     !sampler_bad_prequery /\
     1 <= signing_count) =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (forall v, v \in d => P v => Q v) =>
  (mu d P <= 0%r) &&
  (forall v, v \in d => P v => Q v).
proof.
move=> Hm Hctx Hpk HP Hrejected HQ.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt.
by rewrite mu0; smt.
qed.

lemma mu_ro_output_false_from_rejected_event_pointwise_le0
    (d : ro_output distr) (P : ro_output -> bool) (E : bool) :
  ! E =>
  (forall y, P y => E) =>
  mu d P <= 0%r.
proof.
move=> Hrejected Hpoint.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ move=> y /=.
  case: (P y) => Hy /=.
  + by smt().
  by trivial.
by rewrite mu0.
qed.

lemma mu_ro_output_constant_false_le0
    (d : ro_output distr) (b : bool) :
  ! b =>
  mu d (fun (_ : ro_output) => b) <= 0%r.
proof.
move=> Hb.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt().
by rewrite mu0.
qed.

lemma mu_ro_output_pointwise_false_le0
    (d : ro_output distr) (P : ro_output -> bool) :
  (forall y, P y = false) =>
  mu d P <= 0%r.
proof.
move=> HP.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; rewrite HP.
by rewrite mu0.
qed.

lemma mu_ro_output_rejected_clean_event_bool_reordered_suffix_le0
    (d : ro_output distr) (bad : bool) (count : int) (b : bool) :
  ! (!bad /\ 1 <= count /\ b) =>
  mu d (fun (_ : ro_output) => b /\ !bad /\ 1 <= count) <= 0%r.
proof.
move=> Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ move=> y /=.
  case: b => Hb /=.
  + case: (!bad) => Hbad /=.
    + case: (1 <= count) => Hcount /=.
      + by smt().
      by trivial.
    by trivial.
  by trivial.
by rewrite mu0.
qed.

lemma mu_ro_output_false_from_rejected_event_pointwise_with_support
    (d : ro_output distr) (P Q : ro_output -> bool) (E : bool) :
  ! E =>
  (forall y, P y => E) =>
  (forall y, y \in d => P y => Q y) =>
  (mu d P <= 0%r) &&
  (forall y, y \in d => P y => Q y).
proof.
move=> Hrejected Hpoint Hsupport.
split.
+ apply (mu_ro_output_false_from_rejected_event_pointwise_le0 d P E).
  + exact Hrejected.
  exact Hpoint.
by smt().
qed.

lemma rejected_clean_signature_event_post_sampler_suffix_false
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (count : int) (p : signature -> bool) (sig : signature) :
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\ !bad /\ 1 <= count /\ p sig) =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  (p sig /\ !bad /\ 1 <= count) = false.
proof.
smt().
qed.

lemma rejected_clean_event_post_sampler_bool_suffix_false
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (count : int) (b : bool) :
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\ !bad /\ 1 <= count /\ b) =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  (b /\ !bad /\ 1 <= count) = false.
proof.
smt().
qed.

lemma rejected_clean_event_post_sampler_bool_suffix_false_clean_first
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (count : int) (b : bool) :
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\ !bad /\ 1 <= count /\ b) =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  (!bad /\ 1 <= count /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_with_added_count_suffix_false
  (bad : bool) (count : int) (b : bool) :
  ! (b /\ !bad) =>
  (b /\ !bad /\ 1 <= count) = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_with_added_count_suffix_false_clean_first
  (bad : bool) (count : int) (b : bool) :
  ! (b /\ !bad) =>
  (!bad /\ 1 <= count /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_with_added_count_suffix_false_clean_pair
  (bad : bool) (count : int) (b : bool) :
  ! (!bad /\ b) =>
  (!bad /\ 1 <= count /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_reordered_count_suffix_false
  (bad : bool) (count : int) (b : bool) :
  ! (!bad /\ 1 <= count /\ b) =>
  (b /\ !bad /\ 1 <= count) = false.
proof.
smt().
qed.

lemma rejected_clean_signature_event_reordered_pointwise_eq_false
    (p : signature -> bool)
    (pk : pkey) (msg : message) (ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int) :
  ! (!sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
   !sampler_bad_prequery /\ 1 <= signing_count) = false.
proof.
smt().
qed.

lemma mu_ro_output_rejected_clean_signature_event_reordered_suffix_le0
    (p : signature -> bool)
    (pk : pkey) (msg : message) (ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  ! (!sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk msg ctxt smp) /\
       !sampler_bad_prequery /\ 1 <= signing_count) <= 0%r.
proof.
move=> Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt().
by rewrite mu0.
qed.

lemma rejected_clean_event_bool_no_count_suffix_false
  (bad : bool) (b : bool) :
  ! (b /\ !bad) =>
  (b /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_no_count_suffix_false_clean_first
  (bad : bool) (b : bool) :
  ! (!bad /\ b) =>
  (!bad /\ b) = false.
proof.
smt().
qed.

lemma rejected_plain_bool_suffix_false
  (b clean : bool) :
  ! b =>
  (b /\ clean) = false.
proof.
smt().
qed.

lemma rejected_plain_bool_suffix_false_clean_first
  (b clean : bool) :
  ! b =>
  (clean /\ b) = false.
proof.
smt().
qed.

lemma rejected_plain_bool_self_false (b : bool) :
  ! b =>
  b = false.
proof.
smt().
qed.

lemma rejected_event_implies_false (event rejected_event : bool) :
  (event => rejected_event) =>
  ! rejected_event =>
  event = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_drop_count_from_state_false
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ 1 <= count /\ b) =>
  (b /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_drop_count_from_state_false_clean_first
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ 1 <= count /\ b) =>
  (!bad /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_no_count_from_state_false
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (b : bool) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\ !bad /\ b) =>
  (b /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_bool_no_count_from_state_false_clean_first
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (b : bool) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\ !bad /\ b) =>
  (!bad /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_simplified_bool_suffix_false
  (bad : bool) (count : int) (b : bool) :
  ! (!bad /\ 1 <= count /\ b) =>
  (b /\ !bad /\ 1 <= count) = false.
proof.
smt().
qed.

lemma rejected_clean_event_simplified_bool_suffix_false_clean_first
  (bad : bool) (count : int) (b : bool) :
  ! (!bad /\ 1 <= count /\ b) =>
  (!bad /\ 1 <= count /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_simplified_bool_drop_count_suffix_false
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  ! (!bad /\ 1 <= count /\ b) =>
  (b /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_simplified_bool_drop_count_suffix_false_clean_first
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  ! (!bad /\ 1 <= count /\ b) =>
  (!bad /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_rot_drop_count_suffix_false
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  ! (b /\ !bad /\ 1 <= count) =>
  (b /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_rot_drop_count_suffix_false_clean_first
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  ! (b /\ !bad /\ 1 <= count) =>
  (!bad /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_clean_pair_drop_count_suffix_false
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  ! (!bad /\ b /\ 1 <= count) =>
  (b /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_clean_pair_drop_count_suffix_false_clean_first
  (bad : bool) (count : int) (b : bool) :
  1 <= count =>
  ! (!bad /\ b /\ 1 <= count) =>
  (!bad /\ b) = false.
proof.
smt().
qed.

lemma rejected_clean_event_if_drop_count_suffix_false
  (bad : bool) (count : int) (c b1 b2 : bool) :
  1 <= count =>
  ! (!bad /\ 1 <= count /\ (if c then b1 else b2)) =>
  (if c then b1 /\ !bad else b2 /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_if_drop_count_suffix_false_clean_first
  (bad : bool) (count : int) (c b1 b2 : bool) :
  1 <= count =>
  ! (!bad /\ 1 <= count /\ (if c then b1 else b2)) =>
  (if c then !bad /\ b1 else !bad /\ b2) = false.
proof.
smt().
qed.

lemma rejected_clean_event_if_drop_count_from_state_false
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (count : int) (c b1 b2 : bool) :
  1 <= count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ 1 <= count /\ (if c then b1 else b2)) =>
  (if c then b1 /\ !bad else b2 /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_if_drop_count_from_state_false_clean_first
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (count : int) (c b1 b2 : bool) :
  1 <= count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ 1 <= count /\ (if c then b1 else b2)) =>
  (if c then !bad /\ b1 else !bad /\ b2) = false.
proof.
smt().
qed.

lemma rejected_clean_event_if_no_count_from_state_false
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (c b1 b2 : bool) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ (if c then b1 else b2)) =>
  (if c then b1 /\ !bad else b2 /\ !bad) = false.
proof.
smt().
qed.

lemma rejected_clean_event_if_no_count_from_state_false_clean_first
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (c b1 b2 : bool) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ (if c then b1 else b2)) =>
  (if c then !bad /\ b1 else !bad /\ b2) = false.
proof.
smt().
qed.

lemma rejected_clean_event_if_stronger_clean_drop_count_from_state_false
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (count : int) (c b1 b2 clean1 clean2 : bool) :
  1 <= count =>
  (clean1 => !bad) =>
  (clean2 => !bad) =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ 1 <= count /\ (if c then b1 else b2)) =>
  (if c then b1 /\ clean1 else b2 /\ clean2) = false.
proof.
smt().
qed.

lemma rejected_clean_event_if_stronger_clean_no_count_from_state_false
  (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
  (bad : bool) (c b1 b2 clean1 clean2 : bool) :
  (clean1 => !bad) =>
  (clean2 => !bad) =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ (if c then b1 else b2)) =>
  (if c then b1 /\ clean1 else b2 /\ clean2) = false.
proof.
smt().
qed.

lemma rejected_clean_signature_event_simplified_suffix_false
  (bad : bool) (count : int) (p : signature -> bool) (sig : signature) :
  ! (!bad /\ 1 <= count /\ p sig) =>
  (p sig /\ !bad /\ 1 <= count) = false.
proof.
smt().
qed.

lemma rejected_clean_signature_event_simplified_suffix_false_clean_first
  (bad : bool) (count : int) (p : signature -> bool) (sig : signature) :
  ! (!bad /\ 1 <= count /\ p sig) =>
  (!bad /\ 1 <= count /\ p sig) = false.
proof.
smt().
qed.

lemma rejected_clean_signature_event_drop_count_from_state_false
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int) :
  1 <= signing_count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
   !sampler_bad_prequery) = false.
proof.
move=> Hcount Hm Hctx Hpk Hrejected.
apply (rejected_clean_event_bool_drop_count_suffix_false_base
         sampler_bad_prequery signing_count
         (p (paper_sim_signature haetae_mode pk_current m ctx smp))).
+ exact Hcount.
smt(rejected_clean_signature_event_false).
qed.

lemma rejected_clean_signature_event_drop_count_from_state_false_clean_first
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int) :
  1 <= signing_count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  (!sampler_bad_prequery /\
   p (paper_sim_signature haetae_mode pk_current m ctx smp)) = false.
proof.
move=> Hcount Hm Hctx Hpk Hrejected.
apply (rejected_clean_event_simplified_bool_drop_count_suffix_false_clean_first
         sampler_bad_prequery signing_count
         (p (paper_sim_signature haetae_mode pk_current m ctx smp))).
+ exact Hcount.
smt(rejected_clean_signature_event_false).
qed.

lemma mu_ro_output_rejected_clean_signature_event_one_fro_get_suffix_le0
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       !sampler_bad_prequery /\ 1 <= signing_count) <= 0%r.
proof.
move=> Hm Hctx Hpk Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt().
by rewrite mu0.
qed.

lemma mu_ro_output_rejected_clean_signature_event_one_fro_get_drop_count_suffix_le0
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  1 <= signing_count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (_ : ro_output) =>
       p (paper_sim_signature haetae_mode pk_current m ctx smp) /\
       !sampler_bad_prequery) <= 0%r.
proof.
move=> Hcount Hm Hctx Hpk Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=;
     apply (rejected_clean_signature_event_drop_count_from_state_false
              p pk_current pk m msg ctx ctxt smp sampler_bad_prequery
              signing_count); smt().
by rewrite mu0.
qed.

lemma mu_ro_output_rejected_clean_signature_event_one_fro_get_drop_count_suffix_clean_first_le0
    (p : signature -> bool)
    (pk_current pk : pkey) (m msg : message) (ctx ctxt : context)
    (smp : paper_sim_signature_sample)
    (sampler_bad_prequery : bool) (signing_count : int)
    (x1 : ro_query) :
  1 <= signing_count =>
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !sampler_bad_prequery /\ 1 <= signing_count /\
     p (paper_sim_signature haetae_mode pk msg ctxt smp)) =>
  mu (dro_output x1)
    (fun (_ : ro_output) =>
       !sampler_bad_prequery /\
       p (paper_sim_signature haetae_mode pk_current m ctx smp)) <= 0%r.
proof.
move=> Hcount Hm Hctx Hpk Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=;
     apply (rejected_clean_signature_event_drop_count_from_state_false_clean_first
              p pk_current pk m msg ctx ctxt smp sampler_bad_prequery
              signing_count); smt().
by rewrite mu0.
qed.

lemma mu_ro_output_rejected_clean_event_bool_suffix_le0
    (m msg : message) (ctx ctxt : context) (pk_current pk : pkey)
    (bad : bool) (count : int) (b : bool) (x1 : ro_query) :
  m = msg =>
  ctx = ctxt =>
  pk_current = pk =>
  ! (m = msg /\ ctx = ctxt /\ pk_current = pk /\
     !bad /\ 1 <= count /\ b) =>
  mu (dro_output x1)
    (fun (_ : ro_output) => b /\ !bad /\ 1 <= count) <= 0%r.
proof.
move=> Hm Hctx Hpk Hrejected.
rewrite (mu_eq _ _ (fun (_ : ro_output) => false)).
+ by move=> y /=; smt().
by rewrite mu0.
qed.

equiv concrete_budgeted_o_sign_saturated_fallback_equiv :
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).O.sign ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).O.sign :
  ={glob HAETAE_RO.FRO, arg} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2}
  ==>
  ={glob HAETAE_RO.FRO, res} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2}.
proof.
proc.
rcondf{1} 1; first by auto => />; smt.
rcondf{2} 1; first by auto => />; smt.
by auto.
qed.

equiv concrete_budgeted_o_sign_saturated_fallback_full_state_equiv :
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).O.sign ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).O.sign :
  ={glob HAETAE_RO.FRO, arg} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}
  ==>
  ={glob HAETAE_RO.FRO, res} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}.
proof.
proc.
rcondf{1} 1; first by auto => />; smt.
rcondf{2} 1; first by auto => />; smt.
by auto.
qed.

equiv concrete_budgeted_ah_get_full_state_equiv :
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).AH.get ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).AH.get :
  ={glob HAETAE_RO.FRO, arg} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}
  ==>
  ={glob HAETAE_RO.FRO, res} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}.
proof.
proc.
case (ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} <
        hash_query_budget_count).
+ rcondt{1} 1; first by auto; smt.
  rcondt{2} 1; first by auto; smt.
  case (ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} = 0).
  + rcondt{1} 1; first by auto; smt.
    rcondt{2} 1; first by auto; smt.
    wp.
    call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
    + by sim.
    by auto => />.
  rcondf{1} 1; first by auto; smt.
  rcondf{2} 1; first by auto; smt.
  wp.
  call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
  + by sim.
  by auto => />.
rcondf{1} 1; first by auto; smt.
rcondf{2} 1; first by auto; smt.
by auto => />.
qed.

equiv concrete_budgeted_adversary_forge_saturated_fallback_equiv :
  A(ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
       HAETAE_RO.FRO).AH,
    ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
       HAETAE_RO.FRO).O).forge ~
  A(ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
       HAETAE_RO.FRO).AH,
    ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
       HAETAE_RO.FRO).O).forge :
  ={glob HAETAE_RO.FRO, glob A, arg} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}
  ==>
  ={glob HAETAE_RO.FRO, glob A, res} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}.
proof.
proc
  (={glob HAETAE_RO.FRO} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.records{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
   ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
   signature_query_budget_count <=
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}) => //.
+ move=> />.
+ proc*.
  call concrete_budgeted_ah_get_full_state_equiv.
  by auto => />.
+ proc*.
  call concrete_budgeted_o_sign_saturated_fallback_full_state_equiv.
  by auto => />.
qed.

lemma concrete_budgeted_adversary_forge_saturated_clean_fallback_lifts
    pk (R : message * context * signature -> glob HAETAE_RO.FRO -> bool) &m :
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} =>
  Pr[A(ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
          HAETAE_RO.FRO).AH,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
          HAETAE_RO.FRO).O).forge(pk) @ &m :
       R res (glob HAETAE_RO.FRO) /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[A(ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
          HAETAE_RO.FRO).AH,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
          HAETAE_RO.FRO).O).forge(pk) @ &m :
       R res (glob HAETAE_RO.FRO)].
proof.
move=> saturated.
byequiv
  (: ={glob HAETAE_RO.FRO, glob A, arg} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.records{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
     signature_query_budget_count <=
       ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1}
     ==>
     (R res{1} (glob HAETAE_RO.FRO){1} /\
      ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1}) =>
     R res{2} (glob HAETAE_RO.FRO){2}) => //.
+ by proc*; call concrete_budgeted_adversary_forge_saturated_fallback_equiv.
qed.

lemma concrete_budgeted_o_sign_saturated_clean_fallback_lifts
    m ctx (R : signature -> glob HAETAE_RO.FRO -> bool) &m :
  signature_query_budget_count <=
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{m} =>
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROSigningAttemptPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO) /\
       ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery] <=
  Pr[ROMInternalTranscriptBudgetedPaperSimAsNMA
       (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
        HAETAE_RO.FRO).O.sign(m, ctx) @ &m :
       R res (glob HAETAE_RO.FRO)].
proof.
move=> saturated.
byequiv
  (: ={glob HAETAE_RO.FRO, arg} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
     signature_query_budget_count <=
       ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{1} /\
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1} =
       ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2}
     ==>
     (R res{1} (glob HAETAE_RO.FRO){1} /\
      ! ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{1}) =>
     R res{2} (glob HAETAE_RO.FRO){2}) => //.
+ by proc*; call concrete_budgeted_o_sign_saturated_fallback_equiv.
qed.

equiv concrete_two_call_g0_g1_post_first_ah_get_equiv :
  ROMInternalTranscriptBudgetedTwoCallG0AsNMA
    (A, HAETAE_RO.FRO).AH.get ~
  ROMInternalTranscriptBudgetedTwoCallG1AsNMA
    (A, HAETAE_RO.FRO).AH.get :
  ={glob HAETAE_RO.FRO, arg} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{2} /\
  1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{2} /\
  ROSigningAttemptPaperSimSampler.pk_current{1} =
    ROSigningAttemptPaperSimSampler.pk_current{2} /\
  ROSigningAttemptPaperSimSampler.sk_current{1} =
    ROSigningAttemptPaperSimSampler.sk_current{2}
  ==>
  ={glob HAETAE_RO.FRO, res} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{2} /\
  1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{2} /\
  ROSigningAttemptPaperSimSampler.pk_current{1} =
    ROSigningAttemptPaperSimSampler.pk_current{2} /\
  ROSigningAttemptPaperSimSampler.sk_current{1} =
    ROSigningAttemptPaperSimSampler.sk_current{2}.
proof.
proc.
case (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} <
        hash_query_budget_count).
+ rcondt{1} 1; first by auto; smt.
  rcondt{2} 1; first by auto; smt.
  case (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} = 0).
  + rcondt{1} 1; first by auto; smt.
    rcondt{2} 1; first by auto; smt.
    wp.
    call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
    + by sim.
    by auto => />.
  rcondf{1} 1; first by auto; smt.
  rcondf{2} 1; first by auto; smt.
  wp.
  call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
  + by sim.
  by auto => />.
rcondf{1} 1; first by auto; smt.
rcondf{2} 1; first by auto; smt.
by auto => />.
qed.

equiv concrete_two_call_g0_g1_post_first_o_sign_equiv :
  ROMInternalTranscriptBudgetedTwoCallG0AsNMA
    (A, HAETAE_RO.FRO).O.sign ~
  ROMInternalTranscriptBudgetedTwoCallG1AsNMA
    (A, HAETAE_RO.FRO).O.sign :
  ={glob HAETAE_RO.FRO, arg} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{2} /\
  1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{2} /\
  ROSigningAttemptPaperSimSampler.pk_current{1} =
    ROSigningAttemptPaperSimSampler.pk_current{2} /\
  ROSigningAttemptPaperSimSampler.sk_current{1} =
    ROSigningAttemptPaperSimSampler.sk_current{2}
  ==>
  ={glob HAETAE_RO.FRO, res} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{2} /\
  1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{2} /\
  ROSigningAttemptPaperSimSampler.pk_current{1} =
    ROSigningAttemptPaperSimSampler.pk_current{2} /\
  ROSigningAttemptPaperSimSampler.sk_current{1} =
    ROSigningAttemptPaperSimSampler.sk_current{2}.
proof.
proc.
case (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} <
        signature_query_budget_count).
+ rcondt{1} 1; first by auto; smt.
  rcondt{2} 1; first by auto; smt.
  rcondf{1} 2; first by auto; smt.
  rcondf{2} 2; first by auto; smt.
  rcondf{1} 9; first by auto; smt.
  rcondf{2} 9; first by auto; smt.
  wp.
  call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
  + by sim.
  wp.
  call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
  + by sim.
  wp.
  call (: ={glob HAETAE_RO.FRO, arg} /\
          ROSigningAttemptPaperSimSampler.pk_current{1} =
            ROSigningAttemptPaperSimSampler.pk_current{2} /\
          ROSigningAttemptPaperSimSampler.sk_current{1} =
            ROSigningAttemptPaperSimSampler.sk_current{2}
          ==>
          ={glob HAETAE_RO.FRO, res} /\
          ROSigningAttemptPaperSimSampler.pk_current{1} =
            ROSigningAttemptPaperSimSampler.pk_current{2} /\
          ROSigningAttemptPaperSimSampler.sk_current{1} =
            ROSigningAttemptPaperSimSampler.sk_current{2}).
  + by proc; sim.
  wp.
  rnd.
  by auto => />.
rcondf{1} 1; first by auto; smt.
rcondf{2} 1; first by auto; smt.
by auto => />.
qed.

equiv concrete_two_call_g0_g1_post_first_adversary_forge_equiv :
  A(ROMInternalTranscriptBudgetedTwoCallG0AsNMA
      (A, HAETAE_RO.FRO).AH,
    ROMInternalTranscriptBudgetedTwoCallG0AsNMA
      (A, HAETAE_RO.FRO).O).forge ~
  A(ROMInternalTranscriptBudgetedTwoCallG1AsNMA
      (A, HAETAE_RO.FRO).AH,
    ROMInternalTranscriptBudgetedTwoCallG1AsNMA
      (A, HAETAE_RO.FRO).O).forge :
  ={glob HAETAE_RO.FRO, glob A, arg} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{2} /\
  1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{2} /\
  ROSigningAttemptPaperSimSampler.pk_current{1} =
    ROSigningAttemptPaperSimSampler.pk_current{2} /\
  ROSigningAttemptPaperSimSampler.sk_current{1} =
    ROSigningAttemptPaperSimSampler.sk_current{2}
  ==>
  ={glob HAETAE_RO.FRO, glob A, res} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{2} /\
  1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{2} /\
  ROSigningAttemptPaperSimSampler.pk_current{1} =
    ROSigningAttemptPaperSimSampler.pk_current{2} /\
  ROSigningAttemptPaperSimSampler.sk_current{1} =
    ROSigningAttemptPaperSimSampler.sk_current{2}.
proof.
proc
  (={glob HAETAE_RO.FRO} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{2} /\
   1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{2} /\
   ROSigningAttemptPaperSimSampler.pk_current{1} =
     ROSigningAttemptPaperSimSampler.pk_current{2} /\
   ROSigningAttemptPaperSimSampler.sk_current{1} =
     ROSigningAttemptPaperSimSampler.sk_current{2}) => //.
+ move=> />.
+ proc*.
  call concrete_two_call_g0_g1_post_first_ah_get_equiv.
  by auto => />.
+ proc*.
  call concrete_two_call_g0_g1_post_first_o_sign_equiv.
  by auto => />.
qed.

lemma concrete_two_call_g0_g1_post_first_clean_adversary_lifts
    pk (R : message * context * signature -> glob HAETAE_RO.FRO -> bool) &m :
  1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{m} =>
  Pr[A(ROMInternalTranscriptBudgetedTwoCallG0AsNMA
         (A, HAETAE_RO.FRO).AH,
       ROMInternalTranscriptBudgetedTwoCallG0AsNMA
         (A, HAETAE_RO.FRO).O).forge(pk) @ &m :
       R res (glob HAETAE_RO.FRO) /\
       ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery] <=
  Pr[A(ROMInternalTranscriptBudgetedTwoCallG1AsNMA
         (A, HAETAE_RO.FRO).AH,
       ROMInternalTranscriptBudgetedTwoCallG1AsNMA
         (A, HAETAE_RO.FRO).O).forge(pk) @ &m :
       R res (glob HAETAE_RO.FRO)].
proof.
move=> post_first.
byequiv
  (: ={glob HAETAE_RO.FRO, glob A, arg} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{2} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{2} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{2} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{2} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{2} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{2} /\
     1 <= ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{2} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{2} /\
     ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
       ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{2} /\
     ROSigningAttemptPaperSimSampler.pk_current{1} =
       ROSigningAttemptPaperSimSampler.pk_current{2} /\
     ROSigningAttemptPaperSimSampler.sk_current{1} =
       ROSigningAttemptPaperSimSampler.sk_current{2}
     ==>
     (R res{1} (glob HAETAE_RO.FRO){1} /\
      ! ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1}) =>
     R res{2} (glob HAETAE_RO.FRO){2}) => //.
+ by proc*; call concrete_two_call_g0_g1_post_first_adversary_forge_equiv.
qed.

equiv concrete_two_call_g2_exact_budgeted_ah_get_equiv :
  ROMInternalTranscriptBudgetedTwoCallG2AsNMA
    (A, HAETAE_RO.FRO).AH.get ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).AH.get :
  ={glob HAETAE_RO.FRO, arg} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  ROExactHyperballPaperSimSampler.pk_current{1} =
    ROExactHyperballPaperSimSampler.pk_current{2} /\
  ROExactHyperballPaperSimSampler.sk_current{1} =
    ROExactHyperballPaperSimSampler.sk_current{2}
  ==>
  ={glob HAETAE_RO.FRO, res} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  ROExactHyperballPaperSimSampler.pk_current{1} =
    ROExactHyperballPaperSimSampler.pk_current{2} /\
  ROExactHyperballPaperSimSampler.sk_current{1} =
    ROExactHyperballPaperSimSampler.sk_current{2}.
proof.
proc.
case (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} <
        hash_query_budget_count).
+ rcondt{1} 1; first by auto; smt.
  rcondt{2} 1; first by auto; smt.
  case (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} = 0).
  + rcondt{1} 1; first by auto; smt.
    rcondt{2} 1; first by auto; smt.
    wp.
    call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
    + by sim.
    by auto => />.
  rcondf{1} 1; first by auto; smt.
  rcondf{2} 1; first by auto; smt.
  wp.
  call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
  + by sim.
  by auto => />.
rcondf{1} 1; first by auto; smt.
rcondf{2} 1; first by auto; smt.
by auto => />.
qed.

equiv concrete_two_call_g2_exact_budgeted_o_sign_equiv :
  ROMInternalTranscriptBudgetedTwoCallG2AsNMA
    (A, HAETAE_RO.FRO).O.sign ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).O.sign :
  ={glob HAETAE_RO.FRO, arg} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  ROExactHyperballPaperSimSampler.pk_current{1} =
    ROExactHyperballPaperSimSampler.pk_current{2} /\
  ROExactHyperballPaperSimSampler.sk_current{1} =
    ROExactHyperballPaperSimSampler.sk_current{2}
  ==>
  ={glob HAETAE_RO.FRO, res} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  ROExactHyperballPaperSimSampler.pk_current{1} =
    ROExactHyperballPaperSimSampler.pk_current{2} /\
  ROExactHyperballPaperSimSampler.sk_current{1} =
    ROExactHyperballPaperSimSampler.sk_current{2}.
proof.
proc.
case (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} <
        signature_query_budget_count).
+ rcondt{1} 1; first by auto; smt.
  rcondt{2} 1; first by auto; smt.
  case (ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} = 0).
  + rcondt{1} 2; first by auto; smt.
    rcondt{2} 1; first by auto; smt.
    rcondt{1} 9; first by auto; smt.
    sim.
  rcondf{1} 2; first by auto; smt.
  rcondf{2} 1; first by auto; smt.
  rcondf{1} 9; first by auto; smt.
  sim.
rcondf{1} 1; first by auto; smt.
rcondf{2} 1; first by auto; smt.
sim.
qed.

equiv concrete_two_call_g2_exact_budgeted_adversary_forge_equiv :
  A(ROMInternalTranscriptBudgetedTwoCallG2AsNMA
      (A, HAETAE_RO.FRO).AH,
    ROMInternalTranscriptBudgetedTwoCallG2AsNMA
      (A, HAETAE_RO.FRO).O).forge ~
  A(ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
       HAETAE_RO.FRO).AH,
    ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
       HAETAE_RO.FRO).O).forge :
  ={glob HAETAE_RO.FRO, glob A, arg} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  ROExactHyperballPaperSimSampler.pk_current{1} =
    ROExactHyperballPaperSimSampler.pk_current{2} /\
  ROExactHyperballPaperSimSampler.sk_current{1} =
    ROExactHyperballPaperSimSampler.sk_current{2}
  ==>
  ={glob HAETAE_RO.FRO, glob A, res} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
  ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
    ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
  ROExactHyperballPaperSimSampler.pk_current{1} =
    ROExactHyperballPaperSimSampler.pk_current{2} /\
  ROExactHyperballPaperSimSampler.sk_current{1} =
    ROExactHyperballPaperSimSampler.sk_current{2}.
proof.
proc
  (={glob HAETAE_RO.FRO} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.pk_current{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.pk_current{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.queries{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.queries{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.transcripts{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.transcripts{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.records{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.records{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_count{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_count{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.signing_count{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.signing_count{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.adversary_hash_queries{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.adversary_hash_queries{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_expand_queries{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_expand_queries{2} /\
   ROMInternalTranscriptBudgetedTwoCallHybridAsNMA.sampler_bad_prequery{1} =
     ROMInternalTranscriptBudgetedPaperSimAsNMA.sampler_bad_prequery{2} /\
   ROExactHyperballPaperSimSampler.pk_current{1} =
     ROExactHyperballPaperSimSampler.pk_current{2} /\
   ROExactHyperballPaperSimSampler.sk_current{1} =
     ROExactHyperballPaperSimSampler.sk_current{2}) => //.
+ move=> />.
+ proc*.
  call concrete_two_call_g2_exact_budgeted_ah_get_equiv.
  by auto => />.
+ proc*.
  call concrete_two_call_g2_exact_budgeted_o_sign_equiv.
  by auto => />.
qed.

equiv concrete_two_call_g2_exact_budgeted_forge_equiv :
  ROMInternalTranscriptBudgetedTwoCallG2AsNMA
    (A, HAETAE_RO.FRO).forge ~
  ROMInternalTranscriptBudgetedPaperSimAsNMA
    (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO),
     HAETAE_RO.FRO).forge :
  ={glob HAETAE_RO.FRO, glob A, arg} ==>
  ={glob HAETAE_RO.FRO, glob A, res}.
proof.
proc.
call concrete_two_call_g2_exact_budgeted_adversary_forge_equiv.
inline ROExactHyperballPaperSimSampler(HAETAE_RO.FRO).init.
by auto => />.
qed.

equiv concrete_two_call_g2_exact_budgeted_nma_equiv :
  SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
    ROMInternalTranscriptBudgetedTwoCallG2AsNMA(A)).main ~
  SIG.UF_NMA(HAETAE_RO.FRO, HAETAE,
    ROMInternalTranscriptBudgetedPaperSimAsNMA
      (A, ROExactHyperballPaperSimSampler(HAETAE_RO.FRO))).main :
  ={glob HAETAE_RO.FRO, glob A} ==> ={res}.
proof.
proc.
inline HAETAE(HAETAE_RO.FRO).verify
       HAETAE(HAETAE_RO.FRO).kg.
wp.
call concrete_two_call_g2_exact_budgeted_forge_equiv.
wp.
call (: ={glob HAETAE_RO.FRO, arg} ==> ={glob HAETAE_RO.FRO, res}).
+ by sim.
wp.
rnd.
wp.
call (: ={glob HAETAE_RO.FRO} ==> ={glob HAETAE_RO.FRO}).
+ by sim.
by auto => />; rewrite /keygen_internal.
qed.

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
