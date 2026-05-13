require import AllCore Distr IntDiv List Real StdOrder RealSeries.
require import HAETAE_Params HAETAE_Algebra HAETAE_Distributions.
require import HAETAE_Events HAETAE_Reductions.
require import HAETAE_Transcript.

theory HAETAE_Rejection.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Distributions.
import HAETAE_Events.
import HAETAE_Reductions.
import HAETAE_Transcript.
import RealOrder.

type signing_transcript_record = message * context * signature * transcript.
type signing_attempt_sample = polyvecl * polyveck * polyveck.
type signing_attempt_state =
  random_coins * signing_attempt_sample * polyveck * poly * challenge *
  polyvecl * polyveck * hint_t * signature.

op signing_attempt_state_coins
   (st : signing_attempt_state) : random_coins =
  st.`1.
op signing_attempt_state_sample
   (st : signing_attempt_state) : signing_attempt_sample =
  st.`2.
op signing_attempt_sample_y1 (s : signing_attempt_sample) : polyvecl =
  s.`1.
op signing_attempt_sample_y2 (s : signing_attempt_sample) : polyveck =
  s.`2.
op signing_attempt_sample_commitment_raw
   (s : signing_attempt_sample) : polyveck =
  s.`3.
op signing_attempt_state_sampled_y1
   (st : signing_attempt_state) : polyvecl =
  signing_attempt_sample_y1 (signing_attempt_state_sample st).
op signing_attempt_state_sampled_y2
   (st : signing_attempt_state) : polyveck =
  signing_attempt_sample_y2 (signing_attempt_state_sample st).
op signing_attempt_state_sampled_y
   (st : signing_attempt_state) : polyveck =
  signing_attempt_sample_commitment_raw (signing_attempt_state_sample st).
op signing_attempt_state_highbits
   (st : signing_attempt_state) : polyveck =
  st.`3.
op signing_attempt_state_lowbits
   (st : signing_attempt_state) : poly =
  st.`4.
op signing_attempt_state_challenge
   (st : signing_attempt_state) : challenge =
  st.`5.
op signing_attempt_state_response
   (st : signing_attempt_state) : polyvecl =
  st.`6.
op signing_attempt_state_response_aux
   (st : signing_attempt_state) : polyveck =
  st.`7.
op signing_attempt_state_hint
   (st : signing_attempt_state) : hint_t =
  st.`8.
op signing_attempt_state_signature
   (st : signing_attempt_state) : signature =
  st.`9.
op signature_rejection_branch_byte (sig : signature) : int =
  sig.`6.
op signing_attempt_state_reject2_branch_byte
   (st : signing_attempt_state) : int =
  signature_rejection_branch_byte (signing_attempt_state_signature st).
op signing_attempt_state_reject2_branch_bit
   (st : signing_attempt_state) : bool =
  (signing_attempt_state_reject2_branch_byte st %/ 2) %% 2 = 1.
op polyvecl_double (md : mode) (xs : polyvecl) : polyvecl =
  mkseq
    (fun i => poly_double (nth poly_zero xs i))
    (mode_l md).
op signing_attempt_state_reject2_sampled_y1
   (st : signing_attempt_state) : polyvecl =
  signing_attempt_state_sampled_y1 st.
op signing_attempt_state_reject2_sampled_y2
   (st : signing_attempt_state) : polyveck =
  signing_attempt_state_sampled_y2 st.
op signing_attempt_state_reject2_balance_response
   (md : mode) (st : signing_attempt_state) : polyvecl =
  polyvecl_sub md
    (polyvecl_double md (signing_attempt_state_response st))
    (signing_attempt_state_reject2_sampled_y1 st).
op signing_attempt_state_reject2_balance_aux
   (md : mode) (st : signing_attempt_state) : polyveck =
  polyveck_sub md
    (polyveck_double md (signing_attempt_state_response_aux st))
    (signing_attempt_state_reject2_sampled_y2 st).
op signing_attempt_state_lowbits_carrier
   (st : signing_attempt_state) : poly =
  nth poly_zero (signing_attempt_state_sampled_y st) 0.
op signing_attempt_state_token
   (st : signing_attempt_state) : sig_token =
  ( signing_attempt_state_response st,
    signing_attempt_state_response_aux st,
    signing_attempt_state_hint st).

op signing_attempt_state_programmed_lowbits
   (st : signing_attempt_state) : poly =
  mkseq
    (fun i =>
      if i = 0 then signing_entropy_token_of_coins
        (signing_attempt_state_coins st)
      else poly_coeff (signing_attempt_state_lowbits_carrier st) i)
    n.

op signing_attempt_state_lowbits_consistent
   (st : signing_attempt_state) : bool =
  signing_attempt_state_lowbits st =
    signing_attempt_state_programmed_lowbits st.

op signing_attempt_state_programmed_challenge
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : challenge =
  challenge_hash md
    (signing_attempt_state_response_aux st)
    (signing_attempt_state_lowbits st)
    (message_hash pk ctx m).

op signing_attempt_state_challenge_consistent
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : bool =
  signing_attempt_state_challenge st =
    signing_attempt_state_programmed_challenge md pk m ctx st.

op signing_attempt_state_reconstructed_highbits
   (md : mode) (pk : pkey) (st : signing_attempt_state) : polyveck =
  reconstructed_highbits md
    (signing_attempt_state_response_aux st)
    (public_key_challenge_term md pk (signing_attempt_state_challenge st)).

op signing_attempt_state_public_equation_consistent
   (md : mode) (pk : pkey) (st : signing_attempt_state) : bool =
  signing_attempt_state_highbits st =
    signing_attempt_state_reconstructed_highbits md pk st.

op signing_attempt_state_signature_of_fields
   (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : signature =
  ( signing_attempt_state_highbits st,
    signing_attempt_state_lowbits st,
    message_hash pk ctx m,
    signing_attempt_state_challenge st,
    signing_attempt_state_token st,
    0,
    0).

op signing_attempt_state_fields_match_signature
   (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : bool =
  signing_attempt_state_signature st =
    signing_attempt_state_signature_of_fields pk m ctx st.

op signing_attempt_state_field_accepts
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : bool =
  signing_attempt_state_lowbits_consistent st /\
  signing_attempt_state_challenge_consistent md pk m ctx st /\
  signing_attempt_state_public_equation_consistent md pk st /\
  signing_attempt_state_fields_match_signature pk m ctx st.

op signing_attempt_state_of_coins
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : signing_attempt_state =
  ( coins,
    ( signing_sample_y1 md sk m ctx coins,
      signing_sample_y2 md sk m ctx coins,
      commitment_raw md sk m ctx coins),
    commitment_highbits md sk m ctx coins,
    commitment_lowbits md sk m ctx coins,
    commitment_challenge md sk m ctx coins,
    response_vector md sk m ctx coins,
    response_aux_vector md sk m ctx coins,
    hint_vector md sk m ctx coins,
    sign_internal md sk m ctx coins).

op signing_attempt_sample_of_pair
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) (sample : signing_sample_pair) :
   signing_attempt_sample =
  (signing_sample_pair_y1 sample,
   signing_sample_pair_y2 sample,
   commitment_raw md sk m ctx coins).

op signing_attempt_state_of_sample_pair
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) (sample : signing_sample_pair) :
   signing_attempt_state =
  ( coins,
    signing_attempt_sample_of_pair md sk m ctx coins sample,
    commitment_highbits md sk m ctx coins,
    commitment_lowbits md sk m ctx coins,
    commitment_challenge md sk m ctx coins,
    response_vector md sk m ctx coins,
    response_aux_vector md sk m ctx coins,
    hint_vector md sk m ctx coins,
    sign_internal md sk m ctx coins).

op signing_attempt_state_valid_signature_accepts
   (md : mode) (st : signing_attempt_state) : bool =
  valid_signature md (signing_attempt_state_signature st).

op signing_attempt_state_response_norm_accepts
   (md : mode) (st : signing_attempt_state) : bool =
  response_norm_ok md (signing_attempt_state_signature st).

op signing_attempt_state_hint_norm_accepts
   (md : mode) (st : signing_attempt_state) : bool =
  verify_norm_ok md (signing_attempt_state_signature st).

op signing_attempt_state_accepts
   (md : mode) (st : signing_attempt_state) : bool =
  signing_attempt_state_valid_signature_accepts md st /\
  signing_attempt_state_response_norm_accepts md st /\
  signing_attempt_state_hint_norm_accepts md st.

op signing_attempt_reject1_bound (md : mode) : int =
  mode_b1sq md * mode_ln md * mode_ln md.

op signing_attempt_reject2_bound (md : mode) : int =
  mode_b0sq md * mode_ln md * mode_ln md.

op signing_attempt_reject2_balance_norm_sq
   (md : mode) (z : polyvecl) (zaux : polyveck)
   (y1 : polyvecl) (y2 : polyveck) : int =
  polyvecl_norm_sq md (polyvecl_sub md (polyvecl_double md z) y1) +
  polyveck_norm_sq md (polyveck_sub md (polyveck_double md zaux) y2).

op signing_attempt_reject2_concrete_aborts
   (md : mode) (branch : bool) (z : polyvecl) (zaux : polyveck)
   (y1 : polyvecl) (y2 : polyveck) : bool =
  branch /\
  signing_attempt_reject2_balance_norm_sq md z zaux y1 y2 <
  signing_attempt_reject2_bound md.

op signing_attempt_state_reject1_norm_sq
   (md : mode) (st : signing_attempt_state) : int =
  response_norm_sq md (signing_attempt_state_signature st).

op signing_attempt_state_reject1_accepts
   (md : mode) (st : signing_attempt_state) : bool =
  0 <= signing_attempt_state_reject1_norm_sq md st /\
  signing_attempt_state_reject1_norm_sq md st <=
    signing_attempt_reject1_bound md.

op signing_attempt_state_balance_norm_sq
   (md : mode) (st : signing_attempt_state) : int =
  signing_attempt_reject2_balance_norm_sq md
    (signing_attempt_state_response st)
    (signing_attempt_state_response_aux st)
    (signing_attempt_state_reject2_sampled_y1 st)
    (signing_attempt_state_reject2_sampled_y2 st).

op signing_attempt_state_bimodal_reject2_branch
   (st : signing_attempt_state) : bool =
  signing_attempt_state_reject2_branch_bit st.

op signing_attempt_state_reject2_under_bound
   (md : mode) (st : signing_attempt_state) : bool =
  signing_attempt_state_balance_norm_sq md st <
  signing_attempt_reject2_bound md.

op signing_attempt_state_reject2_aborts
   (md : mode) (st : signing_attempt_state) : bool =
  signing_attempt_reject2_concrete_aborts md
    (signing_attempt_state_bimodal_reject2_branch st)
    (signing_attempt_state_response st)
    (signing_attempt_state_response_aux st)
    (signing_attempt_state_reject2_sampled_y1 st)
    (signing_attempt_state_reject2_sampled_y2 st).

op signing_attempt_state_reject2_accepts
   (md : mode) (st : signing_attempt_state) : bool =
  ! signing_attempt_state_reject2_aborts md st.

op signing_attempt_state_pack_accepts
   (md : mode) (st : signing_attempt_state) : bool =
  signing_attempt_state_valid_signature_accepts md st /\
  0 < mode_crypto_bytes md.

op signing_attempt_state_reference_rejection_accepts
   (md : mode) (st : signing_attempt_state) : bool =
  signing_attempt_state_reject1_accepts md st /\
  signing_attempt_state_reject2_accepts md st /\
  signing_attempt_state_pack_accepts md st /\
  signing_attempt_state_hint_norm_accepts md st.

op signing_attempt_state_reference_rejection_aborts
   (md : mode) (st : signing_attempt_state) : bool =
  ! signing_attempt_state_reference_rejection_accepts md st.

op signing_attempt_state_reject1_aborts
   (md : mode) (st : signing_attempt_state) : bool =
  ! signing_attempt_state_reject1_accepts md st.

op signing_attempt_state_pack_aborts
   (md : mode) (st : signing_attempt_state) : bool =
  ! signing_attempt_state_pack_accepts md st.

op signing_attempt_state_verification_accepts
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : bool =
  signing_attempt_state_field_accepts md pk m ctx st /\
  signing_attempt_state_accepts md st.

op signing_attempt_state_rejection_accepts
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : bool =
  signing_attempt_state_verification_accepts md pk m ctx st /\
  signing_attempt_state_reference_rejection_accepts md st.

op signing_attempt_state_rejection_aborts
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (st : signing_attempt_state) : bool =
  ! signing_attempt_state_rejection_accepts md pk m ctx st.

op signing_attempt_state_response_norm_aborts
   (md : mode) (st : signing_attempt_state) : bool =
  ! signing_attempt_state_response_norm_accepts md st.

op signing_attempt_state_hint_norm_aborts
   (md : mode) (st : signing_attempt_state) : bool =
  ! signing_attempt_state_hint_norm_accepts md st.

op signing_attempt_state_rejection_sampling_aborts
   (md : mode) (st : signing_attempt_state) : bool =
  ! signing_attempt_state_valid_signature_accepts md st.

op signing_attempt_state_aborts
   (md : mode) (st : signing_attempt_state) : bool =
  signing_attempt_state_rejection_sampling_aborts md st \/
  signing_attempt_state_response_norm_aborts md st \/
  signing_attempt_state_hint_norm_aborts md st.

op signing_accepts
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : bool =
  signing_attempt_state_accepts md
    (signing_attempt_state_of_coins md sk m ctx coins).

op dsigning_attempt_state
   (md : mode) (sk : skey) (m : message) (ctx : context) :
   signing_attempt_state distr =
  dmap drandom_coins (signing_attempt_state_of_coins md sk m ctx).

op signing_sample_pair_sampler_ok
   (md : mode) (dsample : random_coins -> signing_sample_pair distr) :
   bool =
  forall coins,
    signing_randomness_domain coins =>
    signing_sample_pair_distribution_ok md (dsample coins).

op dsigning_attempt_state_from_sample_pair_sampler
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (dsample : random_coins -> signing_sample_pair distr) :
   signing_attempt_state distr =
  dlet drandom_coins
    (fun coins =>
      dmap (dsample coins)
        (signing_attempt_state_of_sample_pair md sk m ctx coins)).

type signing_attempt_coin_sample_pair = random_coins * signing_sample_pair.

op signing_attempt_state_of_coin_sample_pair
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (cs : signing_attempt_coin_sample_pair) : signing_attempt_state =
  signing_attempt_state_of_sample_pair md sk m ctx cs.`1 cs.`2.

op dstructural_signing_attempt_coin_sample_pair
   (md : mode) (sk : skey) (m : message) (ctx : context) :
   signing_attempt_coin_sample_pair distr =
  dlet drandom_coins
    (fun coins =>
      dmap (dstructural_signing_sample_pair md sk m ctx coins)
        (fun sample => (coins, sample))).

op dexact_hyperball_signing_attempt_coin_sample_pair
   (md : mode) (sk : skey) (m : message) (ctx : context) :
   signing_attempt_coin_sample_pair distr =
  dlet drandom_coins
    (fun coins =>
      dmap (dexact_hyperball_signing_sample_pair md)
        (fun sample => (coins, sample))).

op dstructural_signing_attempt_state
   (md : mode) (sk : skey) (m : message) (ctx : context) :
   signing_attempt_state distr =
  dmap drandom_coins
    (fun coins =>
      signing_attempt_state_of_sample_pair md sk m ctx coins
        (signing_sample_pair_of_coins md sk m ctx coins)).

op dstructural_signing_attempt_state_from_sampler
   (md : mode) (sk : skey) (m : message) (ctx : context) :
   signing_attempt_state distr =
  dsigning_attempt_state_from_sample_pair_sampler md sk m ctx
    (dstructural_signing_sample_pair md sk m ctx).

op dbounded_unit_signing_attempt_state
   (md : mode) (sk : skey) (m : message) (ctx : context) :
   signing_attempt_state distr =
  dsigning_attempt_state_from_sample_pair_sampler md sk m ctx
    (fun _ => dbounded_unit_signing_sample_pair md).

op dchecked_hyperball_signing_attempt_state
   (md : mode) (sk : skey) (m : message) (ctx : context) :
   signing_attempt_state distr =
  dsigning_attempt_state_from_sample_pair_sampler md sk m ctx
    (fun _ => dchecked_hyperball_signing_sample_pair md).

op dexact_hyperball_signing_attempt_state
   (md : mode) (sk : skey) (m : message) (ctx : context) :
   signing_attempt_state distr =
  dsigning_attempt_state_from_sample_pair_sampler md sk m ctx
    (fun _ => dexact_hyperball_signing_sample_pair md).

op signing_attempt_state_sample_pair_wf
   (md : mode) (st : signing_attempt_state) : bool =
  polyvecl_wf md (signing_attempt_state_sampled_y1 st) /\
  polyveck_wf md (signing_attempt_state_sampled_y2 st).

op signing_attempt_state_sample_pair_unit
   (md : mode) (st : signing_attempt_state) : bool =
  polyvecl_unit md (signing_attempt_state_sampled_y1 st) /\
  polyveck_unit md (signing_attempt_state_sampled_y2 st).

op signing_attempt_state_sample_pair_bounded
   (md : mode) (st : signing_attempt_state) : bool =
  polyvecl_bounded_by md (signing_sample_bound md)
    (signing_attempt_state_sampled_y1 st) /\
  polyveck_bounded_by md (signing_sample_bound md)
    (signing_attempt_state_sampled_y2 st).

op signing_attempt_relation
   (md : mode) (pk : pkey) (sk : skey) (m : message)
   (ctx : context) (coins : random_coins) (sig : signature) : bool =
  valid_keypair md pk sk /\
  signing_accepts md sk m ctx coins /\
  sig = sign_internal md sk m ctx coins.

op signing_simulation_relation
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (sig : signature) : bool =
  verify_internal md pk m ctx sig /\
  exists (sk : skey) (coins : random_coins),
    signing_attempt_relation md pk sk m ctx coins sig.

op signing_transcript_relation
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (sig : signature) (tr : transcript) : bool =
  signing_simulation_relation md pk m ctx sig /\
  tr = transcript_of_signature md pk m ctx sig /\
  transcript_valid md tr.

op signing_record_message (r : signing_transcript_record) : message = r.`1.
op signing_record_context (r : signing_transcript_record) : context = r.`2.
op signing_record_signature (r : signing_transcript_record) : signature = r.`3.
op signing_record_transcript (r : signing_transcript_record) : transcript =
  r.`4.

op signing_record_query (r : signing_transcript_record) : message * context =
  (signing_record_message r, signing_record_context r).

op signing_record_relation
   (md : mode) (pk : pkey) (r : signing_transcript_record) : bool =
  signing_transcript_relation md pk
    (signing_record_message r)
    (signing_record_context r)
    (signing_record_signature r)
    (signing_record_transcript r).

op signing_record_queries (rs : signing_transcript_record list) :
  (message * context) list =
  map signing_record_query rs.

op signing_record_transcripts (rs : signing_transcript_record list) :
  transcript list =
  map signing_record_transcript rs.

op signing_record_log_sound
   (md : mode) (pk : pkey) (rs : signing_transcript_record list) : bool =
  all (signing_record_relation md pk) rs.

op transcript_log_valid (md : mode) (trs : transcript list) : bool =
  all (transcript_valid md) trs.

op structural_to_exact_hyperball_sample_pair_point_loss_obligation : bool =
  forall (md : mode) (sk : skey) (m : message) (ctx : context)
         (coins : random_coins),
    1%r <=
    mu (dexact_hyperball_signing_sample_pair md)
      (pred1 (signing_sample_pair_of_coins md sk m ctx coins)) +
      rejection_sampling_loss_term.

op structural_to_exact_hyperball_sample_pair_loss_obligation : bool =
  forall (md : mode) (sk : skey) (m : message) (ctx : context)
         (coins : random_coins) (p : signing_sample_pair -> bool),
    mu (dstructural_signing_sample_pair md sk m ctx coins) p <=
    mu (dexact_hyperball_signing_sample_pair md) p +
      rejection_sampling_loss_term.

op structural_to_exact_hyperball_coin_sample_pair_loss_obligation : bool =
  forall (md : mode) (sk : skey) (m : message) (ctx : context)
         (p : signing_attempt_coin_sample_pair -> bool),
    mu (dstructural_signing_attempt_coin_sample_pair md sk m ctx) p <=
    mu (dexact_hyperball_signing_attempt_coin_sample_pair md sk m ctx) p +
      rejection_sampling_loss_term.

op structural_to_exact_hyperball_attempt_loss_obligation : bool =
  forall (md : mode) (sk : skey) (m : message) (ctx : context)
         (p : signing_attempt_state -> bool),
    mu (dsigning_attempt_state md sk m ctx) p <=
    mu (dexact_hyperball_signing_attempt_state md sk m ctx) p +
      rejection_sampling_loss_term.

op rejection_sampling_bound_obligation : bool =
  0%r <= rejection_sampling_loss_term /\
  0%r <= fs_with_aborts_reprogramming_term /\
  0%r <= fs_with_aborts_min_entropy_term.

lemma signing_attempt_verifies md pk sk m ctx coins sig :
  signing_attempt_relation md pk sk m ctx coins sig =>
  verify_internal md pk m ctx sig.
proof.
rewrite /signing_attempt_relation /valid_keypair.
move=> [#] pkE _ ->.
rewrite pkE.
by apply verify_internal_sign_internal.
qed.

lemma signing_simulation_verifies md pk m ctx sig :
  signing_simulation_relation md pk m ctx sig =>
  verify_internal md pk m ctx sig.
proof.
by rewrite /signing_simulation_relation.
qed.

lemma signing_attempt_simulates md pk sk m ctx coins sig :
  signing_attempt_relation md pk sk m ctx coins sig =>
  signing_simulation_relation md pk m ctx sig.
proof.
move=> h.
rewrite /signing_simulation_relation.
split.
+ by apply (signing_attempt_verifies md pk sk m ctx coins sig).
exists sk coins.
by apply h.
qed.

lemma sign_internal_attempt_relation md sk m ctx coins :
  signing_attempt_relation md
    (public_key_of_secret md sk) sk m ctx coins
    (sign_internal md sk m ctx coins).
proof.
rewrite /signing_attempt_relation /valid_keypair /signing_accepts.
split=> //.
split.
+ by rewrite /signing_attempt_state_accepts
             /signing_attempt_state_valid_signature_accepts
             /signing_attempt_state_response_norm_accepts
             /signing_attempt_state_hint_norm_accepts;
     smt(valid_signature_sign_internal response_norm_ok_current
         verify_norm_ok_current).
+ by trivial.
qed.

lemma signing_attempt_sample_of_pair_currentE md sk m ctx coins :
  signing_attempt_sample_of_pair md sk m ctx coins
    (signing_sample_pair_of_coins md sk m ctx coins) =
  ( signing_sample_y1 md sk m ctx coins,
    signing_sample_y2 md sk m ctx coins,
    commitment_raw md sk m ctx coins).
proof.
by rewrite /signing_attempt_sample_of_pair
           /signing_sample_pair_of_coins
           /signing_sample_pair_y1 /signing_sample_pair_y2.
qed.

lemma signing_attempt_state_of_sample_pair_currentE md sk m ctx coins :
  signing_attempt_state_of_sample_pair md sk m ctx coins
    (signing_sample_pair_of_coins md sk m ctx coins) =
  signing_attempt_state_of_coins md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_of_sample_pair
           /signing_attempt_state_of_coins
           signing_attempt_sample_of_pair_currentE.
qed.

lemma structural_signing_sample_pair_sampler_ok md sk m ctx :
  signing_sample_pair_sampler_ok md
    (dstructural_signing_sample_pair md sk m ctx).
proof.
rewrite /signing_sample_pair_sampler_ok => coins _.
by apply structural_signing_sample_pair_distribution_ok.
qed.

lemma bounded_unit_signing_sample_pair_sampler_ok md :
  signing_sample_pair_sampler_ok md
    (fun _ => dbounded_unit_signing_sample_pair md).
proof.
rewrite /signing_sample_pair_sampler_ok => coins _.
by apply bounded_unit_signing_sample_pair_distribution_ok.
qed.

lemma checked_hyperball_signing_sample_pair_sampler_ok md :
  signing_sample_pair_sampler_ok md
    (fun _ => dchecked_hyperball_signing_sample_pair md).
proof.
rewrite /signing_sample_pair_sampler_ok => coins _.
by apply checked_hyperball_signing_sample_pair_distribution_ok.
qed.

lemma exact_hyperball_signing_sample_pair_sampler_ok md :
  signing_sample_pair_sampler_ok md
    (fun _ => dexact_hyperball_signing_sample_pair md).
proof.
rewrite /signing_sample_pair_sampler_ok => coins _.
by apply exact_hyperball_signing_sample_pair_distribution_ok.
qed.

lemma dsigning_attempt_state_from_sample_pair_sampler_lossless
   md sk m ctx dsample :
  signing_sample_pair_sampler_ok md dsample =>
  is_lossless
    (dsigning_attempt_state_from_sample_pair_sampler
      md sk m ctx dsample).
proof.
move=> hsample.
rewrite /dsigning_attempt_state_from_sample_pair_sampler.
apply dlet_ll.
+ by apply signing_coin_distribution_lossless.
move=> coins coins_supp.
apply dmap_ll.
move: (hsample coins _).
+ by apply signing_coin_distribution_domain.
by rewrite /signing_sample_pair_distribution_ok => -[hll _].
qed.

lemma dsigning_attempt_state_from_sample_pair_sampler_sample_ok
   md sk m ctx dsample st :
  signing_sample_pair_sampler_ok md dsample =>
  st \in
    dsigning_attempt_state_from_sample_pair_sampler
      md sk m ctx dsample =>
  signing_attempt_state_sample_pair_wf md st /\
  signing_attempt_state_sample_pair_bounded md st.
proof.
move=> hsample.
rewrite /dsigning_attempt_state_from_sample_pair_sampler supp_dlet.
move=> [coins [coins_supp]].
rewrite supp_dmap.
move=> [sample [sample_supp ->]].
move: (hsample coins _).
+ by apply signing_coin_distribution_domain.
rewrite /signing_sample_pair_distribution_ok => -[_ hsupp].
move: (hsupp sample sample_supp).
rewrite /signing_sample_pair_sample_ok => -[sample_wf sample_bounded].
rewrite /signing_attempt_state_sample_pair_wf
        /signing_attempt_state_sample_pair_bounded
        /signing_attempt_state_sampled_y1
        /signing_attempt_state_sampled_y2
        /signing_attempt_sample_y1
        /signing_attempt_sample_y2
        /signing_attempt_state_sample
        /signing_attempt_state_of_sample_pair
        /signing_attempt_sample_of_pair
        /signing_sample_pair_wf
        /signing_sample_pair_bounded
        /signing_sample_pair_y1
        /signing_sample_pair_y2 /=.
by split.
qed.

lemma dstructural_signing_attempt_state_lossless md sk m ctx :
  is_lossless (dstructural_signing_attempt_state md sk m ctx).
proof.
rewrite /dstructural_signing_attempt_state.
by apply dmap_ll; apply signing_coin_distribution_lossless.
qed.

lemma dstructural_signing_attempt_state_from_sampler_lossless
   md sk m ctx :
  is_lossless
    (dstructural_signing_attempt_state_from_sampler md sk m ctx).
proof.
rewrite /dstructural_signing_attempt_state_from_sampler.
apply dsigning_attempt_state_from_sample_pair_sampler_lossless.
by apply structural_signing_sample_pair_sampler_ok.
qed.

lemma dbounded_unit_signing_attempt_state_lossless md sk m ctx :
  is_lossless (dbounded_unit_signing_attempt_state md sk m ctx).
proof.
rewrite /dbounded_unit_signing_attempt_state.
apply dsigning_attempt_state_from_sample_pair_sampler_lossless.
by apply bounded_unit_signing_sample_pair_sampler_ok.
qed.

lemma dbounded_unit_signing_attempt_state_sample_ok md sk m ctx st :
  st \in dbounded_unit_signing_attempt_state md sk m ctx =>
  signing_attempt_state_sample_pair_wf md st /\
  signing_attempt_state_sample_pair_bounded md st.
proof.
rewrite /dbounded_unit_signing_attempt_state.
apply dsigning_attempt_state_from_sample_pair_sampler_sample_ok.
by apply bounded_unit_signing_sample_pair_sampler_ok.
qed.

lemma dchecked_hyperball_signing_attempt_state_lossless md sk m ctx :
  is_lossless (dchecked_hyperball_signing_attempt_state md sk m ctx).
proof.
rewrite /dchecked_hyperball_signing_attempt_state.
apply dsigning_attempt_state_from_sample_pair_sampler_lossless.
by apply checked_hyperball_signing_sample_pair_sampler_ok.
qed.

lemma dchecked_hyperball_signing_attempt_state_sample_ok md sk m ctx st :
  st \in dchecked_hyperball_signing_attempt_state md sk m ctx =>
  signing_attempt_state_sample_pair_wf md st /\
  signing_attempt_state_sample_pair_bounded md st.
proof.
rewrite /dchecked_hyperball_signing_attempt_state.
apply dsigning_attempt_state_from_sample_pair_sampler_sample_ok.
by apply checked_hyperball_signing_sample_pair_sampler_ok.
qed.

lemma dexact_hyperball_signing_attempt_state_lossless md sk m ctx :
  is_lossless (dexact_hyperball_signing_attempt_state md sk m ctx).
proof.
rewrite /dexact_hyperball_signing_attempt_state.
apply dsigning_attempt_state_from_sample_pair_sampler_lossless.
by apply exact_hyperball_signing_sample_pair_sampler_ok.
qed.

lemma dexact_hyperball_signing_attempt_state_sample_ok md sk m ctx st :
  st \in dexact_hyperball_signing_attempt_state md sk m ctx =>
  signing_attempt_state_sample_pair_wf md st /\
  signing_attempt_state_sample_pair_bounded md st.
proof.
rewrite /dexact_hyperball_signing_attempt_state.
apply dsigning_attempt_state_from_sample_pair_sampler_sample_ok.
by apply exact_hyperball_signing_sample_pair_sampler_ok.
qed.

lemma dexact_hyperball_signing_attempt_state_supportP md sk m ctx st :
  st \in dexact_hyperball_signing_attempt_state md sk m ctx <=>
  exists (coins : random_coins) (sample : signing_sample_pair),
    coins \in drandom_coins /\
    hyperball_sample_ok md sample /\
    st = signing_attempt_state_of_sample_pair md sk m ctx coins sample.
proof.
rewrite /dexact_hyperball_signing_attempt_state
        /dsigning_attempt_state_from_sample_pair_sampler supp_dlet.
split.
+ move=> [coins [coins_supp]].
  rewrite supp_dmap.
  move=> [sample [sample_supp ->]].
  exists coins sample.
  split=> //.
  split.
  + by move: sample_supp; rewrite exact_hyperball_signing_sample_pair_supportP.
  by [].
move=> [coins sample [coins_supp [sample_ok stE]]].
rewrite stE.
exists coins.
split=> //.
rewrite supp_dmap.
exists sample.
split.
+ by rewrite exact_hyperball_signing_sample_pair_supportP.
by [].
qed.

lemma dexact_hyperball_signing_attempt_state_reference_rejection_abort_bound1
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reference_rejection_aborts md) <= 1%r.
proof.
by smt(mu_bounded).
qed.

lemma dexact_hyperball_signing_attempt_state_mu_pullback
  md sk m ctx (P : signing_attempt_state -> bool) :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx) P =
  mu (dlet drandom_coins
        (fun coins =>
           dmap (dexact_hyperball_signing_sample_pair md)
             (fun sample =>
                signing_attempt_state_of_sample_pair
                  md sk m ctx coins sample)))
    P.
proof.
by rewrite /dexact_hyperball_signing_attempt_state
           /dsigning_attempt_state_from_sample_pair_sampler.
qed.

lemma signing_attempt_state_reference_rejection_aborts_componentE md st :
  signing_attempt_state_reference_rejection_aborts md st =
  (signing_attempt_state_reject1_aborts md st \/
   signing_attempt_state_reject2_aborts md st \/
   signing_attempt_state_pack_aborts md st \/
   signing_attempt_state_hint_norm_aborts md st).
proof.
rewrite /signing_attempt_state_reference_rejection_aborts
        /signing_attempt_state_reference_rejection_accepts
        /signing_attempt_state_reject1_aborts
        /signing_attempt_state_reject2_accepts
        /signing_attempt_state_pack_aborts
        /signing_attempt_state_hint_norm_aborts.
by smt().
qed.

lemma dexact_hyperball_signing_attempt_state_reference_rejection_abort_split
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reference_rejection_aborts md) =
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (predU
      (signing_attempt_state_reject1_aborts md)
      (predU
        (signing_attempt_state_reject2_aborts md)
        (predU
          (signing_attempt_state_pack_aborts md)
          (signing_attempt_state_hint_norm_aborts md)))).
proof.
apply mu_eq => st.
by rewrite signing_attempt_state_reference_rejection_aborts_componentE /predU.
qed.

lemma dexact_hyperball_signing_attempt_state_reference_rejection_abort_union_bound
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reference_rejection_aborts md) <=
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reject1_aborts md) +
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reject2_aborts md) +
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_pack_aborts md) +
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_hint_norm_aborts md).
proof.
rewrite dexact_hyperball_signing_attempt_state_reference_rejection_abort_split.
rewrite !mu_or.
by smt(mu_bounded).
qed.

lemma signing_attempt_state_of_sample_pair_signatureE
  md sk m ctx coins sample :
  signing_attempt_state_signature
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  sign_internal md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_signature
           /signing_attempt_state_of_sample_pair.
qed.

lemma signing_attempt_state_of_sample_pair_pack_accepts
  md sk m ctx coins sample :
  signing_attempt_state_pack_accepts md
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
rewrite /signing_attempt_state_pack_accepts.
split.
+ by rewrite /signing_attempt_state_valid_signature_accepts
             signing_attempt_state_of_sample_pair_signatureE
             valid_signature_sign_internal.
by apply mode_crypto_bytes_gt0.
qed.

lemma signing_attempt_state_of_sample_pair_pack_no_abort
  md sk m ctx coins sample :
  ! signing_attempt_state_pack_aborts md
      (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_pack_aborts
           signing_attempt_state_of_sample_pair_pack_accepts.
qed.

lemma dexact_hyperball_signing_attempt_state_pack_abort_zero
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_pack_aborts md) =
  0%r.
proof.
have le0 :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_pack_aborts md) <=
  mu (dexact_hyperball_signing_attempt_state md sk m ctx) pred0.
+ apply mu_le => st st_supp abort.
  move: st_supp; rewrite dexact_hyperball_signing_attempt_state_supportP.
  move=> [coins sample [_ [_ stE]]].
  move: abort.
  rewrite stE signing_attempt_state_of_sample_pair_pack_no_abort.
  by [].
rewrite mu0 in le0.
by smt(mu_bounded).
qed.

lemma dstructural_signing_attempt_state_from_samplerE md sk m ctx :
  dstructural_signing_attempt_state_from_sampler md sk m ctx =
  dstructural_signing_attempt_state md sk m ctx.
proof.
rewrite /dstructural_signing_attempt_state_from_sampler
        /dsigning_attempt_state_from_sample_pair_sampler
        /dstructural_signing_attempt_state
        /dstructural_signing_sample_pair.
have -> :
  (fun coins =>
     dmap (dunit (signing_sample_pair_of_coins md sk m ctx coins))
       (signing_attempt_state_of_sample_pair md sk m ctx coins)) =
  (dunit \o
     (fun coins =>
        signing_attempt_state_of_sample_pair md sk m ctx coins
          (signing_sample_pair_of_coins md sk m ctx coins))).
+ apply fun_ext => coins.
  by rewrite /(\o) dmap_dunit.
by rewrite dlet_dunit.
qed.

lemma dstructural_signing_attempt_stateE md sk m ctx :
  dstructural_signing_attempt_state md sk m ctx =
  dsigning_attempt_state md sk m ctx.
proof.
rewrite /dstructural_signing_attempt_state /dsigning_attempt_state.
apply eq_dmap => coins /=.
by rewrite signing_attempt_state_of_sample_pair_currentE.
qed.

lemma dstructural_signing_attempt_state_from_sampler_coin_sample_pairE
   md sk m ctx :
  dmap (dstructural_signing_attempt_coin_sample_pair md sk m ctx)
    (signing_attempt_state_of_coin_sample_pair md sk m ctx) =
  dstructural_signing_attempt_state_from_sampler md sk m ctx.
proof.
rewrite /dstructural_signing_attempt_coin_sample_pair
        /dstructural_signing_attempt_state_from_sampler
        /dsigning_attempt_state_from_sample_pair_sampler.
rewrite dmap_dlet.
apply eq_dlet => // coins.
rewrite dmap_comp.
apply eq_dmap => sample /=.
by rewrite /(\o) /signing_attempt_state_of_coin_sample_pair.
qed.

lemma dexact_hyperball_signing_attempt_state_coin_sample_pairE
   md sk m ctx :
  dmap (dexact_hyperball_signing_attempt_coin_sample_pair md sk m ctx)
    (signing_attempt_state_of_coin_sample_pair md sk m ctx) =
  dexact_hyperball_signing_attempt_state md sk m ctx.
proof.
rewrite /dexact_hyperball_signing_attempt_coin_sample_pair
        /dexact_hyperball_signing_attempt_state
        /dsigning_attempt_state_from_sample_pair_sampler.
rewrite dmap_dlet.
apply eq_dlet => // coins.
rewrite dmap_comp.
apply eq_dmap => sample /=.
by rewrite /(\o) /signing_attempt_state_of_coin_sample_pair.
qed.

lemma mu_dlet_le_add_all ['a 'b 'c]
   (d : 'a distr) (F1 : 'a -> 'b distr) (F2 : 'a -> 'c distr)
   (P1 : 'b -> bool) (P2 : 'c -> bool) (eps : real) :
  0%r <= eps =>
  (forall x, mu (F1 x) P1 <= mu (F2 x) P2 + eps) =>
  mu (dlet d F1) P1 <= mu (dlet d F2) P2 + eps.
proof.
move=> eps_ge h.
rewrite !dletE.
have s1_sbl : summable (fun x => mu1 d x * mu (F1 x) P1).
+ by apply summable_mu1_wght => x; smt(mu_bounded).
have s2_sbl : summable (fun x => mu1 d x * mu (F2 x) P2).
+ by apply summable_mu1_wght => x; smt(mu_bounded).
have seps_sbl : summable (fun x => eps * mu1 d x).
+ by apply summableZ; apply summable_mu1.
have s2eps_sbl :
  summable (fun x => mu1 d x * (mu (F2 x) P2 + eps)).
+ have -> :
    (fun x => mu1 d x * (mu (F2 x) P2 + eps)) =
    (fun x => mu1 d x * mu (F2 x) P2 + eps * mu1 d x).
  + by apply/fun_ext=> x; smt.
  by apply summableD.
have hsum :
  sum (fun x => mu1 d x * mu (F1 x) P1) <=
  sum (fun x => mu1 d x * (mu (F2 x) P2 + eps)).
+ apply RealSeries.ler_sum.
  + move=> x /=.
    by apply ler_wpmul2l; [apply ge0_mu1 | apply h].
  + exact s1_sbl.
  + exact s2eps_sbl.
apply (ler_trans _ _ _ hsum).
rewrite (eq_sum _ (fun x => mu1 d x * mu (F2 x) P2 + eps * mu1 d x)).
+ by move=> x /=; smt.
rewrite sumD // sumZ -weightE.
apply ler_add2l.
by smt(mu_bounded).
qed.

lemma structural_to_exact_hyperball_sample_pair_loss_from_point_loss :
  structural_to_exact_hyperball_sample_pair_point_loss_obligation =>
  structural_to_exact_hyperball_sample_pair_loss_obligation.
proof.
rewrite /structural_to_exact_hyperball_sample_pair_point_loss_obligation
        /structural_to_exact_hyperball_sample_pair_loss_obligation.
move=> hop md sk m ctx coins p.
rewrite /dstructural_signing_sample_pair dunitE.
case: (p (signing_sample_pair_of_coins md sk m ctx coins)) => hs /=.
+ have hpoint := hop md sk m ctx coins.
  have hsub :
    mu (dexact_hyperball_signing_sample_pair md)
      (pred1 (signing_sample_pair_of_coins md sk m ctx coins)) <=
    mu (dexact_hyperball_signing_sample_pair md) p.
  + by apply mu_sub => x; smt.
  by smt.
+ smt(mu_bounded rejection_sampling_loss_term_nonnegative).
qed.

lemma structural_to_exact_hyperball_coin_sample_pair_loss_from_sample_pair_loss :
  structural_to_exact_hyperball_sample_pair_loss_obligation =>
  structural_to_exact_hyperball_coin_sample_pair_loss_obligation.
proof.
rewrite /structural_to_exact_hyperball_sample_pair_loss_obligation
        /structural_to_exact_hyperball_coin_sample_pair_loss_obligation.
move=> hop md sk m ctx p.
rewrite /dstructural_signing_attempt_coin_sample_pair
        /dexact_hyperball_signing_attempt_coin_sample_pair.
apply mu_dlet_le_add_all.
+ apply rejection_sampling_loss_term_nonnegative.
move=> coins.
rewrite !dmapE.
exact (hop md sk m ctx coins (fun sample => p (coins, sample))).
qed.

lemma structural_to_exact_hyperball_attempt_loss_from_coin_sample_pair_loss :
  structural_to_exact_hyperball_coin_sample_pair_loss_obligation =>
  structural_to_exact_hyperball_attempt_loss_obligation.
proof.
rewrite /structural_to_exact_hyperball_coin_sample_pair_loss_obligation
        /structural_to_exact_hyperball_attempt_loss_obligation.
move=> hop md sk m ctx p.
rewrite -dstructural_signing_attempt_stateE.
rewrite -dstructural_signing_attempt_state_from_samplerE.
rewrite -dstructural_signing_attempt_state_from_sampler_coin_sample_pairE.
rewrite -dexact_hyperball_signing_attempt_state_coin_sample_pairE.
rewrite !dmapE.
exact (hop md sk m ctx
  (fun cs => p (signing_attempt_state_of_coin_sample_pair md sk m ctx cs))).
qed.

lemma signing_attempt_state_of_coins_signatureE md sk m ctx coins :
  signing_attempt_state_signature
    (signing_attempt_state_of_coins md sk m ctx coins) =
  sign_internal md sk m ctx coins.
proof. by rewrite /signing_attempt_state_signature
	                  /signing_attempt_state_of_coins. qed.

lemma signing_attempt_state_of_coins_sampled_y1E md sk m ctx coins :
  signing_attempt_state_sampled_y1
    (signing_attempt_state_of_coins md sk m ctx coins) =
  signing_sample_y1 md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_sampled_y1
           /signing_attempt_sample_y1
           /signing_attempt_state_sample
           /signing_attempt_state_of_coins.
qed.

lemma signing_attempt_state_of_coins_sampled_y2E md sk m ctx coins :
  signing_attempt_state_sampled_y2
    (signing_attempt_state_of_coins md sk m ctx coins) =
  signing_sample_y2 md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_sampled_y2
           /signing_attempt_sample_y2
           /signing_attempt_state_sample
           /signing_attempt_state_of_coins.
qed.

lemma signing_attempt_state_of_coins_sampled_yE md sk m ctx coins :
  signing_attempt_state_sampled_y
    (signing_attempt_state_of_coins md sk m ctx coins) =
  commitment_raw md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_sampled_y
           /signing_attempt_sample_commitment_raw
           /signing_attempt_state_sample
           /signing_attempt_state_of_coins.
qed.

lemma signing_attempt_state_of_coins_highbitsE md sk m ctx coins :
  signing_attempt_state_highbits
    (signing_attempt_state_of_coins md sk m ctx coins) =
  commitment_highbits md sk m ctx coins.
proof. by rewrite /signing_attempt_state_highbits
                  /signing_attempt_state_of_coins. qed.

lemma signing_attempt_state_of_coins_lowbitsE md sk m ctx coins :
  signing_attempt_state_lowbits
    (signing_attempt_state_of_coins md sk m ctx coins) =
  commitment_lowbits md sk m ctx coins.
proof. by rewrite /signing_attempt_state_lowbits
                  /signing_attempt_state_of_coins. qed.

lemma signing_attempt_state_of_coins_challengeE md sk m ctx coins :
  signing_attempt_state_challenge
    (signing_attempt_state_of_coins md sk m ctx coins) =
  commitment_challenge md sk m ctx coins.
proof. by rewrite /signing_attempt_state_challenge
                  /signing_attempt_state_of_coins. qed.

lemma signing_attempt_state_of_coins_responseE md sk m ctx coins :
  signing_attempt_state_response
    (signing_attempt_state_of_coins md sk m ctx coins) =
  response_vector md sk m ctx coins.
proof. by rewrite /signing_attempt_state_response
                  /signing_attempt_state_of_coins. qed.

lemma signing_attempt_state_of_coins_response_auxE md sk m ctx coins :
  signing_attempt_state_response_aux
    (signing_attempt_state_of_coins md sk m ctx coins) =
  response_aux_vector md sk m ctx coins.
proof. by rewrite /signing_attempt_state_response_aux
                  /signing_attempt_state_of_coins. qed.

lemma signing_attempt_state_of_coins_hintE md sk m ctx coins :
  signing_attempt_state_hint
    (signing_attempt_state_of_coins md sk m ctx coins) =
  hint_vector md sk m ctx coins.
proof. by rewrite /signing_attempt_state_hint
                  /signing_attempt_state_of_coins. qed.

lemma signing_attempt_state_of_coins_lowbits_carrierE md sk m ctx coins :
  signing_attempt_state_lowbits_carrier
    (signing_attempt_state_of_coins md sk m ctx coins) =
  nth poly_zero (commitment_raw md sk m ctx coins) 0.
proof.
by rewrite /signing_attempt_state_lowbits_carrier
           signing_attempt_state_of_coins_sampled_yE.
qed.

lemma signing_attempt_state_of_coins_tokenE md sk m ctx coins :
  signing_attempt_state_token
    (signing_attempt_state_of_coins md sk m ctx coins) =
  signature_token md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_token
           signing_attempt_state_of_coins_responseE
           signing_attempt_state_of_coins_response_auxE
           signing_attempt_state_of_coins_hintE
           /signature_token.
qed.

lemma signing_attempt_state_of_coins_programmed_lowbitsE md sk m ctx coins :
  signing_attempt_state_programmed_lowbits
    (signing_attempt_state_of_coins md sk m ctx coins) =
  commitment_lowbits md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_programmed_lowbits
           signing_attempt_state_of_coins_lowbits_carrierE
           /signing_attempt_state_coins /signing_attempt_state_of_coins
           /commitment_lowbits.
qed.

lemma signing_attempt_state_of_coins_lowbits_consistent md sk m ctx coins :
  signing_attempt_state_lowbits_consistent
    (signing_attempt_state_of_coins md sk m ctx coins).
proof.
by rewrite /signing_attempt_state_lowbits_consistent
           signing_attempt_state_of_coins_lowbitsE
           signing_attempt_state_of_coins_programmed_lowbitsE.
qed.

lemma signing_attempt_state_of_coins_programmed_challengeE md sk m ctx coins :
  signing_attempt_state_programmed_challenge md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_coins md sk m ctx coins) =
  commitment_challenge md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_programmed_challenge
           signing_attempt_state_of_coins_response_auxE
           signing_attempt_state_of_coins_lowbitsE
           /commitment_challenge.
qed.

lemma signing_attempt_state_of_coins_challenge_consistent md sk m ctx coins :
  signing_attempt_state_challenge_consistent md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_coins md sk m ctx coins).
proof.
by rewrite /signing_attempt_state_challenge_consistent
           signing_attempt_state_of_coins_challengeE
           signing_attempt_state_of_coins_programmed_challengeE.
qed.

lemma signing_attempt_state_of_coins_reconstructed_highbitsE
   md sk m ctx coins :
  signing_attempt_state_reconstructed_highbits md (public_key_of_secret md sk)
    (signing_attempt_state_of_coins md sk m ctx coins) =
  commitment_highbits md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_reconstructed_highbits
           signing_attempt_state_of_coins_response_auxE
           signing_attempt_state_of_coins_challengeE
           /commitment_highbits.
qed.

lemma signing_attempt_state_of_coins_public_equation_consistent
   md sk m ctx coins :
  signing_attempt_state_public_equation_consistent md
    (public_key_of_secret md sk)
    (signing_attempt_state_of_coins md sk m ctx coins).
proof.
by rewrite /signing_attempt_state_public_equation_consistent
           signing_attempt_state_of_coins_highbitsE
           signing_attempt_state_of_coins_reconstructed_highbitsE.
qed.

lemma signing_attempt_state_of_coins_signature_of_fieldsE md sk m ctx coins :
  signing_attempt_state_signature_of_fields
    (public_key_of_secret md sk) m ctx
    (signing_attempt_state_of_coins md sk m ctx coins) =
  sign_internal md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_signature_of_fields /sign_internal
           signing_attempt_state_of_coins_highbitsE
           signing_attempt_state_of_coins_lowbitsE
           signing_attempt_state_of_coins_challengeE
           signing_attempt_state_of_coins_tokenE.
qed.

lemma signing_attempt_state_of_coins_fields_match_signature md sk m ctx coins :
  signing_attempt_state_fields_match_signature
    (public_key_of_secret md sk) m ctx
    (signing_attempt_state_of_coins md sk m ctx coins).
proof.
by rewrite /signing_attempt_state_fields_match_signature
           signing_attempt_state_of_coins_signatureE
           signing_attempt_state_of_coins_signature_of_fieldsE.
qed.

lemma signing_attempt_state_of_coins_field_accepts md sk m ctx coins :
  signing_attempt_state_field_accepts md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_coins md sk m ctx coins).
proof.
rewrite /signing_attempt_state_field_accepts.
split.
+ by apply signing_attempt_state_of_coins_lowbits_consistent.
split.
+ by apply signing_attempt_state_of_coins_challenge_consistent.
split.
+ by apply signing_attempt_state_of_coins_public_equation_consistent.
by apply signing_attempt_state_of_coins_fields_match_signature.
qed.

lemma signing_attempt_state_of_coins_accepts_current md sk m ctx coins :
  signing_attempt_state_accepts md
    (signing_attempt_state_of_coins md sk m ctx coins).
proof.
by rewrite /signing_attempt_state_accepts
           /signing_attempt_state_valid_signature_accepts
           /signing_attempt_state_response_norm_accepts
           /signing_attempt_state_hint_norm_accepts
           signing_attempt_state_of_coins_signatureE
           valid_signature_sign_internal
           response_norm_ok_current
           verify_norm_ok_current.
qed.

lemma signing_attempt_reject1_bound_ge_response_bound md :
  mode_b1sq md <= signing_attempt_reject1_bound md.
proof. by case md. qed.

lemma signing_attempt_state_reject1_accepts_from_response_norm_ok md st :
  signing_attempt_state_response_norm_accepts md st =>
  signing_attempt_state_reject1_accepts md st.
proof.
rewrite /signing_attempt_state_response_norm_accepts
        /response_norm_ok /response_norm_sq
        /signing_attempt_state_reject1_accepts
        /signing_attempt_state_reject1_norm_sq.
move=> [norm_ge0 norm_le].
split=> //.
by smt(signing_attempt_reject1_bound_ge_response_bound).
qed.

lemma signing_attempt_state_balance_norm_sq_concreteE md st :
  signing_attempt_state_balance_norm_sq md st =
  signing_attempt_reject2_balance_norm_sq md
    (signing_attempt_state_response st)
    (signing_attempt_state_response_aux st)
    (signing_attempt_state_reject2_sampled_y1 st)
    (signing_attempt_state_reject2_sampled_y2 st).
proof. by rewrite /signing_attempt_state_balance_norm_sq. qed.

lemma signing_attempt_state_reject2_under_bound_concreteE md st :
  signing_attempt_state_reject2_under_bound md st =
  (signing_attempt_reject2_balance_norm_sq md
    (signing_attempt_state_response st)
    (signing_attempt_state_response_aux st)
    (signing_attempt_state_reject2_sampled_y1 st)
    (signing_attempt_state_reject2_sampled_y2 st) <
   signing_attempt_reject2_bound md).
proof.
by rewrite /signing_attempt_state_reject2_under_bound
           signing_attempt_state_balance_norm_sq_concreteE.
qed.

lemma signing_attempt_state_reject2_aborts_concreteE md st :
  signing_attempt_state_reject2_aborts md st =
  signing_attempt_reject2_concrete_aborts md
    (signing_attempt_state_bimodal_reject2_branch st)
    (signing_attempt_state_response st)
    (signing_attempt_state_response_aux st)
    (signing_attempt_state_reject2_sampled_y1 st)
    (signing_attempt_state_reject2_sampled_y2 st).
proof. by rewrite /signing_attempt_state_reject2_aborts. qed.

lemma signing_attempt_state_reject2_accepts_from_branch_clear md st :
  ! signing_attempt_state_bimodal_reject2_branch st =>
  signing_attempt_state_reject2_accepts md st.
proof.
move=> branch_clear.
by rewrite /signing_attempt_state_reject2_accepts
           /signing_attempt_state_reject2_aborts
           /signing_attempt_reject2_concrete_aborts
           branch_clear.
qed.

lemma signing_attempt_state_of_sample_pair_reject2_branch_clear
   md sk m ctx coins sample :
  ! signing_attempt_state_bimodal_reject2_branch
      (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_bimodal_reject2_branch
           /signing_attempt_state_reject2_branch_bit
           /signing_attempt_state_reject2_branch_byte
           /signature_rejection_branch_byte
           signing_attempt_state_of_sample_pair_signatureE
           /sign_internal.
qed.

lemma signing_attempt_state_of_sample_pair_reject2_accepts
   md sk m ctx coins sample :
  signing_attempt_state_reject2_accepts md
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
apply signing_attempt_state_reject2_accepts_from_branch_clear.
by apply signing_attempt_state_of_sample_pair_reject2_branch_clear.
qed.

lemma signing_attempt_state_of_sample_pair_reject2_no_abort
   md sk m ctx coins sample :
  ! signing_attempt_state_reject2_aborts md
      (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
rewrite /signing_attempt_state_reject2_aborts
        /signing_attempt_reject2_concrete_aborts.
by rewrite signing_attempt_state_of_sample_pair_reject2_branch_clear.
qed.

lemma dexact_hyperball_signing_attempt_state_reject2_abort_zero
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reject2_aborts md) =
  0%r.
proof.
have le0 :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reject2_aborts md) <=
  mu (dexact_hyperball_signing_attempt_state md sk m ctx) pred0.
+ apply mu_le => st st_supp abort.
  move: st_supp; rewrite dexact_hyperball_signing_attempt_state_supportP.
  move=> [coins sample [_ [_ stE]]].
  move: abort.
  rewrite stE signing_attempt_state_of_sample_pair_reject2_no_abort.
  by [].
rewrite mu0 in le0.
by smt(mu_bounded).
qed.

lemma dexact_hyperball_signing_attempt_state_reference_rejection_abort_reduced_bound
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reference_rejection_aborts md) <=
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reject1_aborts md) +
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_hint_norm_aborts md).
proof.
have ub :=
  dexact_hyperball_signing_attempt_state_reference_rejection_abort_union_bound
    md sk m ctx.
rewrite dexact_hyperball_signing_attempt_state_reject2_abort_zero
        dexact_hyperball_signing_attempt_state_pack_abort_zero in ub.
by smt(mu_bounded).
qed.

lemma signing_attempt_state_of_sample_pair_response_norm_accepts
   md sk m ctx coins sample :
  signing_attempt_state_response_norm_accepts md
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_response_norm_accepts
           signing_attempt_state_of_sample_pair_signatureE
           response_norm_ok_current.
qed.

lemma signing_attempt_state_of_sample_pair_reject1_accepts
   md sk m ctx coins sample :
  signing_attempt_state_reject1_accepts md
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
apply signing_attempt_state_reject1_accepts_from_response_norm_ok.
by apply signing_attempt_state_of_sample_pair_response_norm_accepts.
qed.

lemma signing_attempt_state_of_sample_pair_reject1_no_abort
   md sk m ctx coins sample :
  ! signing_attempt_state_reject1_aborts md
      (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_reject1_aborts
           signing_attempt_state_of_sample_pair_reject1_accepts.
qed.

lemma dexact_hyperball_signing_attempt_state_reject1_abort_zero
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reject1_aborts md) =
  0%r.
proof.
have le0 :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reject1_aborts md) <=
  mu (dexact_hyperball_signing_attempt_state md sk m ctx) pred0.
+ apply mu_le => st st_supp abort.
  move: st_supp; rewrite dexact_hyperball_signing_attempt_state_supportP.
  move=> [coins sample [_ [_ stE]]].
  move: abort.
  rewrite stE signing_attempt_state_of_sample_pair_reject1_no_abort.
  by [].
rewrite mu0 in le0.
by smt(mu_bounded).
qed.

lemma dexact_hyperball_signing_attempt_state_reference_rejection_abort_hint_bound
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reference_rejection_aborts md) <=
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_hint_norm_aborts md).
proof.
have ub :=
  dexact_hyperball_signing_attempt_state_reference_rejection_abort_reduced_bound
    md sk m ctx.
rewrite dexact_hyperball_signing_attempt_state_reject1_abort_zero in ub.
by smt(mu_bounded).
qed.

lemma signing_attempt_state_of_sample_pair_hint_norm_accepts
   md sk m ctx coins sample :
  signing_attempt_state_hint_norm_accepts md
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_hint_norm_accepts
           signing_attempt_state_of_sample_pair_signatureE
           verify_norm_ok_current.
qed.

lemma signing_attempt_state_of_sample_pair_hint_norm_no_abort
   md sk m ctx coins sample :
  ! signing_attempt_state_hint_norm_aborts md
      (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_hint_norm_aborts
           signing_attempt_state_of_sample_pair_hint_norm_accepts.
qed.

lemma dexact_hyperball_signing_attempt_state_hint_norm_abort_zero
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_hint_norm_aborts md) =
  0%r.
proof.
have le0 :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_hint_norm_aborts md) <=
  mu (dexact_hyperball_signing_attempt_state md sk m ctx) pred0.
+ apply mu_le => st st_supp abort.
  move: st_supp; rewrite dexact_hyperball_signing_attempt_state_supportP.
  move=> [coins sample [_ [_ stE]]].
  move: abort.
  rewrite stE signing_attempt_state_of_sample_pair_hint_norm_no_abort.
  by [].
rewrite mu0 in le0.
by smt(mu_bounded).
qed.

lemma dexact_hyperball_signing_attempt_state_reference_rejection_abort_zero
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_reference_rejection_aborts md) =
  0%r.
proof.
have ub :=
  dexact_hyperball_signing_attempt_state_reference_rejection_abort_hint_bound
    md sk m ctx.
rewrite dexact_hyperball_signing_attempt_state_hint_norm_abort_zero in ub.
by smt(mu_bounded).
qed.

lemma signing_attempt_state_of_coins_reject2_branch_clear_current
   md sk m ctx coins :
  ! signing_attempt_state_bimodal_reject2_branch
      (signing_attempt_state_of_coins md sk m ctx coins).
proof.
by rewrite /signing_attempt_state_bimodal_reject2_branch
           /signing_attempt_state_reject2_branch_bit
           /signing_attempt_state_reject2_branch_byte
           /signature_rejection_branch_byte
           signing_attempt_state_of_coins_signatureE
           /sign_internal.
qed.

lemma signing_attempt_state_of_coins_reject2_sampled_y1E md sk m ctx coins :
  signing_attempt_state_reject2_sampled_y1
    (signing_attempt_state_of_coins md sk m ctx coins) =
  signing_sample_y1 md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_reject2_sampled_y1
           signing_attempt_state_of_coins_sampled_y1E.
qed.

lemma signing_attempt_state_of_coins_reject2_sampled_y2E md sk m ctx coins :
  signing_attempt_state_reject2_sampled_y2
    (signing_attempt_state_of_coins md sk m ctx coins) =
  signing_sample_y2 md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_reject2_sampled_y2
           signing_attempt_state_of_coins_sampled_y2E.
qed.

lemma signing_attempt_state_of_coins_reject2_balance_norm_sqE
   md sk m ctx coins :
  signing_attempt_state_balance_norm_sq md
    (signing_attempt_state_of_coins md sk m ctx coins) =
  signing_attempt_reject2_balance_norm_sq md
    (response_vector md sk m ctx coins)
    (response_aux_vector md sk m ctx coins)
    (signing_sample_y1 md sk m ctx coins)
    (signing_sample_y2 md sk m ctx coins).
proof.
by rewrite signing_attempt_state_balance_norm_sq_concreteE
           signing_attempt_state_of_coins_responseE
           signing_attempt_state_of_coins_response_auxE
           signing_attempt_state_of_coins_reject2_sampled_y1E
           signing_attempt_state_of_coins_reject2_sampled_y2E.
qed.

lemma signing_attempt_state_of_coins_balance_norm_sq_current
   md sk m ctx coins :
  signing_attempt_state_balance_norm_sq md
    (signing_attempt_state_of_coins md sk m ctx coins) =
  polyvecl_norm_sq md
    (signing_attempt_state_reject2_balance_response md
      (signing_attempt_state_of_coins md sk m ctx coins)) +
  polyveck_norm_sq md
    (signing_attempt_state_reject2_balance_aux md
      (signing_attempt_state_of_coins md sk m ctx coins)).
proof.
by rewrite /signing_attempt_state_balance_norm_sq
           /signing_attempt_reject2_balance_norm_sq
           /signing_attempt_state_reject2_balance_response
           /signing_attempt_state_reject2_balance_aux.
qed.

lemma signing_attempt_state_of_coins_reject2_accepts_current
   md sk m ctx coins :
  signing_attempt_state_reject2_accepts md
    (signing_attempt_state_of_coins md sk m ctx coins).
proof.
apply signing_attempt_state_reject2_accepts_from_branch_clear.
by apply signing_attempt_state_of_coins_reject2_branch_clear_current.
qed.

lemma signing_attempt_state_pack_accepts_from_valid md st :
  signing_attempt_state_valid_signature_accepts md st =>
  signing_attempt_state_pack_accepts md st.
proof.
move=> valid_ok.
rewrite /signing_attempt_state_pack_accepts valid_ok.
split=> //.
by apply mode_crypto_bytes_gt0.
qed.

lemma signing_attempt_state_reference_rejection_accepts_from_accepts md st :
  signing_attempt_state_accepts md st =>
  signing_attempt_state_reject2_accepts md st =>
  signing_attempt_state_reference_rejection_accepts md st.
proof.
rewrite /signing_attempt_state_accepts.
move=> [valid_ok [response_ok hint_ok]] reject2_ok.
rewrite /signing_attempt_state_reference_rejection_accepts.
split.
+ by apply signing_attempt_state_reject1_accepts_from_response_norm_ok.
split.
+ by apply reject2_ok.
split.
+ by apply signing_attempt_state_pack_accepts_from_valid.
by apply hint_ok.
qed.

lemma signing_attempt_state_of_coins_reference_rejection_accepts_current
   md sk m ctx coins :
  signing_attempt_state_reference_rejection_accepts md
    (signing_attempt_state_of_coins md sk m ctx coins).
proof.
apply signing_attempt_state_reference_rejection_accepts_from_accepts.
+ by apply signing_attempt_state_of_coins_accepts_current.
by apply signing_attempt_state_of_coins_reject2_accepts_current.
qed.

lemma signing_attempt_state_of_coins_verification_accepts_current
   md sk m ctx coins :
  signing_attempt_state_verification_accepts md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_coins md sk m ctx coins).
proof.
rewrite /signing_attempt_state_verification_accepts.
split.
+ by apply signing_attempt_state_of_coins_field_accepts.
by apply signing_attempt_state_of_coins_accepts_current.
qed.

lemma signing_attempt_state_of_coins_rejection_accepts_current
   md sk m ctx coins :
  signing_attempt_state_rejection_accepts md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_coins md sk m ctx coins).
proof.
rewrite /signing_attempt_state_rejection_accepts.
split.
+ by apply signing_attempt_state_of_coins_verification_accepts_current.
by apply signing_attempt_state_of_coins_reference_rejection_accepts_current.
qed.

lemma signing_attempt_state_of_coins_rejection_no_abort_current
   md sk m ctx coins :
  ! signing_attempt_state_rejection_aborts md (public_key_of_secret md sk)
      m ctx (signing_attempt_state_of_coins md sk m ctx coins).
proof.
by rewrite /signing_attempt_state_rejection_aborts
           signing_attempt_state_of_coins_rejection_accepts_current.
qed.

lemma signing_attempt_state_of_coins_no_abort_current md sk m ctx coins :
  ! signing_attempt_state_aborts md
      (signing_attempt_state_of_coins md sk m ctx coins).
proof.
by rewrite /signing_attempt_state_aborts
           /signing_attempt_state_rejection_sampling_aborts
           /signing_attempt_state_response_norm_aborts
           /signing_attempt_state_hint_norm_aborts
           /signing_attempt_state_valid_signature_accepts
           /signing_attempt_state_response_norm_accepts
           /signing_attempt_state_hint_norm_accepts
           signing_attempt_state_of_coins_signatureE
           valid_signature_sign_internal
           response_norm_ok_current
           verify_norm_ok_current.
qed.

lemma signing_attempt_state_distribution_lossless md sk m ctx :
  is_lossless (dsigning_attempt_state md sk m ctx).
proof.
rewrite /dsigning_attempt_state.
by apply dmap_ll; apply signing_coin_distribution_lossless.
qed.

lemma signing_attempt_state_distribution_token_spread
  md sk m ctx token :
  mu (dsigning_attempt_state md sk m ctx)
    (fun st =>
      signing_entropy_token_of_coins
        (signing_attempt_state_coins st) = token) <=
  signing_randomness_point_bound.
proof.
rewrite /dsigning_attempt_state dmapE /=.
apply (ler_trans
  (mu drandom_coins
    (fun coins => signing_entropy_token_of_coins coins = token))).
+ apply mu_le => coins _.
  by rewrite /signing_attempt_state_coins /signing_attempt_state_of_coins.
by apply signing_coin_distribution_token_point_bound.
qed.

lemma signing_attempt_state_distribution_reference_rejection_abort_zero_current
  md sk m ctx :
  mu (dsigning_attempt_state md sk m ctx)
    (signing_attempt_state_reference_rejection_aborts md) =
  0%r.
proof.
rewrite /dsigning_attempt_state dmapE /=.
rewrite (mu_eq _ _ (fun (_ : random_coins) => false)).
+ move=> coins.
  rewrite /signing_attempt_state_reference_rejection_aborts.
  by smt(signing_attempt_state_of_coins_reference_rejection_accepts_current).
by rewrite mu0.
qed.

lemma signing_attempt_state_distribution_rejection_abort_zero_current
  md sk m ctx :
  mu (dsigning_attempt_state md sk m ctx)
    (signing_attempt_state_rejection_aborts md
       (public_key_of_secret md sk) m ctx) =
  0%r.
proof.
rewrite /dsigning_attempt_state dmapE /=.
rewrite (mu_eq _ _ (fun (_ : random_coins) => false)).
+ move=> coins.
  by smt(signing_attempt_state_of_coins_rejection_no_abort_current).
by rewrite mu0.
qed.

lemma sign_internal_simulation_relation md sk m ctx coins :
  signing_simulation_relation md
    (public_key_of_secret md sk) m ctx
    (sign_internal md sk m ctx coins).
proof.
by apply (signing_attempt_simulates md (public_key_of_secret md sk)
            sk m ctx coins (sign_internal md sk m ctx coins));
   apply sign_internal_attempt_relation.
qed.

lemma signing_attempt_transcript_valid md pk sk m ctx coins sig :
  signing_attempt_relation md pk sk m ctx coins sig =>
  transcript_valid md (transcript_of_signature md pk m ctx sig).
proof.
rewrite /signing_attempt_relation /valid_keypair.
move=> [#] pkE _ ->.
rewrite /transcript_valid /transcript_verifies
        /transcript_of_signature /transcript_pk /transcript_message
        /transcript_context /transcript_signature /=.
split.
+ rewrite pkE.
  by apply verify_internal_sign_internal.
split.
+ by apply valid_signature_sign_internal.
by rewrite /transcript_fields_match_signature /transcript_of_signature /=.
qed.

lemma signing_attempt_transcript_relation md pk sk m ctx coins sig :
  signing_attempt_relation md pk sk m ctx coins sig =>
  signing_transcript_relation md pk m ctx sig
    (transcript_of_signature md pk m ctx sig).
proof.
move=> attempt.
rewrite /signing_transcript_relation.
split.
+ by apply (signing_attempt_simulates md pk sk m ctx coins sig).
split=> //.
by apply (signing_attempt_transcript_valid md pk sk m ctx coins sig).
qed.

lemma sign_internal_transcript_relation md sk m ctx coins :
  signing_transcript_relation md
    (public_key_of_secret md sk) m ctx
    (sign_internal md sk m ctx coins)
    (transcript_of_signature md (public_key_of_secret md sk) m ctx
      (sign_internal md sk m ctx coins)).
proof.
by apply (signing_attempt_transcript_relation md
            (public_key_of_secret md sk) sk m ctx coins
            (sign_internal md sk m ctx coins));
   apply sign_internal_attempt_relation.
qed.

lemma sign_internal_record_relation md sk m ctx coins :
  signing_record_relation md (public_key_of_secret md sk)
    (m, ctx,
     sign_internal md sk m ctx coins,
     transcript_of_signature md (public_key_of_secret md sk) m ctx
       (sign_internal md sk m ctx coins)).
proof.
rewrite /signing_record_relation /signing_record_message
        /signing_record_context /signing_record_signature
        /signing_record_transcript /=.
by apply sign_internal_transcript_relation.
qed.

lemma signing_record_relation_sound md pk r :
  signing_record_relation md pk r =>
  signing_simulation_relation md pk
    (signing_record_message r)
    (signing_record_context r)
    (signing_record_signature r) /\
  transcript_valid md (signing_record_transcript r).
proof.
rewrite /signing_record_relation /signing_transcript_relation.
move=> h.
case: h => hsim rest.
case: rest => _ valid.
split.
+ by apply hsim.
by apply valid.
qed.

lemma signing_record_log_sound_cons md pk r rs :
  signing_record_relation md pk r =>
  signing_record_log_sound md pk rs =>
  signing_record_log_sound md pk (r :: rs).
proof.
by rewrite /signing_record_log_sound /=.
qed.

lemma signing_record_log_sound_transcripts_valid md pk rs :
  signing_record_log_sound md pk rs =>
  transcript_log_valid md (signing_record_transcripts rs).
proof.
rewrite /signing_record_log_sound /transcript_log_valid
        /signing_record_transcripts.
elim: rs => [|r rs ih] //=.
move=> [rel sound].
split.
+ by case: (signing_record_relation_sound md pk r rel).
by apply ih.
qed.

lemma signing_record_queries_cons r rs :
  signing_record_queries (r :: rs) =
  signing_record_query r :: signing_record_queries rs.
proof. by rewrite /signing_record_queries. qed.

lemma signing_record_transcripts_cons r rs :
  signing_record_transcripts (r :: rs) =
  signing_record_transcript r :: signing_record_transcripts rs.
proof. by rewrite /signing_record_transcripts. qed.

lemma rejection_bound_parts_nonnegative :
  rejection_sampling_bound_obligation =>
  0%r <= rejection_sampling_loss_term.
proof. by rewrite /rejection_sampling_bound_obligation. qed.

lemma rejection_sampling_bound_obligation_holds :
  rejection_sampling_bound_obligation.
proof.
rewrite /rejection_sampling_bound_obligation.
split.
+ by apply rejection_sampling_loss_term_nonnegative.
split.
+ by apply fs_with_aborts_reprogramming_term_nonnegative.
+ by apply fs_with_aborts_min_entropy_term_nonnegative.
qed.

lemma signing_attempt_state_of_sample_pair_sampled_yE md sk m ctx coins sample :
  signing_attempt_state_sampled_y
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  commitment_raw md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_sampled_y
           /signing_attempt_sample_commitment_raw
           /signing_attempt_state_sample
           /signing_attempt_state_of_sample_pair
           /signing_attempt_sample_of_pair.
qed.

lemma signing_attempt_state_of_sample_pair_highbitsE md sk m ctx coins sample :
  signing_attempt_state_highbits
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  commitment_highbits md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_highbits
           /signing_attempt_state_of_sample_pair.
qed.

lemma signing_attempt_state_of_sample_pair_lowbitsE md sk m ctx coins sample :
  signing_attempt_state_lowbits
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  commitment_lowbits md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_lowbits
           /signing_attempt_state_of_sample_pair.
qed.

lemma signing_attempt_state_of_sample_pair_challengeE md sk m ctx coins sample :
  signing_attempt_state_challenge
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  commitment_challenge md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_challenge
           /signing_attempt_state_of_sample_pair.
qed.

lemma signing_attempt_state_of_sample_pair_responseE md sk m ctx coins sample :
  signing_attempt_state_response
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  response_vector md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_response
           /signing_attempt_state_of_sample_pair.
qed.

lemma signing_attempt_state_of_sample_pair_response_auxE
   md sk m ctx coins sample :
  signing_attempt_state_response_aux
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  response_aux_vector md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_response_aux
           /signing_attempt_state_of_sample_pair.
qed.

lemma signing_attempt_state_of_sample_pair_hintE md sk m ctx coins sample :
  signing_attempt_state_hint
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  hint_vector md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_hint
           /signing_attempt_state_of_sample_pair.
qed.

lemma signing_attempt_state_of_sample_pair_lowbits_carrierE
   md sk m ctx coins sample :
  signing_attempt_state_lowbits_carrier
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  nth poly_zero (commitment_raw md sk m ctx coins) 0.
proof.
by rewrite /signing_attempt_state_lowbits_carrier
           signing_attempt_state_of_sample_pair_sampled_yE.
qed.

lemma signing_attempt_state_of_sample_pair_tokenE md sk m ctx coins sample :
  signing_attempt_state_token
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  signature_token md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_token
           signing_attempt_state_of_sample_pair_responseE
           signing_attempt_state_of_sample_pair_response_auxE
           signing_attempt_state_of_sample_pair_hintE
           /signature_token.
qed.

lemma signing_attempt_state_of_sample_pair_programmed_lowbitsE
   md sk m ctx coins sample :
  signing_attempt_state_programmed_lowbits
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  commitment_lowbits md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_programmed_lowbits
           signing_attempt_state_of_sample_pair_lowbits_carrierE
           /signing_attempt_state_coins /signing_attempt_state_of_sample_pair
           /commitment_lowbits.
qed.

lemma signing_attempt_state_of_sample_pair_lowbits_consistent
   md sk m ctx coins sample :
  signing_attempt_state_lowbits_consistent
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_lowbits_consistent
           signing_attempt_state_of_sample_pair_lowbitsE
           signing_attempt_state_of_sample_pair_programmed_lowbitsE.
qed.

lemma signing_attempt_state_of_sample_pair_programmed_challengeE
   md sk m ctx coins sample :
  signing_attempt_state_programmed_challenge md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  commitment_challenge md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_programmed_challenge
           signing_attempt_state_of_sample_pair_response_auxE
           signing_attempt_state_of_sample_pair_lowbitsE
           /commitment_challenge.
qed.

lemma signing_attempt_state_of_sample_pair_challenge_consistent
   md sk m ctx coins sample :
  signing_attempt_state_challenge_consistent md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_challenge_consistent
           signing_attempt_state_of_sample_pair_challengeE
           signing_attempt_state_of_sample_pair_programmed_challengeE.
qed.

lemma signing_attempt_state_of_sample_pair_reconstructed_highbitsE
   md sk m ctx coins sample :
  signing_attempt_state_reconstructed_highbits md (public_key_of_secret md sk)
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  commitment_highbits md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_reconstructed_highbits
           signing_attempt_state_of_sample_pair_response_auxE
           signing_attempt_state_of_sample_pair_challengeE
           /commitment_highbits.
qed.

lemma signing_attempt_state_of_sample_pair_public_equation_consistent
   md sk m ctx coins sample :
  signing_attempt_state_public_equation_consistent md
    (public_key_of_secret md sk)
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_public_equation_consistent
           signing_attempt_state_of_sample_pair_highbitsE
           signing_attempt_state_of_sample_pair_reconstructed_highbitsE.
qed.

lemma signing_attempt_state_of_sample_pair_signature_of_fieldsE
   md sk m ctx coins sample :
  signing_attempt_state_signature_of_fields
    (public_key_of_secret md sk) m ctx
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample) =
  sign_internal md sk m ctx coins.
proof.
by rewrite /signing_attempt_state_signature_of_fields /sign_internal
           signing_attempt_state_of_sample_pair_highbitsE
           signing_attempt_state_of_sample_pair_lowbitsE
           signing_attempt_state_of_sample_pair_challengeE
           signing_attempt_state_of_sample_pair_tokenE.
qed.

lemma signing_attempt_state_of_sample_pair_fields_match_signature
   md sk m ctx coins sample :
  signing_attempt_state_fields_match_signature
    (public_key_of_secret md sk) m ctx
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_fields_match_signature
           signing_attempt_state_of_sample_pair_signatureE
           signing_attempt_state_of_sample_pair_signature_of_fieldsE.
qed.

lemma signing_attempt_state_of_sample_pair_field_accepts
   md sk m ctx coins sample :
  signing_attempt_state_field_accepts md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
rewrite /signing_attempt_state_field_accepts.
split.
+ by apply signing_attempt_state_of_sample_pair_lowbits_consistent.
split.
+ by apply signing_attempt_state_of_sample_pair_challenge_consistent.
split.
+ by apply signing_attempt_state_of_sample_pair_public_equation_consistent.
by apply signing_attempt_state_of_sample_pair_fields_match_signature.
qed.

lemma signing_attempt_state_of_sample_pair_valid_signature_accepts
   md sk m ctx coins sample :
  signing_attempt_state_valid_signature_accepts md
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_valid_signature_accepts
           signing_attempt_state_of_sample_pair_signatureE
           valid_signature_sign_internal.
qed.

lemma signing_attempt_state_of_sample_pair_accepts_current
   md sk m ctx coins sample :
  signing_attempt_state_accepts md
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
rewrite /signing_attempt_state_accepts.
split.
+ by apply signing_attempt_state_of_sample_pair_valid_signature_accepts.
split.
+ by apply signing_attempt_state_of_sample_pair_response_norm_accepts.
by apply signing_attempt_state_of_sample_pair_hint_norm_accepts.
qed.

lemma signing_attempt_state_of_sample_pair_verification_accepts_current
   md sk m ctx coins sample :
  signing_attempt_state_verification_accepts md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
rewrite /signing_attempt_state_verification_accepts.
split.
+ by apply signing_attempt_state_of_sample_pair_field_accepts.
by apply signing_attempt_state_of_sample_pair_accepts_current.
qed.

lemma signing_attempt_state_of_sample_pair_reference_rejection_accepts
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) (sample : signing_sample_pair) :
  signing_attempt_state_reference_rejection_accepts md
    (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
rewrite /signing_attempt_state_reference_rejection_accepts.
split.
+ by apply signing_attempt_state_of_sample_pair_reject1_accepts.
split.
+ by apply signing_attempt_state_of_sample_pair_reject2_accepts.
split.
+ by apply signing_attempt_state_of_sample_pair_pack_accepts.
by apply signing_attempt_state_of_sample_pair_hint_norm_accepts.
qed.

lemma signing_attempt_state_of_sample_pair_reference_rejection_no_abort
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) (sample : signing_sample_pair) :
  ! signing_attempt_state_reference_rejection_aborts md
      (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_reference_rejection_aborts
           signing_attempt_state_of_sample_pair_reference_rejection_accepts.
qed.

lemma signing_attempt_state_of_sample_pair_rejection_accepts_current
   md sk m ctx coins sample :
  signing_attempt_state_rejection_accepts md (public_key_of_secret md sk)
    m ctx (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
rewrite /signing_attempt_state_rejection_accepts.
split.
+ by apply signing_attempt_state_of_sample_pair_verification_accepts_current.
by apply signing_attempt_state_of_sample_pair_reference_rejection_accepts.
qed.

lemma signing_attempt_state_of_sample_pair_rejection_no_abort_current
   md sk m ctx coins sample :
  ! signing_attempt_state_rejection_aborts md (public_key_of_secret md sk)
      m ctx (signing_attempt_state_of_sample_pair md sk m ctx coins sample).
proof.
by rewrite /signing_attempt_state_rejection_aborts
           signing_attempt_state_of_sample_pair_rejection_accepts_current.
qed.

lemma dexact_hyperball_signing_attempt_state_reference_rejection_accepts
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (st : signing_attempt_state) :
  st \in dexact_hyperball_signing_attempt_state md sk m ctx =>
  signing_attempt_state_reference_rejection_accepts md st.
proof.
move=> st_supp.
move: st_supp; rewrite dexact_hyperball_signing_attempt_state_supportP.
move=> [coins sample [_ [_ stE]]].
by rewrite stE signing_attempt_state_of_sample_pair_reference_rejection_accepts.
qed.

lemma dexact_hyperball_signing_attempt_state_reference_rejection_no_abort
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (st : signing_attempt_state) :
  st \in dexact_hyperball_signing_attempt_state md sk m ctx =>
  ! signing_attempt_state_reference_rejection_aborts md st.
proof.
move=> st_supp.
rewrite /signing_attempt_state_reference_rejection_aborts.
by rewrite (dexact_hyperball_signing_attempt_state_reference_rejection_accepts
              md sk m ctx st st_supp).
qed.

lemma dexact_hyperball_signing_attempt_state_rejection_accepts
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (st : signing_attempt_state) :
  st \in dexact_hyperball_signing_attempt_state md sk m ctx =>
  signing_attempt_state_rejection_accepts md (public_key_of_secret md sk)
    m ctx st.
proof.
move=> st_supp.
move: st_supp; rewrite dexact_hyperball_signing_attempt_state_supportP.
move=> [coins sample [_ [_ stE]]].
by rewrite stE signing_attempt_state_of_sample_pair_rejection_accepts_current.
qed.

lemma dexact_hyperball_signing_attempt_state_rejection_no_abort
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (st : signing_attempt_state) :
  st \in dexact_hyperball_signing_attempt_state md sk m ctx =>
  ! signing_attempt_state_rejection_aborts md (public_key_of_secret md sk)
      m ctx st.
proof.
move=> st_supp.
rewrite /signing_attempt_state_rejection_aborts.
by rewrite (dexact_hyperball_signing_attempt_state_rejection_accepts
              md sk m ctx st st_supp).
qed.

lemma dexact_hyperball_signing_attempt_state_rejection_abort_zero
  md sk m ctx :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_rejection_aborts md
       (public_key_of_secret md sk) m ctx) =
  0%r.
proof.
have le0 :
  mu (dexact_hyperball_signing_attempt_state md sk m ctx)
    (signing_attempt_state_rejection_aborts md
       (public_key_of_secret md sk) m ctx) <=
  mu (dexact_hyperball_signing_attempt_state md sk m ctx) pred0.
+ apply mu_le => st st_supp abort.
  move: st_supp; rewrite dexact_hyperball_signing_attempt_state_supportP.
  move=> [coins sample [_ [_ stE]]].
  move: abort.
  rewrite stE signing_attempt_state_of_sample_pair_rejection_no_abort_current.
  by [].
rewrite mu0 in le0.
by smt(mu_bounded).
qed.

end HAETAE_Rejection.
