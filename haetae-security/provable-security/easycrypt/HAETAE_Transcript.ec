require import AllCore List.
require import HAETAE_Params HAETAE_Algebra HAETAE_ROM HAETAE_Assumptions.

theory HAETAE_Transcript.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_ROM.
import HAETAE_Assumptions.

type transcript =
  pkey * message * context * polyveck * poly * crh * challenge * signature.

op signature_commitment_highbits :
  mode -> pkey -> message -> context -> signature -> polyveck =
  fun (_ : mode) (_ : pkey) (_ : message) (_ : context) sig =>
    sig_commitment_highbits sig.
op signature_commitment_lowbits :
  mode -> pkey -> message -> context -> signature -> poly =
  fun (_ : mode) (_ : pkey) (_ : message) (_ : context) sig =>
    sig_commitment_lowbits sig.
op signature_message_hash :
  mode -> pkey -> message -> context -> signature -> crh =
  fun (_ : mode) (_ : pkey) (_ : message) (_ : context) sig =>
    sig_message_hash sig.
op signature_challenge :
  mode -> pkey -> message -> context -> signature -> challenge =
  fun (_ : mode) (_ : pkey) (_ : message) (_ : context) sig =>
    sig_challenge sig.

op transcript_pk (tr : transcript) : pkey = tr.`1.
op transcript_message (tr : transcript) : message = tr.`2.
op transcript_context (tr : transcript) : context = tr.`3.
op transcript_commitment_highbits (tr : transcript) : polyveck = tr.`4.
op transcript_commitment_lowbits (tr : transcript) : poly = tr.`5.
op transcript_message_hash (tr : transcript) : crh = tr.`6.
op transcript_challenge (tr : transcript) : challenge = tr.`7.
op transcript_signature (tr : transcript) : signature = tr.`8.

op transcript_of_signature :
  mode -> pkey -> message -> context -> signature -> transcript =
  fun md pk m ctx sig =>
    (pk, m, ctx,
     signature_commitment_highbits md pk m ctx sig,
     signature_commitment_lowbits md pk m ctx sig,
     signature_message_hash md pk m ctx sig,
     signature_challenge md pk m ctx sig,
     sig).

op transcript_challenge_query (md : mode) (tr : transcript) : ro_query =
  challenge_hash_query
    md
    (transcript_commitment_highbits tr)
    (transcript_commitment_lowbits tr)
    (transcript_message_hash tr).

op transcript_signature_challenge_query (md : mode) (tr : transcript) :
  ro_query =
  challenge_hash_query
    md
    (sig_commitment_highbits (transcript_signature tr))
    (sig_commitment_lowbits (transcript_signature tr))
    (sig_message_hash (transcript_signature tr)).

op transcript_verifies (md : mode) (tr : transcript) : bool =
  verify_internal md
    (transcript_pk tr)
    (transcript_message tr)
    (transcript_context tr)
    (transcript_signature tr).

op transcript_challenge_matches (tr : transcript) (y : ro_output) : bool =
  ro_challenge_hash y = transcript_challenge tr.

op transcript_signature_challenge_matches
   (tr : transcript) (y : ro_output) : bool =
  ro_challenge_hash y = sig_challenge (transcript_signature tr).

op transcript_fields_match_signature (tr : transcript) : bool =
  transcript_commitment_highbits tr =
    sig_commitment_highbits (transcript_signature tr) /\
  transcript_commitment_lowbits tr =
    sig_commitment_lowbits (transcript_signature tr) /\
  transcript_message_hash tr =
    sig_message_hash (transcript_signature tr) /\
  transcript_challenge tr =
    sig_challenge (transcript_signature tr).

op transcript_valid (md : mode) (tr : transcript) : bool =
  transcript_verifies md tr /\
  valid_signature md (transcript_signature tr) /\
  transcript_fields_match_signature tr.

op transcript_public_equation (md : mode) (tr : transcript) : bool =
  verify_public_equation md (transcript_pk tr) (transcript_signature tr).

op same_fork_target (tr1 tr2 : transcript) : bool =
  transcript_pk tr1 = transcript_pk tr2 /\
  transcript_message tr1 = transcript_message tr2 /\
  transcript_context tr1 = transcript_context tr2 /\
  transcript_commitment_highbits tr1 = transcript_commitment_highbits tr2 /\
  transcript_commitment_lowbits tr1 = transcript_commitment_lowbits tr2 /\
  transcript_message_hash tr1 = transcript_message_hash tr2.

op distinct_fork_challenges (tr1 tr2 : transcript) : bool =
  transcript_challenge tr1 <> transcript_challenge tr2.

op valid_forking_pair (md : mode) (tr1 tr2 : transcript) : bool =
  same_fork_target tr1 tr2 /\
  distinct_fork_challenges tr1 tr2 /\
  transcript_valid md tr1 /\
  transcript_valid md tr2.

op transcript_response (tr : transcript) : polyvecl =
  sig_response (transcript_signature tr).
op transcript_response_aux (tr : transcript) : polyveck =
  sig_response_aux (transcript_signature tr).

op transcript_public_key_challenge_term (md : mode) (tr : transcript) :
  polyveck =
  public_key_challenge_term md
    (transcript_pk tr)
    (sig_challenge (transcript_signature tr)).

op active_public_reconstruction (md : mode) (tr : transcript) : bool =
  transcript_public_key_challenge_term md tr <> polyveck_zero md.

op inactive_public_reconstruction (md : mode) (tr : transcript) : bool =
  transcript_public_key_challenge_term md tr = polyveck_zero md.

op forking_difference_solution
   (md : mode) (tr1 tr2 : transcript) : bimodal_selftarget_msis_solution =
  polyvecl_sub md (transcript_response tr1) (transcript_response tr2).

op fork_response_aux_difference (md : mode) (tr1 tr2 : transcript) :
  polyveck =
  polyveck_sub md (transcript_response_aux tr1) (transcript_response_aux tr2).

op fork_public_challenge_relation (md : mode) (tr1 tr2 : transcript) : bool =
  polyveck_add md
    (transcript_response_aux tr1)
    (transcript_public_key_challenge_term md tr1) =
  polyveck_add md
    (transcript_response_aux tr2)
    (transcript_public_key_challenge_term md tr2).

op fork_response_aux_relation (tr1 tr2 : transcript) : bool =
  transcript_response_aux tr1 = transcript_response_aux tr2.

op fork_left_active_public_challenge_relation
   (md : mode) (tr1 tr2 : transcript) : bool =
  polyveck_add md
    (transcript_response_aux tr1)
    (transcript_public_key_challenge_term md tr1) =
  transcript_response_aux tr2.

op fork_right_active_public_challenge_relation
   (md : mode) (tr1 tr2 : transcript) : bool =
  transcript_response_aux tr1 =
  polyveck_add md
    (transcript_response_aux tr2)
    (transcript_public_key_challenge_term md tr2).

op fork_public_reconstruction_cases
   (md : mode) (tr1 tr2 : transcript) : bool =
  fork_public_challenge_relation md tr1 tr2.

op fork_matrix_source (tr1 tr2 : transcript) : byte list =
  encode_pkey (transcript_pk tr1) ++
  transcript_context tr1 ++
  transcript_message tr1 ++
  encode_polyveck (transcript_commitment_highbits tr1) ++
  encode_poly (transcript_commitment_lowbits tr1) ++
  transcript_message_hash tr1 ++
  encode_poly (transcript_challenge tr1) ++
  encode_poly (transcript_challenge tr2).

op fork_module_matrix (md : mode) (tr1 tr2 : transcript) : matrix =
  mkseq
    (fun i =>
      deterministic_unit_polyvecl md (53 + i) (fork_matrix_source tr1 tr2))
    (mode_k md).

op fork_module_target (md : mode) (tr1 tr2 : transcript) : polyveck =
  matrix_vec_mul md
    (fork_module_matrix md tr1 tr2)
    (forking_difference_solution md tr1 tr2).

op bimodal_selftarget_msis_instance_of_fork :
  mode -> transcript -> transcript -> bimodal_selftarget_msis_instance =
  fun md tr1 tr2 =>
    (fork_module_matrix md tr1 tr2, fork_module_target md tr1 tr2).

op extract_bimodal_selftarget_msis_solution :
  mode -> transcript -> transcript ->
  bimodal_selftarget_msis_solution option =
  fun md tr1 tr2 =>
    if valid_forking_pair md tr1 tr2
    then Some (forking_difference_solution md tr1 tr2)
    else None.

op module_sis_instance_of_fork :
  mode -> transcript -> transcript -> module_sis_instance =
  fun md tr1 tr2 =>
    bimodal_to_module_sis_instance md
      (bimodal_selftarget_msis_instance_of_fork md tr1 tr2).

op extract_module_sis_solution :
  mode -> transcript -> transcript -> module_sis_solution option =
  fun md tr1 tr2 =>
    let x = bimodal_selftarget_msis_instance_of_fork md tr1 tr2 in
    let sol = extract_bimodal_selftarget_msis_solution md tr1 tr2 in
      if sol = None then None
      else Some (bimodal_to_module_sis_solution md x (oget sol)).

op bimodal_extraction_success (md : mode) (tr1 tr2 : transcript) : bool =
  extract_bimodal_selftarget_msis_solution md tr1 tr2 <> None /\
  bimodal_selftarget_msis_valid md
    (bimodal_selftarget_msis_instance_of_fork md tr1 tr2)
    (oget (extract_bimodal_selftarget_msis_solution md tr1 tr2)).

lemma extract_bimodal_forking_some md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  extract_bimodal_selftarget_msis_solution md tr1 tr2 =
    Some (forking_difference_solution md tr1 tr2).
proof.
rewrite /extract_bimodal_selftarget_msis_solution.
by case: (valid_forking_pair md tr1 tr2).
qed.

lemma extract_bimodal_forking_nonempty md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  extract_bimodal_selftarget_msis_solution md tr1 tr2 <> None.
proof.
move=> valid_pair.
rewrite (extract_bimodal_forking_some md tr1 tr2 valid_pair).
by case: (Some (forking_difference_solution md tr1 tr2) = None).
qed.

lemma transcript_fields_match_signature_challenge_query md tr :
  transcript_fields_match_signature tr =>
  transcript_challenge_query md tr =
  transcript_signature_challenge_query md tr.
proof.
rewrite /transcript_fields_match_signature
        /transcript_challenge_query
        /transcript_signature_challenge_query.
move=> [highE rest].
case: rest => lowE rest.
case: rest => muE _.
by rewrite highE lowE muE.
qed.

lemma transcript_fields_match_signature_challenge_matches tr y :
  transcript_fields_match_signature tr =>
  transcript_challenge_matches tr y =
  transcript_signature_challenge_matches tr y.
proof.
rewrite /transcript_fields_match_signature
        /transcript_challenge_matches
        /transcript_signature_challenge_matches.
move=> [_ rest].
case: rest => _ rest.
case: rest => _ chE.
by rewrite chE.
qed.

lemma transcript_valid_signature_challenge_query md tr :
  transcript_valid md tr =>
  transcript_challenge_query md tr =
  transcript_signature_challenge_query md tr.
proof.
rewrite /transcript_valid.
move=> [_ [_ fields]].
by apply transcript_fields_match_signature_challenge_query.
qed.

lemma transcript_valid_signature_challenge_matches md tr y :
  transcript_valid md tr =>
  transcript_challenge_matches tr y =
  transcript_signature_challenge_matches tr y.
proof.
rewrite /transcript_valid.
move=> [_ [_ fields]].
by apply transcript_fields_match_signature_challenge_matches.
qed.

lemma transcript_valid_signature_challengeE md tr :
  transcript_valid md tr =>
  transcript_challenge tr = sig_challenge (transcript_signature tr).
proof.
rewrite /transcript_valid /transcript_fields_match_signature.
move=> [_ [_ [_ rest]]].
case: rest => _ rest.
case: rest => _ chE.
by apply chE.
qed.

lemma transcript_valid_public_equation md tr :
  transcript_valid md tr =>
  transcript_public_equation md tr.
proof.
rewrite /transcript_valid /transcript_verifies
        /transcript_public_equation /verify_internal.
move=> h.
case: h => hver _.
case: hver => _ htail.
case: htail => _ hpubnorm.
case: hpubnorm => pub _.
by apply pub.
qed.

lemma transcript_valid_commitment_reconstruction md tr :
  transcript_valid md tr =>
  transcript_commitment_highbits tr =
    verify_reconstructed_highbits md
      (transcript_pk tr)
      (transcript_signature tr).
proof.
move=> valid.
have pub := transcript_valid_public_equation md tr valid.
move: pub.
rewrite /transcript_public_equation /verify_public_equation.
move=> pubE.
move: valid.
rewrite /transcript_valid /transcript_fields_match_signature.
case=> _ rest.
case: rest => _ fields.
case: fields => highE _.
by rewrite highE pubE.
qed.

lemma valid_forking_pair_public_equations md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  transcript_public_equation md tr1 /\
  transcript_public_equation md tr2.
proof.
rewrite /valid_forking_pair.
move=> [_ [_ [valid1 valid2]]].
split.
+ by apply transcript_valid_public_equation.
+ by apply transcript_valid_public_equation.
qed.

lemma same_fork_target_challenge_query md tr1 tr2 :
  same_fork_target tr1 tr2 =>
  transcript_challenge_query md tr1 = transcript_challenge_query md tr2.
proof.
rewrite /same_fork_target /transcript_challenge_query.
move=> [_ [_ [_ [highE [lowE muE]]]]].
by rewrite highE lowE muE.
qed.

lemma valid_forking_pair_challenge_query md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  transcript_challenge_query md tr1 = transcript_challenge_query md tr2.
proof.
rewrite /valid_forking_pair.
move=> [same _].
by apply same_fork_target_challenge_query.
qed.

lemma valid_forking_pair_signature_challenge_query md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  transcript_signature_challenge_query md tr1 =
  transcript_signature_challenge_query md tr2.
proof.
move=> valid_pair.
have queryE := valid_forking_pair_challenge_query md tr1 tr2 valid_pair.
move: valid_pair.
rewrite /valid_forking_pair.
move=> [_ [_ [valid1 valid2]]].
rewrite -(transcript_valid_signature_challenge_query md tr1 valid1).
rewrite -(transcript_valid_signature_challenge_query md tr2 valid2).
by apply queryE.
qed.

lemma valid_forking_pair_distinct_signature_challenges md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  sig_challenge (transcript_signature tr1) <>
  sig_challenge (transcript_signature tr2).
proof.
rewrite /valid_forking_pair.
move=> [_ [distinct [valid1 valid2]]].
have ch1E := transcript_valid_signature_challengeE md tr1 valid1.
have ch2E := transcript_valid_signature_challengeE md tr2 valid2.
move: distinct.
rewrite /distinct_fork_challenges ch1E ch2E.
by [].
qed.

lemma same_fork_target_commitment_highbits tr1 tr2 :
  same_fork_target tr1 tr2 =>
  transcript_commitment_highbits tr1 = transcript_commitment_highbits tr2.
proof. by rewrite /same_fork_target; move=> [_ [_ [_ [highE _]]]]. qed.

lemma valid_forking_pair_commitment_highbits md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  transcript_commitment_highbits tr1 = transcript_commitment_highbits tr2.
proof.
rewrite /valid_forking_pair.
move=> [same _].
by apply same_fork_target_commitment_highbits.
qed.

lemma valid_forking_pair_reconstructed_highbits_equal md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  verify_reconstructed_highbits md
    (transcript_pk tr1) (transcript_signature tr1) =
  verify_reconstructed_highbits md
    (transcript_pk tr2) (transcript_signature tr2).
proof.
move=> valid_pair.
have highE := valid_forking_pair_commitment_highbits md tr1 tr2 valid_pair.
move: valid_pair.
rewrite /valid_forking_pair.
move=> [_ [_ [valid1 valid2]]].
have rec1 := transcript_valid_commitment_reconstruction md tr1 valid1.
have rec2 := transcript_valid_commitment_reconstruction md tr2 valid2.
by rewrite -rec1 -rec2.
qed.

lemma transcript_reconstructionE md tr :
  verify_reconstructed_highbits md
    (transcript_pk tr) (transcript_signature tr) =
  polyveck_add md
    (transcript_response_aux tr)
    (transcript_public_key_challenge_term md tr).
proof.
by rewrite /verify_reconstructed_highbits
           /transcript_response_aux
           /transcript_public_key_challenge_term
           /reconstructed_highbits.
qed.

lemma transcript_active_reconstructionE md tr :
  active_public_reconstruction md tr =>
  verify_reconstructed_highbits md
    (transcript_pk tr) (transcript_signature tr) =
  polyveck_add md
    (transcript_response_aux tr)
    (transcript_public_key_challenge_term md tr).
proof.
move=> _.
by apply transcript_reconstructionE.
qed.

lemma valid_forking_pair_public_challenge_relation md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  fork_public_challenge_relation md tr1 tr2.
proof.
move=> valid_pair.
have recE :=
  valid_forking_pair_reconstructed_highbits_equal md tr1 tr2 valid_pair.
rewrite /fork_public_challenge_relation.
rewrite -(transcript_reconstructionE md tr1).
rewrite -(transcript_reconstructionE md tr2).
by apply recE.
qed.

lemma valid_forking_pair_public_reconstruction_cases md tr1 tr2 :
  valid_forking_pair md tr1 tr2 =>
  fork_public_reconstruction_cases md tr1 tr2.
proof.
move=> valid_pair.
rewrite /fork_public_reconstruction_cases.
by apply valid_forking_pair_public_challenge_relation.
qed.

op extraction_success (md : mode) (tr1 tr2 : transcript) : bool =
  extract_module_sis_solution md tr1 tr2 <> None /\
  module_sis_valid md
    (module_sis_instance_of_fork md tr1 tr2)
    (oget (extract_module_sis_solution md tr1 tr2)).

op forking_extraction_obligation (md : mode) : bool =
  forall (tr1 tr2 : transcript),
    valid_forking_pair md tr1 tr2 =>
    bimodal_extraction_success md tr1 tr2.

op fork_public_reconstruction_obligation (md : mode) : bool =
  forall (tr1 tr2 : transcript),
    valid_forking_pair md tr1 tr2 =>
    fork_public_reconstruction_cases md tr1 tr2.

lemma forking_difference_solution_wf md tr1 tr2 :
  module_sis_solution_wf md (forking_difference_solution md tr1 tr2).
proof.
by rewrite /module_sis_solution_wf /forking_difference_solution
           polyvecl_sub_wf.
qed.

lemma fork_module_matrix_rows_wf md tr1 tr2 :
  all (polyvecl_wf md) (fork_module_matrix md tr1 tr2).
proof.
rewrite /fork_module_matrix.
apply/allP=> row /mkseqP [i [_ ->]].
by apply deterministic_unit_polyvecl_wf.
qed.

lemma fork_module_matrix_size md tr1 tr2 :
  size (fork_module_matrix md tr1 tr2) = mode_k md.
proof. by rewrite /fork_module_matrix size_mkseq; case md. qed.

lemma bimodal_forking_solution_valid md tr1 tr2 :
  bimodal_selftarget_msis_valid md
    (bimodal_selftarget_msis_instance_of_fork md tr1 tr2)
    (forking_difference_solution md tr1 tr2).
proof.
rewrite /bimodal_selftarget_msis_valid /module_sis_valid.
split.
+ by apply forking_difference_solution_wf.
by rewrite /bimodal_selftarget_msis_instance_of_fork /fork_module_target /=.
qed.

lemma forking_extraction_obligation_holds md :
  forking_extraction_obligation md.
proof.
rewrite /forking_extraction_obligation /bimodal_extraction_success.
move=> tr1 tr2 valid_pair.
split.
+ by apply extract_bimodal_forking_nonempty.
+ rewrite (extract_bimodal_forking_some md tr1 tr2 valid_pair) /=.
  by apply bimodal_forking_solution_valid.
qed.

lemma fork_public_reconstruction_obligation_holds md :
  fork_public_reconstruction_obligation md.
proof.
rewrite /fork_public_reconstruction_obligation.
move=> tr1 tr2 valid_pair.
by apply valid_forking_pair_public_reconstruction_cases.
qed.

op bimodal_to_module_sis_lift_obligation (md : mode) : bool =
  forall (x : bimodal_selftarget_msis_instance)
         (sol : bimodal_selftarget_msis_solution),
    bimodal_selftarget_msis_valid md x sol =>
    module_sis_valid md
      (bimodal_to_module_sis_instance md x)
      (bimodal_to_module_sis_solution md x sol).

lemma bimodal_to_module_sis_lift_obligation_holds md :
  bimodal_to_module_sis_lift_obligation md.
proof.
rewrite /bimodal_to_module_sis_lift_obligation.
move=> x sol valid.
by apply bimodal_to_module_sis_valid.
qed.

op special_soundness_obligation (md : mode) : bool =
  forall (tr1 tr2 : transcript),
    valid_forking_pair md tr1 tr2 =>
    extraction_success md tr1 tr2.

op special_soundness_with_public_reconstruction_obligation (md : mode) : bool =
  forall (tr1 tr2 : transcript),
    valid_forking_pair md tr1 tr2 =>
    fork_public_reconstruction_cases md tr1 tr2 /\
    extraction_success md tr1 tr2.

lemma module_sis_extraction_from_bimodal md tr1 tr2 :
  bimodal_extraction_success md tr1 tr2 =>
  bimodal_to_module_sis_lift_obligation md =>
  extraction_success md tr1 tr2.
proof.
rewrite /bimodal_extraction_success /bimodal_to_module_sis_lift_obligation
        /extraction_success /extract_module_sis_solution
        /module_sis_instance_of_fork.
move=> [nz valid] lift.
split.
+ rewrite /extract_module_sis_solution /= ifF.
  + by apply nz.
  by rewrite /=.
rewrite /extract_module_sis_solution /= ifF.
+ by apply nz.
apply (lift (bimodal_selftarget_msis_instance_of_fork md tr1 tr2)
            (oget (extract_bimodal_selftarget_msis_solution md tr1 tr2))).
by apply valid.
qed.

lemma special_soundness_from_bimodal_lift md :
  forking_extraction_obligation md =>
  bimodal_to_module_sis_lift_obligation md =>
  special_soundness_obligation md.
proof.
rewrite /forking_extraction_obligation /special_soundness_obligation.
move=> fork lift tr1 tr2 valid_pair.
by apply module_sis_extraction_from_bimodal; [apply fork | apply lift].
qed.

lemma special_soundness_with_public_reconstruction_from_bimodal_lift md :
  fork_public_reconstruction_obligation md =>
  forking_extraction_obligation md =>
  bimodal_to_module_sis_lift_obligation md =>
  special_soundness_with_public_reconstruction_obligation md.
proof.
rewrite /fork_public_reconstruction_obligation
        /forking_extraction_obligation
        /special_soundness_with_public_reconstruction_obligation.
move=> public fork lift tr1 tr2 valid_pair.
split.
+ by apply public.
by apply module_sis_extraction_from_bimodal; [apply fork | apply lift].
qed.

op transcript_from_honest_signing
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : transcript =
  transcript_of_signature md
    (public_key_of_secret md sk)
    m ctx
    (sign_internal md sk m ctx coins).

lemma honest_transcript_verifies md sk m ctx coins :
  transcript_verifies md
    (transcript_from_honest_signing md sk m ctx coins).
proof.
rewrite /transcript_from_honest_signing /transcript_verifies
        /transcript_of_signature /transcript_pk /transcript_message
        /transcript_context /transcript_signature /=.
by apply verify_internal_sign_internal.
qed.

lemma transcript_of_signature_fields md pk m ctx sig :
  transcript_commitment_highbits
    (transcript_of_signature md pk m ctx sig) =
    sig_commitment_highbits sig /\
  transcript_commitment_lowbits
    (transcript_of_signature md pk m ctx sig) =
    sig_commitment_lowbits sig /\
  transcript_message_hash
    (transcript_of_signature md pk m ctx sig) =
    sig_message_hash sig /\
  transcript_challenge
    (transcript_of_signature md pk m ctx sig) =
    sig_challenge sig.
proof. by rewrite /transcript_of_signature /=. qed.

lemma transcript_of_signature_matches_signature md pk m ctx sig :
  transcript_fields_match_signature
    (transcript_of_signature md pk m ctx sig).
proof.
by rewrite /transcript_fields_match_signature /transcript_of_signature /=.
qed.

lemma honest_transcript_challenge md sk m ctx coins :
  transcript_challenge
    (transcript_from_honest_signing md sk m ctx coins) =
  challenge_hash
    md
    (commitment_highbits md sk m ctx coins)
    (commitment_lowbits md sk m ctx coins)
    (message_hash (public_key_of_secret md sk) ctx m).
proof.
by rewrite /transcript_from_honest_signing /transcript_of_signature
           /signature_challenge /sig_challenge /sign_internal /=.
qed.

end HAETAE_Transcript.
