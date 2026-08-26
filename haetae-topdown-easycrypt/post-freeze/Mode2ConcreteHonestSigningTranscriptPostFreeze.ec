require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget
               SignChallengeM23CarrierBridgePostFreeze
               Mode2ChallengeROMProgrammingPostFreeze
               HAETAE_Algebra HAETAE_Params
               HAETAE_ROM_Programming HAETAE_Transcript.

theory Mode2ConcreteHonestSigningTranscriptPostFreeze.

import HAETAE_Algebra.
import HAETAE_Params.
import HAETAE_ROM_Programming.
import HAETAE_Transcript.

(* Programming-site adapter only.  It keeps the abstract honest signature's
   commitment, message hash, response, and auxiliary fields, but replaces its
   challenge with the generated raw Sign challenge.  Consequently this file
   does not claim that the patched signature verifies, equals sign_internal,
   or is emitted by the full raw signing API.  It also makes no termination,
   SHAKE-randomness, dmode2-distribution, or challenge_from_seed claim. *)

module RawSign = RawSignApiTarget.M.

op mode2_highlen : int =
  SignChallengeM23CarrierBridgePostFreeze.mode2_highlen.

op mode2_tau : int =
  SignChallengeM23CarrierBridgePostFreeze.mode2_tau.

op mu32_prefix =
  SignChallengeM23CarrierBridgePostFreeze.mu32_prefix.

op challenge_of_barray =
  SignChallengeM23CarrierBridgePostFreeze.challenge_of_barray.

op valid_mode2_carrier_challenge =
  SignChallengeM23CarrierBridgePostFreeze.valid_mode2_carrier_challenge.

op signature_with_challenge
    (sig : signature) (ch : challenge) : signature =
  (sig_commitment_highbits sig,
   sig_commitment_lowbits sig,
   sig_message_hash sig,
   ch,
   sig_token_value sig,
   sig.`6,
   sig.`7).

op concrete_honest_signature_mode2
    (sk : skey) (m : message) (ctx : context)
    (coins : random_coins) (cp_raw : BArray1024.t) : signature =
  signature_with_challenge
    (sign_internal Mode2 sk m ctx coins)
    (challenge_of_barray cp_raw).

op concrete_honest_transcript_mode2
    (sk : skey) (m : message) (ctx : context)
    (coins : random_coins) (cp_raw : BArray1024.t) : transcript =
  transcript_of_signature Mode2
    (public_key_of_secret Mode2 sk) m ctx
    (concrete_honest_signature_mode2 sk m ctx coins cp_raw).

op concrete_honest_programming_site_mode2
    (sk : skey) (m : message) (ctx : context)
    (coins : random_coins) (cp_raw : BArray1024.t) : programming_site =
  actual_signature_programming_site Mode2
    (concrete_honest_transcript_mode2 sk m ctx coins cp_raw).

lemma signature_with_challenge_challengeE sig ch :
  sig_challenge (signature_with_challenge sig ch) = ch.
proof. by rewrite /signature_with_challenge /sig_challenge. qed.

lemma concrete_honest_transcript_mode2_challengeE
    sk m ctx coins cp_raw :
  transcript_challenge
    (concrete_honest_transcript_mode2 sk m ctx coins cp_raw) =
  challenge_of_barray cp_raw.
proof.
by rewrite /concrete_honest_transcript_mode2
           /transcript_of_signature /signature_challenge
           signature_with_challenge_challengeE.
qed.

lemma concrete_honest_transcript_mode2_fields_match
    sk m ctx coins cp_raw :
  transcript_fields_match_signature
    (concrete_honest_transcript_mode2 sk m ctx coins cp_raw).
proof.
rewrite /concrete_honest_transcript_mode2.
exact
  (transcript_of_signature_matches_signature Mode2
    (public_key_of_secret Mode2 sk) m ctx
    (concrete_honest_signature_mode2 sk m ctx coins cp_raw)).
qed.

lemma fields_match_actual_signature_programming_site md tr :
  transcript_fields_match_signature tr =>
  programming_site_matches_transcript md tr
    (actual_signature_programming_site md tr).
proof.
move=> hfields.
rewrite /programming_site_matches_transcript
        /actual_signature_programming_site
        /signature_programming_site_of_transcript
        /programming_site_query /programming_site_output /=.
split.
+ apply eq_sym.
  exact
    (transcript_fields_match_signature_challenge_query md tr hfields).
+ rewrite
    (transcript_fields_match_signature_challenge_matches tr
      (transcript_signature_challenge_output tr) hfields).
  exact (transcript_signature_challenge_output_matches tr).
qed.

lemma concrete_honest_transcript_mode2_actual_site_matches
    sk m ctx coins cp_raw :
  programming_site_matches_transcript Mode2
    (concrete_honest_transcript_mode2 sk m ctx coins cp_raw)
    (concrete_honest_programming_site_mode2 sk m ctx coins cp_raw).
proof.
rewrite /concrete_honest_programming_site_mode2.
apply fields_match_actual_signature_programming_site.
exact
  (concrete_honest_transcript_mode2_fields_match
    sk m ctx coins cp_raw).
qed.

lemma concrete_honest_transcript_mode2_actual_site_no_failure
    sk m ctx coins cp_raw :
  valid_mode2_carrier_challenge (challenge_of_barray cp_raw) =>
  ! Mode2ChallengeROMProgrammingPostFreeze.mode2_fs_with_aborts_failure
      (concrete_honest_transcript_mode2 sk m ctx coins cp_raw)
      (concrete_honest_programming_site_mode2 sk m ctx coins cp_raw).
proof.
move=> hvalid.
apply
  (Mode2ChallengeROMProgrammingPostFreeze.mode2_fs_with_aborts_no_failure_for_site
    (concrete_honest_transcript_mode2 sk m ctx coins cp_raw)
    (concrete_honest_programming_site_mode2 sk m ctx coins cp_raw)).
+ exact
    (concrete_honest_transcript_mode2_actual_site_matches
      sk m ctx coins cp_raw).
+ rewrite concrete_honest_transcript_mode2_challengeE.
  exact hvalid.
qed.

lemma raw_sign_challenge_m23_concrete_honest_site_no_failure
    (mu0 : BArray32.t) (sk : skey) (m : message) (ctx : context)
    (coins : random_coins) :
  hoare [RawSign.__sign_challenge_m23 :
    tau = W64.of_int mode2_tau /\
    highlen = W64.of_int mode2_highlen /\
    mu32_prefix mup mu0
    ==>
    ! Mode2ChallengeROMProgrammingPostFreeze.mode2_fs_with_aborts_failure
        (concrete_honest_transcript_mode2 sk m ctx coins res)
        (concrete_honest_programming_site_mode2 sk m ctx coins res)].
proof.
conseq
  (SignChallengeM23CarrierBridgePostFreeze.raw_sign_challenge_m23_mode2_valid_carrier
    mu0).
move=> &hr _ result hvalid.
exact
  (concrete_honest_transcript_mode2_actual_site_no_failure
    sk m ctx coins result hvalid).
qed.

end Mode2ConcreteHonestSigningTranscriptPostFreeze.
