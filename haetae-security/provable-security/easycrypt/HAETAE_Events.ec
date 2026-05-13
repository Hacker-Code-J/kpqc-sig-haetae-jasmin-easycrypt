require import AllCore.
require import HAETAE_Params HAETAE_Algebra.

theory HAETAE_Events.

import HAETAE_Params.
import HAETAE_Algebra.

op keygen_rejection_failure (md : mode) (pk : pkey) (sk : skey) : bool =
  ! valid_keypair md pk sk \/ ! secret_norm_ok md sk.

op signing_rejection_failure (md : mode) (sig : signature) : bool =
  ! valid_signature md sig \/ ! response_norm_ok md sig.

op verification_rejection_failure (md : mode) (sig : signature) : bool =
  ! valid_signature md sig \/ ! verify_norm_ok md sig.

op any_rejection_failure (md : mode) (pk : pkey) (sk : skey)
                         (sig : signature) : bool =
  keygen_rejection_failure md pk sk \/
  signing_rejection_failure md sig \/
  verification_rejection_failure md sig.

lemma keygen_rejection_free_current md sd :
  ! keygen_rejection_failure md (keygen_internal md sd).`1
      (keygen_internal md sd).`2.
proof.
by rewrite /keygen_rejection_failure /valid_keypair /secret_norm_ok
           /secret_norm_sq /keygen_internal /secret_key_of_seed; case md.
qed.

lemma signing_rejection_free_current md sk m ctx coins :
  ! signing_rejection_failure md (sign_internal md sk m ctx coins).
proof.
rewrite /signing_rejection_failure.
rewrite valid_signature_sign_internal response_norm_ok_current.
by rewrite /=.
qed.

lemma verification_rejection_free_current md sk m ctx coins :
  ! verification_rejection_failure md (sign_internal md sk m ctx coins).
proof.
rewrite /verification_rejection_failure.
rewrite valid_signature_sign_internal verify_norm_ok_current.
by rewrite /=.
qed.

lemma accepted_transcript_rejection_free_current md sd m ctx coins :
  ! any_rejection_failure md (keygen_internal md sd).`1
      (keygen_internal md sd).`2
      (sign_internal md (keygen_internal md sd).`2 m ctx coins).
proof.
by rewrite /any_rejection_failure keygen_rejection_free_current
           signing_rejection_free_current verification_rejection_free_current.
qed.

end HAETAE_Events.
