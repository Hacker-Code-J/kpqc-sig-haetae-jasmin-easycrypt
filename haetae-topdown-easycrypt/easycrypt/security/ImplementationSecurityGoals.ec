require import AllCore Real.

theory ImplementationSecurityGoals.

op delta_keygen : real.
op delta_sign : real.
op delta_verify : real.
op delta_encoding : real.
op qsign : int.
op jasmin_adv : real.
op paper_adv : real.

op nonnegative_refinement_losses : bool =
  0%r <= delta_keygen /\ 0%r <= delta_sign /\
  0%r <= delta_verify /\ 0%r <= delta_encoding.

op implementation_to_paper_bound : bool =
  0 <= qsign /\
  jasmin_adv <= paper_adv + delta_keygen +
    qsign%r * delta_sign + delta_verify + delta_encoding.

(* These are proof obligations, deliberately not exported assumptions. *)
op obl_public_key_algebra_ntt : bool.
op obl_sampler_distribution : bool.
op obl_signing_accepted_distribution : bool.
op obl_challenge_encoding_entropy : bool.
op obl_fips202_byte_transcripts : bool.
op obl_two_transcript_extraction : bool.
op obl_public_api_composition : bool.
op obl_canonical_packing : bool.
op obl_memory_contract : bool.
op obl_retry_loss : bool.
op obl_fft_tie_policy : bool.

op implementation_security_obligations : bool =
  obl_public_key_algebra_ntt /\
  obl_sampler_distribution /\
  obl_signing_accepted_distribution /\
  obl_challenge_encoding_entropy /\
  obl_fips202_byte_transcripts /\
  obl_two_transcript_extraction /\
  obl_public_api_composition /\
  obl_canonical_packing /\
  obl_memory_contract /\
  obl_retry_loss /\
  obl_fft_tie_policy.

end ImplementationSecurityGoals.
