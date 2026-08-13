require import AllCore IntDiv List.

require import HAETAE_Params HAETAE_Algebra.
require import KeygenM23FinalizeSemantics.
require import KgActualAvecQjSemantics.

theory KgActualAvecQjBlocker.

(* Despite its name, the current security-side object is the synthetic
   [public_rounding_vector_seed], not the paper q*j vector and not the actual
   SHAKE128/rejection expansion.  Its first two constant coefficients do not
   depend on the seed. *)
lemma security_named_qj_mode2_row0_coeff0 (sd : HAETAE_Algebra.seed) :
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (HAETAE_Algebra.haetae_mode23_qj_vector
        HAETAE_Params.Mode2 sd) 0) 0 = 401.
proof.
rewrite /HAETAE_Algebra.haetae_mode23_qj_vector
        /HAETAE_Algebra.public_rounding_vector_seed
        /HAETAE_Algebra.public_key_seed_polyveck
        /HAETAE_Algebra.poly_coeff
        nth_mkseq 1:/# /=
        /HAETAE_Algebra.public_key_seed_poly
        nth_mkseq 1:/# /=
        /HAETAE_Algebra.coeff_mod
        /HAETAE_Params.q.
by rewrite modz_small.
qed.

lemma security_named_qj_mode2_row1_coeff0 (sd : HAETAE_Algebra.seed) :
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (HAETAE_Algebra.haetae_mode23_qj_vector
        HAETAE_Params.Mode2 sd) 1) 0 = 403.
proof.
rewrite /HAETAE_Algebra.haetae_mode23_qj_vector
        /HAETAE_Algebra.public_rounding_vector_seed
        /HAETAE_Algebra.public_key_seed_polyveck
        /HAETAE_Algebra.poly_coeff
        nth_mkseq 1:/# /=
        /HAETAE_Algebra.public_key_seed_poly
        nth_mkseq 1:/# /=
        /HAETAE_Algebra.coeff_mod
        /HAETAE_Params.q.
by rewrite modz_small.
qed.

lemma security_named_qj_is_not_paper_qj
    (sd : HAETAE_Algebra.seed) :
  HAETAE_Algebra.poly_coeff
    (nth HAETAE_Algebra.poly_zero
      (HAETAE_Algebra.haetae_mode23_qj_vector
        HAETAE_Params.Mode2 sd) 0) 0 <>
  KgActualAvecQjSemantics.paper_qj_coeff 0 0.
proof.
rewrite security_named_qj_mode2_row0_coeff0
        KgActualAvecQjSemantics.paper_qj_row0_coeff0
        /KeygenM23FinalizeSemantics.q.
trivial.
qed.

end KgActualAvecQjBlocker.
