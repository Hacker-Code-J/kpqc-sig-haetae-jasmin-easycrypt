require import RefJasminNTT.
require import AllCore IntDiv Ring StdOrder BitEncoding.
from Jasmin require import JWord JModel_x86.
import SLH64.
require import Fq GFq NTT_Fq Hpoly_extract.
import Zq.

theory ProbeFqmulGeneric.

lemma fqmul_word_to_coeff_mul_h_probe aa bb :
  hoare [Hpoly_extract.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb <
      Fq.SignedReductions.R %/ 2 * Fq.q ==>
    NTT_Fq.word_to_coeff res = incoeff aa * incoeff bb * inv NTT_Fq.R].
proof.
conseq (Fq.fqmul_corr_h aa bb).
+ by smt().
move=> &hr [Ha [Hb Hbound]] result Hres /=.
rewrite /NTT_Fq.word_to_coeff Hres RefJasminNTT.inv_R_ref -!incoeffM.
apply/eq_incoeff.
rewrite !incoeffK qE /=.
have hq : 0 < Fq.q < Fq.SignedReductions.R %/ 2.
+ by rewrite /Fq.q /Fq.SignedReductions.R /=.
have hs := Fq.SignedReductions.SREDCp_corr (aa * bb) hq Hbound.
move: hs => [_ hsmod].
rewrite /Fq.q in hsmod.
rewrite hsmod.
smt(modzMml modzMmr).
qed.

lemma fqmul_word_to_coeff_mul_bound_probe aa bb :
  - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb <
    Fq.SignedReductions.R %/ 2 * Fq.q =>
  hoare [Hpoly_extract.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    NTT_Fq.word_to_coeff res = incoeff aa * incoeff bb * inv NTT_Fq.R /\
    Fq.bw32 res 16].
proof.
move=> hbound.
conseq
  (RefJasminNTT.fqmul_word_to_coeff_mul aa bb hbound)
  (RefJasminNTT.fqmul_bw32_16 aa bb hbound).
+ by smt().
qed.

lemma fqmul_word_to_coeff_mul_bound_h_probe aa bb :
  hoare [Hpoly_extract.M.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb <
      Fq.SignedReductions.R %/ 2 * Fq.q ==>
    NTT_Fq.word_to_coeff res = incoeff aa * incoeff bb * inv NTT_Fq.R /\
    Fq.bw32 res 16].
proof.
conseq
  (fqmul_word_to_coeff_mul_h_probe aa bb)
  (_: W32.to_sint a = aa /\ W32.to_sint b = bb /\
      - Fq.SignedReductions.R %/ 2 * Fq.q <= aa * bb <
      Fq.SignedReductions.R %/ 2 * Fq.q ==> Fq.bw32 res 16).
+ by smt().
conseq (Fq.fqmul_corr_h aa bb).
+ by smt().
move=> &hr [Ha [Hb Hbound]] result Hres /=.
rewrite /Fq.bw32.
have hq : 0 < Fq.q < Fq.SignedReductions.R %/ 2.
+ by rewrite /Fq.q /Fq.SignedReductions.R /=.
have hs := Fq.SignedReductions.SREDCp_corr (aa * bb) hq Hbound.
rewrite Hres.
have hq16 : Fq.q < 2^16 by rewrite /Fq.q /=.
have hs' : -Fq.q <= Fq.SignedReductions.SREDC (aa * bb) < Fq.q by have := hs; smt().
by smt().
qed.

end ProbeFqmulGeneric.
