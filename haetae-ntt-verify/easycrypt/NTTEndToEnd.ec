require import AllCore IntDiv List Ring StdOrder BitEncoding.

require import Array256.
require import GFq Rq.
require import NTT_Fq NTTFullSpec NTTFullAlgebra RefJasminNTT.
require import Hpoly_extract.

import Zq IntOrder BitReverse.

theory NTTEndToEnd.

type poly = coeff Array256.t.

op jasmin_ntt_full_post (rp : BArray1024.t) (p : poly) =
  NTT_Fq.poly_repr_bound rp (NTTFullSpec.full_ntt p) 24.

op jasmin_invntt_full_post (rp : BArray1024.t) (p : poly) =
  NTT_Fq.poly_repr_bound rp
    (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16.

lemma full_ntt_post_from_core rp r p :
  NTT_Fq.poly_repr_bound rp r 24 =>
  r = NTTFullSpec.full_ntt p =>
  jasmin_ntt_full_post rp p.
proof. by move=> h heq; rewrite /jasmin_ntt_full_post -heq. qed.

lemma full_invntt_post_from_core rp r p :
  NTT_Fq.poly_repr_bound rp (NTT_Fq.array256_mont r) 16 =>
  r = NTTFullSpec.full_invntt p =>
  jasmin_invntt_full_post rp p.
proof. by move=> h heq; rewrite /jasmin_invntt_full_post -heq. qed.

lemma jasmin_ntt_full_from_core_and_alg p :
  hoare [NTT_Fq.NTT.ntt :
    arg = (p, NTT_Fq.zetas) ==> res = NTTFullSpec.full_ntt p] =>
  hoare [Hpoly_extract.M._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 16 ==> jasmin_ntt_full_post res p].
proof.
move=> hntt.
conseq (_:
  NTT_Fq.poly_repr_bound rp p 16 ==>
  NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24).
by conseq RefJasminNTT.poly_ntt_core_ref hntt => /#.
qed.

lemma jasmin_ntt_full p :
  hoare [Hpoly_extract.M._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 16 ==> jasmin_ntt_full_post res p].
proof.
by apply jasmin_ntt_full_from_core_and_alg; apply NTTFullAlgebra.ntt_full_ntt.
qed.

lemma jasmin_poly_ntt_jazz_full p :
  hoare [Hpoly_extract.M.poly_ntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==> jasmin_ntt_full_post res p].
proof.
by conseq RefJasminNTT.poly_ntt_jazz_ref (jasmin_ntt_full p) => /#.
qed.

lemma jasmin_invntt_full_from_core_and_alg p :
  hoare [NTT_Fq.NTT.invntt :
    arg = (p, NTT_Fq.zetas_inv) ==> res = NTTFullSpec.full_invntt p] =>
  hoare [Hpoly_extract.M._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 16 ==> jasmin_invntt_full_post res p].
proof.
move=> hinvntt.
conseq (_:
  NTT_Fq.poly_repr_bound rp p 16 ==>
  NTT_Fq.poly_repr_bound res (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16).
by conseq RefJasminNTT.poly_invntt_core_ref hinvntt => /#.
qed.

lemma jasmin_invntt_full p :
  hoare [Hpoly_extract.M._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 16 ==> jasmin_invntt_full_post res p].
proof.
by apply jasmin_invntt_full_from_core_and_alg; apply NTTFullAlgebra.invntt_full_invntt.
qed.

lemma jasmin_poly_invntt_jazz_full p :
  hoare [Hpoly_extract.M.poly_invntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==> jasmin_invntt_full_post res p].
proof.
by conseq RefJasminNTT.poly_invntt_jazz_ref (jasmin_invntt_full p) => /#.
qed.

lemma haetae_jasmin_ntt_correct p :
  hoare [Hpoly_extract.M.poly_ntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24].
proof.
by conseq (jasmin_poly_ntt_jazz_full p) => /#.
qed.

lemma haetae_jasmin_invntt_correct p :
  hoare [Hpoly_extract.M.poly_invntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
proof.
by conseq (jasmin_poly_invntt_jazz_full p) => /#.
qed.

end NTTEndToEnd.
