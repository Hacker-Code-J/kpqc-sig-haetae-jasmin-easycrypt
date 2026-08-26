require import AllCore List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra HAETAE_Scheme.
require import Mode2KeygenSnapshotAlgebra.
require import TargetKeygenM23FinalizeComposition.
require import KgFaithfulAugmentedModel
               Mode2FaithfulSecurityExpandVecAPostFreeze
               Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
               Mode2FaithfulSecurityKeygenRelationPostFreeze
               Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
               Mode2FaithfulSecurityKeygenViewPostFreeze.

theory Mode2FaithfulSecurityNMAViewAdapterPostFreeze.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Scheme.

(* This adapter exposes only the public-key/NMA view.  It does not identify
   with [HAETAE], [keygen_internal], [public_key_of_secret], any actual key
   distribution, any CMA interface, or any secret-key semantics.  The sign
   procedure below is a placeholder because [SIG.UF_NMA] never calls it. *)

op nma_public_only_dummy_seed : seed = nseq seedbytes 0.

op nma_public_only_dummy_skey : skey =
  (nma_public_only_dummy_seed, 0).

op nma_public_only_dummy_sig : signature =
  (polyveck_zero Mode2,
   poly_zero,
   [],
   poly_zero,
   (polyvecl_zero Mode2, polyveck_zero Mode2, polyveck_zero Mode2),
   0, 0).

op faithful_mode2_nma_ready
    (pk : pkey)
    (sd : seed)
    (a b1 : polyveck)
    (Agen : matrix)
    (sgen : poly list)
    (eadj : polyveck) : bool =
  Mode2FaithfulSecurityKeygenViewPostFreeze
    .faithful_mode2_keygen_view pk sd a b1 Agen sgen eadj /\
  haetae_public_key_unpacked_wf Mode2 pk.

op faithful_mode2_nma_product_coeff
    (a b1 : polyveck)
    (Agen : matrix)
    (sgen : poly list)
    (eadj : polyveck)
    row coeff : int =
  Mode2FaithfulSecurityKeygenRelationPostFreeze
    .faithful_packaged_matrix_vector_product_coeff
    (Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
      .faithful_kg3_matrix a b1 Agen)
    (Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
      .faithful_kg4_secret sgen eadj)
    row coeff.

lemma faithful_mode2_nma_ready_as_qj
    (pk : pkey) (sd : seed)
    (a b1 : polyveck)
    (Agen : matrix)
    (sgen : poly list)
    (eadj : polyveck) :
  faithful_mode2_nma_ready pk sd a b1 Agen sgen eadj =>
  forall row coeff,
    0 <= row < 2 =>
    0 <= coeff < 256 =>
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (faithful_mode2_nma_product_coeff
        a b1 Agen sgen eadj row coeff)
      (KgFaithfulAugmentedModel.faithful_qj_coeff row coeff).
proof.
move=> [hview _].
exact
  (Mode2FaithfulSecurityKeygenViewPostFreeze
    .faithful_mode2_keygen_view_as_qj
    pk sd a b1 Agen sgen eadj hview).
qed.

lemma faithful_mode2_nma_ready_pk_wf
    (pk : pkey) (sd : seed)
    (a b1 : polyveck)
    (Agen : matrix)
    (sgen : poly list)
    (eadj : polyveck) :
  faithful_mode2_nma_ready pk sd a b1 Agen sgen eadj =>
  haetae_public_key_unpacked_wf Mode2 pk.
proof.
by move=> [_ hpk].
qed.

lemma checked_mode2_parent_m23_finalize_faithful_mode2_nma_ready
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [
    TargetKeygenM23FinalizeComposition.CheckedMode2ParentM23Finalize.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0
    ==>
    exists pk sd a b1 Agen sgen eadj,
      faithful_mode2_nma_ready pk sd a b1 Agen sgen eadj /\
      sd =
        Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
          .raw_security_seed raw_seed0 /\
      a =
        Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
          res.`3 /\
      b1 =
        Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
          res.`9 /\
      Agen =
        Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.actual_Agen
          res.`2 /\
      sgen =
        Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.actual_sgen
          res.`4 /\
      eadj =
        Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.actual_eadj
          res.`10 /\
      pk =
        Mode2FaithfulSecurityKeygenViewPostFreeze
          .faithful_mode2_public_key sd b1].
proof.
conseq
  (Mode2FaithfulSecurityKeygenViewPostFreeze
    .checked_mode2_parent_m23_finalize_faithful_mode2_keygen_view
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result
  [pk sd a b1 Agen sgen eadj
    [hview [hsd [ha [hb1 [hAgen [hsgen [headj hpk]]]]]]]].
have hb1wf : polyveck_wf Mode2 b1.
+ move:
    (Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca_wf
      result.`9).
  by rewrite -hb1.
have hpkwf : haetae_public_key_unpacked_wf Mode2 pk.
+ rewrite hpk.
  exact
    (Mode2FaithfulSecurityKeygenViewPostFreeze.faithful_mode2_public_key_wf
      sd b1 hb1wf).
exists pk.
exists sd.
exists a.
exists b1.
exists Agen.
exists sgen.
exists eadj.
split.
+ split; first exact hview.
   exact hpkwf.
split; first exact hsd.
split; first exact ha.
split; first exact hb1.
split; first exact hAgen.
split; first exact hsgen.
split; first exact headj.
exact hpk.
qed.

module type PublicKeySource = {
  proc sample() : pkey
}.

module NMAViewScheme(Src : PublicKeySource) (H : SIG.POracle) = {
  proc kg() : pkey * skey = {
    var pk : pkey;

    pk <@ Src.sample();
    return (pk, nma_public_only_dummy_skey);
  }

  proc sign(sk : skey, m : message, ctx : context) : signature = {
    return nma_public_only_dummy_sig;
  }

  proc verify(pk : pkey, m : message, ctx : context,
              sig : signature) : bool = {
    return verify_internal Mode2 pk m ctx sig;
  }
}.

module DirectPublicOnlyUFNMA
    (H : SIG.Oracle, Src : PublicKeySource, A : SIG.NMA_Adversary) = {
  module A = A(H)

  proc main() : bool = {
    var pk : pkey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    pk <@ Src.sample();
    (m, ctx, sig) <@ A.forge(pk);
    ok <- verify_internal Mode2 pk m ctx sig;
    return ok;
  }
}.

section PublicOnlyNMAExact.

declare module H <: SIG.Oracle {-SIG.UF_NMA, -DirectPublicOnlyUFNMA}.
declare module Src <: PublicKeySource {-H, -SIG.UF_NMA, -DirectPublicOnlyUFNMA}.
declare module A <: SIG.NMA_Adversary {-H, -Src, -SIG.UF_NMA,
                                       -DirectPublicOnlyUFNMA}.

lemma public_only_nma_equiv :
  equiv [SIG.UF_NMA(H, NMAViewScheme(Src), A).main ~
         DirectPublicOnlyUFNMA(H, Src, A).main :
    ={glob H, glob Src, glob A} ==> ={res}].
proof.
proc.
inline NMAViewScheme(Src, H).kg
       NMAViewScheme(Src, H).verify.
wp.
call (: ={glob H, glob Src, glob A, arg}
        ==> ={glob H, glob Src, glob A, res}).
+ by sim.
wp.
call (: ={glob H, glob Src, arg} ==> ={glob H, glob Src, res}).
+ by sim.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />.
qed.

lemma public_only_nma_wrapper_direct_exact &m :
  Pr[SIG.UF_NMA(H, NMAViewScheme(Src), A).main() @ &m : res] =
  Pr[DirectPublicOnlyUFNMA(H, Src, A).main() @ &m : res].
proof.
byequiv public_only_nma_equiv => //.
qed.

end section PublicOnlyNMAExact.

end Mode2FaithfulSecurityNMAViewAdapterPostFreeze.
