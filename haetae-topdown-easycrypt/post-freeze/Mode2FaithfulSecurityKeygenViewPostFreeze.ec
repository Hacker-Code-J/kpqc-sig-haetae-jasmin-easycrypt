require import AllCore List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra.
require import Mode2KeygenSnapshotAlgebra.
require import TargetKeygenM23FinalizeComposition.
require import KgFaithfulAugmentedModel
               Mode2FaithfulSecurityExpandVecAPostFreeze
               Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
               Mode2FaithfulSecurityKeygenRelationPostFreeze
               Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.

theory Mode2FaithfulSecurityKeygenViewPostFreeze.

import HAETAE_Params.

(* This file exposes only the public-key view carried by the existing paper
   witnesses.  It does not claim equality with [keygen_internal],
   [public_key_of_secret], any secret-key object, API/scheme equality,
   termination, uniqueness, or any distributional statement. *)

op faithful_mode2_public_key
    (master_sd : HAETAE_Algebra.seed)
    (b1 : HAETAE_Algebra.polyveck) : HAETAE_Algebra.pkey =
  (HAETAE_Algebra.haetae_keygen_rhoprime master_sd, b1).

lemma faithful_mode2_public_key_seedE master_sd b1 :
  (faithful_mode2_public_key master_sd b1).`1 =
  HAETAE_Algebra.haetae_keygen_rhoprime master_sd.
proof. by rewrite /faithful_mode2_public_key. qed.

lemma faithful_mode2_public_key_bodyE master_sd b1 :
  (faithful_mode2_public_key master_sd b1).`2 = b1.
proof. by rewrite /faithful_mode2_public_key. qed.

lemma faithful_mode2_public_key_wf master_sd b1 :
  HAETAE_Algebra.polyveck_wf Mode2 b1 =>
  HAETAE_Algebra.haetae_public_key_unpacked_wf Mode2
    (faithful_mode2_public_key master_sd b1).
proof.
move=> hb1.
rewrite /HAETAE_Algebra.haetae_public_key_unpacked_wf
        /faithful_mode2_public_key.
split.
+ exact (HAETAE_Algebra.haetae_keygen_rhoprime_size master_sd).
+ exact hb1.
qed.

op faithful_mode2_keygen_view
    (pk : HAETAE_Algebra.pkey)
    (sd : HAETAE_Algebra.seed)
    (a b1 : HAETAE_Algebra.polyveck)
    (Agen : HAETAE_Algebra.matrix)
    (sgen : HAETAE_Algebra.poly list)
    (eadj : HAETAE_Algebra.polyveck) : bool =
  Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
    .faithful_mode2_keygen_paper_lift sd a b1 Agen sgen eadj /\
  pk = faithful_mode2_public_key sd b1.

lemma faithful_mode2_keygen_view_as_qj
    pk sd a b1 Agen sgen eadj :
  faithful_mode2_keygen_view pk sd a b1 Agen sgen eadj =>
  forall row coeff,
    0 <= row < 2 =>
    0 <= coeff < 256 =>
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (Mode2FaithfulSecurityKeygenRelationPostFreeze
        .faithful_packaged_matrix_vector_product_coeff
        (Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
          .faithful_kg3_matrix a b1 Agen)
        (Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
          .faithful_kg4_secret sgen eadj)
        row coeff)
      (KgFaithfulAugmentedModel.faithful_qj_coeff row coeff).
proof.
move=> [hview _].
exact
  (Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
    .faithful_mode2_keygen_paper_lift_as_qj
    sd a b1 Agen sgen eadj hview).
qed.

lemma checked_mode2_parent_m23_finalize_faithful_mode2_keygen_view
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
      faithful_mode2_keygen_view pk sd a b1 Agen sgen eadj /\
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
      pk = faithful_mode2_public_key sd b1].
proof.
conseq
  (Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
    .checked_mode2_parent_m23_finalize_faithful_mode2_keygen_paper_lift
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result
  [sd a b1 Agen sgen eadj
    [hlift [hsd [ha [hb1 [hAgen [hsgen headj]]]]]]].
exists (faithful_mode2_public_key sd b1).
exists sd.
exists a.
exists b1.
exists Agen.
exists sgen.
exists eadj.
split.
+ split; first exact hlift.
   trivial.
split; first exact hsd.
split; first exact ha.
split; first exact hb1.
split; first exact hAgen.
split; first exact hsgen.
split; first exact headj.
trivial.
qed.

end Mode2FaithfulSecurityKeygenViewPostFreeze.
