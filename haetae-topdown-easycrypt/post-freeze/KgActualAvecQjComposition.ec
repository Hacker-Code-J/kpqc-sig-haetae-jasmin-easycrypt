require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import KeygenSamplerCallersSpec
               KeygenM23MatrixSpec KeygenM23FinalizeArraySemantics.
require import TargetKeygenM23FinalizeComposition
               TargetKeygenM23FinalizeSemanticComposition.
require import Mode2KeygenCoreEquation Mode2KeygenSnapshotAlgebra.
require import KgActualAvecQjSemantics.

theory KgActualAvecQjComposition.

op actual_paper_mode2_a
    (avec : BArray8192.t) (seedbuf : BArray128.t) : bool =
  forall row coeff,
    0 <= row < 2 =>
    0 <= coeff < 256 =>
    KgActualAvecQjSemantics.paper_mode2_a_coeff
      seedbuf row coeff
      (W32.to_uint
        (BArray8192.get32 avec (row * 256 + coeff))).

lemma mode2_sampler_facts_actual_paper_a
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  TargetKeygenM23FinalizeComposition.mode2_sampler_facts
    seedbuf mat avec s1 s2 counter mat0 avec0 s10 s20 raw_seed0 =>
  actual_paper_mode2_a avec seedbuf.
proof.
move=> hf.
have hstream :
    KeygenSamplerCallersSpec.uniform_vector_stream8192
      avec seedbuf 2 3 2.
+ move: hf.
  rewrite /TargetKeygenM23FinalizeComposition.mode2_sampler_facts
          /KeygenSamplerCallersSpec.mode2_k_i
          /KeygenSamplerCallersSpec.mode2_m_i.
  smt().
rewrite /actual_paper_mode2_a.
move=> row coeff hrow hcoeff.
exact (KgActualAvecQjSemantics.mode2_uniform_stream_paper_a_flat
  avec seedbuf row coeff hstream hrow hcoeff).
qed.

(* This is the coefficient expansion of the paper augmented key equation at
   the finalizer snapshot.  It adds the independent q*j term to the already
   proved zero congruence; it does not assume KG-3, KG-4, or As=qj. *)
op actual_snapshot_paper_qj
    (pre_bp sampled_s2 a b1 adjusted : BArray8192.t) : bool =
  forall row coeff,
    0 <= row < 2 =>
    0 <= coeff < 256 =>
    let i = row * 256 + coeff in
    Mode2KeygenSnapshotAlgebra.congruent_mod_2q
      (2 * (W32.to_uint (BArray8192.get32 a i) -
              2 * W32.to_uint (BArray8192.get32 b1 i)) +
       KgActualAvecQjSemantics.paper_qj_coeff row coeff +
       2 * W32.to_sint (BArray8192.get32 pre_bp i) +
       2 * W32.to_sint (BArray8192.get32 adjusted i))
      (KgActualAvecQjSemantics.paper_qj_coeff row coeff).

lemma actual_snapshot_zero_adds_paper_qj
    (pre_bp sampled_s2 a b1 adjusted : BArray8192.t) :
  Mode2KeygenCoreEquation.actual_snapshot_mod2q_zero
    pre_bp sampled_s2 a b1 adjusted =>
  actual_snapshot_paper_qj pre_bp sampled_s2 a b1 adjusted.
proof.
move=> hzero.
rewrite /actual_snapshot_paper_qj.
move=> row coeff hrow hcoeff /=.
have hi : 0 <= row * 256 + coeff <
    KeygenM23MatrixSpec.mode2_b_words_i.
+ move: hrow hcoeff.
  rewrite /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i.
  smt().
have hz := hzero (row * 256 + coeff) hi.
move: hz.
rewrite /Mode2KeygenSnapshotAlgebra.congruent_mod_2q.
move=> hz.
rewrite /Mode2KeygenSnapshotAlgebra.congruent_mod_2q.
have -> :
    2 *
        (W32.to_uint
           (BArray8192.get32 a (row * 256 + coeff)) -
         2 * W32.to_uint
           (BArray8192.get32 b1 (row * 256 + coeff))) +
      KgActualAvecQjSemantics.paper_qj_coeff row coeff +
      2 * W32.to_sint
        (BArray8192.get32 pre_bp (row * 256 + coeff)) +
      2 * W32.to_sint
        (BArray8192.get32 adjusted (row * 256 + coeff)) -
      KgActualAvecQjSemantics.paper_qj_coeff row coeff =
    2 *
        (W32.to_uint
           (BArray8192.get32 a (row * 256 + coeff)) -
         2 * W32.to_uint
           (BArray8192.get32 b1 (row * 256 + coeff))) +
      2 * W32.to_sint
        (BArray8192.get32 pre_bp (row * 256 + coeff)) +
      2 * W32.to_sint
        (BArray8192.get32 adjusted (row * 256 + coeff)) by ring.
exact hz.
qed.

lemma checked_mode2_parent_m23_finalize_actual_avec_qj
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
    actual_paper_mode2_a res.`3 res.`1 /\
    actual_snapshot_paper_qj
      res.`7 res.`5 res.`3 res.`9 res.`10].
proof.
conseq
  (TargetKeygenM23FinalizeSemanticComposition.checked_mode2_parent_m23_finalize_semantic_correct
       seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
move=> &hr _ result [hsampler [hm23 [hfinal hsemantic]]].
split.
+ exact (mode2_sampler_facts_actual_paper_a
    result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
    mat0 avec0 s10 s20 raw_seed0 hsampler).
have hzero :=
  Mode2KeygenCoreEquation.finalize_semantic_output_snapshot_mod2q_zero
    result.`7 result.`5 result.`3 result.`9 result.`10 hsemantic.
exact (actual_snapshot_zero_adds_paper_qj
  result.`7 result.`5 result.`3 result.`9 result.`10 hzero).
qed.

end KgActualAvecQjComposition.
