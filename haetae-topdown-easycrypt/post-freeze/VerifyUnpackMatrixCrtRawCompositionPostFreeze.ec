require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 BArray2752 BArray8192 BArray32768 Rq
               RawVerifyApiTarget
               VerifyUnpackV3AssemblyPostFreeze
               VerifyUnpackV3ExpandBoundsPostFreeze
               VerifyUnpackV3FullPostFreeze
               VerifyUnpackV3RawBoundaryPostFreeze
               VerifyMatrixCrtPostFreeze
               VerifyMatrixCrtCompositionPostFreeze
               VerifyMatrixCrtRawBoundaryPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.
import VerifyMatrixCrtPostFreeze VerifyMatrixCrtCompositionPostFreeze.

theory VerifyUnpackMatrixCrtRawCompositionPostFreeze.

module Raw = RawVerifyApiTarget.M.
module RawMatrixCrt =
  VerifyMatrixCrtRawBoundaryPostFreeze.RawVerifyMatrixCrtMode2.

module RawVerifyUnpackThenMatrixCrtMode2 = {
  proc run
      (matp : BArray32768.t, vkp : BArray2752.t, seedu : int,
       z1p : BArray8192.t, highp : BArray8192.t,
       wprimep : BArray1024.t)
      : BArray8192.t * BArray8192.t = {
    matp <@ Raw._unpack_vk_m23_full
      (matp, vkp, seedu,
       W64.of_int mode2_rows,
       W64.of_int mode2_cols,
       W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m);
    (z1p, highp) <@ RawMatrixCrt.run
      (z1p, highp, matp, wprimep);
    return (z1p, highp);
  }
}.

op raw_verify_unpack_matrix_crt_mode2_result
    (vkp0 : BArray2752.t)
    (z10 high0 : BArray8192.t)
    (wprime0 : BArray1024.t)
    (out high : BArray8192.t) : bool =
  exists outbp outmat,
    VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
      vkp0 outbp outmat /\
    verify_matrix_crt_mode2_result
      z10 high0 outmat wprime0 out high.

lemma verify_unpack_tight20_result_matrix_crt_bound
    (vkp0 : BArray2752.t) (outbp : BArray8192.t)
    (outmat : BArray32768.t) :
  VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
    vkp0 outbp outmat =>
  verify_mode2_matrix_repr_bound20_17 outmat.
proof.
move=> htight.
apply (verify_unpack_matrix_profile20_17_to_matrix_crt outmat).
move: htight.
rewrite /VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20.
by move=> [decoded expanded pre_ntt preinstall_mat] />.
qed.

lemma raw_verify_unpack_mode2_tight20_matrix_crt_ready
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0 :
  hoare [Raw._unpack_vk_m23_full :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    k = W64.of_int mode2_rows /\
    l = W64.of_int mode2_cols /\
    m = W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m
    ==>
    (exists outbp,
      VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
        vkp0 outbp res) /\
    verify_mode2_matrix_repr_bound20_17 res].
proof.
conseq
  (VerifyUnpackV3RawBoundaryPostFreeze.raw_verify_unpack_mode2_tight20_correct
    mat0 vkp0 seed0) => //=.
move=> &m _ result [outbp htight].
split.
+ exists outbp.
  exact htight.
exact
  (verify_unpack_tight20_result_matrix_crt_bound
    vkp0 outbp result htight).
qed.

lemma raw_verify_unpack_then_matrix_crt_mode2_tight20_exact
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0
    (z10 high0 : BArray8192.t)
    (wprime0 : BArray1024.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [RawVerifyUnpackThenMatrixCrtMode2.run :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    z1p = z10 /\ highp = high0 /\ wprimep = wprime0 /\
    verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3
    ==>
    raw_verify_unpack_matrix_crt_mode2_result
      vkp0 z10 high0 wprime0 res.`1 res.`2].
proof.
proc.
seq 1 :
  (z1p = z10 /\ highp = high0 /\ wprimep = wprime0 /\
   verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3 /\
   (exists outbp,
     VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
       vkp0 outbp matp) /\
     verify_mode2_matrix_repr_bound20_17 matp).
+ call
    (raw_verify_unpack_mode2_tight20_matrix_crt_ready
      mat0 vkp0 seed0).
  auto => />.
exlim matp => unpacked0.
call
  (VerifyMatrixCrtRawBoundaryPostFreeze.raw_verify_matrix_crt_mode2_fromcrt_freeze_mixed_exact
    z10 high0 unpacked0 wprime0 p0 p1 p2 p3).
auto.
move=> &hr
  [hunpacked [hz1 [hhigh [hwprime [hinput [hunpack hmatrix]]]]]].
split.
+ split; first exact hz1.
  split; first exact hhigh.
  split; first by rewrite hunpacked.
  split; first exact hwprime.
  split; first exact hinput.
  rewrite hunpacked.
  exact hmatrix.
move=> _ result hcrt.
rewrite /raw_verify_unpack_matrix_crt_mode2_result.
move: hunpack => [outbp htight].
exists outbp unpacked0.
split.
+ rewrite hunpacked.
  exact htight.
exact hcrt.
qed.

end VerifyUnpackMatrixCrtRawCompositionPostFreeze.
