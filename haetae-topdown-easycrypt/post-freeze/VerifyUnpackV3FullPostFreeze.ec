require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray8192 BArray32768 VerifyUnpackMode2Target
  KeygenM23ArithmeticSpec KeygenM23MatrixSpec NTTRowProductSpec
  VerifyUnpackVkM23CoefficientsPostFreeze VerifyUnpackVkM23BoundsPostFreeze
  VerifyUnpackV3AssemblyPostFreeze VerifyUnpackV3ExpandBoundsPostFreeze
  VerifyUnpackV3PreNttPostFreeze VerifyUnpackV3PreNttBoundPostFreeze
  VerifyUnpackV3NttBound17PostFreeze VerifyUnpackV3NttInstallPostFreeze
  VerifyUnpackV3MatrixProfilePostFreeze
  VerifyUnpackV3SourceBoundPostFreeze
  VerifyUnpackV3PostDecodeThroughNttPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3FullPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

op verify_unpack_mode2_result
    (vkp0 : BArray2752.t) (outbp : BArray8192.t)
    (outmat : BArray32768.t) : bool =
  exists decoded expanded pre_ntt preinstall_mat,
    VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
      decoded vkp0 mode2_vec_words /\
    VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound
      expanded /\
    VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
      vkp0 preinstall_mat pre_ntt mode2_vec_words /\
    mat_firstcol_frame expanded preinstall_mat /\
    VerifyUnpackV3MatrixProfilePostFreeze.unpack_matrix_nonfirst_bound17
      preinstall_mat /\
    VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
      pre_ntt
      (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
      (KeygenM23ArithmeticSpec.wide_poly
        pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
    VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
      outbp
      (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
      (KeygenM23ArithmeticSpec.wide_poly
        pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
    NTTRowProductSpec.vector_forward_repr
      VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_polys
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          outbp (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          pre_ntt (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      pre_ntt outbp
        VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_words /\
    mat_firstcol_install_prefix outbp outmat mode2_vec_words /\
    mat_firstcol_install_frame
      preinstall_mat outmat mode2_vec_words /\
    VerifyUnpackV3MatrixProfilePostFreeze.verify_unpack_mode2_matrix_repr_bound25_17
      outmat.

module StructuredVerifyUnpackMode2 = {
  proc run (matp : BArray32768.t, vkp : BArray2752.t, seedu : int)
      : BArray8192.t * BArray32768.t = {
    var bp : BArray8192.t;
    bp <- witness;
    bp <@ Verify.__unpack_vk_m23_coeffs
      (bp, vkp, W64.of_int mode2_rows);
    matp <@ Verify.__polymatkl_expand_matA_with_vecA
      (matp, seedu,
       W64.of_int mode2_rows,
       W64.of_int mode2_cols,
       W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m);
    (bp, matp) <@
      VerifyUnpackV3PostDecodeThroughNttPostFreeze.ActualVerifyUnpackPostDecodeThroughNttInstallMode2.run
          (bp, vkp, matp);
    return (bp, matp);
  }
}.

lemma structured_verify_unpack_mode2_correct
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0 :
  hoare [StructuredVerifyUnpackMode2.run :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0
    ==>
    verify_unpack_mode2_result vkp0 res.`1 res.`2].
proof.
proc.
seq 2 :
  (matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
   VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
     bp vkp0 mode2_vec_words).
+ call
    (VerifyUnpackVkM23CoefficientsPostFreeze.unpack_vk_m23_coeffs_mode2_actual_exact
       witness vkp0).
  auto.
seq 1 :
  (vkp = vkp0 /\
   VerifyUnpackVkM23CoefficientsPostFreeze.decoded_coeff_prefix
     bp vkp0 mode2_vec_words /\
   VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound
     matp /\
   VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp0 matp).
+ call
    (VerifyUnpackV3ExpandBoundsPostFreeze.verify_expand_with_vecA_mode2_prefix_bound
       mat0 seed0).
  auto => /> &hr hdecoded result hexpand.
  exact
    (VerifyUnpackV3SourceBoundPostFreeze.expanded_decoder_mode2_source_bound
       vkp0 result hexpand).
exlim bp => decoded0.
exlim matp => expanded0.
call
  (VerifyUnpackV3PostDecodeThroughNttPostFreeze.actual_verify_unpack_post_decode_through_ntt_install_mode2_correct
       decoded0 vkp0 expanded0).
auto => />.
move=> hdecoded hexpand hsource out pre_ntt preinstall_mat
        hprefix hframe hnonfirst hinput0 hinput1 hntt0 hntt0bound
        hntt1 hntt1bound hforward htail hinstall hinstallframe
        hmatrixfirst.
move=> hmatrixnonfirst.
have hmatrixprofile :
    VerifyUnpackV3MatrixProfilePostFreeze.verify_unpack_mode2_matrix_repr_bound25_17
      out.`2 by
  rewrite
    /VerifyUnpackV3MatrixProfilePostFreeze.verify_unpack_mode2_matrix_repr_bound25_17;
  auto.
rewrite /verify_unpack_mode2_result.
exists decoded0 expanded0 pre_ntt preinstall_mat.
rewrite
  /VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
  /VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
  /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
by auto.
qed.

lemma actual_verify_unpack_mode2_equiv_structured :
  equiv [Verify._unpack_vk_m23_full ~ StructuredVerifyUnpackMode2.run :
    ={Glob.mem, matp, vkp, seedu} /\
    k{1} = W64.of_int mode2_rows /\
    l{1} = W64.of_int mode2_cols /\
    m{1} = W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m
    ==>
    res{1} = res{2}.`2].
proof.
proc.
inline
  VerifyUnpackV3PostDecodeThroughNttPostFreeze.ActualVerifyUnpackPostDecodeThroughNttInstallMode2.run
  VerifyUnpackV3PostDecodeThroughNttPostFreeze.ActualVerifyUnpackPostDecodePreNttMode2.run
  VerifyUnpackV3NttInstallPostFreeze.ActualVerifyUnpackNttInstallMode2.run
  VerifyUnpackV3NttInstallPostFreeze.InstallFirstColumnMode2.run.
wp.
call (_ : ={mp, vp, rows, cols} ==> ={res}).
+ by sim.
wp.
call (_ : ={xp, count} ==> ={res}).
+ by sim.
wp.
call (_ : ={vp, count} ==> ={res}).
+ by sim.
wp.
call (_ : ={bp, matp, l, rows} ==> ={res}).
+ by sim.
wp.
call (_ : ={vp, count} ==> ={res}).
+ by sim.
wp.
call (_ : ={mp, rows, cols} ==> ={res}).
+ by sim.
wp.
call (_ : ={Glob.mem, matp, seedp, rows, cols, m}
          ==> ={Glob.mem, res}).
+ by proc; sim.
wp.
call (_ : ={bp, vkp, count} ==> ={res}).
+ by sim.
auto => />.
qed.

lemma actual_verify_unpack_mode2_correct
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0 :
  hoare [Verify._unpack_vk_m23_full :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    k = W64.of_int mode2_rows /\
    l = W64.of_int mode2_cols /\
    m = W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m
    ==>
    exists outbp,
      verify_unpack_mode2_result vkp0 outbp res].
proof.
conseq actual_verify_unpack_mode2_equiv_structured
  (structured_verify_unpack_mode2_correct mat0 vkp0 seed0).
+ move=> &1 [hmat [hvkp [hseed [hk [hl hm]]]]].
  exists Glob.mem{1}.
  exists (matp{1}, vkp{1}, seedu{1}).
  by auto.
+ move=> &1 &2 hres hresult.
  exists res{2}.`1.
  rewrite hres.
  exact hresult.
qed.

end VerifyUnpackV3FullPostFreeze.
