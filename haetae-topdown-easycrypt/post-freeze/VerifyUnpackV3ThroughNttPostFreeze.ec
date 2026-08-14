require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray8192 BArray32768
  KeygenM23ArithmeticSpec KeygenM23MatrixSpec NTTRowProductSpec
  VerifyUnpackV3AssemblyPostFreeze VerifyUnpackV3PreNttPostFreeze
  VerifyUnpackV3PreNttBoundPostFreeze
  VerifyUnpackV3NttBound17PostFreeze
  VerifyUnpackV3NttInstallPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3ThroughNttPostFreeze.

module ActualVerifyUnpackPostExpandThroughNttInstallMode2 = {
  proc run (bp : BArray8192.t, vkp : BArray2752.t,
            matp : BArray32768.t)
      : BArray8192.t * BArray32768.t = {
    (bp, matp) <@
      VerifyUnpackV3PreNttPostFreeze.ActualVerifyUnpackPostExpandPreNttMode2.run
        (bp, vkp, matp);
    (bp, matp) <@
      VerifyUnpackV3NttInstallPostFreeze.ActualVerifyUnpackNttInstallMode2.run
        (bp, matp);
    return (bp, matp);
  }
}.

lemma actual_verify_unpack_post_expand_through_ntt_install_mode2_correct
    (bp0 : BArray8192.t) (vkp0 : BArray2752.t)
    (mat0 : BArray32768.t) :
  hoare [ActualVerifyUnpackPostExpandThroughNttInstallMode2.run :
    bp = bp0 /\ vkp = vkp0 /\ matp = mat0 /\
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp0 mat0
    ==>
    exists pre_ntt preinstall_mat,
      VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
        vkp0 preinstall_mat pre_ntt mode2_vec_words /\
      mat_firstcol_frame mat0 preinstall_mat /\
      VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
        pre_ntt
        (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
        (KeygenM23ArithmeticSpec.wide_poly
          pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
      VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
        res.`1
        (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
        (KeygenM23ArithmeticSpec.wide_poly
          pre_ntt KeygenM23MatrixSpec.poly_words_i) /\
      NTTRowProductSpec.vector_forward_repr
        VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_polys
        (fun col =>
          KeygenM23ArithmeticSpec.wide_poly
            res.`1 (col * KeygenM23MatrixSpec.poly_words_i))
        (fun col =>
          KeygenM23ArithmeticSpec.wide_poly
            pre_ntt (col * KeygenM23MatrixSpec.poly_words_i)) /\
      KeygenM23MatrixSpec.word_tail_frame
        pre_ntt res.`1
          VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_words /\
      mat_firstcol_install_prefix res.`1 res.`2 mode2_vec_words /\
      mat_firstcol_install_frame
        preinstall_mat res.`2 mode2_vec_words].
proof.
proc.
seq 1 :
  (exists pre_ntt preinstall_mat,
     bp = pre_ntt /\ vkp = vkp0 /\ matp = preinstall_mat /\
     VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
       vkp0 preinstall_mat pre_ntt mode2_vec_words /\
     mat_firstcol_frame mat0 preinstall_mat /\
     VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
       pre_ntt
       (KeygenM23ArithmeticSpec.wide_poly pre_ntt 0)
       (KeygenM23ArithmeticSpec.wide_poly
         pre_ntt KeygenM23MatrixSpec.poly_words_i)).
+ call
    (VerifyUnpackV3PreNttBoundPostFreeze.actual_verify_unpack_post_expand_pre_ntt_mode2_bound17
       bp0 vkp0 mat0).
  auto => /> hsource result hprefix hframe hactive hbound0 hbound1.
  exists result.`1 result.`2.
  rewrite
    /VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
    /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  by auto.
exlim bp => pre_ntt0.
exlim matp => preinstall_mat0.
call
  (VerifyUnpackV3NttInstallPostFreeze.actual_verify_unpack_ntt_install_mode2_full_correct17
     pre_ntt0 preinstall_mat0
     (KeygenM23ArithmeticSpec.wide_poly pre_ntt0 0)
     (KeygenM23ArithmeticSpec.wide_poly
       pre_ntt0 KeygenM23MatrixSpec.poly_words_i)).
auto => />.
move=> &m hprefix hmatframe hinput result
        hbound hforward htail hinstall hinstallframe.
move=> hvector htailframe hinstallprefix hmatrixframe.
exists pre_ntt0 preinstall_mat0.
rewrite
  /VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
  /VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
  /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
by auto.
qed.

end VerifyUnpackV3ThroughNttPostFreeze.
