require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray32768 RawVerifyApiTarget
  VerifyUnpackMode2Target VerifyUnpackV3AssemblyPostFreeze
  VerifyUnpackV3ExpandBoundsPostFreeze VerifyUnpackV3FullPostFreeze.

theory VerifyUnpackV3RawBoundaryPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Focused = VerifyUnpackMode2Target.M.

import VerifyUnpackV3AssemblyPostFreeze.

lemma raw_verify_unpack_mode2_equiv_focused :
  equiv [Raw._unpack_vk_m23_full ~ Focused._unpack_vk_m23_full :
    ={Glob.mem, matp, vkp, seedu, k, l, m}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_verify_unpack_mode2_correct
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0 :
  hoare [Raw._unpack_vk_m23_full :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    k = W64.of_int mode2_rows /\
    l = W64.of_int mode2_cols /\
    m = W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m
    ==>
    exists outbp,
      VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result
        vkp0 outbp res].
proof.
conseq raw_verify_unpack_mode2_equiv_focused
  (VerifyUnpackV3FullPostFreeze.actual_verify_unpack_mode2_correct
     mat0 vkp0 seed0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists (matp{1}, vkp{1}, seedu{1}, k{1}, l{1}, m{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

lemma raw_verify_unpack_mode2_tight20_correct
    (mat0 : BArray32768.t) (vkp0 : BArray2752.t) seed0 :
  hoare [Raw._unpack_vk_m23_full :
    matp = mat0 /\ vkp = vkp0 /\ seedu = seed0 /\
    k = W64.of_int mode2_rows /\
    l = W64.of_int mode2_cols /\
    m = W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m
    ==>
    exists outbp,
      VerifyUnpackV3FullPostFreeze.verify_unpack_mode2_result_tight20
        vkp0 outbp res].
proof.
conseq raw_verify_unpack_mode2_equiv_focused
  (VerifyUnpackV3FullPostFreeze.actual_verify_unpack_mode2_tight20_correct
     mat0 vkp0 seed0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists (matp{1}, vkp{1}, seedu{1}, k{1}, l{1}, m{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

end VerifyUnpackV3RawBoundaryPostFreeze.
