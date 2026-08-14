require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray32768 VerifyUnpackMode2Target
  VerifyUnpackV3AssemblyPostFreeze VerifyUnpackV3ExpandBoundsPostFreeze
  VerifyUnpackV3PreNttBoundPostFreeze
  VerifyUnpackVkM23CoefficientsPostFreeze VerifyUnpackVkM23BoundsPostFreeze.

theory VerifyUnpackV3SourceBoundPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

lemma expanded_decoder_mode2_source_bound
    (vkp : BArray2752.t) (mat : BArray32768.t) :
  VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound mat =>
  VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp mat.
proof.
move=> hexpand i hi.
split.
+ exact
    (VerifyUnpackV3ExpandBoundsPostFreeze.expanded_mode2_prefix_bound_firstcol
       mat hexpand i hi).
apply VerifyUnpackVkM23BoundsPostFreeze.unpack_vk_coeff_word_bound.
rewrite /VerifyUnpackV3AssemblyPostFreeze.mode2_vec_words
        /VerifyUnpackV3AssemblyPostFreeze.mode2_rows
        /VerifyUnpackV3AssemblyPostFreeze.poly_words in hi.
rewrite /VerifyUnpackVkM23CoefficientsPostFreeze.mode2_active_words.
exact hi.
qed.

lemma verify_expand_with_vecA_mode2_source_bound
    (mat0 : BArray32768.t) seed0 (vkp0 : BArray2752.t) :
  hoare [Verify.__polymatkl_expand_matA_with_vecA :
    matp = mat0 /\ seedp = seed0 /\
    rows = W64.of_int VerifyUnpackV3AssemblyPostFreeze.mode2_rows /\
    cols = W64.of_int VerifyUnpackV3AssemblyPostFreeze.mode2_cols /\
    m = W64.of_int VerifyUnpackV3ExpandBoundsPostFreeze.mode2_m
    ==>
    VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp0 res].
proof.
conseq
  (VerifyUnpackV3ExpandBoundsPostFreeze.verify_expand_with_vecA_mode2_prefix_bound
     mat0 seed0).
+ auto.
move=> &m _ result hexpand.
exact (expanded_decoder_mode2_source_bound vkp0 result hexpand).
qed.

end VerifyUnpackV3SourceBoundPostFreeze.
