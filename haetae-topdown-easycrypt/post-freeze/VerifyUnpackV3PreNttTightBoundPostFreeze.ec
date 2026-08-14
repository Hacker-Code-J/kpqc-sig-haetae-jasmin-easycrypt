require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray2752 BArray8192 BArray32768
  VerifyUnpackV3AssemblyPostFreeze VerifyUnpackV3PreNttPostFreeze
  VerifyUnpackV3PreNttBoundPostFreeze
  VerifyUnpackVkM23CoefficientsPostFreeze.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3PreNttTightBoundPostFreeze.

op pre_ntt_sint_limit : int = 131068.

op pre_ntt_active_sint_bound (a : BArray8192.t) : bool =
  forall i, 0 <= i < mode2_vec_words =>
    -pre_ntt_sint_limit <= W32.to_sint (BArray8192.get32 a i) <
      pre_ntt_sint_limit.

lemma mode2_pre_ntt_word_sint_bound (a b : W32.t) :
  0 <= W32.to_uint a < 64513 =>
  0 <= W32.to_uint b < 32768 =>
  -pre_ntt_sint_limit <= W32.to_sint (mode2_pre_ntt_word a b) <
    pre_ntt_sint_limit.
proof.
move=> ha hb.
have heq :
    mode2_pre_ntt_word a b =
    W32.of_int (2 * (W32.to_uint a - 2 * W32.to_uint b)).
+ rewrite /mode2_pre_ntt_word /(`<<`) !W8.of_uintK /=;
  rewrite -(W32.to_uintK a) -(W32.to_uintK b).
  rewrite !W32.shlMP 1:/#.
  rewrite !W32.to_uintK_small 1:/# 1:/#.
  rewrite W32.of_intS' W32.shlMP 1:/#.
  congr; ring.
rewrite heq W32.to_sintK_small /pre_ntt_sint_limit; smt().
qed.

lemma pre_ntt_active_sint_bound_of_prefix_frame
    (vkp : BArray2752.t)
    (mat0 mat : BArray32768.t) (after : BArray8192.t) :
  VerifyUnpackV3PreNttBoundPostFreeze.pre_ntt_source_bound vkp mat0 =>
  VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix
    vkp mat after mode2_vec_words =>
  mat_firstcol_frame mat0 mat =>
  pre_ntt_active_sint_bound after.
proof.
move=> hsource hprefix hframe.
rewrite /pre_ntt_active_sint_bound => i hi.
rewrite /VerifyUnpackV3PreNttPostFreeze.pre_ntt_prefix in hprefix.
rewrite hprefix 1:hi hframe 1:hi.
apply mode2_pre_ntt_word_sint_bound.
+ have ha := W32.to_uint_cmp
    (BArray32768.get32 mat0 (firstcol_slot_idx i)).
  have hs := hsource i hi.
  smt().
have hb := W32.to_uint_cmp
  (VerifyUnpackVkM23CoefficientsPostFreeze.unpack_vk_coeff_word vkp i).
have hs := hsource i hi.
smt().
qed.

end VerifyUnpackV3PreNttTightBoundPostFreeze.
