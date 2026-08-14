require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 BArray8192 Fq Rq.
require import VerifyCoreTarget.
require import Mode2VerifyPrepareNorm Mode2HbzCodecSpec.
require import KeygenM23ArithmeticSpec KeygenM23MatrixSpec.
require import VerifyMatrixCrtPostFreeze.

import Mode2VerifyPrepareNorm VerifyMatrixCrtPostFreeze.

theory VerifyPrepareZ1BoundPostFreeze.

module Verify = VerifyCoreTarget.M.

lemma verify_prepare_z1_word_of_int
    (highz lowz : BArray8192.t) (idx : int) :
  verify_prepare_z1_word highz lowz idx =
    W32.of_int
      (256 * W32.to_sint (BArray8192.get32 highz idx) +
       W32.to_sint (BArray8192.get32 lowz idx)).
proof.
rewrite /verify_prepare_z1_word.
rewrite -(Mode2HbzCodecSpec.w32_of_sintK (BArray8192.get32 highz idx)).
rewrite -(Mode2HbzCodecSpec.w32_of_sintK (BArray8192.get32 lowz idx)).
rewrite /(`<<`) W8.of_uintK /= W32.shlMP 1:/#.
rewrite W32.of_intD'.
congr.
have hhigh_range :=
  W32.to_sint_cmp (BArray8192.get32 highz idx).
have hlow_range :=
  W32.to_sint_cmp (BArray8192.get32 lowz idx).
rewrite !W32.to_sintK_small 1:hhigh_range 1:hlow_range.
ring.
qed.

lemma verify_prepare_z1_word_bound16
    (highz lowz : BArray8192.t) (idx : int) :
  canonical_hbz_mode2 highz =>
  canonical_signed_low lowz =>
  0 <= idx < low_words =>
  Fq.bw32 (verify_prepare_z1_word highz lowz idx) 16.
proof.
move=> hhigh hlow hi.
have hhighi := hhigh idx hi.
have hlowi := hlow idx hi.
move: hlowi => [hlowi _].
rewrite verify_prepare_z1_word_of_int /Fq.bw32 W32.to_sintK_small /=.
+ smt().
smt().
qed.

lemma verify_prepare_z1_active_bound16_of_prefix
    (out highz lowz : BArray8192.t) :
  canonical_hbz_mode2 highz =>
  canonical_signed_low lowz =>
  verify_prepare_z1_prefix out highz lowz low_words =>
  forall i, 0 <= i < low_words =>
    Fq.bw32 (BArray8192.get32 out i) 16.
proof.
move=> hhigh hlow hprefix i hi.
rewrite /verify_prepare_z1_prefix in hprefix.
rewrite hprefix 1:hi.
exact (verify_prepare_z1_word_bound16 highz lowz i hhigh hlow hi).
qed.

lemma verify_prepare_z1_input_repr_bound16_self
    (out highz lowz : BArray8192.t) :
  canonical_hbz_mode2 highz =>
  canonical_signed_low lowz =>
  verify_prepare_z1_prefix out highz lowz low_words =>
  verify_mode2_input_repr_bound16
    out
    (KeygenM23ArithmeticSpec.wide_poly out 0)
    (KeygenM23ArithmeticSpec.wide_poly
      out KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      out (2 * KeygenM23MatrixSpec.poly_words_i))
    (KeygenM23ArithmeticSpec.wide_poly
      out (3 * KeygenM23MatrixSpec.poly_words_i)).
proof.
move=> hhigh hlow hprefix.
have hbound :
    forall i, 0 <= i < low_words =>
      Fq.bw32 (BArray8192.get32 out i) 16.
+ exact
    (verify_prepare_z1_active_bound16_of_prefix
      out highz lowz hhigh hlow hprefix).
rewrite /verify_mode2_input_repr_bound16.
split.
+ apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
  rewrite /KeygenM23ArithmeticSpec.wide_slice_bound => j hj.
  apply hbound.
  rewrite /low_words /KeygenM23MatrixSpec.poly_words_i in hj.
  smt().
split.
+ apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
  rewrite /KeygenM23ArithmeticSpec.wide_slice_bound => j hj.
  apply hbound.
  rewrite /low_words /KeygenM23MatrixSpec.poly_words_i in hj.
  smt().
split.
+ apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
  rewrite /KeygenM23ArithmeticSpec.wide_slice_bound => j hj.
  apply hbound.
  rewrite /low_words /KeygenM23MatrixSpec.poly_words_i in hj.
  smt().
apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
rewrite /KeygenM23ArithmeticSpec.wide_slice_bound => j hj.
apply hbound.
rewrite /low_words /KeygenM23MatrixSpec.poly_words_i in hj.
smt().
qed.

lemma verify_prepare_z1_wprime_mode2_input_repr_bound16
    (z10 highz0 lowz0 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t) :
  hoare [Verify._verify_prepare_z1_wprime :
    z1p = z10 /\ wprimep = wprime0 /\ highzp = highz0 /\ lowzp = lowz0 /\
    cp = cp0 /\ lcount = W64.of_int low_words /\
    canonical_hbz_mode2 highz0 /\ canonical_signed_low lowz0
    ==>
    verify_prepare_z1_prefix res.`1 highz0 lowz0 low_words /\
    coeff_tail_frame z10 res.`1 low_words /\
    verify_mode2_input_repr_bound16
      res.`1
      (KeygenM23ArithmeticSpec.wide_poly res.`1 0)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`1 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`1 (2 * KeygenM23MatrixSpec.poly_words_i))
      (KeygenM23ArithmeticSpec.wide_poly
        res.`1 (3 * KeygenM23MatrixSpec.poly_words_i)) /\
    verify_prepare_wprime_prefix res.`2 highz0 lowz0 cp0 challenge_words /\
    wprime_tail_frame wprime0 res.`2 challenge_words /\
    res.`3 = verify_prepare_total_prefix highz0 lowz0 low_words].
proof.
conseq
  (verify_prepare_z1_wprime_mode2_word_exact
    z10 highz0 lowz0 wprime0 cp0) => //=.
move=> &m hpre result [hzprefix [hzframe [hwprefix [hwframe htotal]]]].
move: hpre => [_ [_ [_ [_ [_ [_ [hhigh hlow]]]]]]].
split; first exact hzprefix.
split; first exact hzframe.
split.
+ exact
    (verify_prepare_z1_input_repr_bound16_self
      result.`1 highz0 lowz0 hhigh hlow hzprefix).
split; first exact hwprefix.
split; first exact hwframe.
exact htotal.
qed.

end VerifyPrepareZ1BoundPostFreeze.
