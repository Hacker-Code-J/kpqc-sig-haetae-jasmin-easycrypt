require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 BArray8192 RawVerifyApiTarget VerifyCoreTarget
               KeygenM23ArithmeticSpec KeygenM23MatrixSpec
               Mode2VerifyPrepareNorm VerifyMatrixCrtPostFreeze
               VerifyPrepareZ1BoundPostFreeze.

import Mode2VerifyPrepareNorm VerifyMatrixCrtPostFreeze.

theory VerifyPrepareZ1RawBoundaryPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Focused = VerifyCoreTarget.M.

lemma raw_verify_prepare_z1_wprime_equiv_focused :
  equiv [Raw._verify_prepare_z1_wprime ~
         Focused._verify_prepare_z1_wprime :
    ={Glob.mem, z1p, wprimep, highzp, lowzp, cp, lcount}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

module RawVerifyPrepareZ1WprimeMode2 = {
  proc run
      (z1p highzp lowzp : BArray8192.t,
       wprimep cp : BArray1024.t)
      : BArray8192.t * BArray1024.t * W64.t = {
    var total : W64.t;
    (z1p, wprimep, total) <@ Raw._verify_prepare_z1_wprime
      (z1p, wprimep, highzp, lowzp, cp, W64.of_int low_words);
    return (z1p, wprimep, total);
  }
}.

lemma raw_verify_prepare_z1_wprime_mode2_input_repr_bound16
    (z10 highz0 lowz0 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t) :
  hoare [Raw._verify_prepare_z1_wprime :
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
conseq raw_verify_prepare_z1_wprime_equiv_focused
  (VerifyPrepareZ1BoundPostFreeze.verify_prepare_z1_wprime_mode2_input_repr_bound16
    z10 highz0 lowz0 wprime0 cp0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists
    (z1p{1}, wprimep{1}, highzp{1}, lowzp{1}, cp{1}, lcount{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

lemma raw_verify_prepare_z1_wprime_mode2_wrapper_input_repr_bound16
    (z10 highz0 lowz0 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t) :
  hoare [RawVerifyPrepareZ1WprimeMode2.run :
    z1p = z10 /\ highzp = highz0 /\ lowzp = lowz0 /\
    wprimep = wprime0 /\ cp = cp0 /\
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
proc.
call
  (raw_verify_prepare_z1_wprime_mode2_input_repr_bound16
    z10 highz0 lowz0 wprime0 cp0).
auto.
qed.

end VerifyPrepareZ1RawBoundaryPostFreeze.
