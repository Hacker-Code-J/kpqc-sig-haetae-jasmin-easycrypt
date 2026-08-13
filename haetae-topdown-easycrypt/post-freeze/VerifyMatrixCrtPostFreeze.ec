require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import VerifyCoreTarget KeygenMode2ParentTarget.
require import KeygenM23MatrixSpec KeygenM23ArithmeticSpec.
require import NTT_Fq NTTFullSpec.
require import TargetKeygenM23WideInvNTT.

theory VerifyMatrixCrtPostFreeze.

module Verify = VerifyCoreTarget.M.
module Parent = KeygenMode2ParentTarget.M.

op verify_mode2_rows_i : int = 2.
op verify_mode2_cols_i : int = 4.
op verify_mode2_vec_words_i : int =
  verify_mode2_cols_i * KeygenM23MatrixSpec.poly_words_i.
op verify_mode2_out_words_i : int =
  verify_mode2_rows_i * KeygenM23MatrixSpec.poly_words_i.

module ActualVerifyMatrixNttAccMode2 = {
  var input_z1 : BArray8192.t
  var input_high : BArray8192.t
  var input_a1 : BArray32768.t

  var after_ntt : BArray8192.t
  var after_acc : BArray8192.t
  var after_inv : BArray8192.t

  proc run
      (z1p : BArray8192.t, highp : BArray8192.t, a1p : BArray32768.t)
      : BArray8192.t * BArray8192.t = {
    input_z1 <- z1p;
    input_high <- highp;
    input_a1 <- a1p;

    z1p <@ Verify._polyvec_ntt (z1p, W64.of_int verify_mode2_cols_i);
    after_ntt <- z1p;

    highp <@ Verify._polymat_pointwise_acc
      (highp, a1p, z1p,
       W64.of_int verify_mode2_rows_i, W64.of_int verify_mode2_cols_i);
    after_acc <- highp;

    highp <@ Verify._polyvec_invntt (highp, W64.of_int verify_mode2_rows_i);
    after_inv <- highp;

    return (z1p, highp);
  }
}.

lemma verify_polyvec_ntt_equiv_parent :
  equiv [Verify._polyvec_ntt ~ Parent._polyvec_ntt :
    ={xp, count} ==> ={res}].
proof.
proc.
sim.
qed.

lemma verify_polymat_pointwise_acc_equiv_parent :
  equiv [Verify._polymat_pointwise_acc ~ Parent._polymat_pointwise_acc :
    ={tp, mp, vp, rows, cols} ==> ={res}].
proof.
proc.
sim.
qed.

lemma verify_polyvec_invntt_equiv_parent :
  equiv [Verify._polyvec_invntt ~ Parent._polyvec_invntt :
    ={xp, count} ==> ={res}].
proof.
proc.
sim.
qed.

end VerifyMatrixCrtPostFreeze.
