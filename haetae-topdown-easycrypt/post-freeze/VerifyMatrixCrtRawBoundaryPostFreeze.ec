require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 BArray8192 BArray32768 RawVerifyApiTarget
               VerifyCoreTarget Rq VerifyMatrixCrtPostFreeze
               VerifyMatrixCrtCompositionPostFreeze.

import VerifyMatrixCrtPostFreeze VerifyMatrixCrtCompositionPostFreeze.

theory VerifyMatrixCrtRawBoundaryPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Focused = VerifyCoreTarget.M.

lemma raw_verify_matrix_crt_equiv_focused :
  equiv [Raw._verify_matrix_crt ~ Focused._verify_matrix_crt :
    ={Glob.mem, z1p, highp, a1p, wprimep, rows, cols}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

module RawVerifyMatrixCrtMode2 = {
  proc run
      (z1p : BArray8192.t, highp : BArray8192.t,
       a1p : BArray32768.t, wprimep : BArray1024.t)
      : BArray8192.t * BArray8192.t = {
    (z1p, highp) <@ Raw._verify_matrix_crt
      (z1p, highp, a1p, wprimep,
       W64.of_int verify_mode2_rows_i,
       W64.of_int verify_mode2_cols_i);
    return (z1p, highp);
  }
}.

lemma raw_verify_matrix_crt_mode2_equiv_actual :
  equiv [RawVerifyMatrixCrtMode2.run ~
         ActualVerifyMatrixCrtMode2.run :
    ={Glob.mem, z1p, highp, a1p, wprimep}
    ==>
    ={Glob.mem, res}].
proof.
proc.
call raw_verify_matrix_crt_equiv_focused.
auto.
qed.

lemma raw_verify_matrix_crt_mode2_fromcrt_freeze_mixed_exact
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [RawVerifyMatrixCrtMode2.run :
    z1p = z10 /\ highp = high0 /\
    a1p = a10 /\ wprimep = wprime0 /\
    verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3 /\
    verify_mode2_matrix_repr_bound20_17 a10
    ==>
    verify_matrix_crt_mode2_result
      z10 high0 a10 wprime0 res.`1 res.`2].
proof.
conseq raw_verify_matrix_crt_mode2_equiv_actual
  (verify_matrix_crt_mode2_fromcrt_freeze_mixed_exact
    z10 high0 a10 wprime0 p0 p1 p2 p3).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists (z1p{1}, highp{1}, a1p{1}, wprimep{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

end VerifyMatrixCrtRawBoundaryPostFreeze.
