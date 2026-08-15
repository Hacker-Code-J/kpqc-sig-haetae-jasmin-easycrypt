require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 BArray8192 BArray32768 Rq
               VerifyCoreTarget RawVerifyApiTarget
               VerifyMatrixCrtPostFreeze
               VerifyMatrixCrtCompositionPostFreeze
               VerifyMatrixCrtRawBoundaryPostFreeze.

import VerifyMatrixCrtPostFreeze VerifyMatrixCrtCompositionPostFreeze.

theory VerifyMatrixCrtDirectRawPostFreeze.

module Focused = VerifyCoreTarget.M.
module Raw = RawVerifyApiTarget.M.

lemma focused_verify_matrix_crt_mode2_equiv_sequential :
  equiv [Focused._verify_matrix_crt ~ SequentialVerifyMatrixCrtMode2.run :
    ={Glob.mem, z1p, highp, a1p, wprimep} /\
    rows{1} = W64.of_int verify_mode2_rows_i /\
    cols{1} = W64.of_int verify_mode2_cols_i
    ==>
    ={Glob.mem, res}].
proof.
proc.
inline NttAcc.run CrtFreeze.run.
wp.
call (: ={vp, count} ==> ={res}).
+ by sim.
wp.
call (: ={wp_0, up, vp, count} ==> ={res}).
+ by sim.
wp.
call (: ={xp, count} ==> ={res}).
+ by sim.
wp.
call (: ={tp, mp, vp, rows, cols} ==> ={res}).
+ by sim.
wp.
call (: ={xp, count} ==> ={res}).
+ by sim.
auto => />.
qed.

lemma focused_verify_matrix_crt_mode2_fromcrt_freeze_mixed_exact
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [Focused._verify_matrix_crt :
    z1p = z10 /\ highp = high0 /\
    a1p = a10 /\ wprimep = wprime0 /\
    rows = W64.of_int verify_mode2_rows_i /\
    cols = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3 /\
    verify_mode2_matrix_repr_bound20_17 a10
    ==>
    verify_matrix_crt_mode2_result
      z10 high0 a10 wprime0 res.`1 res.`2].
proof.
conseq focused_verify_matrix_crt_mode2_equiv_sequential
  (sequential_verify_matrix_crt_mode2_mixed_correct
    z10 high0 a10 wprime0 p0 p1 p2 p3).
+ move=> &1 hpre.
  move: hpre => />.
  move=> *.
  exists Glob.mem{1}.
  exists (z1p{1}, highp{1}, a1p{1}, wprimep{1}).
  trivial.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

lemma raw_verify_matrix_crt_mode2_direct_fromcrt_freeze_mixed_exact
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (wprime0 : BArray1024.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [Raw._verify_matrix_crt :
    z1p = z10 /\ highp = high0 /\
    a1p = a10 /\ wprimep = wprime0 /\
    rows = W64.of_int verify_mode2_rows_i /\
    cols = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3 /\
    verify_mode2_matrix_repr_bound20_17 a10
    ==>
    verify_matrix_crt_mode2_result
      z10 high0 a10 wprime0 res.`1 res.`2].
proof.
conseq
  VerifyMatrixCrtRawBoundaryPostFreeze.raw_verify_matrix_crt_equiv_focused
  (focused_verify_matrix_crt_mode2_fromcrt_freeze_mixed_exact
    z10 high0 a10 wprime0 p0 p1 p2 p3).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists
    (z1p{1}, highp{1}, a1p{1}, wprimep{1}, rows{1}, cols{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

end VerifyMatrixCrtDirectRawPostFreeze.
