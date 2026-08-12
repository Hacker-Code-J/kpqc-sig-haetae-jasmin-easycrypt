require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget.

theory Mode2VerifyCoreSequence.

module Verify = VerifyCoreTarget.M.

op mode2_lcount : W64.t = W64.of_int 1024.
op mode2_rows : W64.t = W64.of_int 2.
op mode2_cols : W64.t = W64.of_int 4.
op mode2_kcount : W64.t = W64.of_int 512.
op mode2_half_alpha : int = 256.
op mode2_log_alpha : int = 9.
op mode2_hint_bound : int = 252.
op mode2_alpha : int = 512.
op mode2_norm_bound : W64.t = W64.of_int 163265017.
op mode2_tail_k : int = 2.
op mode2_tail_highlen : int = 576.
op mode2_tail_vklen : int = 992.
op mode2_tail_tau : int = 58.

module ActualVerifyCoreSequence = {
  var input_highz : BArray8192.t
  var input_lowz : BArray8192.t
  var input_h : BArray8192.t
  var input_c : BArray1024.t
  var input_a1 : BArray32768.t
  var input_desc : BArray40.t

  var prepare_z1 : BArray8192.t
  var prepare_wprime : BArray1024.t
  var prepare_sqnorm2 : W64.t

  var matrix_z1 : BArray8192.t
  var matrix_highbits : BArray8192.t

  var recover_w : BArray8192.t
  var recover_z2 : BArray8192.t

  var norm_reject : W64.t
  var tail_desc : BArray40.t
  var tail_reject : W64.t
  var tail_called : bool

  proc run (highzp : BArray8192.t, lowzp : BArray8192.t,
            hp : BArray8192.t, cp : BArray1024.t,
            a1p : BArray32768.t, descp : BArray40.t) : W64.t = {
    var z1p : BArray8192.t;
    var wprimep : BArray1024.t;
    var sqnorm2 : W64.t;
    var highbitsp : BArray8192.t;
    var wp_out : BArray8192.t;
    var z2p : BArray8192.t;
    var reject : W64.t;

    input_highz <- highzp;
    input_lowz <- lowzp;
    input_h <- hp;
    input_c <- cp;
    input_a1 <- a1p;
    input_desc <- descp;

    prepare_z1 <- witness;
    prepare_wprime <- witness;
    prepare_sqnorm2 <- witness;
    matrix_z1 <- witness;
    matrix_highbits <- witness;
    recover_w <- witness;
    recover_z2 <- witness;
    norm_reject <- witness;
    tail_desc <- witness;
    tail_reject <- witness;
    tail_called <- false;

    z1p <- witness;
    wprimep <- witness;
    highbitsp <- witness;
    wp_out <- witness;
    z2p <- witness;
    reject <- witness;

    (z1p, wprimep, sqnorm2) <@
      Verify._verify_prepare_z1_wprime
        (z1p, wprimep, input_highz, input_lowz, input_c, mode2_lcount);
    prepare_z1 <- z1p;
    prepare_wprime <- wprimep;
    prepare_sqnorm2 <- sqnorm2;

    (z1p, highbitsp) <@
      Verify._verify_matrix_crt
        (z1p, highbitsp, input_a1, wprimep, mode2_rows, mode2_cols);
    matrix_z1 <- z1p;
    matrix_highbits <- highbitsp;

    (wp_out, z2p) <@
      Verify._sign_verify_recover_w_z2
        (wp_out, z2p, z1p, input_h, wprimep, mode2_kcount,
         mode2_half_alpha, mode2_log_alpha, mode2_hint_bound, mode2_alpha);
    recover_w <- wp_out;
    recover_z2 <- z2p;

    reject <@ Verify._sign_verify_norm_reject
      (z2p, sqnorm2, mode2_kcount, mode2_norm_bound);
    norm_reject <- reject;
    tail_desc <- input_desc;
    tail_reject <- reject;
    tail_called <- false;

    if (reject = W64.zero) {
      reject <@ Verify._sign_verify_tail_m23
        (wp_out, wprimep, input_c, tail_desc, mode2_tail_k,
         mode2_tail_highlen, mode2_tail_vklen, mode2_tail_tau);
      tail_reject <- reject;
      tail_called <- true;
    }

    return reject;
  }
}.

(* This is a direct control/snapshot harness only. It does not claim any
   reconstruction, norm, or challenge semantics beyond the real call order and
   the saved intermediate states. *)
lemma actual_verify_core_sequence_branch_control_mode2 :
  hoare [ActualVerifyCoreSequence.run :
    true
    ==>
    ActualVerifyCoreSequence.tail_called =
      (ActualVerifyCoreSequence.norm_reject = W64.zero) /\
    (!ActualVerifyCoreSequence.tail_called =>
      res = ActualVerifyCoreSequence.norm_reject /\
      ActualVerifyCoreSequence.tail_reject =
        ActualVerifyCoreSequence.norm_reject) /\
    (ActualVerifyCoreSequence.tail_called =>
      ActualVerifyCoreSequence.norm_reject = W64.zero /\
      res = ActualVerifyCoreSequence.tail_reject)].
proof.
proc.
sp 23.
seq 1 : true.
+ call (_ : true ==> true); first by auto.
  auto.
sp 3.
seq 1 : true.
+ call (_ : true ==> true); first by auto.
  auto.
sp 2.
seq 1 : true.
+ call (_ : true ==> true); first by auto.
  auto.
sp 2.
seq 1 : true.
+ call (_ : true ==> true); first by auto.
  auto.
sp 4.
if.
+ wp.
  call (_ : true); first by auto.
  auto => />.
+ auto => />.
qed.

lemma actual_verify_core_sequence_input_snapshots_mode2
    (highz0 lowz0 h0 : BArray8192.t)
    (c0 : BArray1024.t)
    (a10 : BArray32768.t)
    (desc0 : BArray40.t) :
  hoare [ActualVerifyCoreSequence.run :
    highzp = highz0 /\ lowzp = lowz0 /\ hp = h0 /\
    cp = c0 /\ a1p = a10 /\ descp = desc0
    ==>
    ActualVerifyCoreSequence.input_highz = highz0 /\
    ActualVerifyCoreSequence.input_lowz = lowz0 /\
    ActualVerifyCoreSequence.input_h = h0 /\
    ActualVerifyCoreSequence.input_c = c0 /\
    ActualVerifyCoreSequence.input_a1 = a10 /\
    ActualVerifyCoreSequence.input_desc = desc0 /\
    ActualVerifyCoreSequence.tail_desc = desc0 /\
    res = ActualVerifyCoreSequence.tail_reject].
proof.
proc.
sp 23.
seq 1 :
  (ActualVerifyCoreSequence.input_highz = highz0 /\
   ActualVerifyCoreSequence.input_lowz = lowz0 /\
   ActualVerifyCoreSequence.input_h = h0 /\
   ActualVerifyCoreSequence.input_c = c0 /\
   ActualVerifyCoreSequence.input_a1 = a10 /\
   ActualVerifyCoreSequence.input_desc = desc0).
+ call (_ : true ==> true); first by auto.
  auto.
sp 3.
seq 1 :
  (ActualVerifyCoreSequence.input_highz = highz0 /\
   ActualVerifyCoreSequence.input_lowz = lowz0 /\
   ActualVerifyCoreSequence.input_h = h0 /\
   ActualVerifyCoreSequence.input_c = c0 /\
   ActualVerifyCoreSequence.input_a1 = a10 /\
   ActualVerifyCoreSequence.input_desc = desc0).
+ call (_ : true ==> true); first by auto.
  auto.
sp 2.
seq 1 :
  (ActualVerifyCoreSequence.input_highz = highz0 /\
   ActualVerifyCoreSequence.input_lowz = lowz0 /\
   ActualVerifyCoreSequence.input_h = h0 /\
   ActualVerifyCoreSequence.input_c = c0 /\
   ActualVerifyCoreSequence.input_a1 = a10 /\
   ActualVerifyCoreSequence.input_desc = desc0).
+ call (_ : true ==> true); first by auto.
  auto.
sp 2.
seq 1 :
  (ActualVerifyCoreSequence.input_highz = highz0 /\
   ActualVerifyCoreSequence.input_lowz = lowz0 /\
   ActualVerifyCoreSequence.input_h = h0 /\
   ActualVerifyCoreSequence.input_c = c0 /\
   ActualVerifyCoreSequence.input_a1 = a10 /\
   ActualVerifyCoreSequence.input_desc = desc0).
+ call (_ : true ==> true); first by auto.
  auto.
sp 4.
if.
+ wp.
  call (_ : true); first by auto.
  auto => />.
+ auto => />.
qed.

end Mode2VerifyCoreSequence.
