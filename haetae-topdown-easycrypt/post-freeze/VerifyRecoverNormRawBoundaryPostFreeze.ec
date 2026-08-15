require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 BArray8192
               RawVerifyApiTarget VerifyCoreTarget
               Mode2VerifyRecover Mode2VerifyPrepareNorm.

theory VerifyRecoverNormRawBoundaryPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Focused = VerifyCoreTarget.M.

lemma raw_sign_verify_recover_w_z2_equiv_focused :
  equiv [Raw._sign_verify_recover_w_z2 ~
         Focused._sign_verify_recover_w_z2 :
    ={Glob.mem, wp_0, z2p, highp, hp, wprimep, count,
      half_alpha, log_alpha, bound, alpha}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_sign_verify_recover_w_z2_mode2_direct
    (wp0 z20 high0 hp0 : BArray8192.t)
    (wprime0 : BArray1024.t) :
  hoare [Raw._sign_verify_recover_w_z2 :
    wp_0 = wp0 /\ z2p = z20 /\ highp = high0 /\ hp = hp0 /\
    wprimep = wprime0 /\
    count = W64.of_int Mode2VerifyRecover.mode2_verify_recover_count /\
    half_alpha = Mode2VerifyRecover.mode2_verify_recover_half_alpha /\
    log_alpha = Mode2VerifyRecover.mode2_verify_recover_log_alpha /\
    bound = Mode2VerifyRecover.mode2_verify_recover_bound /\
    alpha = Mode2VerifyRecover.mode2_verify_recover_alpha
    ==>
    Mode2VerifyRecover.recover_w_prefix
      res.`1 high0 hp0 Mode2VerifyRecover.mode2_verify_recover_count /\
    Mode2VerifyRecover.recover_z2_prefix
      res.`2 high0 hp0 wprime0
      Mode2VerifyRecover.mode2_verify_recover_count].
proof.
conseq raw_sign_verify_recover_w_z2_equiv_focused
  (Mode2VerifyRecover.actual_sign_verify_recover_w_z2_mode2_word_semantics
    wp0 z20 high0 hp0 wprime0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists
    (wp_0{1}, z2p{1}, highp{1}, hp{1}, wprimep{1}, count{1},
     half_alpha{1}, log_alpha{1}, bound{1}, alpha{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

module RawSignVerifyRecoverMode2 = {
  proc run
      (wp_0 z2p highp hp : BArray8192.t,
       wprimep : BArray1024.t)
      : BArray8192.t * BArray8192.t = {
    (wp_0, z2p) <@ Raw._sign_verify_recover_w_z2
      (wp_0, z2p, highp, hp, wprimep,
       W64.of_int Mode2VerifyRecover.mode2_verify_recover_count,
       Mode2VerifyRecover.mode2_verify_recover_half_alpha,
       Mode2VerifyRecover.mode2_verify_recover_log_alpha,
       Mode2VerifyRecover.mode2_verify_recover_bound,
       Mode2VerifyRecover.mode2_verify_recover_alpha);
    return (wp_0, z2p);
  }
}.

lemma raw_sign_verify_recover_w_z2_mode2_word_semantics
    (wp0 z20 high0 hp0 : BArray8192.t)
    (wprime0 : BArray1024.t) :
  hoare [RawSignVerifyRecoverMode2.run :
    wp_0 = wp0 /\ z2p = z20 /\ highp = high0 /\ hp = hp0 /\
    wprimep = wprime0
    ==>
    Mode2VerifyRecover.recover_w_prefix
      res.`1 high0 hp0 Mode2VerifyRecover.mode2_verify_recover_count /\
    Mode2VerifyRecover.recover_z2_prefix
      res.`2 high0 hp0 wprime0
      Mode2VerifyRecover.mode2_verify_recover_count].
proof.
proc.
call
  (raw_sign_verify_recover_w_z2_mode2_direct
    wp0 z20 high0 hp0 wprime0).
auto.
qed.

lemma raw_sign_verify_norm_reject_equiv_focused :
  equiv [Raw._sign_verify_norm_reject ~
         Focused._sign_verify_norm_reject :
    ={Glob.mem, z2p, z1norm, kcount, bound}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_sign_verify_norm_reject_mode2_direct
    (z20 : BArray8192.t) (z1norm0 : W64.t) :
  hoare [Raw._sign_verify_norm_reject :
    z2p = z20 /\ z1norm = z1norm0 /\
    kcount = W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_words /\
    bound = W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_bound
    ==>
    (res = W64.zero <=>
      Mode2VerifyPrepareNorm.verify_norm_accepts_word z20 z1norm0) /\
    (res = W64.one <=>
      W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_bound \ult
        Mode2VerifyPrepareNorm.verify_norm_total_word z20 z1norm0)].
proof.
conseq raw_sign_verify_norm_reject_equiv_focused
  (Mode2VerifyPrepareNorm.sign_verify_norm_reject_mode2_word_exact
    z20 z1norm0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists (z2p{1}, z1norm{1}, kcount{1}, bound{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

module RawSignVerifyNormRejectMode2 = {
  proc run (z2p : BArray8192.t, z1norm : W64.t) : W64.t = {
    var reject : W64.t;
    reject <@ Raw._sign_verify_norm_reject
      (z2p, z1norm,
       W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_words,
       W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_bound);
    return reject;
  }
}.

lemma raw_sign_verify_norm_reject_mode2_word_exact
    (z20 : BArray8192.t) (z1norm0 : W64.t) :
  hoare [RawSignVerifyNormRejectMode2.run :
    z2p = z20 /\ z1norm = z1norm0
    ==>
    (res = W64.zero <=>
      Mode2VerifyPrepareNorm.verify_norm_accepts_word z20 z1norm0) /\
    (res = W64.one <=>
      W64.of_int Mode2VerifyPrepareNorm.mode2_verify_norm_bound \ult
        Mode2VerifyPrepareNorm.verify_norm_total_word z20 z1norm0)].
proof.
proc.
call
  (raw_sign_verify_norm_reject_mode2_direct
    z20 z1norm0).
auto.
qed.

end VerifyRecoverNormRawBoundaryPostFreeze.
