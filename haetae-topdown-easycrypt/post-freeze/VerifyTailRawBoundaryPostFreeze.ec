require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray40 BArray1024 BArray8192
               RawVerifyApiTarget VerifyCoreTarget
               Mode2VerifyTailChallenge.

theory VerifyTailRawBoundaryPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Focused = VerifyCoreTarget.M.
module Trace = Mode2VerifyTailChallenge.ActualVerifyTailChallengeTrace.

lemma raw_sign_verify_tail_m23_equiv_focused :
  equiv [Raw._sign_verify_tail_m23 ~ Focused._sign_verify_tail_m23 :
    ={Glob.mem, wp_0, wprimep, cp, descp,
      k_i, highbits_len_i, vklen_i, tau_i}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_sign_verify_tail_m23_equiv_trace :
  equiv [Raw._sign_verify_tail_m23 ~ Trace.run :
    ={Glob.mem, wp_0, wprimep, cp, descp,
      k_i, highbits_len_i, vklen_i, tau_i}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma verify_tail_trace_mismatch_word_exact
    (cp0 : BArray1024.t) :
  hoare [Trace.run :
    cp = cp0
    ==>
    res = Mode2VerifyTailChallenge.poly_mismatch_result_word
      (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
        cp0 Trace.observed_cprimep
        Mode2VerifyTailChallenge.mode2_challenge_words)].
proof.
proc.
seq 74 : (cp = cp0 /\ cprimep = Trace.observed_cprimep).
+ wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  auto.
+ wp.
  exlim cprimep => cprime0.
  call (Mode2VerifyTailChallenge.poly_mismatch_mode2_word_exact cp0 cprime0).
  auto => &hr />.
qed.

lemma raw_sign_verify_tail_m23_mismatch_word_exact
    (cp0 : BArray1024.t) :
  hoare [Raw._sign_verify_tail_m23 :
    cp = cp0
    ==>
    exists cprime,
      res = Mode2VerifyTailChallenge.poly_mismatch_result_word
        (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
          cp0 cprime Mode2VerifyTailChallenge.mode2_challenge_words)].
proof.
conseq raw_sign_verify_tail_m23_equiv_trace
  (verify_tail_trace_mismatch_word_exact cp0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists
    (wp_0{1}, wprimep{1}, cp{1}, descp{1},
     k_i{1}, highbits_len_i{1}, vklen_i{1}, tau_i{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  exists Trace.observed_cprimep{2}.
  rewrite hres.
  exact hpost.
qed.

module RawSignVerifyTailMode2 = {
  proc run
      (wp_0 : BArray8192.t, wprimep cp : BArray1024.t,
       descp : BArray40.t) : W64.t = {
    var reject : W64.t;
    reject <@ Raw._sign_verify_tail_m23
      (wp_0, wprimep, cp, descp,
       Mode2VerifyTailChallenge.mode2_tail_k,
       Mode2VerifyTailChallenge.mode2_tail_highlen,
       Mode2VerifyTailChallenge.mode2_tail_vklen,
       Mode2VerifyTailChallenge.mode2_tail_tau);
    return reject;
  }
}.

lemma raw_sign_verify_tail_mode2_mismatch_word_exact
    (cp0 : BArray1024.t) :
  hoare [RawSignVerifyTailMode2.run :
    cp = cp0
    ==>
    exists cprime,
      res = Mode2VerifyTailChallenge.poly_mismatch_result_word
        (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix
          cp0 cprime Mode2VerifyTailChallenge.mode2_challenge_words)].
proof.
proc.
call (raw_sign_verify_tail_m23_mismatch_word_exact cp0).
auto.
qed.

end VerifyTailRawBoundaryPostFreeze.
