require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget.

theory Mode2VerifyTailChallenge.

module Verify = VerifyCoreTarget.M.

op mode2_tail_k : int = 2.
op mode2_tail_highlen : int = 576.
op mode2_tail_vklen : int = 992.
op mode2_tail_tau : int = 58.
op mode2_challenge_words : int = 256.

op poly_mismatch_term
    (ap bp : BArray1024.t) (idx : int) : W64.t =
  zeroextu64
    (BArray1024.get32 ap idx `^` BArray1024.get32 bp idx).

op poly_mismatch_acc_prefix
    (ap bp : BArray1024.t) (n : int) : W64.t =
  foldl
    (fun (acc : W64.t) (idx : int) =>
      acc `|` poly_mismatch_term ap bp idx)
    W64.zero (iota_ 0 n).

op poly_mismatch_result_word (acc : W64.t) : W64.t =
  (acc `|` (W64.zero - acc)) `>>` W8.of_int 63.

lemma poly_mismatch_acc_prefix_step ap bp n :
  0 <= n =>
  poly_mismatch_acc_prefix ap bp (n + 1) =
    poly_mismatch_acc_prefix ap bp n `|` poly_mismatch_term ap bp n.
proof.
move=> hn.
rewrite /poly_mismatch_acc_prefix (iotaSr 0 n) 1:hn.
rewrite foldl_rcons /=.
trivial.
qed.

(* Exact comparison-word semantics of the final challenge-array check.  This
   deliberately stops short of identifying the recomputed array with the
   paper SampleInBall expression. *)
lemma poly_mismatch_mode2_word_exact
    (ap0 bp0 : BArray1024.t) :
  hoare [Verify._poly_mismatch :
    ap = ap0 /\ bp = bp0
    ==>
    res = poly_mismatch_result_word
      (poly_mismatch_acc_prefix ap0 bp0 mode2_challenge_words)].
proof.
proc.
wp.
while
  (ap = ap0 /\ bp = bp0 /\
   0 <= W64.to_uint i <= mode2_challenge_words /\
   acc = poly_mismatch_acc_prefix ap0 bp0 (W64.to_uint i)).
+ auto => /> &hr hi0 hile hguard.
  have hilt : W64.to_uint i{hr} < mode2_challenge_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /mode2_challenge_words /=.
    smt(W64.to_uint_cmp).
  have hnext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split; first by rewrite hnext; smt(W64.to_uint_cmp).
  rewrite hnext poly_mismatch_acc_prefix_step 1:/#.
  rewrite /poly_mismatch_term.
  trivial.
+ auto => />.
  split.
  + by rewrite /poly_mismatch_acc_prefix iota0.
  + move=> i0 hdone hi0 hile.
    have hieq : W64.to_uint i0 = mode2_challenge_words.
    + move: hdone.
      rewrite W64.ultE W64.of_uintK /mode2_challenge_words /=.
      smt(W64.to_uint_cmp).
    rewrite /poly_mismatch_result_word hieq.
    trivial.
qed.

module ActualVerifyTailChallengeTrace = {
  var observed_highp : BArray1152.t
  var observed_lsbp : BArray32.t
  var observed_mup : BArray32.t
  var observed_cprimep : BArray1024.t
  var observed_reject : W64.t
  var observed_vkp : W64.t
  var observed_prep : W64.t
  var observed_prelen : W64.t
  var observed_mp : W64.t
  var observed_mlen : W64.t
  var observed_highlen : W64.t
  var observed_count : W64.t
  var observed_vklen : W64.t
  var observed_tau : W64.t

  proc run (wp_0 : BArray8192.t, wprimep : BArray1024.t,
            cp : BArray1024.t, descp : BArray40.t, k_i : int,
            highbits_len_i : int, vklen_i : int, tau_i : int) : W64.t = {
    var reject : W64.t;
    var ms : W64.t;
    var highbuf : BArray1152.t;
    var highp : BArray1152.t;
    var lsb : BArray32.t;
    var lsbp : BArray32.t;
    var mu : BArray32.t;
    var mup : BArray32.t;
    var cprime : BArray1024.t;
    var cprimep : BArray1024.t;
    var vkp : W64.t;
    var prep : W64.t;
    var prelen : W64.t;
    var mp : W64.t;
    var mlen : W64.t;
    var highlen : W64.t;
    var count : W64.t;
    var vklen : W64.t;
    var tau : W64.t;

    cprime <- witness;
    cprimep <- witness;
    highbuf <- witness;
    highp <- witness;
    lsb <- witness;
    lsbp <- witness;
    mu <- witness;
    mup <- witness;
    observed_highp <- witness;
    observed_lsbp <- witness;
    observed_mup <- witness;
    observed_cprimep <- witness;
    observed_reject <- witness;
    observed_vkp <- witness;
    observed_prep <- witness;
    observed_prelen <- witness;
    observed_mp <- witness;
    observed_mlen <- witness;
    observed_highlen <- witness;
    observed_count <- witness;
    observed_vklen <- witness;
    observed_tau <- witness;

    ms <- init_msf;
    descp <- protect_ptr descp ms;
    highp <- highbuf;
    lsbp <- lsb;
    mup <- mu;
    cprimep <- cprime;
    vkp <- BArray40.get64 descp 0;
    prep <- BArray40.get64 descp 1;
    prelen <- BArray40.get64 descp 2;
    mp <- BArray40.get64 descp 3;
    mlen <- BArray40.get64 descp 4;
    observed_vkp <- vkp;
    observed_prep <- prep;
    observed_prelen <- prelen;
    observed_mp <- mp;
    observed_mlen <- mlen;

    highlen <- W64.of_int highbits_len_i;
    observed_highlen <- highlen;
    ms <- init_msf;
    highp <- protect_ptr highp ms;
    highlen <- protect_64 highlen ms;
    highp <@ Verify.__verify_zero_highbuf (highp, highlen);

    count <- W64.of_int k_i;
    observed_count <- count;
    ms <- init_msf;
    highp <- protect_ptr highp ms;
    wp_0 <- protect_ptr wp_0 ms;
    count <- protect_64 count ms;
    highp <@ Verify._pack_vec_highbits_m23 (highp, wp_0, count);
    observed_highp <- highp;

    ms <- init_msf;
    lsbp <- protect_ptr lsbp ms;
    wprimep <- protect_ptr wprimep ms;
    lsbp <@ Verify._pack_poly_lsb (lsbp, wprimep);
    observed_lsbp <- lsbp;

    vklen <- W64.of_int vklen_i;
    observed_vklen <- vklen;
    ms <- init_msf;
    mup <- protect_ptr mup ms;
    mup <@ Verify.__verify_hash_mu (mup, vkp, prep, prelen, mp, mlen, vklen);
    observed_mup <- mup;

    tau <- W64.of_int tau_i;
    observed_tau <- tau;
    ms <- init_msf;
    cprimep <- protect_ptr cprimep ms;
    highp <- protect_ptr highp ms;
    lsbp <- protect_ptr lsbp ms;
    mup <- protect_ptr mup ms;
    highlen <- protect_64 highlen ms;
    tau <- protect_64 tau ms;
    cprimep <@ Verify.__verify_challenge_m23
      (cprimep, highp, highlen, lsbp, mup, tau);
    observed_cprimep <- cprimep;

    ms <- init_msf;
    cp <- protect_ptr cp ms;
    cprimep <- protect_ptr cprimep ms;
    reject <@ Verify._poly_mismatch (cp, cprimep);
    observed_reject <- reject;
    return reject;
  }
}.

lemma verify_tail_exact_trace_mode2 :
  equiv [Verify._sign_verify_tail_m23 ~ ActualVerifyTailChallengeTrace.run :
    ={Glob.mem, wp_0, wprimep, cp, descp, k_i, highbits_len_i, vklen_i, tau_i}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

end Mode2VerifyTailChallenge.
