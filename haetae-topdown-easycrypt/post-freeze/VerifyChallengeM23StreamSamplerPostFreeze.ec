require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget
               VerifyChallengeM23SamplerStructurePostFreeze.

theory VerifyChallengeM23StreamSamplerPostFreeze.

module Verify = VerifyCoreTarget.M.

op mode2_tau : int =
  VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau.
op challenge_words : int =
  VerifyChallengeM23SamplerStructurePostFreeze.challenge_words.
op challenge_shuffle_update
    (cp : BArray1024.t) (i bidx : int) : BArray1024.t =
  VerifyChallengeM23SamplerStructurePostFreeze.challenge_shuffle_update
    cp i bidx.

op stream_sampler_step
    (st : BArray1024.t * int) (byte : int) :
    BArray1024.t * int =
  if 0 <= byte <= st.`2
  then (challenge_shuffle_update st.`1 st.`2 byte, st.`2 + 1)
  else st.

op stream_sampler_replay
    (cp0 : BArray1024.t) (i0 : int) (bytes : int list) :
    BArray1024.t * int =
  foldl stream_sampler_step (cp0, i0) bytes.

lemma stream_sampler_step_accept cp i byte :
  0 <= i < challenge_words =>
  0 <= byte <= i =>
  stream_sampler_step (cp, i) byte =
    (challenge_shuffle_update cp i byte, i + 1).
proof.
move=> hi hbyte.
rewrite /stream_sampler_step ifT; smt().
qed.

lemma stream_sampler_step_reject cp i byte :
  0 <= i < challenge_words =>
  !(0 <= byte <= i) =>
  stream_sampler_step (cp, i) byte = (cp, i).
proof.
move=> hi hbyte.
rewrite /stream_sampler_step ifF; smt().
qed.

lemma stream_sampler_replay_rcons cp0 i0 bytes byte :
  stream_sampler_replay cp0 i0 (rcons bytes byte) =
  stream_sampler_step
    (stream_sampler_replay cp0 i0 bytes) byte.
proof.
rewrite /stream_sampler_replay foldl_rcons.
trivial.
qed.

module ActualVerifyChallengeM23StreamTrace = {
  var observed_bytes : int list
  var observed_init_cp : BArray1024.t
  var observed_start_i : int
  var observed_final_cp : BArray1024.t
  var observed_final_i : int

  proc run (cp : BArray1024.t, highp : BArray1152.t, highlen : W64.t,
            lsbp : BArray32.t, mup : BArray32.t, tau : W64.t) :
            BArray1024.t = {
    var state : BArray200.t;
    var sp_0 : BArray200.t;
    var buf : BArray136.t;
    var bp : BArray136.t;
    var ms : W64.t;
    var i : W64.t;
    var pos : W64.t;
    var b : W32.t;
    var bidx : W64.t;
    var limit : W64.t;
    var old : W32.t;

    bp <- witness;
    buf <- witness;
    sp_0 <- witness;
    state <- witness;
    observed_bytes <- [];
    observed_init_cp <- witness;
    observed_start_i <- 0;
    observed_final_cp <- witness;
    observed_final_i <- 0;

    sp_0 <- state;
    bp <- buf;
    sp_0 <@ Verify.__verify_challenge_absorb
      (sp_0, highp, highlen, lsbp, mup);
    (bp, sp_0) <@ Verify.__poly_challenge_squeeze256_136 (bp, sp_0);
    ms <- init_msf;
    cp <- protect_ptr cp ms;
    cp <@ Verify._poly_challenge_m23_init (cp);
    i <- W64.of_int 256;
    i <- i - tau;
    observed_init_cp <- cp;
    observed_start_i <- W64.to_uint i;
    pos <- W64.of_int 0;
    while (i \ult W64.of_int 256) {
      if (W64.of_int 136 \ule pos) {
        (bp, sp_0) <@ Verify.__poly_challenge_squeeze256_136 (bp, sp_0);
        ms <- init_msf;
        cp <- protect_ptr cp ms;
        pos <- W64.of_int 0;
      } else {
      }
      observed_bytes <-
        rcons observed_bytes
          (W8.to_uint (BArray136.get8 bp (W64.to_uint pos)));
      b <- zeroextu32 (BArray136.get8 bp (W64.to_uint pos));
      pos <- pos + W64.of_int 1;
      bidx <- zeroextu64 b;
      ms <- init_msf;
      bidx <- protect_64 bidx ms;
      limit <- i;
      limit <- limit + W64.of_int 1;
      if (bidx \ult limit) {
        old <- BArray1024.get32 cp (W64.to_uint bidx);
        cp <- BArray1024.set32 cp (W64.to_uint i) old;
        cp <- BArray1024.set32 cp (W64.to_uint bidx) (W32.of_int 1);
        i <- i + W64.of_int 1;
      } else {
      }
    }
    observed_final_cp <- cp;
    observed_final_i <- W64.to_uint i;
    return cp;
  }
}.

(* Partial correctness only: every byte fetched from the current 136-byte
   squeeze block is recorded before the generated accept/reject step.  This
   theorem replays exactly those bytes; it does not characterize the squeeze
   blocks, prove termination, or make a distributional claim. *)
lemma verify_challenge_m23_stream_trace_replay :
  hoare [ActualVerifyChallengeM23StreamTrace.run :
    tau = W64.of_int mode2_tau ==>
    stream_sampler_replay
      ActualVerifyChallengeM23StreamTrace.observed_init_cp
      ActualVerifyChallengeM23StreamTrace.observed_start_i
      ActualVerifyChallengeM23StreamTrace.observed_bytes =
      (ActualVerifyChallengeM23StreamTrace.observed_final_cp,
       ActualVerifyChallengeM23StreamTrace.observed_final_i) /\
    res = ActualVerifyChallengeM23StreamTrace.observed_final_cp /\
    ActualVerifyChallengeM23StreamTrace.observed_final_i = challenge_words].
proof.
proc.
wp.
while
  (tau = W64.of_int mode2_tau /\
   W64.to_uint i <= challenge_words /\
   W64.to_uint pos <= 136 /\
   stream_sampler_replay
     ActualVerifyChallengeM23StreamTrace.observed_init_cp
     ActualVerifyChallengeM23StreamTrace.observed_start_i
     ActualVerifyChallengeM23StreamTrace.observed_bytes =
     (cp, W64.to_uint i)).
+ seq 1 :
    (tau = W64.of_int mode2_tau /\
     W64.to_uint i < challenge_words /\
     W64.to_uint pos < 136 /\
     stream_sampler_replay
       ActualVerifyChallengeM23StreamTrace.observed_init_cp
       ActualVerifyChallengeM23StreamTrace.observed_start_i
       ActualVerifyChallengeM23StreamTrace.observed_bytes =
       (cp, W64.to_uint i)).
  + if.
    + wp.
      call (_ : true ==> true); first by auto.
      auto => />.
      rewrite /protect_ptr.
      move=> &hr hi hpos hreplay hloop hguard.
      have hcw : challenge_words = 256 by trivial.
      move: hloop.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    + auto => />.
      move=> &hr hi hpos hreplay hloop hnot.
      have hcw : challenge_words = 256 by trivial.
      move: hloop hnot.
      rewrite W64.ultE W64.uleE !W64.of_uintK /=.
      smt(W64.to_uint_cmp).
  + wp.
    auto => />.
    move=> &hr hi hpos hreplay.
    split.
    + move=> hacc.
      rewrite /protect_64 in hacc.
      rewrite /protect_64.
      rewrite !W2u32.to_uint_zeroextu64
              !W4u8.to_uint_zeroextu32.
      have hnexti :
          W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
      * rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      have hnextpos :
          W64.to_uint (pos{hr} + W64.one) = W64.to_uint pos{hr} + 1.
      * rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      have hbyte :
          0 <=
            W8.to_uint
              (BArray136.get8 bp{hr} (W64.to_uint pos{hr})) <=
            W64.to_uint i{hr}.
      * move: hacc.
        rewrite W64.ultE W64.to_uintD_small 1:/# W64.to_uint1
                W2u32.to_uint_zeroextu64 W4u8.to_uint_zeroextu32.
        smt(W8.to_uint_cmp pow2_8).
      split.
      * rewrite hnexti.
        have hcw : challenge_words = 256 by trivial.
        smt().
      split.
      * rewrite hnextpos.
        smt().
      rewrite stream_sampler_replay_rcons hreplay.
      rewrite stream_sampler_step_accept 1:/# 1:hbyte.
      rewrite hnexti.
      rewrite /challenge_shuffle_update.
      trivial.
    + move=> hrej.
      rewrite /protect_64 in hrej.
      have hnextpos :
          W64.to_uint (pos{hr} + W64.one) = W64.to_uint pos{hr} + 1.
      * rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      have hnotbyte :
          !(0 <=
              W8.to_uint
                (BArray136.get8 bp{hr} (W64.to_uint pos{hr})) <=
              W64.to_uint i{hr}).
      * move: hrej.
        rewrite W64.ultE W64.to_uintD_small 1:/# W64.to_uint1
                W2u32.to_uint_zeroextu64 W4u8.to_uint_zeroextu32.
        smt(W8.to_uint_cmp pow2_8).
      split; first by smt().
      split; first by rewrite hnextpos; smt().
      rewrite stream_sampler_replay_rcons hreplay.
      apply stream_sampler_step_reject.
      * smt(W64.to_uint_cmp).
      * exact hnotbyte.
+ wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  call (_ : true ==> true); first by auto.
  auto => />.
  move=> result observed_bytes cp0 i0 pos0 hdone hi hpos hreplay.
  have hcw : challenge_words = 256 by trivial.
  move: hdone hi.
  rewrite W64.ultE W64.of_uintK /=.
  smt(W64.to_uint_cmp).
qed.

lemma verify_challenge_m23_exact_stream_trace :
  equiv [Verify.__verify_challenge_m23 ~ ActualVerifyChallengeM23StreamTrace.run :
    ={Glob.mem, cp, highp, highlen, lsbp, mup, tau}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma verify_challenge_m23_actual_stream_replay :
  equiv [Verify.__verify_challenge_m23 ~
         ActualVerifyChallengeM23StreamTrace.run :
    ={Glob.mem, cp, highp, highlen, lsbp, mup, tau} /\
    tau{1} = W64.of_int mode2_tau
    ==>
    ={Glob.mem, res} /\
    stream_sampler_replay
      ActualVerifyChallengeM23StreamTrace.observed_init_cp{2}
      ActualVerifyChallengeM23StreamTrace.observed_start_i{2}
      ActualVerifyChallengeM23StreamTrace.observed_bytes{2} =
      (ActualVerifyChallengeM23StreamTrace.observed_final_cp{2},
       ActualVerifyChallengeM23StreamTrace.observed_final_i{2}) /\
    res{2} = ActualVerifyChallengeM23StreamTrace.observed_final_cp{2} /\
    ActualVerifyChallengeM23StreamTrace.observed_final_i{2} =
      challenge_words].
proof.
conseq verify_challenge_m23_exact_stream_trace
  (_ : true ==> true)
  verify_challenge_m23_stream_trace_replay => //=.
move=> &1 &2 [heq htau].
split; first exact heq.
move: heq htau.
smt().
qed.

end VerifyChallengeM23StreamSamplerPostFreeze.
