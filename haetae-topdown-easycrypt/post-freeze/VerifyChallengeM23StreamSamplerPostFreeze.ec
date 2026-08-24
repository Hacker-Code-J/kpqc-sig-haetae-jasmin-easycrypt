require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget
               KeygenShakeStreamSpec
               VerifyChallengeM23SamplerStructurePostFreeze
               VerifyChallengeM23SqueezeStreamPostFreeze.

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

op challenge_squeeze_consumed_prefix
    (initial : int list) (blocks pos : int) : int list =
  KeygenShakeStreamSpec.shake256_squeeze_bytes initial (blocks - 1) ++
  take pos
    (KeygenShakeStreamSpec.shake256_squeeze_block initial (blocks - 1)).

lemma challenge_squeeze_consumed_prefix_initial initial :
  challenge_squeeze_consumed_prefix initial 1 0 = [].
proof.
rewrite /challenge_squeeze_consumed_prefix /=.
rewrite /KeygenShakeStreamSpec.shake256_squeeze_bytes
        KeygenShakeStreamSpec.squeeze_bytes_iter0 take0.
trivial.
qed.

lemma challenge_squeeze_consumed_prefix_refill initial blocks :
  1 <= blocks =>
  challenge_squeeze_consumed_prefix initial blocks 136 =
    challenge_squeeze_consumed_prefix initial (blocks + 1) 0.
proof.
move=> hblocks.
rewrite /challenge_squeeze_consumed_prefix.
rewrite take0 cats0.
rewrite (_ : blocks + 1 - 1 = blocks) 1:/#.
rewrite (_ : 136 = size
  (KeygenShakeStreamSpec.shake256_squeeze_block initial (blocks - 1))).
+ by rewrite KeygenShakeStreamSpec.shake256_squeeze_block_size.
rewrite take_size.
rewrite -KeygenShakeStreamSpec.shake256_squeeze_bytes_succ 1:/#.
congr; smt().
qed.

lemma challenge_squeeze_consumed_prefix_rcons initial blocks pos :
  1 <= blocks =>
  0 <= pos < 136 =>
  challenge_squeeze_consumed_prefix initial blocks (pos + 1) =
    rcons (challenge_squeeze_consumed_prefix initial blocks pos)
      (nth 0
        (KeygenShakeStreamSpec.shake256_squeeze_block
          initial (blocks - 1)) pos).
proof.
move=> hblocks hpos.
rewrite /challenge_squeeze_consumed_prefix.
rewrite (take_nth 0 pos
  (KeygenShakeStreamSpec.shake256_squeeze_block initial (blocks - 1))).
+ rewrite KeygenShakeStreamSpec.shake256_squeeze_block_size.
  exact hpos.
by rewrite rcons_cat.
qed.

lemma challenge_squeeze_consumed_prefix_take initial blocks pos :
  1 <= blocks =>
  0 <= pos <= 136 =>
  challenge_squeeze_consumed_prefix initial blocks pos =
    take ((blocks - 1) * 136 + pos)
      (KeygenShakeStreamSpec.shake256_squeeze_bytes initial blocks).
proof.
move=> hblocks hpos.
have hcat := KeygenShakeStreamSpec.shake256_squeeze_bytes_succ
  initial (blocks - 1) _.
+ smt().
rewrite (_ : blocks - 1 + 1 = blocks) 1:/# in hcat.
rewrite hcat /challenge_squeeze_consumed_prefix.
rewrite take_catr.
+ rewrite KeygenShakeStreamSpec.squeeze_bytes_iter_size 1:/# 1:/#.
  smt().
rewrite KeygenShakeStreamSpec.squeeze_bytes_iter_size 1:/# 1:/#.
congr; smt().
qed.

module ActualVerifyChallengeM23StreamTrace = {
  var observed_bytes : int list
  var observed_init_cp : BArray1024.t
  var observed_start_i : int
  var observed_final_cp : BArray1024.t
  var observed_final_i : int
  var observed_squeeze_initial : int list
  var observed_loaded_blocks : int
  var observed_final_pos : int
  var observed_final_state : BArray200.t

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
    var loaded_blocks : int;

    bp <- witness;
    buf <- witness;
    sp_0 <- witness;
    state <- witness;
    observed_bytes <- [];
    observed_init_cp <- witness;
    observed_start_i <- 0;
    observed_final_cp <- witness;
    observed_final_i <- 0;
    observed_squeeze_initial <- [];
    observed_loaded_blocks <- 0;
    observed_final_pos <- 0;
    observed_final_state <- witness;
    loaded_blocks <- 0;

    sp_0 <- state;
    bp <- buf;
    sp_0 <@ Verify.__verify_challenge_absorb
      (sp_0, highp, highlen, lsbp, mup);
    observed_squeeze_initial <- KeygenShakeStreamSpec.state_bytes_le sp_0;
    (bp, sp_0) <@ Verify.__poly_challenge_squeeze256_136 (bp, sp_0);
    observed_bytes <- [];
    loaded_blocks <- 1;
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
        loaded_blocks <- loaded_blocks + 1;
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
    observed_loaded_blocks <- loaded_blocks;
    observed_final_pos <- W64.to_uint pos;
    observed_final_state <- sp_0;
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
    move=> hacc.
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
    move=> hrej.
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
  wp.
  call (_ : true ==> true); first by auto.
  auto => />.
  move=> result observed_bytes cp0 i0 pos0 hdone hi hpos hreplay.
  have hcw : challenge_words = 256 by trivial.
  move: hdone hi.
  rewrite W64.ultE W64.of_uintK /=.
  smt(W64.to_uint_cmp).
qed.

(* Partial correctness only: the post-absorb state is treated as an opaque
   SHAKE256 starting state.  The theorem characterizes every loaded block and
   consumed byte, but not absorb framing, termination, distributions, or any
   paper-level challenge equality. *)
lemma verify_challenge_m23_stream_trace_squeeze_replay :
  hoare [ActualVerifyChallengeM23StreamTrace.run :
    tau = W64.of_int mode2_tau ==>
    1 <= ActualVerifyChallengeM23StreamTrace.observed_loaded_blocks /\
    0 <= ActualVerifyChallengeM23StreamTrace.observed_final_pos <= 136 /\
    KeygenShakeStreamSpec.state_bytes_le
      ActualVerifyChallengeM23StreamTrace.observed_final_state =
      KeygenShakeStreamSpec.squeeze_state_iter
        ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial
        ActualVerifyChallengeM23StreamTrace.observed_loaded_blocks /\
    ActualVerifyChallengeM23StreamTrace.observed_bytes =
      challenge_squeeze_consumed_prefix
        ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial
        ActualVerifyChallengeM23StreamTrace.observed_loaded_blocks
        ActualVerifyChallengeM23StreamTrace.observed_final_pos /\
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
   1 <= loaded_blocks /\
   KeygenShakeStreamSpec.state_bytes_le sp_0 =
     KeygenShakeStreamSpec.squeeze_state_iter
       ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial
       loaded_blocks /\
   VerifyChallengeM23SqueezeStreamPostFreeze.squeeze136_fips_prefix_matches
     bp
     (KeygenShakeStreamSpec.shake256_squeeze_block
       ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial
       (loaded_blocks - 1)) 136 /\
   ActualVerifyChallengeM23StreamTrace.observed_bytes =
     challenge_squeeze_consumed_prefix
       ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial
       loaded_blocks (W64.to_uint pos) /\
   stream_sampler_replay
     ActualVerifyChallengeM23StreamTrace.observed_init_cp
     ActualVerifyChallengeM23StreamTrace.observed_start_i
     ActualVerifyChallengeM23StreamTrace.observed_bytes =
     (cp, W64.to_uint i)); last first.
+ seq 18 :
    (tau = W64.of_int mode2_tau /\
     ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial =
       KeygenShakeStreamSpec.state_bytes_le sp_0).
  + wp.
    call (_ : true ==> true); first by auto.
    auto => />.
  + wp.
    call (_ : true ==> true); first by auto.
    wp.
    exlim bp => before_out.
    exlim sp_0 => before_state.
    call
      (VerifyChallengeM23SqueezeStreamPostFreeze.verify_poly_challenge_squeeze256_136_block
         before_out before_state).
    auto => />.
    move=> result hblock hstate result0.
    split.
    + by rewrite challenge_squeeze_consumed_prefix_initial.
    move=> bp0 cp0 i0 blocks0 pos0 sp0 hdone hi hpos hblocks
            hstate0 hblock0 hreplay.
    split.
    + smt(W64.to_uint_cmp).
    have hcw : challenge_words = 256 by trivial.
    move: hdone hi.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
+ seq 1 :
    (tau = W64.of_int mode2_tau /\
     W64.to_uint i < challenge_words /\
     W64.to_uint pos < 136 /\
     1 <= loaded_blocks /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial
         loaded_blocks /\
     VerifyChallengeM23SqueezeStreamPostFreeze.squeeze136_fips_prefix_matches
       bp
       (KeygenShakeStreamSpec.shake256_squeeze_block
         ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial
         (loaded_blocks - 1)) 136 /\
     ActualVerifyChallengeM23StreamTrace.observed_bytes =
       challenge_squeeze_consumed_prefix
         ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial
         loaded_blocks (W64.to_uint pos) /\
     stream_sampler_replay
       ActualVerifyChallengeM23StreamTrace.observed_init_cp
       ActualVerifyChallengeM23StreamTrace.observed_start_i
       ActualVerifyChallengeM23StreamTrace.observed_bytes =
       (cp, W64.to_uint i)).
  + if.
    + wp.
      exlim bp => before_out.
      exlim sp_0 => before_state.
      call
        (VerifyChallengeM23SqueezeStreamPostFreeze.verify_poly_challenge_squeeze256_136_block
           before_out before_state).
      auto => />.
      move=> &hr hi hpos hblocks hstate hblock hsampler hloop
              hrefill callresult hresultblock hresultstate.
      have hpos136 : W64.to_uint pos{hr} = 136.
      * move: hrefill.
        rewrite W64.uleE W64.of_uintK /=.
        smt(W64.to_uint_cmp).
      have hstate_next :
          KeygenShakeStreamSpec.state_bytes_le callresult.`2 =
          KeygenShakeStreamSpec.squeeze_state_iter
            ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial{hr}
            (loaded_blocks{hr} + 1).
      * rewrite hresultstate hstate.
        apply
          VerifyChallengeM23SqueezeStreamPostFreeze.squeeze_state_iter_shift_one.
        smt().
      have hblock_next :
          VerifyChallengeM23SqueezeStreamPostFreeze.squeeze136_fips_prefix_matches
              callresult.`1
              (KeygenShakeStreamSpec.shake256_squeeze_block
                ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial{hr}
                loaded_blocks{hr}) 136.
      * move: hresultblock.
        rewrite /VerifyChallengeM23SqueezeStreamPostFreeze.shake256_136_block_matches
                hstate.
        rewrite
          VerifyChallengeM23SqueezeStreamPostFreeze.shake256_squeeze_block_shift
          1:/#.
        trivial.
      have hp := challenge_squeeze_consumed_prefix_refill
        ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial{hr}
        loaded_blocks{hr} hblocks.
      rewrite /protect_ptr.
      do split.
      * have hcw : challenge_words = 256 by trivial.
        move: hloop.
        rewrite W64.ultE W64.of_uintK /=.
        smt().
      * smt().
      * exact hstate_next.
      * exact hblock_next.
      * rewrite hpos136.
        exact hp.
    + auto => />.
      move=> &hr hi hpos hblocks hstate hblock hsampler hloop hnot.
      have hcw : challenge_words = 256 by trivial.
      move: hloop hnot.
      rewrite W64.ultE W64.uleE !W64.of_uintK /=.
      smt(W64.to_uint_cmp).
  + wp.
    auto => />.
    move=> &hr hi hpos hblocks hstate hblock hsampler.
    have hnextpos :
        W64.to_uint (pos{hr} + W64.one) = W64.to_uint pos{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hblockbyte := hblock (W64.to_uint pos{hr}) _.
    + smt(W64.to_uint_cmp).
    have hpstep := challenge_squeeze_consumed_prefix_rcons
      ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial{hr}
      loaded_blocks{hr} (W64.to_uint pos{hr}) hblocks _.
    + smt(W64.to_uint_cmp).
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
      have hbyte :
          0 <=
            W8.to_uint
              (BArray136.get8 bp{hr} (W64.to_uint pos{hr})) <=
            W64.to_uint i{hr}.
      * move: hacc.
        rewrite W64.ultE W64.to_uintD_small 1:/# W64.to_uint1
                W2u32.to_uint_zeroextu64 W4u8.to_uint_zeroextu32.
        smt(W8.to_uint_cmp pow2_8).
      have hsampler_next :
          stream_sampler_replay
            ActualVerifyChallengeM23StreamTrace.observed_init_cp{hr}
            ActualVerifyChallengeM23StreamTrace.observed_start_i{hr}
            (rcons
              (challenge_squeeze_consumed_prefix
                ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial{hr}
                loaded_blocks{hr} (W64.to_uint pos{hr}))
              (W8.to_uint
                (BArray136.get8 bp{hr} (W64.to_uint pos{hr})))) =
          (challenge_shuffle_update cp{hr} (W64.to_uint i{hr})
             (W8.to_uint
               (BArray136.get8 bp{hr} (W64.to_uint pos{hr}))),
           W64.to_uint i{hr} + 1).
      * rewrite stream_sampler_replay_rcons hsampler.
        apply stream_sampler_step_accept.
        - smt(W64.to_uint_cmp).
        - exact hbyte.
      do split.
      * rewrite hnexti.
        have hcw : challenge_words = 256 by trivial.
        smt().
      * rewrite hnextpos.
        smt().
      * rewrite hnextpos.
        rewrite hpstep hblockbyte.
      move: hsampler_next.
      rewrite /challenge_shuffle_update.
      trivial.
    smt(stream_sampler_replay_rcons stream_sampler_step_reject
        W8.to_uint_cmp W64.to_uint_cmp).
    auto => />.
    move=> hrej.
    rewrite /protect_64 in hrej.
    have hnotbyte :
        !(0 <=
            W8.to_uint
              (BArray136.get8 bp{hr} (W64.to_uint pos{hr})) <=
            W64.to_uint i{hr}).
    + move: hrej.
      rewrite W64.ultE W64.to_uintD_small 1:/# W64.to_uint1
              W2u32.to_uint_zeroextu64 W4u8.to_uint_zeroextu32.
      smt(W8.to_uint_cmp pow2_8).
    do split.
    + smt().
    + rewrite hnextpos.
      smt().
    + rewrite hnextpos hpstep hblockbyte.
      trivial.
    rewrite stream_sampler_replay_rcons hsampler.
    apply stream_sampler_step_reject.
    + smt(W64.to_uint_cmp).
    + exact hnotbyte.
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

lemma verify_challenge_m23_actual_squeeze_replay :
  equiv [Verify.__verify_challenge_m23 ~
         ActualVerifyChallengeM23StreamTrace.run :
    ={Glob.mem, cp, highp, highlen, lsbp, mup, tau} /\
    tau{1} = W64.of_int mode2_tau
    ==>
    ={Glob.mem, res} /\
    1 <= ActualVerifyChallengeM23StreamTrace.observed_loaded_blocks{2} /\
    0 <= ActualVerifyChallengeM23StreamTrace.observed_final_pos{2} <= 136 /\
    KeygenShakeStreamSpec.state_bytes_le
      ActualVerifyChallengeM23StreamTrace.observed_final_state{2} =
      KeygenShakeStreamSpec.squeeze_state_iter
        ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial{2}
        ActualVerifyChallengeM23StreamTrace.observed_loaded_blocks{2} /\
    ActualVerifyChallengeM23StreamTrace.observed_bytes{2} =
      challenge_squeeze_consumed_prefix
        ActualVerifyChallengeM23StreamTrace.observed_squeeze_initial{2}
        ActualVerifyChallengeM23StreamTrace.observed_loaded_blocks{2}
        ActualVerifyChallengeM23StreamTrace.observed_final_pos{2} /\
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
  verify_challenge_m23_stream_trace_squeeze_replay => //=.
move=> &1 &2 [heq htau].
split; first exact heq.
move: heq htau.
smt().
qed.

end VerifyChallengeM23StreamSamplerPostFreeze.
