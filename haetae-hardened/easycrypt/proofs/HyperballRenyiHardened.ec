require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import HardenedSignerTarget GaussianIidBufferSpec
  HyperballIidPayloadSpec HyperballIidPayloadBatch.

module HRHSigner = HardenedSignerTarget.M(HardenedSignerTarget.Syscall).

(* These bridges check the fresh hardened namespace against the pinned
   Gaussian helpers, including the unchanged calls nested in the consumer. *)
lemma hrh_copy_signs_equiv :
  equiv [GIBSigner.__sample_gauss_N_copy_signs_at ~ HRHSigner.__sample_gauss_N_copy_signs_at :
    ={signsp,bufp,signbytes,signoff} ==> ={res}].
proof. proc; sim. qed.

lemma hrh_carry_equiv :
  equiv [GIBSigner._sample_gauss_N_carry ~ HRHSigner._sample_gauss_N_carry :
    ={bufp,bytecnt,signbytes,firstflag,off} ==> ={res}].
proof. proc; sim. qed.

lemma hrh_consume_equiv :
  equiv [GIBSigner.__sample_gauss_at ~ HRHSigner.__sample_gauss_at :
    ={rp,sqsump,coefcntp,bufp,counts,dont_write_last,bufoff,outoff} ==> ={res}].
proof. proc; inline *; sim. qed.

(* The byte source is explicit and independent: 49 initial 136-byte blocks,
   the actual sign-copy and finite consumer, then carry and 136-byte refills.
   All executable helper calls use the fresh hardened signer extraction. *)
module HyperballRenyiHardenedBuffer = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var buf : BArray8192.t;
    var count : BArray8.t;
    var bytes : W8.t list;
    var block, available, remaining, accepted : int;
    var has_prefix : bool;
    buf <- witness;
    count <- witness;
    block <- 0;
    while (block < 49) {
      bytes <$ gib_block;
      buf <- gib_fill buf (136 * block) bytes;
      block <- block + 1;
    }
    signsp <@ HRHSigner.__sample_gauss_N_copy_signs_at
      (signsp, buf, W64.of_int 32, W64.of_int sign_offset);
    available <- 6632;
    has_prefix <- true;
    (rp, sqsump, count) <@ HRHSigner.__sample_gauss_at
      (rp, sqsump, count, buf, gib_counts n available, W64.of_int (n - 256),
       W64.of_int 32, W64.of_int sample_offset);
    accepted <- W64.to_uint (BArray8.get64 count 0);
    while (accepted < n) {
      remaining <- available %% 26;
      buf <@ HRHSigner._sample_gauss_N_carry
        (buf, W64.of_int available, W64.of_int 32, W64.of_int (b2i has_prefix),
         W64.of_int remaining);
      bytes <$ gib_block;
      buf <- gib_fill buf remaining bytes;
      available <- remaining + 136;
      (rp, sqsump, count) <@ HRHSigner.__sample_gauss_at
        (rp, sqsump, count, buf, gib_counts (n - accepted) available,
         W64.of_int (n - 256), W64.zero, W64.of_int (sample_offset + accepted));
      accepted <- accepted + W64.to_uint (BArray8.get64 count 0);
      has_prefix <- false;
    }
    return (rp, signsp, sqsump);
  }
}.

lemma hrh_buffer_equiv :
  equiv [GaussianIidBuffer.sample ~ HyperballRenyiHardenedBuffer.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}].
proof.
  proc.
  while (={rp,signsp,sqsump,n,sample_offset,sign_offset,buf,count,
    available,accepted,has_prefix}).
  + wp; call hrh_consume_equiv.
    wp; rnd; call hrh_carry_equiv; auto.
  wp; call hrh_consume_equiv.
  wp; call hrh_copy_signs_equiv.
  while (={rp,signsp,sqsump,n,sample_offset,sign_offset,buf,count,block}).
  + by auto.
  by auto.
qed.

(* The same zero initial arrays and 257,257,256,... schedule as the existing
   iid Hyperball Gaussian batch. Both dummy payloads still enter the square
   accumulator. This model does not invoke the seeded SHAKE controller. *)
module HyperballRenyiHardenedBatch = {
  proc sample(mode : int) : gib_result = {
    var state : gib_result;
    var index : int;
    state <- hip_initial;
    index <- 0;
    while (index < hip_polys mode) {
      state <@ HyperballRenyiHardenedBuffer.sample(state.`1,state.`2,state.`3,
        hip_requests index,256*index,32*index);
      index <- index+1;
    }
    return state;
  }
}.

lemma hrh_batch_equiv :
  equiv [HyperballIidGaussian.sample ~ HyperballRenyiHardenedBatch.sample :
    ={mode} /\ hip_mode mode{1} ==> ={res}].
proof.
  proc.
  while (={mode,index,state} /\ hip_mode mode{1} /\
    0 <= index{1} <= hip_polys mode{1}).
  + wp; call hrh_buffer_equiv; auto => />; smt(hip_call_bounds).
  auto => />; smt(hip_mode_polys).
qed.

lemma hrh_batch_terminates mode &m : hip_mode mode =>
  Pr[HyperballRenyiHardenedBatch.sample(mode) @ &m : true] = 1%r.
proof.
  move=> hm.
  have he : Pr[HyperballIidGaussian.sample(mode) @ &m : true] =
      Pr[HyperballRenyiHardenedBatch.sample(mode) @ &m : true] by
    byequiv hrh_batch_equiv.
  rewrite -he; exact (hip_actual_terminates mode &m hm).
qed.

lemma hrh_batch_total mode0 : hip_mode mode0 =>
  phoare [HyperballRenyiHardenedBatch.sample : mode=mode0 ==> true] = 1%r.
proof.
  move=> hm; bypr => &m ->.
  exact (hrh_batch_terminates mode0 &m hm).
qed.
