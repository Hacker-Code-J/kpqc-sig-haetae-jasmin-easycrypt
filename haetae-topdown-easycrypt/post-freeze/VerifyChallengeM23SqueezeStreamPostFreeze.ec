require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget KeygenSamplerCallersTarget
               KeygenShakeStreamSpec KeygenKeccak1600Spec
               HAETAE_Keccak1600 TargetKeygenKeccak1600.

theory VerifyChallengeM23SqueezeStreamPostFreeze.

(* Partial correctness only: this file covers one fresh 136-byte squeeze block
   from an already-prepared SHAKE256 state. It does not cover absorb
   transcripts, repeated refills, termination, distributional claims, or any
   paper-level challenge equality. *)

module Verify = VerifyCoreTarget.M.
module Keygen = KeygenSamplerCallersTarget.M.

op squeeze136_rate_prefix_matches
    (out : BArray136.t) (state : BArray200.t) (count : int) : bool =
  forall i,
    0 <= i < count =>
    BArray136.get8 out i =
      KeygenShakeStreamSpec.rate_lane_byte state (i %/ 8) (i %% 8).

op squeeze136_fips_prefix_matches
    (out : BArray136.t) (bytes : int list) (count : int) : bool =
  forall i,
    0 <= i < count =>
    W8.to_uint (BArray136.get8 out i) = nth 0 bytes i.

op shake256_136_block_matches
    (out : BArray136.t) (initial : int list) : bool =
  squeeze136_fips_prefix_matches out
    (KeygenShakeStreamSpec.shake256_squeeze_block initial 0) 136.

lemma verify_keygen_keccakf1600_same_state :
  equiv [Verify._keccakf1600 ~ Keygen._keccakf1600 :
    ={sp_0}
    ==>
    ={res}].
proof.
proc; sim.
qed.

lemma verify_keccakf1600_correct (sp0 : BArray200.t) :
  hoare [Verify._keccakf1600 :
    sp_0 = sp0
    ==>
    KeygenKeccak1600Spec.state_of_barray res =
      HAETAE_Keccak1600.keccak_f1600_lanes
        (KeygenKeccak1600Spec.state_of_barray sp0)].
proof.
conseq verify_keygen_keccakf1600_same_state
  (TargetKeygenKeccak1600.keccakf1600_correct sp0).
+ move=> &1 hpre.
   exists sp_0{1}.
   by auto.
+ move=> &1 &2 hres hpost.
   rewrite hres.
   exact hpost.
qed.

lemma squeeze136_rate_prefix_zero out state :
  squeeze136_rate_prefix_matches out state 0.
proof. by rewrite /squeeze136_rate_prefix_matches => i /#. qed.

lemma squeeze136_rate_prefix_set_next out state count :
  0 <= count < 136 =>
  squeeze136_rate_prefix_matches out state count =>
  squeeze136_rate_prefix_matches
    (BArray136.set8 out count
      (KeygenShakeStreamSpec.rate_lane_byte state (count %/ 8) (count %% 8)))
    state (count + 1).
proof.
move=> hcount hprefix.
rewrite /squeeze136_rate_prefix_matches => i hi.
case (i = count) => heq.
+ subst i.
   by rewrite BArray136.get_setE 1:/# 1:/#.
+ have hlt : 0 <= i < count by smt().
   have hp := hprefix i hlt.
   have -> :
       BArray136.get8
         (BArray136.set8 out count
            (KeygenShakeStreamSpec.rate_lane_byte state
               (count %/ 8) (count %% 8))) i =
       BArray136.get8 out i.
   + rewrite BArray136.get_setE 1:/# 1:/#.
     smt().
qed.

lemma squeeze136_fips_prefix_of_rate_prefix out state count :
  0 <= count <= 136 =>
  squeeze136_rate_prefix_matches out state count =>
  squeeze136_fips_prefix_matches
    out (KeygenShakeStreamSpec.state_bytes_le state) count.
proof.
rewrite /squeeze136_fips_prefix_matches /squeeze136_rate_prefix_matches.
move=> hcount hprefix i hi.
rewrite (hprefix i hi).
have hlane : 0 <= i %/ 8 < 25 by smt(divz_cmp).
have hbyte : 0 <= i %% 8 < 8 by smt(modz_cmp).
rewrite KeygenShakeStreamSpec.rate_lane_byte_get8 1:hlane 1:hbyte.
rewrite KeygenShakeStreamSpec.state_bytes_le_nth 1:/#.
congr.
have hdiv := divz_eq i 8.
smt().
qed.

lemma squeeze136_fips_prefix_matches_shake256_block
    out state :
  squeeze136_fips_prefix_matches out
    (KeygenShakeStreamSpec.squeeze_state_iter state 1) 136 =>
  shake256_136_block_matches out state.
proof.
rewrite /shake256_136_block_matches.
rewrite /squeeze136_fips_prefix_matches
        /KeygenShakeStreamSpec.shake256_squeeze_block.
move=> hprefix i hi.
rewrite nth_mkseq 1:hi.
exact (hprefix i hi).
qed.

lemma squeeze_state_iter_shift_one initial blocks :
  0 <= blocks =>
  KeygenShakeStreamSpec.squeeze_state_iter
      (KeygenShakeStreamSpec.squeeze_state_iter initial blocks) 1 =
    KeygenShakeStreamSpec.squeeze_state_iter initial (blocks + 1).
proof.
move=> hblocks.
rewrite (KeygenShakeStreamSpec.squeeze_state_iter_succ
           (KeygenShakeStreamSpec.squeeze_state_iter initial blocks) 0) 1:/#.
rewrite KeygenShakeStreamSpec.squeeze_state_iter0.
rewrite KeygenShakeStreamSpec.squeeze_state_iter_succ 1://.
trivial.
qed.

lemma shake256_squeeze_block_shift initial blocks :
  0 <= blocks =>
  KeygenShakeStreamSpec.shake256_squeeze_block
      (KeygenShakeStreamSpec.squeeze_state_iter initial blocks) 0 =
    KeygenShakeStreamSpec.shake256_squeeze_block initial blocks.
proof.
move=> hblocks.
rewrite /KeygenShakeStreamSpec.shake256_squeeze_block /=.
rewrite squeeze_state_iter_shift_one 1://.
trivial.
qed.

lemma verify_poly_challenge_squeeze256_136_block
    (out0 : BArray136.t) (state0 : BArray200.t) :
  hoare [Verify.__poly_challenge_squeeze256_136 :
    outp = out0 /\ sp_0 = state0
    ==>
    shake256_136_block_matches
      res.`1 (KeygenShakeStreamSpec.state_bytes_le state0) /\
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.state_bytes_le state0) 1].
proof.
proc.
while
  (squeeze136_rate_prefix_matches outp sp_0 (W64.to_uint i) /\
   W64.to_uint idx = W64.to_uint i /\
   0 <= W64.to_uint i <= 136 /\
   W64.to_uint i %% 8 = 0 /\
   KeygenKeccak1600Spec.state_of_barray sp_0 =
     HAETAE_Keccak1600.keccak_f1600_lanes
       (KeygenKeccak1600Spec.state_of_barray state0)).
+ wp.
   while
     (squeeze136_rate_prefix_matches outp sp_0
        (W64.to_uint i + W64.to_uint j) /\
      W64.to_uint idx = W64.to_uint i + W64.to_uint j /\
      W64.to_uint lane = W64.to_uint i %/ 8 /\
      t = KeygenShakeStreamSpec.drop_bytes
            (BArray200.get64 sp_0 (W64.to_uint i %/ 8))
            (W64.to_uint j) /\
      0 <= W64.to_uint i < 136 /\
      W64.to_uint i %% 8 = 0 /\
      0 <= W64.to_uint j <= 8 /\
      KeygenKeccak1600Spec.state_of_barray sp_0 =
        HAETAE_Keccak1600.keccak_f1600_lanes
          (KeygenKeccak1600Spec.state_of_barray state0)).
   + auto => /> &hr hprefix hidx hlane hi0 hi136 himod hj0 hj8 hperm hguard.
     rewrite W64.ultE W64.of_uintK /= in hguard.
     have hnextj :
         W64.to_uint (j{hr} + W64.one) = W64.to_uint j{hr} + 1.
     + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
       trivial.
     have hnextidx :
         W64.to_uint (idx{hr} + W64.one) = W64.to_uint idx{hr} + 1.
     + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
       trivial.
     have hcount :
         0 <= W64.to_uint i{hr} + W64.to_uint j{hr} < 136 by smt().
     have hi8 := KeygenShakeStreamSpec.div8_split
       (W64.to_uint i{hr}) hi0 himod.
     have hquot :
         (W64.to_uint i{hr} + W64.to_uint j{hr}) %/ 8 =
         W64.to_uint i{hr} %/ 8 by smt(divz_eq modz_cmp).
     have hrem :
         (W64.to_uint i{hr} + W64.to_uint j{hr}) %% 8 =
         W64.to_uint j{hr} by smt(divz_eq modz_cmp).
     have hp := squeeze136_rate_prefix_set_next
       outp{hr} sp_0{hr}
       (W64.to_uint i{hr} + W64.to_uint j{hr})
       hcount hprefix.
     rewrite /KeygenShakeStreamSpec.rate_lane_byte hquot hrem in hp.
     do split.
     + rewrite hnextj hidx.
       have -> :
           W64.to_uint i{hr} + (W64.to_uint j{hr} + 1) =
           W64.to_uint i{hr} + W64.to_uint j{hr} + 1 by ring.
       exact hp.
     + rewrite hnextidx hnextj hidx.
       ring.
     + rewrite hnextj KeygenShakeStreamSpec.drop_bytes_succ 1:/#.
       trivial.
     + smt().
     + smt().
   auto => /> &hr hprefix hidx hi0 hi136 himod hperm hguard.
   split.
   + split.
     * rewrite W64.shr_div_le 1:/# /=.
     split.
     * rewrite KeygenShakeStreamSpec.drop_bytes0.
       rewrite W64.shr_div_le 1:/# /=.
     rewrite W64.ultE W64.of_uintK /= in hguard.
     exact hguard.
   move=> idx0 j0 outp0 hjdone hpdone hidx0 hlane hi136' hj0 hj8.
   rewrite W64.ultE W64.of_uintK /= in hjdone.
   have hj : W64.to_uint j0 = 8 by smt(W64.to_uint_cmp).
   have hjword : j0 = W64.of_int 8.
   + by rewrite -(W64.to_uintK' j0) hj.
   subst j0.
   rewrite W64.to_uintD_small 1:/# /=.
   do split.
   + exact hpdone.
   + rewrite hidx0.
     ring.
   + smt(W64.to_uint_cmp).
   + smt(W64.to_uint_cmp).
   smt().
+ wp.
  call (verify_keccakf1600_correct state0).
  auto => /> state1 hperm.
  split.
  + exact (squeeze136_rate_prefix_zero
      (SLH64.protect_ptr out0 W64.zero) state1).
  move=> i0 idx0 outp0 hdone hprefix hidx hi0 hi136 himod.
  have hiword : i0 = W64.of_int 136.
  + apply W64.to_uint_eq.
    rewrite W64.of_uintK /=.
    move: hdone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  subst i0.
  have hstate :
      KeygenShakeStreamSpec.state_bytes_le state1 =
      KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.state_bytes_le state0) 1.
  + apply (KeygenShakeStreamSpec.squeeze_state_iter_barray_step
             (KeygenShakeStreamSpec.state_bytes_le state0)
             state0 state1 0).
    * trivial.
    * by rewrite KeygenShakeStreamSpec.squeeze_state_iter0.
    * exact hperm.
  split.
  + apply squeeze136_fips_prefix_matches_shake256_block.
    rewrite -hstate.
    apply squeeze136_fips_prefix_of_rate_prefix.
    * smt().
    * exact hprefix.
  + exact hstate.
qed.

lemma verify_poly_challenge_squeeze256_136_iter_block
    (out0 : BArray136.t) (before : BArray200.t)
    (initial : int list) (blocks : int) :
  0 <= blocks =>
  KeygenShakeStreamSpec.state_bytes_le before =
    KeygenShakeStreamSpec.squeeze_state_iter initial blocks =>
  hoare [Verify.__poly_challenge_squeeze256_136 :
    outp = out0 /\ sp_0 = before
    ==>
    squeeze136_fips_prefix_matches
      res.`1
      (KeygenShakeStreamSpec.shake256_squeeze_block initial blocks) 136 /\
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.squeeze_state_iter initial (blocks + 1)].
proof.
move=> hblocks hbefore.
conseq
  (verify_poly_challenge_squeeze256_136_block out0 before).
+ move=> &hr hpre.
  smt().
qed.

end VerifyChallengeM23SqueezeStreamPostFreeze.
