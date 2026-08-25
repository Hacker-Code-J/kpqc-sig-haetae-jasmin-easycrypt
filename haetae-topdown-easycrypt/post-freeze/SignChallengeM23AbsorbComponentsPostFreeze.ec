require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import ExtractedChallengeAbsorb
               RawSignApiTarget RawVerifyApiTarget
               TranscriptBytes
               SignTranscriptTarget VerifyTranscriptTarget.

theory SignChallengeM23AbsorbComponentsPostFreeze.

(* Partial component closure only.  This file proves the generated helper
   identities and the post-highbits suffix coupling; it does not yet claim
   equality of the full Sign/Verify absorb procedures or sampler outputs. *)

module Sign = SignTranscriptTarget.M.
module Verify = VerifyTranscriptTarget.M.
module RawSign = RawSignApiTarget.M.
module RawVerify = RawVerifyApiTarget.M.

op mu32_prefix = ExtractedChallengeAbsorb.mu32_prefix.

(* The generated highbits absorbers differ only in their source-level names
   and harmless protect ordering. *)
lemma sign_verify_absorb_buf_identity :
  equiv [Sign.__sign_challenge_shake256_absorb_buf ~
         Verify.__verify_shake256_absorb_buf :
    ={sp_0, statep, inp, inlen} ==> ={res}].
proof.
proc.
swap{1} 2 1.
wp.
while (={sp_0, statep, inp, inlen, pos, i}).
+ sp 11 11.
  if => //.
  + wp.
    call (: ={arg} ==> ={res}).
    + by proc; sim.
    auto.
  + auto.
qed.

op mode2_highlen : int = 576.

lemma mode2_highlen_mod_rate : mode2_highlen %% 136 = 32.
proof. by rewrite /mode2_highlen. qed.

(* In Mode 2 the 576-byte highbits prefix leaves the rate position at 32.
   Absorbing the 32-byte LSB segment therefore ends at 64 and cannot enter the
   Sign helper's generic position-136 refill branch. *)
lemma sign_verify_absorb32_from_pos32 :
  equiv [Sign.__sign_challenge_shake256_absorb32 ~
         Verify.__verify_shake256_absorb_mu32 :
    ={sp_0, statep, inp} /\
    BArray16.get64 statep{1} 0 = W64.of_int 32
    ==>
    ={res} /\ BArray16.get64 res{1}.`2 0 = W64.of_int 64].
proof.
proc.
wp.
while (={sp_0, statep, pos, i, inp} /\
       W64.to_uint pos{1} = 32 + W64.to_uint i{1} /\
       W64.to_uint i{1} <= 32).
+ rcondf{1} 12.
  + auto => /> &hr hpos hibound.
    have hpos_small :
        W64.to_uint pos{m} + 1 < W64.modulus by
      smt(W64.ultE W64.to_uint_cmp).
    rewrite W64.to_uint_eq W64.to_uintD_small 1:hpos_small
            W64.to_uint1 W64.of_uintK /=.
    smt().
  auto => /> &hr hpos hibound.
  have hi_small :
      W64.to_uint i{hr} + 1 < W64.modulus.
  + smt(W64.to_uint_cmp).
  have hpos_small :
      W64.to_uint pos{hr} + 1 < W64.modulus.
  + smt(W64.to_uint_cmp).
  have hi_succ :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hpos_succ :
      W64.to_uint (pos{hr} + W64.one) = W64.to_uint pos{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  rewrite hi_succ hpos_succ.
  smt().
+ auto => /> &hr hstate.
  rewrite /protect_64 /protect_ptr hstate W64.of_uintK /=.
  move=> i0 pos0 sp00 hdone hpos hi32.
  move: hdone.
  rewrite W64.ultE W64.of_uintK /=.
  have hi_done : W64.to_uint i0 = 32 by
    smt(W64.to_uint_cmp).
  have hpos_done : W64.to_uint pos0 = 64 by smt().
  smt().
qed.

lemma sign_verify_mu32_from_pos64 :
  equiv [Sign.__sign_challenge_shake256_absorb_mu32 ~
         Verify.__verify_shake256_absorb_mu32 :
    ={sp_0, statep} /\
    BArray16.get64 statep{1} 0 = W64.of_int 64 /\
    mu32_prefix inp{1} inp{2}
    ==>
    ={res}].
proof.
exact ExtractedChallengeAbsorb.sign_verify_mu32_absorb_from_pos64.
qed.

lemma sign_verify_keccak_init_identity :
  equiv [Sign._keccak_init_state ~ Verify._keccak_init_state :
    ={sp_0} ==> ={res}].
proof.
proc; sim.
qed.

lemma sign_verify_challenge_finalize_identity :
  equiv [Sign.__poly_challenge_shake256_finalize ~
         Verify.__poly_challenge_shake256_finalize :
    ={sp_0, statep} ==> ={res}].
proof.
proc; sim.
qed.

lemma raw_sign_absorb_buf_equiv_focused :
  equiv [RawSign.__sign_challenge_shake256_absorb_buf ~
         Sign.__sign_challenge_shake256_absorb_buf :
    ={sp_0, statep, inp, inlen} ==> ={res}].
proof. by proc; sim. qed.

lemma raw_verify_absorb_buf_equiv_focused :
  equiv [RawVerify.__verify_shake256_absorb_buf ~
         Verify.__verify_shake256_absorb_buf :
    ={sp_0, statep, inp, inlen} ==> ={res}].
proof. by proc; sim. qed.

lemma raw_sign_absorb32_equiv_focused :
  equiv [RawSign.__sign_challenge_shake256_absorb32 ~
         Sign.__sign_challenge_shake256_absorb32 :
    ={sp_0, statep, inp} ==> ={res}].
proof. by proc; sim. qed.

lemma raw_verify_absorb_mu32_equiv_focused :
  equiv [RawVerify.__verify_shake256_absorb_mu32 ~
         Verify.__verify_shake256_absorb_mu32 :
    ={sp_0, statep, inp} ==> ={res}].
proof. by proc; sim. qed.

lemma raw_sign_absorb_mu32_equiv_focused :
  equiv [RawSign.__sign_challenge_shake256_absorb_mu32 ~
         Sign.__sign_challenge_shake256_absorb_mu32 :
    ={sp_0, statep, inp} ==> ={res}].
proof. by proc; sim. qed.

lemma raw_sign_finalize_equiv_focused :
  equiv [RawSign.__poly_challenge_shake256_finalize ~
         Sign.__poly_challenge_shake256_finalize :
    ={sp_0, statep} ==> ={res}].
proof. by proc; sim. qed.

lemma raw_verify_finalize_equiv_focused :
  equiv [RawVerify.__poly_challenge_shake256_finalize ~
         Verify.__poly_challenge_shake256_finalize :
    ={sp_0, statep} ==> ={res}].
proof. by proc; sim. qed.

lemma mode2_sign_verify_challenge_input_bytes
    highbits_s highbits_v lsb_s lsb_v mu64 mu32 :
  highbits_s = highbits_v =>
  lsb_s = lsb_v =>
  TranscriptBytes.mu32 mu64 = mu32 =>
  TranscriptBytes.sign_challenge_input highbits_s lsb_s mu64 =
  TranscriptBytes.verify_challenge_input highbits_v lsb_v mu32.
proof.
exact TranscriptBytes.challenge_input_eq_components.
qed.

module SignChallengeAbsorbSuffix = {
  proc run(sp_0 : BArray200.t, statep : BArray16.t,
           lsbp : BArray32.t, mup : BArray64.t) : BArray200.t = {
    (sp_0, statep) <@
      Sign.__sign_challenge_shake256_absorb32(sp_0, statep, lsbp);
    (sp_0, statep) <@
      Sign.__sign_challenge_shake256_absorb_mu32(sp_0, statep, mup);
    sp_0 <@
      Sign.__poly_challenge_shake256_finalize(sp_0, statep);
    return sp_0;
  }
}.

module VerifyChallengeAbsorbSuffix = {
  proc run(sp_0 : BArray200.t, statep : BArray16.t,
           lsbp : BArray32.t, mup : BArray32.t) : BArray200.t = {
    (sp_0, statep) <@
      Verify.__verify_shake256_absorb_mu32(sp_0, statep, lsbp);
    (sp_0, statep) <@
      Verify.__verify_shake256_absorb_mu32(sp_0, statep, mup);
    sp_0 <@
      Verify.__poly_challenge_shake256_finalize(sp_0, statep);
    return sp_0;
  }
}.

lemma sign_verify_absorb_suffix_from_pos32 :
  equiv [SignChallengeAbsorbSuffix.run ~ VerifyChallengeAbsorbSuffix.run :
    ={sp_0, statep, lsbp} /\
    BArray16.get64 statep{1} 0 = W64.of_int 32 /\
    mu32_prefix mup{1} mup{2}
    ==>
    ={res}].
proof.
proc.
call sign_verify_challenge_finalize_identity.
call sign_verify_mu32_from_pos64.
call sign_verify_absorb32_from_pos32.
auto => />.
qed.

(* The only remaining premise for composing the full generated absorb calls is
   a focused proof that the 576-byte highbits helper started at position zero
   returns position 32.  The byte/state equality of that helper, the LSB
   32-to-64 bridge, the mu-prefix 64-to-96 bridge, and finalization equality
   are all closed above. *)

end SignChallengeM23AbsorbComponentsPostFreeze.
