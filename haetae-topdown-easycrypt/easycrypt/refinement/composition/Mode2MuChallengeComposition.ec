require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

require import ExtractedPackedKeyPrefix Mode2KeyMemoryBridge.
require import ExtractedMuHashPrefix ExtractedChallengeAbsorb TranscriptBytes.

theory Mode2MuChallengeComposition.

module MuSign = ExtractedMuHashPrefix.SignRawMuTop.
module MuVerify = ExtractedMuHashPrefix.VerifyRawMuTop.
module ChallengeSign = ExtractedChallengeAbsorb.Sign.
module ChallengeVerify = ExtractedChallengeAbsorb.Verify.

op mode2_vkbytes : int = 992.

lemma mode2_base_zero_no_wrap :
  W64.to_uint W64.zero + mode2_vkbytes < W64.modulus.
proof.
by rewrite /mode2_vkbytes W64.to_uint0 /=.
qed.

lemma mu_prefix_relation_bridge mu64 mu32 :
  ExtractedMuHashPrefix.mu32_prefix mu64 mu32 =>
  ExtractedChallengeAbsorb.mu32_prefix mu64 mu32.
proof.
by rewrite /ExtractedMuHashPrefix.mu32_prefix
           /ExtractedChallengeAbsorb.mu32_prefix.
qed.

lemma keygen_prefix_reaches_mu_memory
    (sk : BArray2752.t) (vk : BArray2080.t)
    (mem : global_mem_t) (base : W64.t) :
  ExtractedPackedKeyPrefix.vk_prefix_eq
    sk vk ExtractedPackedKeyPrefix.mode2_vkbytes =>
  ExtractedMuHashPrefix.sk_memory_prefix
    sk
    (stores mem (W64.to_uint base)
      (take mode2_vkbytes (BArray2080.to_list vk)))
    base.
proof.
move=> hpref.
have hstored :=
  Mode2KeyMemoryBridge.keygen_prefix_memory_relation_is_constructible
    sk vk mem (W64.to_uint base) hpref.
rewrite /ExtractedMuHashPrefix.sk_memory_prefix => i hi.
by rewrite (hstored i hi).
qed.

module SignRawMuThenChallenge = {
  proc run (mup : BArray64.t, skp : BArray2752.t,
            preaddr : W64.t, prelen : W64.t,
            maddr : W64.t, mlen : W64.t,
            challenge_state : BArray200.t,
            challenge_pos : BArray16.t) : BArray200.t * BArray16.t = {
    mup <@ MuSign.run(mup, skp, preaddr, prelen, maddr, mlen);
    (challenge_state, challenge_pos) <@
      ChallengeSign.__sign_challenge_shake256_absorb_mu32
        (challenge_state, challenge_pos, mup);
    return (challenge_state, challenge_pos);
  }
}.

module VerifyRawMuThenChallenge = {
  proc run (mup : BArray32.t, vkp : W64.t,
            prep : W64.t, prelen : W64.t,
            mp : W64.t, mlen : W64.t,
            challenge_state : BArray200.t,
            challenge_pos : BArray16.t) : BArray200.t * BArray16.t = {
    mup <@ MuVerify.run(mup, vkp, prep, prelen, mp, mlen);
    (challenge_state, challenge_pos) <@
      ChallengeVerify.__verify_shake256_absorb_mu32
        (challenge_state, challenge_pos, mup);
    return (challenge_state, challenge_pos);
  }
}.

lemma raw_mu_to_challenge_suffix_zero_loss
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [SignRawMuThenChallenge.run ~ VerifyRawMuThenChallenge.run :
    ={Glob.mem, challenge_state, challenge_pos} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    vkp{2} = base /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 mem0 base /\
    BArray16.get64 challenge_pos{1} 0 = W64.of_int 64
    ==>
    ={res}].
proof.
move=> hbase.
proc.
call ExtractedChallengeAbsorb.sign_verify_mu32_absorb_from_pos64.
call (ExtractedMuHashPrefix.sign_verify_raw_mu_top_wrappers_prefix
        sk0 mem0 base hbase).
auto => />.
qed.

lemma challenge_input_eq_after_raw_mu
    highbits lsb mu64 mu32 :
  take 32 mu64 = mu32 =>
  TranscriptBytes.sign_challenge_input highbits lsb mu64 =
  TranscriptBytes.verify_challenge_input highbits lsb mu32.
proof.
exact (TranscriptBytes.challenge_input_eq_from_mu_prefix
         highbits lsb mu64 mu32).
qed.

end Mode2MuChallengeComposition.
