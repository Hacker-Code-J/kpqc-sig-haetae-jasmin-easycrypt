require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

require import SignMuHashTarget VerifyMuHashTarget.
require import ExtractedMuHashPrefix ExtractedChallengeAbsorb.
require import ExactMuTopControl.
require import ExtractedPackedKeyPrefix Mode2MuChallengeComposition.

theory ExactMode2RawMuComposition.

module SignMu = SignMuHashTarget.M.
module VerifyMu = VerifyMuHashTarget.M.
module ChallengeSign = ExtractedChallengeAbsorb.Sign.
module ChallengeVerify = ExtractedChallengeAbsorb.Verify.
module KeyGen = ExtractedPackedKeyPrefix.Parent.

op mode2_vkbytes : int = 992.

lemma generated_raw_mu_preconditions_from_keygen_prefix
    (sk : BArray2752.t) (vk : BArray2080.t) (mem : global_mem_t) :
  ExtractedPackedKeyPrefix.vk_prefix_eq
    sk vk ExtractedPackedKeyPrefix.mode2_vkbytes =>
  W64.to_uint W64.zero + mode2_vkbytes < W64.modulus /\
  ExactMuTopControl.raw_prelen W64.zero /\
  ExactMuTopControl.valid_region W64.zero W64.zero /\
  ExactMuTopControl.valid_region W64.zero W64.zero /\
  ExtractedMuHashPrefix.sk_memory_prefix
    sk (stores mem 0 (take mode2_vkbytes (BArray2080.to_list vk)))
    W64.zero.
proof.
move=> hpref /=.
split.
+ exact Mode2MuChallengeComposition.mode2_base_zero_no_wrap.
split.
+ exact ExactMuTopControl.raw_prelen_zero.
split.
+ by rewrite /ExactMuTopControl.valid_region W64.to_uint0 /=.
split.
+ by rewrite /ExactMuTopControl.valid_region W64.to_uint0 /=.
have hmem :
    ExtractedMuHashPrefix.sk_memory_prefix
      sk (stores mem 0 (take mode2_vkbytes (BArray2080.to_list vk)))
      W64.zero.
+ exact (Mode2MuChallengeComposition.keygen_prefix_reaches_mu_memory
           sk vk mem W64.zero hpref).
exact hmem.
qed.

lemma keypair_internal_return_reaches_generated_raw_mu_preconditions
    (mem : global_mem_t) :
  hoare [KeyGen.crypto_sign_keypair_internal_mode2_jazz :
    true
    ==>
    let verify_mem =
      stores mem 0
        (take mode2_vkbytes (BArray2080.to_list res.`1)) in
      W64.to_uint W64.zero + mode2_vkbytes < W64.modulus /\
      ExactMuTopControl.raw_prelen W64.zero /\
      ExactMuTopControl.valid_region W64.zero W64.zero /\
      ExactMuTopControl.valid_region W64.zero W64.zero /\
      ExtractedMuHashPrefix.sk_memory_prefix
        res.`2 verify_mem W64.zero].
proof.
conseq ExtractedPackedKeyPrefix.keypair_internal_mode2_return_prefix.
move=> &hr /> result hpref.
exact (generated_raw_mu_preconditions_from_keygen_prefix
         result.`2 result.`1 mem hpref).
qed.

module GeneratedSignRawMuThenChallenge = {
  proc run (mup : BArray64.t, skp : BArray2752.t,
            preaddr : W64.t, prelen : W64.t,
            maddr : W64.t, mlen : W64.t,
            challenge_state : BArray200.t,
            challenge_pos : BArray16.t) : BArray200.t * BArray16.t = {
    mup <@ SignMu._sf_mu_rawpre
      (mup, skp, W64.of_int mode2_vkbytes,
       preaddr, prelen, maddr, mlen);
    (challenge_state, challenge_pos) <@
      ChallengeSign.__sign_challenge_shake256_absorb_mu32
        (challenge_state, challenge_pos, mup);
    return (challenge_state, challenge_pos);
  }
}.

module GeneratedVerifyRawMuThenChallenge = {
  proc run (mup : BArray32.t, vkp : W64.t,
            prep : W64.t, prelen : W64.t,
            mp : W64.t, mlen : W64.t,
            challenge_state : BArray200.t,
            challenge_pos : BArray16.t) : BArray200.t * BArray16.t = {
    mup <@ VerifyMu.__verify_hash_mu
      (mup, vkp, prep, prelen, mp, mlen,
       W64.of_int mode2_vkbytes);
    (challenge_state, challenge_pos) <@
      ChallengeVerify.__verify_shake256_absorb_mu32
        (challenge_state, challenge_pos, mup);
    return (challenge_state, challenge_pos);
  }
}.

lemma generated_raw_mu_to_challenge_suffix_zero_loss
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [GeneratedSignRawMuThenChallenge.run ~
         GeneratedVerifyRawMuThenChallenge.run :
    ={Glob.mem, challenge_state, challenge_pos} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    vkp{2} = base /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    ExactMuTopControl.raw_prelen prelen{2} /\
    ExactMuTopControl.valid_region prep{2} prelen{2} /\
    ExactMuTopControl.valid_region mp{2} mlen{2} /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 mem0 base /\
    BArray16.get64 challenge_pos{1} 0 = W64.of_int 64
    ==>
    ={res}].
proof.
move=> hbase.
proc.
call ExtractedChallengeAbsorb.sign_verify_mu32_absorb_from_pos64.
call (ExactMuTopControl.sign_verify_generated_raw_mu_prefix
        sk0 mem0 base hbase).
auto => />.
qed.

end ExactMode2RawMuComposition.
