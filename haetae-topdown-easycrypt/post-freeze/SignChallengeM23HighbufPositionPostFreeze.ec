require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import SignChallengeM23AbsorbComponentsPostFreeze
               SignTranscriptTarget VerifyTranscriptTarget.

theory SignChallengeM23HighbufPositionPostFreeze.

(* The loop invariant counts completed 136-byte rate blocks.  At the fixed
   Mode-2 length 576 = 4 * 136 + 32, it exposes the exact final position needed
   to compose the highbits helper with the already-proved absorb suffix. *)

module Sign = SignTranscriptTarget.M.
module Verify = VerifyTranscriptTarget.M.

op mode2_highlen : int =
  SignChallengeM23AbsorbComponentsPostFreeze.mode2_highlen.

lemma verify_absorb_buf_mode2_position :
  hoare [Verify.__verify_shake256_absorb_buf :
    inlen = W64.of_int mode2_highlen /\
    BArray16.get64 statep 0 = W64.zero
    ==>
    BArray16.get64 res.`2 0 = W64.of_int 32].
proof.
proc.
wp.
while
  (inlen = W64.of_int mode2_highlen /\
   0 <= W64.to_uint i <= mode2_highlen /\
   0 <= W64.to_uint pos < 136 /\
   exists blocks,
     0 <= blocks <= 4 /\
     W64.to_uint i = 136 * blocks + W64.to_uint pos).
+ sp.
  if.
  + wp.
    call (_ : true ==> true); first by auto.
    auto => /> pos0 i0 hi0 hiend hp0 hplt
                 blocks hb0 hb4 heq hguard hfull.
    have hilt : W64.to_uint i0 < mode2_highlen.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_highlen /=.
      smt(W64.to_uint_cmp).
    have hinext :
        W64.to_uint (i0 + W64.one) = W64.to_uint i0 + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hpos135 : W64.to_uint pos0 = 135.
    + move: hfull.
      rewrite W64.to_uint_eq W64.to_uintD_small 1:/# W64.to_uint1
              W64.of_uintK /=.
      smt().
    split.
    + smt(W64.to_uint_cmp).
    exists (blocks + 1).
    split; first smt().
    smt().
  + skip => />.
    move=> pos0 i0 hi0 hiend hp0 hplt
            blocks hb0 hb4 heq hguard hnotfull.
    have hilt : W64.to_uint i0 < mode2_highlen.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_highlen /=.
      smt(W64.to_uint_cmp).
    have hinext :
        W64.to_uint (i0 + W64.one) = W64.to_uint i0 + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hposnext :
        W64.to_uint (pos0 + W64.one) = W64.to_uint pos0 + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hnot136 : W64.to_uint pos0 + 1 <> 136.
    + move: hnotfull.
      rewrite W64.to_uint_eq W64.to_uintD_small 1:/# W64.to_uint1
              W64.of_uintK /=.
      smt().
    rewrite hinext hposnext.
    split.
    + smt(W64.to_uint_cmp).
    split.
    + smt().
    exists blocks.
    smt().
+ auto => />.
  move=> &hr hstate.
  rewrite /protect_64 /protect_ptr hstate W64.of_uintK /=.
  split.
  + rewrite /mode2_highlen
            /SignChallengeM23AbsorbComponentsPostFreeze.mode2_highlen.
    smt(W64.to_uint_cmp).
  smt().
qed.

lemma sign_absorb_buf_mode2_position :
  hoare [Sign.__sign_challenge_shake256_absorb_buf :
    inlen = W64.of_int mode2_highlen /\
    BArray16.get64 statep 0 = W64.zero
    ==>
    BArray16.get64 res.`2 0 = W64.of_int 32].
proof.
conseq
  SignChallengeM23AbsorbComponentsPostFreeze.sign_verify_absorb_buf_identity
  verify_absorb_buf_mode2_position.
+ move=> &1 hpre.
  exists (sp_0{1}, statep{1}, inp{1}, inlen{1}).
  by auto.
+ move=> &1 &2 hres hpos.
  by rewrite hres.
qed.

lemma sign_verify_absorb_buf_mode2_position :
  equiv [Sign.__sign_challenge_shake256_absorb_buf ~
         Verify.__verify_shake256_absorb_buf :
    ={sp_0, statep, inp, inlen} /\
    inlen{1} = W64.of_int mode2_highlen /\
    BArray16.get64 statep{1} 0 = W64.zero
    ==>
    ={res} /\ BArray16.get64 res{1}.`2 0 = W64.of_int 32].
proof.
conseq
  SignChallengeM23AbsorbComponentsPostFreeze.sign_verify_absorb_buf_identity
  sign_absorb_buf_mode2_position => //=.
qed.

lemma sign_verify_challenge_absorb_mode2 :
  equiv [Sign.__sign_challenge_absorb ~
         Verify.__verify_challenge_absorb :
    ={sp_0, highp, highlen, lsbp} /\
    highlen{1} = W64.of_int mode2_highlen /\
    SignChallengeM23AbsorbComponentsPostFreeze.mu32_prefix mup{1} mup{2}
    ==>
    ={res}].
proof.
proc.
call
  SignChallengeM23AbsorbComponentsPostFreeze.sign_verify_challenge_finalize_identity.
call
  SignChallengeM23AbsorbComponentsPostFreeze.sign_verify_mu32_from_pos64.
call
  SignChallengeM23AbsorbComponentsPostFreeze.sign_verify_absorb32_from_pos32.
call sign_verify_absorb_buf_mode2_position.
call
  SignChallengeM23AbsorbComponentsPostFreeze.sign_verify_keccak_init_identity.
auto => />.
qed.

end SignChallengeM23HighbufPositionPostFreeze.
