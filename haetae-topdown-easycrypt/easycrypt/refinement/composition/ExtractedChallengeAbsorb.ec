require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignTranscriptTarget VerifyTranscriptTarget.

theory ExtractedChallengeAbsorb.

module Sign = SignTranscriptTarget.M.
module Verify = VerifyTranscriptTarget.M.

op mu32_prefix (mu64 : BArray64.t) (mu32 : BArray32.t) : bool =
  forall i, 0 <= i < 32 =>
    BArray64.get8 mu64 i = BArray32.get8 mu32 i.

lemma zero_mu32_prefix :
  mu32_prefix
    (BArray64.init_arr W8.zero)
    (BArray32.init_arr W8.zero).
proof.
rewrite /mu32_prefix => i [hi0 hi32].
have hi64b : 0 <= i < BArray64.size.
+ change (0 <= i < 64).
  smt().
have hi32b : 0 <= i < BArray32.size.
+ change (0 <= i < 32).
  smt().
by rewrite BArray64.initE 1:hi64b BArray32.initE 1:hi32b.
qed.

lemma absorb_precondition_has_witness :
  exists (statep : BArray16.t) (mu64 : BArray64.t)
         (mu32 : BArray32.t),
    BArray16.get64 statep 0 = W64.of_int 64 /\
    mu32_prefix mu64 mu32.
proof.
exists
  (BArray16.set64 (BArray16.init_arr W8.zero) 0 (W64.of_int 64)).
exists (BArray64.init_arr W8.zero).
exists (BArray32.init_arr W8.zero).
split.
+ by rewrite BArray16.get_set64E_eq 1:// 1://.
+ exact zero_mu32_prefix.
qed.

lemma sign_verify_mu32_absorb_from_pos64 :
  equiv [Sign.__sign_challenge_shake256_absorb_mu32 ~
         Verify.__verify_shake256_absorb_mu32 :
    ={sp_0, statep} /\
    BArray16.get64 statep{1} 0 = W64.of_int 64 /\
    mu32_prefix inp{1} inp{2}
    ==>
    ={res}].
proof.
proc.
wp.
while (={sp_0, statep, pos, i} /\
       mu32_prefix inp{1} inp{2} /\
       W64.to_uint pos{1} = 64 + W64.to_uint i{1} /\
       W64.to_uint i{1} <= 32).
+ rcondf{1} 12.
  + auto => /> &hr hprefix hpos hibound hguard.
    have hpos_small :
        W64.to_uint pos{m} + 1 < W64.modulus by
      smt(W64.ultE W64.to_uint_cmp).
    rewrite W64.to_uint_eq W64.to_uintD_small 1:hpos_small
            W64.to_uint1 W64.of_uintK /=.
    move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt().
  auto => /> &1 &2 hprefix hpos hibound hguard.
  have hi : 0 <= W64.to_uint i{2} < 32.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hbyte :
      BArray64.get8 inp{1} (W64.to_uint i{2}) =
      BArray32.get8 inp{2} (W64.to_uint i{2}).
  + exact (hprefix (W64.to_uint i{2}) hi).
  have hi_small :
      W64.to_uint i{2} + 1 < W64.modulus.
  + smt(W64.to_uint_cmp).
  have hpos_small :
      W64.to_uint pos{2} + 1 < W64.modulus.
  + smt(W64.to_uint_cmp).
  have hi_succ :
      W64.to_uint (i{2} + W64.one) = W64.to_uint i{2} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hpos_succ :
      W64.to_uint (pos{2} + W64.one) = W64.to_uint pos{2} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  rewrite hbyte hi_succ hpos_succ.
  smt().
auto => /> &1 &2 hstate hprefix.
rewrite /protect_64 /protect_ptr hstate W64.of_uintK /=.
trivial.
qed.

end ExtractedChallengeAbsorb.
