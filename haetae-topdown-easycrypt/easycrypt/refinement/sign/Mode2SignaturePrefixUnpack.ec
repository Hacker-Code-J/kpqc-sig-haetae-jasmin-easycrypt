require import AllCore IntDiv.
from Jasmin require import JModel_x86.
import SLH64.
require import SignatureUnpackMode2Target Mode2SignaturePrefixCodec.

theory Mode2SignaturePrefixUnpack.
import Mode2SignaturePrefixCodec.
module Unpack = SignatureUnpackMode2Target.M.

lemma unpack_sig_prefix_mode2_layout
    (cp0 cpsrc : BArray1024.t)
    (low0 lowsrc : BArray8192.t) :
  hoare [Unpack._unpack_sig_prefix :
    cp = cp0 /\ lowp = low0 /\
    lcount = W64.of_int mode2_lcount /\
    packed_challenge_prefix sigp cpsrc challenge_bytes /\
    packed_low_prefix sigp lowsrc low_words
    ==>
    decoded_challenge_prefix res.`1 cpsrc challenge_words /\
    decoded_low_prefix res.`2 lowsrc low_words /\
    low_tail_frame low0 res.`2].
proof.
proc.
while
  (lcount = W64.of_int mode2_lcount /\
   off = W64.of_int challenge_bytes /\
   total = W64.of_int low_words /\
   packed_challenge_prefix sigp cpsrc challenge_bytes /\
   packed_low_prefix sigp lowsrc low_words /\
   decoded_challenge_prefix cp cpsrc challenge_words /\
   0 <= W64.to_uint i <= low_words /\
   decoded_low_prefix lowp lowsrc (W64.to_uint i) /\
   low_tail_frame low0 lowp).
+ auto => /> &hr hclayout hlayout hcpdone hi0 hile hdecoded htail hguard.
  have hilt : W64.to_uint i{hr} < low_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hidx :
      W64.to_uint (W64.of_int challenge_bytes + i{hr}) =
      challenge_bytes + W64.to_uint i{hr}.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    trivial.
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split; first by rewrite hi_next; smt(W64.to_uint_cmp).
  split.
  + rewrite hidx.
    have hbyte :
        BArray2948.get8 sigp{hr}
          (challenge_bytes + W64.to_uint i{hr}) =
        truncateu8
          (BArray8192.get32 lowsrc (W64.to_uint i{hr})).
    + rewrite /packed_low_prefix in hlayout.
      apply (hlayout (W64.to_uint i{hr})); smt().
    change (decoded_low_prefix
      (BArray8192.set32 lowp{hr} (W64.to_uint i{hr})
        (sign_extend_byte
          (BArray2948.get8 sigp{hr}
            (challenge_bytes + W64.to_uint i{hr}))))
      lowsrc (W64.to_uint (i{hr} + W64.one))).
    rewrite hbyte hi_next.
    apply decoded_low_prefix_step; first by smt().
    exact hdecoded.
  + rewrite /low_tail_frame => k hk.
    rewrite BArray8192.get_set32E 1:/# 1:/#.
    case (k = W64.to_uint i{hr}) => hkeq.
    * have : k < low_words by smt().
      smt().
    * rewrite ifF 1:/#.
      exact (htail k hk).
auto => />.
move=> &hr.
move=> [hcp [hlow [hlcount [hclayout hlayout]]]]
        cp1 [[hcpdone hlowzero] hexit].
rewrite hlow in hlowzero.
split.
+ rewrite hlcount
          /mode2_lcount /challenge_bytes /low_words /=.
  split; first exact hclayout.
  split; first exact hlayout.
  split; first exact hcpdone.
  split; first by smt().
  rewrite /low_tail_frame => k hk.
  rewrite hlow.
  trivial.
+ move=> i1 lowp1 hdone
          [hlcount1 [hoff [htotal
           [hclayout1 [hlayout1 [hcpdone1
            [hibounds [hdecoded htail]]]]]]]].
  have hieq : W64.to_uint i1 = low_words.
  + move: hdone.
    rewrite htotal W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  split; first exact hcpdone1.
  split.
  + rewrite -hieq.
    exact hdecoded.
  + exact htail.
while
  (lowp = low0 /\
   lcount = W64.of_int mode2_lcount /\
   packed_challenge_prefix sigp cpsrc challenge_bytes /\
   packed_low_prefix sigp lowsrc low_words /\
   0 <= W64.to_uint i <= challenge_bytes /\
   decoded_challenge_prefix cp cpsrc (8 * W64.to_uint i)).
+ wp.
  while
    (lowp = low0 /\
     lcount = W64.of_int mode2_lcount /\
     packed_challenge_prefix sigp cpsrc challenge_bytes /\
     packed_low_prefix sigp lowsrc low_words /\
     0 <= W64.to_uint i < challenge_bytes /\
     b = zeroextu32 (BArray2948.get8 sigp (W64.to_uint i)) /\
     0 <= j <= 8 /\
     decoded_challenge_prefix cp cpsrc (8 * W64.to_uint i + j)).
  + auto => /> &hr hclayout hlayout hi0 hilt hj0 hjle hdecoded.
    move=> hloop.
    have hjlt : j{hr} < 8 by exact hloop.
    have hidx :
        W64.to_uint
          (W64.of_int 8 * i{hr} + W64.of_int j{hr}) =
        8 * W64.to_uint i{hr} + j{hr}.
    + rewrite W64.to_uintD_small 1:/#.
      rewrite W64.to_uintM_small 1:/# !W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    split.
    + split; smt().
    have hbit :
        (((zeroextu32 (BArray2948.get8 sigp{hr} (W64.to_uint i{hr})))
           `>>` (W8.of_int j{hr})) `&` W32.one) =
        bitword
          ((BArray2948.get8 sigp{hr} (W64.to_uint i{hr})).[j{hr}]).
    + apply decode_w8_bit.
      smt().
    rewrite /packed_challenge_prefix in hclayout.
    have hsource :
        (BArray2948.get8 sigp{hr} (W64.to_uint i{hr})).[j{hr}] =
        challenge_source cpsrc (W64.to_uint i{hr}) j{hr}.
    + apply (hclayout (W64.to_uint i{hr}) j{hr});
        smt(W64.to_uint_cmp).
    have hvalue :
        (((zeroextu32 (BArray2948.get8 sigp{hr} (W64.to_uint i{hr})))
           `>>` (W8.of_int j{hr})) `&` W32.one) =
        bitword
          (BArray1024.get32 cpsrc
             (8 * W64.to_uint i{hr} + j{hr})).[0].
    + rewrite hbit hsource /challenge_source.
      trivial.
    have hnext :
        8 * W64.to_uint i{hr} + (j{hr} + 1) =
        (8 * W64.to_uint i{hr} + j{hr}) + 1 by ring.
    rewrite hidx hvalue hnext.
    apply decoded_challenge_prefix_step; first by smt().
    exact hdecoded.
  auto => />.
  move=> &hr hclayout hlayout hi0 hile hdecoded hguard.
  have hilt : W64.to_uint i{hr} < challenge_bytes.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  split; first exact hilt.
  move=> cp1 j0 hjdone hilt0 hj0 hjle hdecoded1.
  have hj_eq : j0 = 8 by smt().
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split.
  + rewrite hi_next.
    split; smt(W64.to_uint_cmp).
  + rewrite hi_next.
    have hcount :
        8 * (W64.to_uint i{hr} + 1) =
        8 * W64.to_uint i{hr} + 8 by ring.
    rewrite hcount.
    have -> :
        8 * W64.to_uint i{hr} + 8 =
        8 * W64.to_uint i{hr} + j0 by smt().
    exact hdecoded1.
auto => />.
move=> &hr hclayout hlayout.
split.
+ apply decoded_challenge_prefix_zero.
+ move=> cp1 i0 hdone hi0 hile hdecoded.
  move: hdone.
  rewrite W64.ultE W64.of_uintK /challenge_bytes /=.
  move=> hdone_int.
  split.
  + split.
    * rewrite /decoded_challenge_prefix => k hk.
      rewrite /decoded_challenge_prefix in hdecoded.
      apply hdecoded.
      rewrite /challenge_words in hk.
      rewrite /challenge_bytes in hile.
      smt(W64.to_uint_cmp).
    * apply decoded_low_prefix_zero.
  + move=> i1 lowp1 hlow_done htotalword hcpfull hi10 hi1le
           hlowdecoded htail.
    move: hlow_done.
    rewrite W64.ultE W64.of_uintK
            /mode2_lcount /low_words /=.
    move=> hlow_done_int.
    rewrite /decoded_low_prefix => k hk.
    rewrite /decoded_low_prefix in hlowdecoded.
    apply hlowdecoded.
    rewrite /low_words in hk.
    rewrite /low_words in hi1le.
    smt(W64.to_uint_cmp).
qed.

end Mode2SignaturePrefixUnpack.
