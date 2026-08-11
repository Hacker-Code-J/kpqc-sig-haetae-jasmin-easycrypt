require import AllCore IntDiv.
from Jasmin require import JModel_x86.
import SLH64.
require import SignaturePackMode2Target Mode2SignaturePrefixCodec.

theory Mode2SignaturePrefixPack.
import Mode2SignaturePrefixCodec.
module Pack = SignaturePackMode2Target.M.

lemma pack_sig_prefix_mode2_layout
    (cp0 : BArray1024.t) (low0 : BArray8192.t) :
  hoare [Pack._pack_sig_prefix :
    cp = cp0 /\ lowp = low0 /\
    lcount = W64.of_int mode2_lcount /\
    sigbytes = W64.of_int mode2_sigbytes
    ==>
    packed_challenge_prefix res cp0 challenge_bytes /\
    packed_low_prefix res low0 low_words].
proof.
proc.
while
  (cp = cp0 /\ lowp = low0 /\
   lcount = W64.of_int mode2_lcount /\
   sigbytes = W64.of_int mode2_sigbytes /\
   off = W64.of_int challenge_bytes /\
   total = W64.of_int low_words /\
   0 <= W64.to_uint i <= low_words /\
   packed_challenge_prefix sigp cp0 challenge_bytes /\
   packed_low_prefix sigp low0 (W64.to_uint i)).
+ auto => /> &hr hi0 hile hchallenge hpacked hguard.
  have hilt : W64.to_uint i{hr} < low_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hidx :
      W64.to_uint (W64.of_int challenge_bytes + i{hr}) =
      challenge_bytes + W64.to_uint i{hr}.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    trivial.
  split; first by rewrite hi_next; smt(W64.to_uint_cmp).
  split.
  + apply packed_challenge_prefix_set_after.
    * rewrite hidx; smt().
    * smt().
    * rewrite hidx; smt().
    * exact hchallenge.
  + rewrite /packed_low_prefix => k hk.
    have hsetidx :
        0 <= W64.to_uint (W64.of_int challenge_bytes + i{hr}) < 2948.
    + rewrite hidx; smt().
    rewrite BArray2948.get_setE 1:hsetidx.
    case (challenge_bytes + k =
          W64.to_uint (W64.of_int challenge_bytes + i{hr})) => heq.
    + have -> : k = W64.to_uint i{hr} by smt().
      trivial.
    + rewrite /packed_low_prefix in hpacked.
      have hkold : 0 <= k < W64.to_uint i{hr}.
      + exact (low_prior_index_from_actual
                 k (W64.to_uint i{hr})
                 (W64.to_uint (i{hr} + W64.one))
                 (W64.to_uint (W64.of_int challenge_bytes + i{hr}))
                 hk hi_next hidx heq).
      exact (hpacked k hkold).
auto => />.
move=> &hr.
move=> [hcp [hlow [hlcount hsigbytes]]] sigp0
        [[hchallenge0 hlowzero] hexit].
rewrite hcp hlow hlcount.
rewrite /mode2_lcount /challenge_bytes /low_words /=.
rewrite hcp /challenge_bytes in hchallenge0.
rewrite hlow in hlowzero.
split.
+ split; first exact hsigbytes.
  split; first exact hchallenge0.
  exact hlowzero.
+ move=> i0 sigp1 hdone [hsig [hi [hchallenge1 hpacked1]]].
  split; first exact hchallenge1.
  have hieq : W64.to_uint i0 = 1024.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  rewrite -hieq.
  exact hpacked1.
while
  (cp = cp0 /\ lowp = low0 /\
   lcount = W64.of_int mode2_lcount /\
   sigbytes = W64.of_int mode2_sigbytes /\
   0 <= W64.to_uint i <= challenge_bytes /\
   packed_challenge_prefix sigp cp0 (W64.to_uint i)).
+ wp.
  while
    (cp = cp0 /\ lowp = low0 /\
     lcount = W64.of_int mode2_lcount /\
     sigbytes = W64.of_int mode2_sigbytes /\
     0 <= W64.to_uint i < challenge_bytes /\
     0 <= j <= 8 /\
     packed_challenge_prefix sigp cp0 (W64.to_uint i) /\
     partial_word out (challenge_source cp0 (W64.to_uint i)) j).
  + auto => /> &hr hi0 hilt hj0 hjle hpacked hpartial hguard.
    have hjlt : j{hr} < 8 by smt().
    have hidx :
        W64.to_uint
          (W64.of_int 8 * i{hr} + W64.of_int j{hr}) =
        8 * W64.to_uint i{hr} + j{hr}.
    + rewrite W64.to_uintD_small 1:/#.
      rewrite W64.to_uintM_small 1:/# !W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    split; first by smt().
    rewrite hidx.
    rewrite (and_one_is_bitword
               (BArray1024.get32 cp0
                  (8 * W64.to_uint i{hr} + j{hr}))).
    rewrite /challenge_source.
    rewrite /challenge_source in hpartial.
    rewrite /partial_word in hpartial.
    rewrite /partial_word.
    move=> b hb.
    have hjbounds : 0 <= j{hr} < 8 by smt().
    rewrite W32.orwE
      (shifted_bitword_bit
         (fun bit0 =>
            (BArray1024.get32 cp0
               (8 * W64.to_uint i{hr} + bit0)).[0])
         j{hr} b hjbounds hb)
      (hpartial b hb).
    smt().
  auto => />.
  move=> &hr hi0 hile hpacked hguard.
  have hilt : W64.to_uint i{hr} < challenge_bytes.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  split.
  + split; first exact hilt.
    apply partial_word_zero.
  move=> j0 out0 hdone hilt0 hj0 hjle0 hpartial0.
  have hj_eq : j0 = 8 by smt().
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split; first by rewrite hi_next; smt(W64.to_uint_cmp).
  rewrite hi_next.
  apply packed_challenge_prefix_step; first by smt().
  + exact hpacked.
  + rewrite -hj_eq; exact hpartial0.
auto => />.
move=> &hr.
move=> [hcp [hlow [hlcount hsigbytes]]] sigp0 hpost.
move: hpost => [hzero hcont].
split.
+ rewrite hcp hlow hlcount hsigbytes /=.
  rewrite hcp in hzero.
  exact hzero.
+ move=> i1 sigp1 hdone
          [hcp1 [hlow1 [hlcount1 [hsigbytes1 [hibounds hprefix]]]]].
  have hres := hcont i1 sigp1 hdone _ _ _.
  - smt().
  - smt().
  - rewrite hcp.
    exact hprefix.
  exact hres.
while
  (cp = cp0 /\ lowp = low0 /\
   lcount = W64.of_int mode2_lcount /\
   sigbytes = W64.of_int mode2_sigbytes /\
   0 <= W64.to_uint i <= mode2_sigbytes /\
   packed_challenge_prefix sigp cp0 0).
+ auto => /> &hr hi0 hile hprefix hguard.
  have hilt : W64.to_uint i{hr} < mode2_sigbytes.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split.
  + rewrite hi_next.
    split; first smt(W64.to_uint_cmp).
    move=> _.
    smt(W64.to_uint_cmp).
  + apply packed_challenge_prefix_zero.
auto.
move=> &hr [hcp [hlow [hlcount hsigbytes]]].
split.
+ rewrite hcp hlow hlcount hsigbytes /=.
  split; first by smt().
  apply packed_challenge_prefix_zero.
+ move=> i1 sigp0 hdone
          [hcp1 [hlow1 [hlcount1 [hsigbytes1 [hibounds hprefix0]]]]].
  split.
  + rewrite hcp.
    exact hprefix0.
  + move=> i2 sigp1 hchallenge_done hi0 hile hchallenge.
    have hieq : W64.to_uint i2 = challenge_bytes.
    + move: hchallenge_done.
      rewrite W64.ultE W64.of_uintK /challenge_bytes /=.
      smt(W64.to_uint_cmp).
    split.
    + split.
      * rewrite -hieq.
        exact hchallenge.
      * apply packed_low_prefix_zero.
    + move=> i3 sigp2 hlow_done hoff htotal hlo0 hlole
             hchallenge2 hlowprefix.
      have hloweq : W64.to_uint i3 = low_words.
      + move: hlow_done.
        rewrite W64.ultE W64.of_uintK
                /mode2_lcount /low_words /=.
        smt(W64.to_uint_cmp).
      rewrite -hloweq.
      exact hlowprefix.
qed.

end Mode2SignaturePrefixPack.
