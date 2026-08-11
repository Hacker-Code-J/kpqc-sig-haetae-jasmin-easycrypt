require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import SignaturePackMode2Target SignatureUnpackMode2Target.
require import Mode2SignaturePrefixCodec.
require import Mode2SignaturePrefixPack Mode2SignaturePrefixUnpack.

theory Mode2SignaturePrefixRoundTrip.

import Mode2SignaturePrefixCodec.

module Pack = SignaturePackMode2Target.M.
module Unpack = SignatureUnpackMode2Target.M.

module PrefixRoundTrip = {
  proc run(sig : BArray2948.t,
           cp : BArray1024.t,
           low : BArray8192.t,
           decoded_cp : BArray1024.t,
           decoded_low : BArray8192.t) :
      BArray1024.t * BArray8192.t = {
    sig <@ Pack._pack_sig_prefix
      (sig, cp, low,
       W64.of_int mode2_lcount, W64.of_int mode2_sigbytes);
    (decoded_cp, decoded_low) <@ Unpack._unpack_sig_prefix
      (decoded_cp, decoded_low, sig, W64.of_int mode2_lcount);
    return (decoded_cp, decoded_low);
  }
}.

lemma pack_unpack_sig_prefix_mode2_roundtrip
    (cp0 decoded_cp0 : BArray1024.t)
    (low0 decoded_low0 : BArray8192.t) :
  hoare [PrefixRoundTrip.run :
    cp = cp0 /\ low = low0 /\
    decoded_cp = decoded_cp0 /\ decoded_low = decoded_low0 /\
    canonical_challenge cp0 /\ canonical_signed_low low0
    ==>
    challenge_prefix_eq res.`1 cp0 /\
    low_mode2_eq res.`2 low0 /\
    low_tail_frame decoded_low0 res.`2].
proof.
proc.
call (Mode2SignaturePrefixUnpack.unpack_sig_prefix_mode2_layout
        decoded_cp0 cp0 decoded_low0 low0).
call (Mode2SignaturePrefixPack.pack_sig_prefix_mode2_layout cp0 low0).
auto => />.
move=> hcanoncp hcanonlow result hpackedcp hpackedlow
       result0 hdecodedcp_layout hdecodedlow_layout htail.
split.
+ apply (decoded_challenge_prefix_canonical_eq result0.`1 cp0).
  + exact hcanoncp.
  + exact hdecodedcp_layout.
+ apply (decoded_low_prefix_canonical_eq result0.`2 low0).
  + exact hcanonlow.
  + exact hdecodedlow_layout.
qed.

end Mode2SignaturePrefixRoundTrip.
