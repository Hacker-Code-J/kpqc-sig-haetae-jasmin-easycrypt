require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansEncodeTarget SignaturePackMode2Target
  Mode2HbzCodecSpec Mode2HbzTableCertificate.

theory Mode2RansEncodeRefinement.

import Mode2HbzCodecSpec Mode2HbzTableCertificate.

module Encode = RansEncodeTarget.M.

op mode2_hbz_symbol_stream (symsp : BArray2048.t) : bool =
  forall i, 0 <= i < mode2_hbz_count =>
    0 <= W8.to_uint (BArray2048.get8 symsp i) < mode2_hbz_alphabet.

lemma actual_rans_encode_mode2_control
    (enc0 : BArray2048.t)
    (state0 : BArray16.t)
    (symbols0 : BArray2048.t) :
  hoare [Encode._rans_encode :
    encp = enc0 /\
    statep = state0 /\
    symsp = symbols0 /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int mode2_hbz_count /\
    mode2_hbz_symbol_stream symbols0
    ==>
    res.`2 =
      BArray16.set64
        (BArray16.set64 state0 0 (BArray16.get64 res.`2 0))
        1 (BArray16.get64 res.`2 1) /\
    (BArray16.get64 res.`2 1 = W64.zero \/
     BArray16.get64 res.`2 1 = W64.one)].
proof.
proc.
wp.
while
  (statep = state0 /\
   symsp = symbols0 /\
   esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
   count = W64.of_int mode2_hbz_count /\
   mode2_hbz_symbol_stream symbols0 /\
   (bad = W64.zero \/ bad = W64.one)).
+ if.
  - auto.
  - wp.
    while (bad = W64.zero \/ bad = W64.one).
    * auto.
    * auto.
auto => />.
qed.

lemma actual_rans_encode_mode2_jazz_control
    (enc0 : BArray2048.t)
    (state0 : BArray16.t)
    (symbols0 : BArray2048.t) :
  hoare [Encode.rans_encode_jazz :
    encp = enc0 /\
    statep = state0 /\
    symsp = symbols0 /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int mode2_hbz_count /\
    mode2_hbz_symbol_stream symbols0
    ==>
    res.`2 =
      BArray16.set64
        (BArray16.set64 state0 0 (BArray16.get64 res.`2 0))
        1 (BArray16.get64 res.`2 1) /\
    (BArray16.get64 res.`2 1 = W64.zero \/
     BArray16.get64 res.`2 1 = W64.one)].
proof.
proc.
call (actual_rans_encode_mode2_control enc0 state0 symbols0).
auto.
qed.

end Mode2RansEncodeRefinement.
