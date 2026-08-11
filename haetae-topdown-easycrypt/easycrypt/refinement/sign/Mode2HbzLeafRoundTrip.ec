require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import HbzPrepareTarget HbzApplyTarget.
require import Mode2HbzCodecSpec Mode2HbzPrepare Mode2HbzApply.

theory Mode2HbzLeafRoundTrip.

import Mode2HbzCodecSpec.

module Prepare = HbzPrepareTarget.M.
module Apply = HbzApplyTarget.M.

module HbzPrepareApply = {
  proc run(symbols : BArray2048.t,
           bad : BArray8.t,
           hbz : BArray8192.t,
           decoded : BArray8192.t) : BArray8.t * BArray8192.t = {
    (symbols, bad) <@ Prepare.encode_hb_z1_prepare_jazz
      (symbols, bad, hbz,
       W64.of_int mode2_hbz_count,
       W64.of_int mode2_hbz_alphabet,
       W64.of_int mode2_hbz_offset);
    decoded <@ Apply.decode_hb_z1_apply_jazz
      (decoded, symbols,
       W64.of_int mode2_hbz_count,
       W64.of_int mode2_hbz_offset);
    return (bad, decoded);
  }
}.

lemma encode_prepare_decode_apply_mode2_inverse
    (symbols0 : BArray2048.t)
    (bad0 : BArray8.t)
    (hbz0 decoded0 : BArray8192.t) :
  hoare [HbzPrepareApply.run :
    symbols = symbols0 /\ bad = bad0 /\ hbz = hbz0 /\
    decoded = decoded0 /\ canonical_hbz_mode2 hbz0
    ==>
    BArray8.get64 res.`1 0 = W64.zero /\
    decoded_hbz_prefix res.`2 hbz0 mode2_hbz_count /\
    coeff_tail_frame decoded0 res.`2 mode2_hbz_count].
proof.
proc.
call (Mode2HbzApply.decode_hb_z1_apply_mode2_correct
        decoded0 hbz0).
call (Mode2HbzPrepare.encode_hb_z1_prepare_mode2_correct
        symbols0 bad0 hbz0).
auto.
qed.

end Mode2HbzLeafRoundTrip.
