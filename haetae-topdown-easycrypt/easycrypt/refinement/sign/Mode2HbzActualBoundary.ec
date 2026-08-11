require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import
  HbzFullEncodeTarget HbzFullDecodeTarget
  SignaturePackMode2Target SignatureUnpackMode2Target
  Mode2HbzCodecSpec.

theory Mode2HbzActualBoundary.

import Mode2HbzCodecSpec.

module FocusEncode = HbzFullEncodeTarget.M.
module FocusDecode = HbzFullDecodeTarget.M.
module Pack = SignaturePackMode2Target.M.
module Unpack = SignatureUnpackMode2Target.M.

lemma pack_target_encode_hb_z1_full_exact_focused :
  equiv [Pack._encode_hb_z1_full ~ FocusEncode._encode_hb_z1_full :
    ={outp, hp, esymsp, count, mhb, offset}
    ==>
    ={res}].
proof.
proc; sim.
qed.

lemma unpack_target_decode_hb_z1_full_exact_focused :
  equiv [Unpack._decode_hb_z1_full ~ FocusDecode._decode_hb_z1_full :
    ={hp, badp, bufp, size_in, symbolwp, dsymswp, count, mhb, offset}
    ==>
    ={res}].
proof.
proc; sim.
qed.

end Mode2HbzActualBoundary.
