require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansDecodeTarget SignatureUnpackMode2Target
  Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansByteStack
  Mode2RansNormalization.

theory Mode2RansDecodeRefinement.

import Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansByteStack.

module Decode = RansDecodeTarget.M.

op mode2_decode_state
    (statep : BArray24.t) (size : int) : bool =
  BArray24.get64 statep 0 = W64.of_int mode2_hbz_count /\
  BArray24.get64 statep 1 = W64.of_int size /\
  BArray24.get64 statep 2 = W64.of_int mode2_hbz_alphabet.

lemma actual_rans_decode_mode2_control
    (symbols0 buffer0 : BArray2048.t)
    (state0 : BArray24.t)
    (size : int) :
  hoare [Decode._rans_decode :
    symsp = symbols0 /\
    statep = state0 /\
    bufp = buffer0 /\
    symbolwp = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words /\
    dsymswp = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words /\
    4 <= size <= mode2_hbz_count /\
    mode2_decode_state state0 size
    ==>
    (BArray24.get64 res.`2 1 = W64.zero \/
     BArray24.get64 res.`2 1 = W64.one)].
proof.
proc.
wp.
while (bad = W64.zero \/ bad = W64.one).
+ wp.
  sp 2.
  if.
  - auto.
  - seq 15 : (bad = W64.zero \/ bad = W64.one).
    * auto.
    * wp.
    if.
    * auto.
    * wp.
      sp 20.
      while (bad = W64.zero \/ bad = W64.one).
      + auto.
      + auto.
auto => />.
qed.

lemma actual_rans_decode_mode2_jazz_control
    (symbols0 buffer0 : BArray2048.t)
    (state0 : BArray24.t)
    (size : int) :
  hoare [Decode.rans_decode_jazz :
    symsp = symbols0 /\
    statep = state0 /\
    bufp = buffer0 /\
    symbolwp = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words /\
    dsymswp = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words /\
    4 <= size <= mode2_hbz_count /\
    mode2_decode_state state0 size
    ==>
    (BArray24.get64 res.`2 1 = W64.zero \/
     BArray24.get64 res.`2 1 = W64.one)].
proof.
proc.
call (actual_rans_decode_mode2_control symbols0 buffer0 state0 size).
auto.
qed.

lemma mode2_decode_state_satisfiable :
  exists statep,
    mode2_decode_state statep 4.
proof.
exists (BArray24.set64
  (BArray24.set64
    (BArray24.set64 witness 0 (W64.of_int mode2_hbz_count))
    1 (W64.of_int 4))
  2 (W64.of_int mode2_hbz_alphabet)).
rewrite /mode2_decode_state /=.
trivial.
qed.

end Mode2RansDecodeRefinement.
