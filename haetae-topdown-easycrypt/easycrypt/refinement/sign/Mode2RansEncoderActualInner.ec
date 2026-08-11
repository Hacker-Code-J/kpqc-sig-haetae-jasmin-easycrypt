require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansEncodeTarget SignaturePackMode2Target
  Mode2HbzCodecSpec Mode2RansArrayListBridge
  Mode2RansEncodeRefinement Mode2RansNormalization
  Mode2RansEncoderTrace.

theory Mode2RansEncoderActualInner.

import Mode2HbzCodecSpec Mode2RansArrayListBridge
       Mode2RansEncodeRefinement Mode2RansNormalization
       Mode2RansEncoderTrace.

module Encode = RansEncodeTarget.M.

lemma actual_rans_encode_inner_no_underflow
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
    BArray16.get64 res.`2 1 <> W64.zero \/
    (BArray16.get64 res.`2 1 = W64.zero /\
     W64.to_uint (BArray16.get64 res.`2 0) <= 1020)].
proof.
proc.
wp.
while
  (statep = state0 /\
   symsp = symbols0 /\
   esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
   count = W64.of_int mode2_hbz_count /\
   mode2_hbz_symbol_stream symbols0 /\
   0 <= W64.to_uint i <= mode2_hbz_count /\
   (bad = W64.zero \/ bad = W64.one) /\
   (bad = W64.zero =>
      4 <= W64.to_uint off <= mode2_hbz_count)).
+ if.
  - auto.
  - wp.
    while
      (encoder_inner_phase_inv x_max x off /\
       encoder_inner_segment_inv x_max x off encp).
    * auto => &m hboth.
      move: hboth => [[hphase hsegment] hguard].
      split.
      - exact (encoder_inner_phase_step _ _ _ hphase hguard).
      - exact (encoder_inner_segment_step _ _ _ _ hsegment hguard).
    * auto.
    auto => &m houter.
    move: houter => [[hout higuard] hbadzero].
    move: hout =>
      [hstate [hsym [hesym [hcount [hstream [hi [hbaddisj hoff]]]]]]].
    move: hi => [hilo hihi].
    rewrite W64.ultE in higuard.
    rewrite W64.to_uint0 in higuard.
    have hipos : 0 < W64.to_uint i{m} by exact higuard.
    have hi0 : 0 <= W64.to_uint (i{m} - W64.one) < mode2_hbz_count.
    - rewrite (cursor_decrement_no_underflow i{m} hipos).
      smt().
    have hs := hstream (W64.to_uint (i{m} - W64.one)) hi0.
    have hxmax := actual_mode2_esym_xmax_positive
      (W8.to_uint (BArray2048.get8 symbols0
        (W64.to_uint (i{m} - W64.one)))) hs.
    have hidx_product :
        W64.to_uint
          (zeroextu64 (BArray2048.get8 symbols0
            (W64.to_uint (i{m} - W64.one)))) *
        W64.to_uint (W64.of_int 4) < W64.modulus.
    - rewrite W8u8.to_uint_zeroextu64 W64.of_uintK /=.
      have hu := W8.to_uint_cmp
        (BArray2048.get8 symbols0
          (W64.to_uint (i{m} - W64.one))).
      smt().
    have hidx :
        W64.to_uint
          ((zeroextu64 (BArray2048.get8 symbols0
              (W64.to_uint (i{m} - W64.one)))) * W64.of_int 4) =
        4 * W8.to_uint (BArray2048.get8 symbols0
          (W64.to_uint (i{m} - W64.one))).
    - rewrite W64.to_uintM_small 1:hidx_product
              W8u8.to_uint_zeroextu64 W64.of_uintK /=.
      ring.
    split.
    - rewrite hsym hesym /protect_64 /protect_32 hidx /=.
      exact (andI _ _
        (encoder_inner_phase_init _ _ _ (hoff hbadzero) hxmax)
        (encoder_inner_segment_init _ _ _ _ (hoff hbadzero) hxmax)).
    move=> encp1 off1 x1 hguarddone [hphase hsegment].
    have hoffhi := encoder_inner_phase_off_upper _ _ _ hphase.
    case (off1 \ult W64.of_int 4) => hofflt.
    - simplify.
      split; first exact hstate.
      split; first exact hsym.
      split; first exact hesym.
      split; first exact hcount.
      split; first exact hstream.
      split; first by smt().
      move=> hone.
      have hone_uint : W64.to_uint W64.one = W64.to_uint W64.zero.
      - rewrite -W64.to_uint_eq.
        exact hone.
      rewrite W64.to_uint1 W64.to_uint0 in hone_uint.
      smt().
    - simplify.
      have hofflo : 4 <= W64.to_uint off1.
      + rewrite W64.ultE W64.of_uintK /= in hofflt.
        smt(W64.to_uint_cmp).
      split; first exact hstate.
      split; first exact hsym.
      split; first exact hesym.
      split; first exact hcount.
      split; first exact hstream.
      split; first by smt().
      split; first by left.
      move=> hbad_after.
      split.
      + exact hofflo.
      + move=> _.
        exact hoffhi.
auto => />.
move=> _ bad0 i0 off0 _ _ _ _ hoff hbad.
have hoff_bounds := hoff hbad.
rewrite W64.to_uintB.
+ rewrite W64.uleE W64.of_uintK /=.
  smt().
rewrite W64.of_uintK /=.
rewrite /mode2_hbz_count in hoff_bounds.
smt().
qed.

lemma actual_rans_encode_success_size_bound
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
    BArray16.get64 res.`2 1 <> W64.zero \/
    (BArray16.get64 res.`2 1 = W64.zero /\
     0 <= W64.to_uint (BArray16.get64 res.`2 0) <= 1020 /\
     4 <= mode2_hbz_count -
       W64.to_uint (BArray16.get64 res.`2 0) <= mode2_hbz_count)].
proof.
conseq (actual_rans_encode_inner_no_underflow enc0 state0 symbols0)
  => //=.
move=> &m _ result hpost.
elim hpost => hbad; first by left.
right.
move: hbad => [hzero hoff].
split; first exact hzero.
have hword := W64.to_uint_cmp (BArray16.get64 result.`2 0).
rewrite /mode2_hbz_count.
smt().
qed.

end Mode2RansEncoderActualInner.
