require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignatureUnpackMode2Target.
require import Mode2HbzCodecSpec Mode2SignaturePrefixCodec
               Mode2VerifyPrepareNorm.
require import VerifyHbzDecodeCanonicalPostFreeze
               VerifySignaturePrefixCanonicalPostFreeze.

theory VerifyHbzRansSuccessCanonicalPostFreeze.

import Mode2HbzCodecSpec VerifyHbzDecodeCanonicalPostFreeze
       VerifySignaturePrefixCanonicalPostFreeze.

module Unpack = SignatureUnpackMode2Target.M.

lemma truncateu8_uint_lt_mode2_hbz_alphabet (w : W64.t) :
  W64.to_uint w < mode2_hbz_alphabet =>
  W8.to_uint (truncateu8 w) < mode2_hbz_alphabet.
proof.
move=> hw.
have [hw0 _] := W64.to_uint_cmp w.
rewrite W8u8.to_uint_truncateu8.
rewrite modz_small.
+ smt().
+ trivial.
qed.

lemma mode2_symbol_prefix_bound_step_valid_word symsp n (w : W64.t) :
  0 <= n < mode2_hbz_count =>
  mode2_symbol_prefix_bound symsp n =>
  !(W64.of_int mode2_hbz_alphabet \ule w) =>
  mode2_symbol_prefix_bound
    (BArray2048.set8 symsp n (truncateu8 w)) (n + 1).
proof.
move=> hn hprefix hvalid.
apply mode2_symbol_prefix_bound_step.
+ exact hn.
+ exact hprefix.
+ apply truncateu8_uint_lt_mode2_hbz_alphabet.
  move: hvalid.
  rewrite W64.uleE W64.of_uintK /=.
  smt(W64.to_uint_cmp).
qed.

lemma rans_decode_success_mode2_symbol_prefix_bound :
  hoare [Unpack._rans_decode :
    BArray24.get64 statep 0 = W64.of_int mode2_hbz_count /\
    BArray24.get64 statep 2 = W64.of_int mode2_hbz_alphabet
    ==>
    BArray24.get64 res.`2 1 = W64.zero =>
    mode2_symbol_prefix_bound res.`1 mode2_hbz_count].
proof.
proc.
seq 32 :
  (count = W64.of_int mode2_hbz_count /\
   m = W64.of_int mode2_hbz_alphabet /\
   0 <= W64.to_uint i <= mode2_hbz_count /\
   (bad = W64.zero =>
      mode2_symbol_prefix_bound symsp (W64.to_uint i)) /\
   cond = (i \ult count) /\
   !cond).
+ while
    (count = W64.of_int mode2_hbz_count /\
     m = W64.of_int mode2_hbz_alphabet /\
     0 <= W64.to_uint i <= mode2_hbz_count /\
     (bad = W64.zero =>
        mode2_symbol_prefix_bound symsp (W64.to_uint i)) /\
     cond = (i \ult count)).
  - wp.
    sp 2.
    if.
    * auto => />.
    * seq 14 :
        (count = W64.of_int mode2_hbz_count /\
         m = W64.of_int mode2_hbz_alphabet /\
         0 <= W64.to_uint i < mode2_hbz_count /\
         bad = W64.zero /\
         mode2_symbol_prefix_bound symsp (W64.to_uint i) /\
         tmp64 = zeroextu64 s32).
      + auto => /> &hr ms0 hi0 hile hprefix hguard;
        split; move=> _;
        move: hguard;
        rewrite W64.ultE W64.of_uintK /=;
        smt(W64.to_uint_cmp).
      + sp 1.
        if.
        * auto => />; rewrite /protect_64; smt(W64.to_uint_cmp).
        * seq 21 :
            (count = W64.of_int mode2_hbz_count /\
             m = W64.of_int mode2_hbz_alphabet /\
             0 <= W64.to_uint i < mode2_hbz_count /\
             bad = W64.zero /\
             mode2_symbol_prefix_bound symsp (W64.to_uint i + 1) /\
             cond = (again <> W64.zero) /\
             !cond).
          - wp.
            while
              (count = W64.of_int mode2_hbz_count /\
               m = W64.of_int mode2_hbz_alphabet /\
               0 <= W64.to_uint i < mode2_hbz_count /\
               bad = W64.zero /\
               mode2_symbol_prefix_bound symsp (W64.to_uint i + 1) /\
               cond = (again <> W64.zero)).
            * auto => />.
            * auto => />;
              smt(mode2_symbol_prefix_bound_step_valid_word).
          - auto => /> &hr hi0 hilt hprefix.
            rewrite /protect_64.
            have hi_next :
                W64.to_uint (i{hr} + W64.one) =
                W64.to_uint i{hr} + 1.
            + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
              trivial.
            rewrite hi_next.
            smt(W64.to_uint_cmp).
  - auto => />; smt(mode2_symbol_prefix_bound_zero).
+ auto => /> &hr hi0 hile hprefix hnot hbad.
  have hieq : W64.to_uint i{hr} = mode2_hbz_count.
  + move: hnot.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hfull : mode2_symbol_prefix_bound symsp{hr} mode2_hbz_count.
  + rewrite -hieq.
    exact (hprefix hbad).
  smt().
qed.

lemma decode_hb_z1_full_success_mode2_canonical
    (hbz0 : BArray8192.t) (bad0 : BArray8.t) :
  hoare [Unpack._decode_hb_z1_full :
    hp = hbz0 /\
    badp = bad0 /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset
    ==>
    BArray8.get64 res.`2 0 = W64.zero =>
    canonical_hbz_prefix res.`1 mode2_hbz_count /\
    Mode2VerifyPrepareNorm.canonical_hbz_mode2 res.`1 /\
    Mode2VerifyPrepareNorm.coeff_tail_frame
      hbz0 res.`1 mode2_hbz_count].
proof.
proc.
seq 10 :
  (hp = hbz0 /\
   badp = bad0 /\
   count = W64.of_int mode2_hbz_count /\
   offset = W64.of_int mode2_hbz_offset /\
   (BArray24.get64 statep 1 = W64.zero =>
      mode2_symbol_prefix_bound symsp mode2_hbz_count)).
+ wp.
  call rans_decode_success_mode2_symbol_prefix_bound.
  auto => />.
+ sp 4.
  if.
  - wp.
    exists* symsp{hr}; elim* => symsp1.
    call (decode_hb_z1_apply_mode2_symbol_prefix_canonical hbz0 symsp1).
    auto => />; smt(canonical_hbz_prefix_implies_verify).
  - auto => />; rewrite /protect_64; smt().
qed.

lemma unpack_sig_full_mode2_verify_canonical
    (cp0 : BArray1024.t) (low0 hbz0 : BArray8192.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t) :
  hoare [Unpack._unpack_sig_full :
    cp = cp0 /\
    lowp = low0 /\
    hbzp = hbz0 /\
    badp = bad0 /\
    sigp = sig0 /\
    lcount_i = Mode2SignaturePrefixCodec.mode2_lcount /\
    hb_count_i = mode2_hbz_count /\
    hb_m_i = mode2_hbz_alphabet /\
    hb_offset_i = mode2_hbz_offset
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res.`1 /\
    Mode2VerifyPrepareNorm.canonical_signed_low res.`2 /\
    (BArray8.get64 res.`5 0 = W64.zero =>
      Mode2VerifyPrepareNorm.canonical_hbz_mode2 res.`3 /\
      Mode2VerifyPrepareNorm.coeff_tail_frame
        hbz0 res.`3 mode2_hbz_count)].
proof.
proc.
seq 11 :
  (hbzp = hbz0 /\
   badp = bad0 /\
   hb_count_i = mode2_hbz_count /\
   hb_m_i = mode2_hbz_alphabet /\
   hb_offset_i = mode2_hbz_offset /\
   Mode2VerifyPrepareNorm.canonical_challenge cp /\
   Mode2VerifyPrepareNorm.canonical_signed_low lowp).
+ call (unpack_sig_prefix_mode2_canonical cp0 low0 sig0).
  auto.
+ seq 25 :
    (hbzp = hbz0 /\
     badp = bad0 /\
     hb_count_i = mode2_hbz_count /\
     hb_m_i = mode2_hbz_alphabet /\
     hb_offset_i = mode2_hbz_offset /\
     Mode2VerifyPrepareNorm.canonical_challenge cp /\
     Mode2VerifyPrepareNorm.canonical_signed_low lowp).
  + wp.
    call (_ : true); first by auto.
    auto.
  if.
  + seq 12 :
      (Mode2VerifyPrepareNorm.canonical_challenge cp /\
       Mode2VerifyPrepareNorm.canonical_signed_low lowp /\
       (bad = W64.zero =>
         Mode2VerifyPrepareNorm.canonical_hbz_mode2 hbzp /\
         Mode2VerifyPrepareNorm.coeff_tail_frame
           hbz0 hbzp mode2_hbz_count)).
    + wp.
      call (decode_hb_z1_full_success_mode2_canonical hbz0 bad0).
      wp.
      call (_ : true); first by auto.
      wp.
      call (_ : true); first by auto.
      auto => /> &hr hchallenge hlow result hdecode hsuccess.
      have hbad : BArray8.get64 result.`2 0 = W64.zero.
      + move: hsuccess.
        rewrite /protect_64.
        trivial.
      move: (hdecode hbad) => [_ [hcanon htail]].
      split; first exact hcanon.
      exact htail.
    if.
    + wp.
      call (_ : true); first by auto.
      auto => />; rewrite /protect_64; smt().
    + auto => />; rewrite /protect_64; smt().
  + auto => />; rewrite /protect_64; smt().
qed.

lemma unpack_sig_mode2_full_jazz_verify_canonical
    (cp0 : BArray1024.t) (low0 hbz0 : BArray8192.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t) :
  hoare [Unpack.unpack_sig_mode2_full_jazz :
    cp = cp0 /\
    lowp = low0 /\
    hbzp = hbz0 /\
    badp = bad0 /\
    sigp = sig0
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res.`1 /\
    Mode2VerifyPrepareNorm.canonical_signed_low res.`2 /\
    (BArray8.get64 res.`5 0 = W64.zero =>
      Mode2VerifyPrepareNorm.canonical_hbz_mode2 res.`3 /\
      Mode2VerifyPrepareNorm.coeff_tail_frame
        hbz0 res.`3 mode2_hbz_count)].
proof.
proc.
call (unpack_sig_full_mode2_verify_canonical cp0 low0 hbz0 bad0 sig0).
auto => />; rewrite /protect_ptr; smt().
qed.

end VerifyHbzRansSuccessCanonicalPostFreeze.
