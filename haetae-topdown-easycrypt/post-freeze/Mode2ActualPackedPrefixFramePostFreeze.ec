require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget SignaturePackMode2Target
               Mode2SignaturePrefixCodec Mode2SignaturePrefixPack.

theory Mode2ActualPackedPrefixFramePostFreeze.

import Mode2SignaturePrefixCodec.

module Sign = RawSignApiTarget.M.
module PrefixPack = SignaturePackMode2Target.M.

(* Prefix-layout and suffix-frame partial correctness only.  The payload-copy
   theorem needs the explicit 416-byte total bound; this file does not yet
   claim that a complete signer call reaches a successful full pack. *)

op prefix_bytes : int = challenge_bytes + low_words.

op packed_prefix
    (sig : BArray2948.t) (cp : BArray1024.t)
    (low : BArray8192.t) : bool =
  packed_challenge_prefix sig cp challenge_bytes /\
  packed_low_prefix sig low low_words.

lemma packed_low_prefix_set_after
    sig low idx value :
  0 <= idx < 2948 =>
  prefix_bytes <= idx =>
  packed_low_prefix sig low low_words =>
  packed_low_prefix (BArray2948.set8 sig idx value) low low_words.
proof.
move=> hidx hafter hprefix.
rewrite /packed_low_prefix => i hi.
rewrite BArray2948.get_setE 1:hidx.
rewrite ifF.
+ rewrite /prefix_bytes /challenge_bytes /low_words in hafter.
  smt().
+ exact (hprefix i hi).
qed.

lemma packed_prefix_set_after
    sig cp low idx value :
  0 <= idx < 2948 =>
  prefix_bytes <= idx =>
  packed_prefix sig cp low =>
  packed_prefix (BArray2948.set8 sig idx value) cp low.
proof.
move=> hidx hafter [hcp hlow].
split.
+ apply packed_challenge_prefix_set_after.
  + exact hidx.
  + rewrite /challenge_bytes; smt().
  + rewrite /prefix_bytes /challenge_bytes /low_words in hafter.
    smt().
  + exact hcp.
+ exact (packed_low_prefix_set_after sig low idx value
           hidx hafter hlow).
qed.

lemma raw_pack_sig_prefix_exact :
  equiv [Sign._pack_sig_prefix ~ PrefixPack._pack_sig_prefix :
    ={sigp, cp, lowp, lcount, sigbytes}
    ==>
    ={res}].
proof.
by proc; sim.
qed.

lemma raw_pack_sig_prefix_mode2_layout
    (cp0 : BArray1024.t) (low0 : BArray8192.t) :
  hoare [Sign._pack_sig_prefix :
    cp = cp0 /\ lowp = low0 /\
    lcount = W64.of_int mode2_lcount /\
    sigbytes = W64.of_int mode2_sigbytes
    ==>
    packed_prefix res cp0 low0].
proof.
conseq raw_pack_sig_prefix_exact
  (Mode2SignaturePrefixPack.pack_sig_prefix_mode2_layout cp0 low0).
+ move=> &1 hpre.
  exists (sigp{1}, cp{1}, lowp{1}, lcount{1}, sigbytes{1}).
  exact hpre.
+ move=> &1 &2 hres hpost.
  rewrite /packed_prefix hres.
  exact hpost.
qed.

lemma raw_pack_sig_size_offsets_zero_payload_bound
    (hbsize0 hsize0 : W64.t) :
  hoare [Sign.__pack_sig_size_offsets_values :
    hbsize = hbsize0 /\ hsize = hsize0 /\
    base_hb = W64.of_int 132 /\ base_h = W64.of_int 7 /\
    payload_limit = W64.of_int 416
    ==>
    res.`2 = W64.zero =>
    W64.to_uint hbsize0 + W64.to_uint hsize0 <= 416].
proof.
proc.
auto => />.
rewrite /protect_64.
smt(W64.to_uint_cmp).
qed.

lemma raw_pack_sig_suffix_preserves_prefix
    (sig0 : BArray2948.t) (cp0 : BArray1024.t)
    (low0 : BArray8192.t) (hbsize0 hsize0 : W64.t) :
  hoare [Sign.__pack_sig_suffix_at :
    sigp = sig0 /\ off = W64.of_int prefix_bytes /\
    hbsize = hbsize0 /\ hsize = hsize0 /\
    W64.to_uint hbsize0 + W64.to_uint hsize0 <= 416 /\
    packed_prefix sig0 cp0 low0
    ==>
    packed_prefix res cp0 low0].
proof.
proc.
while
  (off = W64.of_int prefix_bytes /\
   hbsize = hbsize0 /\ hsize = hsize0 /\
   W64.to_uint hbsize0 + W64.to_uint hsize0 <= 416 /\
   0 <= W64.to_uint i <= W64.to_uint hsize0 /\
   W64.to_uint dst =
     prefix_bytes + 2 + W64.to_uint hbsize0 + W64.to_uint i /\
   packed_prefix sigp cp0 low0).
+ auto => /> &hr hsum hi0 hile hdst hchallenge hlow hguard.
  have hilt : W64.to_uint i{hr} < W64.to_uint hsize0.
  + move: hguard; smt(W64.to_uint_cmp).
  have hdstbound :
      0 <= W64.to_uint dst{hr} < 2948 by
    rewrite hdst /prefix_bytes /challenge_bytes /low_words; smt().
  have hdstafter : prefix_bytes <= W64.to_uint dst{hr} by
    rewrite hdst; smt(W64.to_uint_cmp).
  have hinext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  have hdstnext :
      W64.to_uint (dst{hr} + W64.one) = W64.to_uint dst{hr} + 1.
  + have hdstlim : W64.to_uint dst{hr} < W64.modulus - 1 by
      rewrite hdst /prefix_bytes /challenge_bytes /low_words;
      smt(W64.to_uint_cmp).
    by rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  split.
  + clear hsum hdst hchallenge hlow hguard hdstbound hdstafter hdstnext.
    rewrite hinext.
    smt(W64.to_uint_cmp).
  split.
  + rewrite hdstnext hdst hinext; ring.
  + apply packed_prefix_set_after.
    + exact hdstbound.
    + exact hdstafter.
    + split; assumption.
wp.
while
  (off = W64.of_int prefix_bytes /\
   hbsize = hbsize0 /\ hsize = hsize0 /\
   W64.to_uint hbsize0 + W64.to_uint hsize0 <= 416 /\
   0 <= W64.to_uint i <= W64.to_uint hbsize0 /\
   W64.to_uint dst = prefix_bytes + 2 + W64.to_uint i /\
   packed_prefix sigp cp0 low0).
+ auto => /> &hr hsum hi0 hile hdst hchallenge hlow hguard.
  have hilt : W64.to_uint i{hr} < W64.to_uint hbsize0.
  + move: hguard; smt(W64.to_uint_cmp).
  have hdstbound :
      0 <= W64.to_uint dst{hr} < 2948 by
    rewrite hdst /prefix_bytes /challenge_bytes /low_words; smt().
  have hdstafter : prefix_bytes <= W64.to_uint dst{hr} by
    rewrite hdst; smt(W64.to_uint_cmp).
  have hinext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  have hdstnext :
      W64.to_uint (dst{hr} + W64.one) = W64.to_uint dst{hr} + 1.
  + have hdstlim : W64.to_uint dst{hr} < W64.modulus - 1 by
      rewrite hdst /prefix_bytes /challenge_bytes /low_words;
      smt(W64.to_uint_cmp).
    by rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  split.
  + clear hsum hdst hchallenge hlow hguard hdstbound hdstafter hdstnext.
    rewrite hinext.
    smt(W64.to_uint_cmp).
  split.
  + rewrite hdstnext hdst hinext; ring.
  + apply packed_prefix_set_after.
    + exact hdstbound.
    + exact hdstafter.
    + split; assumption.
auto => />.
move=> &hr hsum hprefix.
have hoff : W64.to_uint (W64.of_int prefix_bytes) = prefix_bytes by
  rewrite /prefix_bytes /challenge_bytes /low_words W64.of_uintK /=.
move=> hlow.
have hmeta0 :
    packed_prefix
      (BArray2948.set8 sig0 prefix_bytes
        (truncateu8 (truncateu32 offsets{hr}))) cp0 low0.
+ apply packed_prefix_set_after.
  + rewrite /prefix_bytes /challenge_bytes /low_words; smt().
  + trivial.
  + split; assumption.
have hmeta1 :
    packed_prefix
      (BArray2948.set8
        (BArray2948.set8 sig0 prefix_bytes
          (truncateu8 (truncateu32 offsets{hr})))
        (prefix_bytes + 1)
        (truncateu8 (truncateu32 offsets{hr} `>>` W8.of_int 8)))
      cp0 low0.
+ apply packed_prefix_set_after.
  + rewrite /prefix_bytes /challenge_bytes /low_words; smt().
  + smt().
  + exact hmeta0.
split.
+ split; first smt(W64.to_uint_cmp).
  exact hmeta1.
+ move=> dst0 i0 sigp0 hdone hi0 hile hdst hchallenge hlow0.
  have hieq : W64.to_uint i0 = W64.to_uint hbsize0.
  + move: hdone.
    rewrite W64.ultE.
    smt(W64.to_uint_cmp).
  split; first smt(W64.to_uint_cmp).
  by rewrite hdst hieq.
qed.

(* Prefix packing is unconditional.  A failing full pack skips the suffix;
   a successful one uses the explicit payload bound to frame suffix writes.
   Thus this theorem preserves the prefix without asserting pack success. *)
lemma raw_pack_sig_full_mode2_prefix
    (cp0 : BArray1024.t) (low0 : BArray8192.t) :
  hoare [Sign._pack_sig_full :
    cp = cp0 /\ lowp = low0 /\
    sigbytes_i = mode2_sigbytes /\ lcount_i = mode2_lcount /\
    base_hb_i = 132 /\ base_h_i = 7 /\ payload_limit_i = 416
    ==>
    packed_prefix res.`1 cp0 low0].
proof.
proc.
seq 9 :
  (packed_prefix sigp cp0 low0 /\
   lcount_i = mode2_lcount /\
   base_hb_i = 132 /\ base_h_i = 7 /\ payload_limit_i = 416).
+ call (raw_pack_sig_prefix_mode2_layout cp0 low0).
  auto.
+ seq 14 :
    (packed_prefix sigp cp0 low0 /\
     lcount_i = mode2_lcount /\
     base_hb = W64.of_int 132 /\ base_h = W64.of_int 7 /\
     payload_limit = W64.of_int 416).
  + wp.
    call (_ : true); first by auto.
    wp.
    call (_ : true); first by auto.
    auto => />.
    rewrite /protect_64.
    auto.
  + seq 4 :
      (packed_prefix sigp cp0 low0 /\
       lcount_i = mode2_lcount /\
       (bad = W64.zero =>
         W64.to_uint hbsize + W64.to_uint hsize <= 416)).
    + exlim hbsize => hbsize_before_size.
      exlim hsize => hsize_before_size.
      wp.
      call
        (raw_pack_sig_size_offsets_zero_payload_bound
          hbsize_before_size hsize_before_size).
      auto => />.
      rewrite /protect_64.
      auto.
    + wp.
      if; last by auto => />.
      exlim sigp => sig_before_suffix.
      exlim hbsize => hbsize_before_suffix.
      exlim hsize => hsize_before_suffix.
      call
        (raw_pack_sig_suffix_preserves_prefix
          sig_before_suffix cp0 low0
          hbsize_before_suffix hsize_before_suffix).
      auto => />.
qed.

end Mode2ActualPackedPrefixFramePostFreeze.
