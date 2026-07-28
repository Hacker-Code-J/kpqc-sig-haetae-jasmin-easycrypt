require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import
  KeygenSamplerCallersTarget
  KeygenUniformXofLeafSpec
  KeygenShakeStreamSpec
  HAETAE_Keccak1600
  KeygenKeccak1600Spec
  TargetKeygenShakeStream.

theory TargetKeygenUniformXofLeaf.

lemma shake128_squeeze_block_step
    (initial : int list)
    (original before_out after_out : BArray1024.t)
    (before_state after_state : BArray200.t)
    (block : int) :
  0 <= block < 4 =>
  KeygenShakeStreamSpec.state_bytes_le before_state =
    KeygenShakeStreamSpec.squeeze_state_iter initial block =>
  KeygenShakeStreamSpec.squeeze_blocks_matches
    before_out 0 initial 168 block =>
  KeygenShakeStreamSpec.squeeze_region_frame
    original before_out 0 168 block =>
  KeygenShakeStreamSpec.rate_block_matches
    after_out (block * 168) after_state 168 =>
  KeygenShakeStreamSpec.rate_block_frame
    before_out after_out (block * 168) 168 =>
  KeygenKeccak1600Spec.state_of_barray after_state =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray before_state) =>
  KeygenShakeStreamSpec.state_bytes_le after_state =
    KeygenShakeStreamSpec.squeeze_state_iter initial (block + 1) /\
  KeygenShakeStreamSpec.squeeze_blocks_matches
    after_out 0 initial 168 (block + 1) /\
  KeygenShakeStreamSpec.squeeze_region_frame
    original after_out 0 168 (block + 1).
proof.
move=> hblock hstate hmatches hregion hblock_matches hframe hperm.
have hstate_next :=
  KeygenShakeStreamSpec.squeeze_state_iter_barray_step
    initial before_state after_state block
    _ hstate hperm.
+ smt().
have hprefix :=
  KeygenShakeStreamSpec.rate_block_matches_fips_prefix
    after_out (block * 168) after_state
    (KeygenShakeStreamSpec.squeeze_state_iter initial (block + 1)) 168
    _ hstate_next hblock_matches.
+ smt().
have [hmatches_next hregion_next] :=
  KeygenShakeStreamSpec.squeeze_blocks_induction_step
    original before_out after_out 0 initial 168 block
    _ _ _ _ hmatches hregion hprefix hframe.
+ smt().
+ smt().
+ smt().
+ smt().
by do split.
qed.

lemma le16_word_uint (lo hi : W8.t) :
  W32.to_uint
    ((zeroextu32 lo) `|` ((zeroextu32 hi) `<<` (W8.of_int 8))) =
  W8.to_uint lo + 256 * W8.to_uint hi.
proof.
rewrite W32.to_uint_orw_disjoint.
+ apply W32.wordP => bit hbit.
  rewrite W32.andwE W4u8.zeroextu32_bit.
  rewrite /(`<<`) W32.shlwE.
  rewrite W8.of_uintK /= W4u8.zeroextu32_bit.
  smt().
rewrite /(`<<`) W32.to_uint_shl 1:/#.
rewrite W8.of_uintK /=.
rewrite !W4u8.to_uint_zeroextu32.
rewrite (modz_small (W8.to_uint hi * 256) 4294967296).
+ smt(W8.to_uint_cmp).
by ring.
qed.

lemma uniform_ctr_succ_uint (ctr : W64.t) :
  W64.to_uint ctr < KeygenUniformXofLeafSpec.uniform_poly_words_i =>
  W64.to_uint (ctr + W64.one) = W64.to_uint ctr + 1.
proof.
rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i.
move=> hctr.
by rewrite W64.to_uintD_small 1:/# W64.to_uint1.
qed.

lemma uniform_ctr_succ_le (ctr : W64.t) :
  W64.to_uint ctr < KeygenUniformXofLeafSpec.uniform_poly_words_i =>
  W64.to_uint (ctr + W64.one) <=
    KeygenUniformXofLeafSpec.uniform_poly_words_i.
proof.
move=> hctr.
rewrite (uniform_ctr_succ_uint ctr hctr).
rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i in hctr.
rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i.
smt().
qed.

lemma uniform_ctr_succ_nonnegative (ctr : W64.t) :
  0 <= W64.to_uint (ctr + W64.one).
proof.
have hbound := W64.to_uint_cmp (ctr + W64.one).
smt().
qed.

lemma shake128_first_bytes_size (state : int list) :
  size (KeygenShakeStreamSpec.shake128_squeeze_bytes state 4) =
    KeygenUniformXofLeafSpec.uniform_first_bytes_i.
proof.
rewrite /KeygenShakeStreamSpec.shake128_squeeze_bytes
        KeygenShakeStreamSpec.squeeze_bytes_iter_size 1:/# 1:/#
        /KeygenUniformXofLeafSpec.uniform_first_bytes_i.
trivial.
qed.

lemma w64_and1_word (w : W64.t) :
  w `&` W64.of_int 1 = W64.of_int (W64.to_uint w %% 2).
proof.
have h :
  w `&` W64.of_int (2 ^ 1 - 1) =
  W64.of_int (W64.to_uint w %% (2 ^ 1)).
+ by apply W64.and_mod; smt().
by move: h => /=.
qed.

lemma uniform_even_buflen_and1_zero (w : W64.t) :
  (w = W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
   w = W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) =>
  w `&` W64.of_int 1 = W64.of_int 0.
proof.
move=> [-> | ->];
  rewrite w64_and1_word
          /KeygenUniformXofLeafSpec.uniform_first_bytes_i
          /KeygenUniformXofLeafSpec.uniform_block_bytes_i
          !W64.of_uintK /=; trivial.
qed.

lemma shake128_squeeze_bytes_size state blocks :
  0 <= blocks =>
  size (KeygenShakeStreamSpec.shake128_squeeze_bytes state blocks) =
    blocks * KeygenUniformXofLeafSpec.uniform_block_bytes_i.
proof.
move=> hblocks.
rewrite /KeygenShakeStreamSpec.shake128_squeeze_bytes
        KeygenShakeStreamSpec.squeeze_bytes_iter_size 1:/# 1://
        /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
trivial.
qed.

lemma uniform_accepted_shake128_succ state blocks pairs :
  0 <= blocks =>
  0 <= pairs =>
  KeygenUniformXofLeafSpec.uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_bytes state (blocks + 1))
      (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i + pairs) =
    KeygenUniformXofLeafSpec.uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_bytes state blocks)
      (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i) ++
    KeygenUniformXofLeafSpec.uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_block state blocks) pairs.
proof.
move=> hblocks hpairs.
rewrite KeygenShakeStreamSpec.shake128_squeeze_bytes_succ 1://.
apply KeygenUniformXofLeafSpec.uniform_accepted_cat_even.
+ smt().
+ exact hpairs.
rewrite shake128_squeeze_bytes_size 1://
        /KeygenUniformXofLeafSpec.uniform_block_bytes_i
        /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
ring.
qed.

lemma shake128_squeeze_overwrite_step
    (initial : int list)
    (before_state after_state : BArray200.t)
    (after_out : BArray1024.t)
    (blocks : int) :
  0 <= blocks =>
  KeygenShakeStreamSpec.state_bytes_le before_state =
    KeygenShakeStreamSpec.squeeze_state_iter initial blocks =>
  KeygenShakeStreamSpec.rate_block_matches
    after_out 0 after_state KeygenUniformXofLeafSpec.uniform_block_bytes_i =>
  KeygenKeccak1600Spec.state_of_barray after_state =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray before_state) =>
  KeygenShakeStreamSpec.state_bytes_le after_state =
      KeygenShakeStreamSpec.squeeze_state_iter initial (blocks + 1) /\
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    after_out 0
    (KeygenShakeStreamSpec.shake128_squeeze_block initial blocks)
    KeygenUniformXofLeafSpec.uniform_block_bytes_i.
proof.
move=> hblocks hstate hblock hperm.
have hstate_next :=
  KeygenShakeStreamSpec.squeeze_state_iter_barray_step
    initial before_state after_state blocks hblocks hstate hperm.
have hprefix :=
  KeygenShakeStreamSpec.rate_block_matches_fips_prefix
    after_out 0 after_state
    (KeygenShakeStreamSpec.squeeze_state_iter initial (blocks + 1)) 168
    _ hstate_next _.
+ smt().
+ rewrite /KeygenUniformXofLeafSpec.uniform_block_bytes_i in hblock.
  exact hblock.
split; first exact hstate_next.
rewrite /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
exact (KeygenShakeStreamSpec.fips_rate_prefix_matches_shake128_block
  after_out 0 initial blocks hprefix).
qed.

lemma consume2048_counter ctr0 :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_consume_2048 :
    ctr = ctr0 /\
    W64.to_uint ctr0 <= KeygenUniformXofLeafSpec.uniform_poly_words_i
    ==>
    W64.to_uint ctr0 <= W64.to_uint res.`2 <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i].
proof.
proc.
while (W64.to_uint ctr0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ if.
  + by auto.
  sp 2.
  if.
  + by auto.
  sp 10.
  if.
  + auto => /> &hr pos0 hlow hhigh hlive hnotfull hrem haccept.
    rewrite W64.to_uintD_small 1:/#.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            W64.uleE W64.of_uintK /= in hnotfull.
    smt(W64.to_uint_cmp).
  by auto.
wp.
by skip => />.
qed.

lemma consume8192_counter ctr0 :
  hoare [KeygenSamplerCallersTarget.M.__poly_uniform_consume :
    ctr = ctr0 /\
    W64.to_uint ctr0 <= KeygenUniformXofLeafSpec.uniform_poly_words_i
    ==>
    W64.to_uint ctr0 <= W64.to_uint res.`2 <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i].
proof.
proc.
while (W64.to_uint ctr0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ if.
  + by auto.
  sp 2.
  if.
  + by auto.
  sp 11.
  if.
  + auto => /> &hr pos0 hlow hhigh hlive hnotfull hrem haccept.
    rewrite W64.to_uintD_small 1:/#.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            W64.uleE W64.of_uintK /= in hnotfull.
    smt(W64.to_uint_cmp).
  by auto.
wp.
by skip => />.
qed.

lemma consume2048_frame ap0 base_i :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_consume_2048 :
    KeygenUniformXofLeafSpec.frame8192 ap0 ap base_i /\
    W64.to_uint base = base_i /\
    base_i +
      KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4 /\
    0 <= W64.to_uint ctr <= KeygenUniformXofLeafSpec.uniform_poly_words_i
    ==>
    KeygenUniformXofLeafSpec.frame8192 ap0 res.`1 base_i /\
    0 <= W64.to_uint res.`2 <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i].
proof.
proc.
while (KeygenUniformXofLeafSpec.frame8192
         ap0 ap base_i /\
       W64.to_uint base = base_i /\
       base_i +
         KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ if.
  + by auto.
  sp 2.
  if.
  + by auto.
  sp 10.
  if.
  + auto => /> &hr pos0 hframe hcap hctr0 hctrle
               hlive hnotfull hrem haccept.
    split.
    + apply (KeygenUniformXofLeafSpec.frame8192_set32_word
               ap0 ap{hr} (W64.to_uint base{hr})
               base{hr} ctr{hr} _).
      + exact hframe.
      + trivial.
      + exact hcap.
      rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
              W64.uleE W64.of_uintK /= in hnotfull.
      smt().
    rewrite W64.to_uintD_small 1:/#.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            W64.uleE W64.of_uintK /= in hnotfull.
    smt().
  by auto.
wp.
skip => />.
qed.

lemma consume8192_frame ap0 base_i :
  hoare [KeygenSamplerCallersTarget.M.__poly_uniform_consume :
    KeygenUniformXofLeafSpec.frame32768 ap0 ap base_i /\
    W64.to_uint base = base_i /\
    base_i +
      KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    0 <= W64.to_uint ctr <= KeygenUniformXofLeafSpec.uniform_poly_words_i
    ==>
    KeygenUniformXofLeafSpec.frame32768 ap0 res.`1 base_i /\
    0 <= W64.to_uint res.`2 <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i].
proof.
proc.
while (KeygenUniformXofLeafSpec.frame32768
         ap0 ap base_i /\
       W64.to_uint base = base_i /\
       base_i +
         KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ if.
  + by auto.
  sp 2.
  if.
  + by auto.
  sp 11.
  if.
  + auto => /> &hr pos0 hframe hcap hctr0 hctrle
               hlive hnotfull hrem haccept.
    split.
    + apply (KeygenUniformXofLeafSpec.frame32768_set32_word
               ap0 ap{hr} (W64.to_uint base{hr})
               base{hr} ctr{hr} _).
      + exact hframe.
      + trivial.
      + exact hcap.
      rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
              W64.uleE W64.of_uintK /= in hnotfull.
      smt().
    rewrite W64.to_uintD_small 1:/#.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            W64.uleE W64.of_uintK /= in hnotfull.
    smt().
  by auto.
wp.
skip => />.
qed.

lemma consume2048_range base_i :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_consume_2048 :
    W64.to_uint base = base_i /\
    base_i +
      KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4 /\
    KeygenUniformXofLeafSpec.bounded_prefix8192
      ap base_i (W64.to_uint ctr) /\
    0 <= W64.to_uint ctr <= KeygenUniformXofLeafSpec.uniform_poly_words_i
    ==>
    0 <= W64.to_uint res.`2 <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    KeygenUniformXofLeafSpec.bounded_prefix8192
      res.`1 base_i (W64.to_uint res.`2)].
proof.
proc.
while (KeygenUniformXofLeafSpec.bounded_prefix8192
         ap base_i (W64.to_uint ctr) /\
       W64.to_uint base = base_i /\
       base_i +
         KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ if.
  + by auto.
  sp 2.
  if.
  + by auto.
  sp 10.
  if.
  + auto => /> &hr pos0 hprefix hcap hctr0 hctrle
               hlive hnotfull hrem haccept.
    split.
    + apply (KeygenUniformXofLeafSpec.bounded_prefix8192_set32_word
               ap{hr} (W64.to_uint base{hr})
               base{hr} ctr{hr} _).
      + trivial.
      + exact hcap.
      + rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
                W64.uleE W64.of_uintK /= in hnotfull.
        smt().
      + exact hprefix.
      rewrite /KeygenUniformXofLeafSpec.uniform_q_i
              W32.ultE W32.of_uintK /= in haccept.
      exact haccept.
    rewrite W64.to_uintD_small 1:/#.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            W64.uleE W64.of_uintK /= in hnotfull.
    smt().
  by auto.
wp.
skip => />.
qed.

lemma consume8192_range base_i :
  hoare [KeygenSamplerCallersTarget.M.__poly_uniform_consume :
    W64.to_uint base = base_i /\
    base_i +
      KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    KeygenUniformXofLeafSpec.bounded_prefix32768
      ap base_i (W64.to_uint ctr) /\
    0 <= W64.to_uint ctr <= KeygenUniformXofLeafSpec.uniform_poly_words_i
    ==>
    0 <= W64.to_uint res.`2 <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    KeygenUniformXofLeafSpec.bounded_prefix32768
      res.`1 base_i (W64.to_uint res.`2)].
proof.
proc.
while (KeygenUniformXofLeafSpec.bounded_prefix32768
         ap base_i (W64.to_uint ctr) /\
       W64.to_uint base = base_i /\
       base_i +
         KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ if.
  + by auto.
  sp 2.
  if.
  + by auto.
  sp 11.
  if.
  + auto => /> &hr pos0 hprefix hcap hctr0 hctrle
               hlive hnotfull hrem haccept.
    split.
    + apply (KeygenUniformXofLeafSpec.bounded_prefix32768_set32_word
               ap{hr} (W64.to_uint base{hr})
               base{hr} ctr{hr} _).
      + trivial.
      + exact hcap.
      + rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
                W64.uleE W64.of_uintK /= in hnotfull.
        smt().
      + exact hprefix.
      rewrite /KeygenUniformXofLeafSpec.uniform_q_i
              W32.ultE W32.of_uintK /= in haccept.
      exact haccept.
    rewrite W64.to_uintD_small 1:/#.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            W64.uleE W64.of_uintK /= in hnotfull.
    smt().
  by auto.
wp.
skip => />.
qed.

lemma consume2048_first672 ap0 bytes base_i :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_consume_2048 :
    ap = ap0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4 /\
    ctr = W64.of_int 0 /\
    buflen = W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
    size bytes = KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bp 0 bytes KeygenUniformXofLeafSpec.uniform_first_bytes_i
    ==>
    exists pairs,
      0 <= pairs <= KeygenUniformXofLeafSpec.uniform_first_pairs_i /\
      W64.to_uint res.`2 =
        size (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
      size (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) <=
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      0 <= W64.to_uint res.`2 <=
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      KeygenUniformXofLeafSpec.decoded_prefix8192
        res.`1 base_i
        (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
      KeygenUniformXofLeafSpec.bounded_prefix8192
        res.`1 base_i (W64.to_uint res.`2) /\
      KeygenUniformXofLeafSpec.frame8192 ap0 res.`1 base_i /\
      (W64.to_uint res.`2 =
         KeygenUniformXofLeafSpec.uniform_poly_words_i \/
       pairs = KeygenUniformXofLeafSpec.uniform_first_pairs_i)].
proof.
proc.
while (exists pairs,
         0 <= pairs <=
           KeygenUniformXofLeafSpec.uniform_first_pairs_i /\
         W64.to_uint pos = 2 * pairs /\
         W64.to_uint ctr =
           size (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
         size (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i /\
         KeygenUniformXofLeafSpec.decoded_prefix8192
           ap base_i
           (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
         KeygenUniformXofLeafSpec.bounded_prefix8192
           ap base_i (W64.to_uint ctr) /\
         KeygenUniformXofLeafSpec.frame8192 ap0 ap base_i /\
         W64.to_uint base = base_i /\
         W64.to_uint base +
           KeygenUniformXofLeafSpec.uniform_poly_words_i <=
           BArray8192.size %/ 4 /\
         buflen = W64.of_int
           KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
         size bytes = KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
         KeygenShakeStreamSpec.fips_rate_prefix_matches
           bp 0 bytes KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
         0 <= W64.to_uint ctr <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i /\
         (live = W64.of_int 0 =>
            W64.to_uint ctr =
              KeygenUniformXofLeafSpec.uniform_poly_words_i \/
            pairs = KeygenUniformXofLeafSpec.uniform_first_pairs_i)).
+ if.
  + auto => /> &hr pairs hpairs0 hpairsle hpos hctr hacceptedle
        hdecoded hbounded hframe hbase hcap hbuflen hbytelen hprefix
        hctrle hstop hfull.
    exists pairs.
    rewrite W64.uleE W64.of_uintK /= in hfull.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /KeygenUniformXofLeafSpec.uniform_first_pairs_i in hprefix.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /KeygenUniformXofLeafSpec.uniform_first_pairs_i in hfull.
    do split; try assumption; smt().
  sp 2.
  if.
  + auto => /> &hr pairs hpairs0 hpairsle hpos hctr hacceptedle
        hdecoded hbounded hframe hbase hcap hbuflen hbytelen hprefix
        hctrle hstop hnotfull hrem.
    have hposle : pos{hr} \ule W64.of_int 672.
    + rewrite W64.uleE W64.of_uintK /=.
      smt().
    have hremuint :
      W64.to_uint (W64.of_int 672 - pos{hr}) = 672 - 2 * pairs.
    + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
      trivial.
    have hpairs336 : pairs = 336.
    + rewrite W64.ultE W64.of_uintK /= in hrem.
      smt().
    smt(W64.to_uint_cmp).
  sp 10.
  if.
  + auto => /> &hr pos0 pairs hpairs0 hpairsle hpos hctr
        hacceptedle hdecoded hbounded hframe hbase hcap hbuflen
        hbytelen hprefix hctrle hstop hnotfull hrem
        haccept.
    have hposle : pos0 \ule W64.of_int 672.
    + rewrite W64.uleE W64.of_uintK /=.
      smt().
    have hremuint :
      W64.to_uint (W64.of_int 672 - pos0) = 672 - 2 * pairs.
    + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
      trivial.
    have hpairslt : pairs < 336.
    + rewrite W64.ultE W64.of_uintK /= in hrem.
      smt().
    have hpos1 :
      W64.to_uint (pos0 + W64.of_int 1) = 2 * pairs + 1.
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hpos.
      trivial.
    have hword :
      W32.to_uint
        ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
         ((zeroextu32
             (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
            (W8.of_int 8))) =
      KeygenUniformXofLeafSpec.uniform_le16 bytes pairs.
    + have hstream :
        KeygenShakeStreamSpec.fips_rate_prefix_matches
          bp{hr} 0 bytes 672.
      + exact hbuflen.
      rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches in hstream.
      have hlo := hstream (2 * pairs) _; first smt().
      have hhi := hstream (2 * pairs + 1) _; first smt().
      rewrite /KeygenUniformXofLeafSpec.uniform_le16.
      rewrite -(hlo) -(hhi).
      exact (le16_word_uint
        (BArray1024.get8 bp{hr} (2 * pairs))
        (BArray1024.get8 bp{hr} (2 * pairs + 1))).
    have hcandidate :
      KeygenUniformXofLeafSpec.uniform_le16 bytes pairs <
        KeygenUniformXofLeafSpec.uniform_q_i.
    + rewrite W32.ultE W32.of_uintK /= in haccept.
      rewrite /KeygenUniformXofLeafSpec.uniform_q_i.
      smt().
    have haccepted :=
      KeygenUniformXofLeafSpec.uniform_accepted_snoc bytes pairs hpairs0.
    rewrite hcandidate /= in haccepted.
    have hctrlt :
      W64.to_uint ctr{hr} <
        KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
              W64.uleE W64.of_uintK /= in hnotfull.
      smt().
    have hdecoded_rcons :
      KeygenUniformXofLeafSpec.decoded_prefix8192
        (BArray8192.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (rcons (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs)
          (KeygenUniformXofLeafSpec.uniform_le16 bytes pairs)).
    + apply (KeygenUniformXofLeafSpec.decoded_prefix8192_set32_word
        ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr}
        (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) _
        (KeygenUniformXofLeafSpec.uniform_le16 bytes pairs)).
      + trivial.
      + exact hbase.
      + exact hctr.
      + exact hctrlt.
      + exact hdecoded.
      exact hword.
    have hdecoded_next :
      KeygenUniformXofLeafSpec.decoded_prefix8192
        (BArray8192.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
    + rewrite haccepted.
      exact hdecoded_rcons.
    have hbounded_next :
      KeygenUniformXofLeafSpec.bounded_prefix8192
        (BArray8192.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (W64.to_uint (ctr{hr} + W64.one)).
    + apply (KeygenUniformXofLeafSpec.bounded_prefix8192_set32_word
        ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr} _).
      + trivial.
      + exact hbase.
      + exact hctrlt.
      + exact hbounded.
      by rewrite hword.
    have hframe_next :
      KeygenUniformXofLeafSpec.frame8192 ap0
        (BArray8192.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr}).
    + apply (KeygenUniformXofLeafSpec.frame8192_set32_word
        ap0 ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr} _).
      + exact hframe.
      + trivial.
      + exact hbase.
      exact hctrlt.
    have hctrupper_next := uniform_ctr_succ_le ctr{hr} hctrlt.
    have hctrlower_next := uniform_ctr_succ_nonnegative ctr{hr}.
    have hctr_next :
      W64.to_uint (ctr{hr} + W64.one) =
      size (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
    + rewrite (uniform_ctr_succ_uint ctr{hr} hctrlt)
              haccepted size_rcons hctr.
      trivial.
    have hacceptedle_next :
      size (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)) <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite haccepted size_rcons -hctr.
      rewrite -(uniform_ctr_succ_uint ctr{hr} hctrlt).
      exact hctrupper_next.
    have hpairs_next :
      0 <= pairs + 1 <=
        KeygenUniformXofLeafSpec.uniform_first_pairs_i.
    + rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i.
      smt().
    have hpos_next :
      W64.to_uint ((pos0 + W64.one) + W64.one) = 2 * (pairs + 1).
    + rewrite !W64.to_uintD_small 1:/# 1:/# /=.
      smt().
    have hterminal_next :
      live{hr} = W64.of_int 0 =>
      W64.to_uint (ctr{hr} + W64.one) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i \/
      pairs + 1 = KeygenUniformXofLeafSpec.uniform_first_pairs_i.
    + move=> hlive0.
      have hfalse : false.
      + apply hstop.
        exact hlive0.
      by elim hfalse.
    rewrite hpos.
    ring.
    exists (pairs + 1).
    do split; try assumption; try trivial.
    + smt().
    + smt().
    + rewrite /protect_32 hpos hpos1.
      exact hdecoded_next.
    + rewrite /protect_32 hpos hpos1.
      exact hbounded_next.
    + rewrite /protect_32 hpos hpos1.
      exact hframe_next.
  auto => /> &hr pos0 pairs hpairs0 hpairsle hpos hctr
      hacceptedle hdecoded hbounded hframe hbase hcap hbuflen
      hbytelen hprefix hctrle hstop hnotfull hrem
      hrejected.
  have hposle : pos0 \ule W64.of_int 672.
  + rewrite W64.uleE W64.of_uintK /=.
    smt().
  have hremuint :
    W64.to_uint (W64.of_int 672 - pos0) = 672 - 2 * pairs.
  + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
    trivial.
  have hpairslt : pairs < 336.
  + rewrite W64.ultE W64.of_uintK /= in hrem.
    smt().
  have hpos1 :
    W64.to_uint (pos0 + W64.of_int 1) = 2 * pairs + 1.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hpos.
    trivial.
  have hword :
    W32.to_uint
      ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
       ((zeroextu32
           (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
          (W8.of_int 8))) =
    KeygenUniformXofLeafSpec.uniform_le16 bytes pairs.
  + have hstream :
      KeygenShakeStreamSpec.fips_rate_prefix_matches
        bp{hr} 0 bytes 672.
    + exact hbuflen.
    rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches in hstream.
    have hlo := hstream (2 * pairs) _; first smt().
    have hhi := hstream (2 * pairs + 1) _; first smt().
    rewrite /KeygenUniformXofLeafSpec.uniform_le16.
    rewrite -(hlo) -(hhi).
    exact (le16_word_uint
      (BArray1024.get8 bp{hr} (2 * pairs))
      (BArray1024.get8 bp{hr} (2 * pairs + 1))).
  have hcandidate :
    !(KeygenUniformXofLeafSpec.uniform_le16 bytes pairs <
      KeygenUniformXofLeafSpec.uniform_q_i).
  + rewrite W32.ultE W32.of_uintK /= in hrejected.
    rewrite /KeygenUniformXofLeafSpec.uniform_q_i.
    smt().
  have haccepted :=
    KeygenUniformXofLeafSpec.uniform_accepted_snoc bytes pairs hpairs0.
  rewrite hcandidate /= in haccepted.
  have hctr_next :
    W64.to_uint ctr{hr} =
      size (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
  + rewrite haccepted.
    exact hctr.
  have hacceptedle_next :
    size (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)) <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
  + rewrite haccepted.
    exact hacceptedle.
  have hdecoded_next :
    KeygenUniformXofLeafSpec.decoded_prefix8192 ap{hr}
      (W64.to_uint base{hr})
      (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
  + rewrite haccepted.
    exact hdecoded.
  have hpairs_next :
    0 <= pairs + 1 <=
      KeygenUniformXofLeafSpec.uniform_first_pairs_i.
  + rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i.
    smt().
  have hpos_next :
    W64.to_uint ((pos0 + W64.one) + W64.one) = 2 * (pairs + 1).
  + rewrite !W64.to_uintD_small 1:/# 1:/# /=.
    smt().
  have hterminal_next :
    live{hr} = W64.of_int 0 =>
    W64.to_uint ctr{hr} =
      KeygenUniformXofLeafSpec.uniform_poly_words_i \/
    pairs + 1 = KeygenUniformXofLeafSpec.uniform_first_pairs_i.
  + move=> hlive0.
    have hfalse : false.
    + apply hstop.
      exact hlive0.
    by elim hfalse.
  rewrite hpos.
  ring.
  exists (pairs + 1).
  do split; try assumption; try trivial.
  + smt().
  + smt().
wp.
skip => /> &hr hbase hcap hprefix.
split.
+ exists 0.
  rewrite KeygenUniformXofLeafSpec.uniform_accepted_zero
          /KeygenUniformXofLeafSpec.uniform_first_pairs_i
          /KeygenUniformXofLeafSpec.uniform_poly_words_i.
  have hdecoded0 := KeygenUniformXofLeafSpec.decoded_prefix8192_zero
    ap0 (W64.to_uint base{hr}).
  have hbounded0 := KeygenUniformXofLeafSpec.bounded_prefix8192_zero
    ap0 (W64.to_uint base{hr}).
  have hframe0 := KeygenUniformXofLeafSpec.frame8192_refl
    ap0 (W64.to_uint base{hr}).
  do split; try assumption; try trivial; smt().
+ move=> ap1 ctr0 pos0 pairs hpairs0 hpairsle hpos hctr
      hacceptedle hdecoded hbounded hframe hctrlower hctrupper
      hterminal.
  exists pairs.
  do split.
  + smt().
  + smt().
  + exact hctr.
  + exact hacceptedle.
  + exact hdecoded.
  + exact hterminal.
qed.

lemma consume8192_first672 ap0 bytes base_i :
  hoare [KeygenSamplerCallersTarget.M.__poly_uniform_consume :
    ap = ap0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    ctr = W64.of_int 0 /\
    buflen = W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
    size bytes = KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bp 0 bytes KeygenUniformXofLeafSpec.uniform_first_bytes_i
    ==>
    exists pairs,
      0 <= pairs <= KeygenUniformXofLeafSpec.uniform_first_pairs_i /\
      W64.to_uint res.`2 =
        size (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
      size (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) <=
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      0 <= W64.to_uint res.`2 <=
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      KeygenUniformXofLeafSpec.decoded_prefix32768
        res.`1 base_i
        (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
      KeygenUniformXofLeafSpec.bounded_prefix32768
        res.`1 base_i (W64.to_uint res.`2) /\
      KeygenUniformXofLeafSpec.frame32768 ap0 res.`1 base_i /\
      (W64.to_uint res.`2 =
         KeygenUniformXofLeafSpec.uniform_poly_words_i \/
       pairs = KeygenUniformXofLeafSpec.uniform_first_pairs_i)].
proof.
proc.
while (exists pairs,
         0 <= pairs <=
           KeygenUniformXofLeafSpec.uniform_first_pairs_i /\
         W64.to_uint pos = 2 * pairs /\
         W64.to_uint ctr =
           size (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
         size (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i /\
         KeygenUniformXofLeafSpec.decoded_prefix32768
           ap base_i
           (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
         KeygenUniformXofLeafSpec.bounded_prefix32768
           ap base_i (W64.to_uint ctr) /\
         KeygenUniformXofLeafSpec.frame32768 ap0 ap base_i /\
         W64.to_uint base = base_i /\
         W64.to_uint base +
           KeygenUniformXofLeafSpec.uniform_poly_words_i <=
           BArray32768.size %/ 4 /\
         buflen = W64.of_int
           KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
         size bytes = KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
         KeygenShakeStreamSpec.fips_rate_prefix_matches
           bp 0 bytes KeygenUniformXofLeafSpec.uniform_first_bytes_i /\
         0 <= W64.to_uint ctr <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i /\
         (live = W64.of_int 0 =>
            W64.to_uint ctr =
              KeygenUniformXofLeafSpec.uniform_poly_words_i \/
            pairs = KeygenUniformXofLeafSpec.uniform_first_pairs_i)).
+ if.
  + auto => /> &hr pairs hpairs0 hpairsle hpos hctr hacceptedle
        hdecoded hbounded hframe hbase hcap hbuflen hbytelen hprefix
        hctrle hstop hfull.
    exists pairs.
    rewrite W64.uleE W64.of_uintK /= in hfull.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /KeygenUniformXofLeafSpec.uniform_first_pairs_i in hprefix.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /KeygenUniformXofLeafSpec.uniform_first_pairs_i in hfull.
    do split; try assumption; smt().
  sp 2.
  if.
  + auto => /> &hr pairs hpairs0 hpairsle hpos hctr hacceptedle
        hdecoded hbounded hframe hbase hcap hbuflen hbytelen hprefix
        hctrle hstop hnotfull hrem.
    have hposle : pos{hr} \ule W64.of_int 672.
    + rewrite W64.uleE W64.of_uintK /=.
      smt().
    have hremuint :
      W64.to_uint (W64.of_int 672 - pos{hr}) = 672 - 2 * pairs.
    + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
      trivial.
    have hpairs336 : pairs = 336.
    + rewrite W64.ultE W64.of_uintK /= in hrem.
      smt().
    smt(W64.to_uint_cmp).
  sp 11.
  if.
  + auto => /> &hr pos0 pairs hpairs0 hpairsle hpos hctr
        hacceptedle hdecoded hbounded hframe hbase hcap hbuflen
        hbytelen hprefix hctrle hstop hnotfull hrem
        haccept.
    have hposle : pos0 \ule W64.of_int 672.
    + rewrite W64.uleE W64.of_uintK /=.
      smt().
    have hremuint :
      W64.to_uint (W64.of_int 672 - pos0) = 672 - 2 * pairs.
    + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
      trivial.
    have hpairslt : pairs < 336.
    + rewrite W64.ultE W64.of_uintK /= in hrem.
      smt().
    have hpos1 :
      W64.to_uint (pos0 + W64.of_int 1) = 2 * pairs + 1.
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hpos.
      trivial.
    have hword :
      W32.to_uint
        ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
         ((zeroextu32
             (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
            (W8.of_int 8))) =
      KeygenUniformXofLeafSpec.uniform_le16 bytes pairs.
    + have hstream :
        KeygenShakeStreamSpec.fips_rate_prefix_matches
          bp{hr} 0 bytes 672.
      + exact hbuflen.
      rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches in hstream.
      have hlo := hstream (2 * pairs) _; first smt().
      have hhi := hstream (2 * pairs + 1) _; first smt().
      rewrite /KeygenUniformXofLeafSpec.uniform_le16.
      rewrite -(hlo) -(hhi).
      exact (le16_word_uint
        (BArray1024.get8 bp{hr} (2 * pairs))
        (BArray1024.get8 bp{hr} (2 * pairs + 1))).
    have hcandidate :
      KeygenUniformXofLeafSpec.uniform_le16 bytes pairs <
        KeygenUniformXofLeafSpec.uniform_q_i.
    + rewrite W32.ultE W32.of_uintK /= in haccept.
      rewrite /KeygenUniformXofLeafSpec.uniform_q_i.
      smt().
    have haccepted :=
      KeygenUniformXofLeafSpec.uniform_accepted_snoc bytes pairs hpairs0.
    rewrite hcandidate /= in haccepted.
    have hctrlt :
      W64.to_uint ctr{hr} <
        KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
              W64.uleE W64.of_uintK /= in hnotfull.
      smt().
    have hdecoded_rcons :
      KeygenUniformXofLeafSpec.decoded_prefix32768
        (BArray32768.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (rcons (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs)
          (KeygenUniformXofLeafSpec.uniform_le16 bytes pairs)).
    + apply (KeygenUniformXofLeafSpec.decoded_prefix32768_set32_word
        ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr}
        (KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) _
        (KeygenUniformXofLeafSpec.uniform_le16 bytes pairs)).
      + trivial.
      + exact hbase.
      + exact hctr.
      + exact hctrlt.
      + exact hdecoded.
      exact hword.
    have hdecoded_next :
      KeygenUniformXofLeafSpec.decoded_prefix32768
        (BArray32768.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
    + rewrite haccepted.
      exact hdecoded_rcons.
    have hbounded_next :
      KeygenUniformXofLeafSpec.bounded_prefix32768
        (BArray32768.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (W64.to_uint (ctr{hr} + W64.one)).
    + apply (KeygenUniformXofLeafSpec.bounded_prefix32768_set32_word
        ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr} _).
      + trivial.
      + exact hbase.
      + exact hctrlt.
      + exact hbounded.
      by rewrite hword.
    have hframe_next :
      KeygenUniformXofLeafSpec.frame32768 ap0
        (BArray32768.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr}).
    + apply (KeygenUniformXofLeafSpec.frame32768_set32_word
        ap0 ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr} _).
      + exact hframe.
      + trivial.
      + exact hbase.
      exact hctrlt.
    have hctrupper_next := uniform_ctr_succ_le ctr{hr} hctrlt.
    have hctrlower_next := uniform_ctr_succ_nonnegative ctr{hr}.
    have hctr_next :
      W64.to_uint (ctr{hr} + W64.one) =
      size (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
    + rewrite (uniform_ctr_succ_uint ctr{hr} hctrlt)
              haccepted size_rcons hctr.
      trivial.
    have hacceptedle_next :
      size (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)) <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite haccepted size_rcons -hctr.
      rewrite -(uniform_ctr_succ_uint ctr{hr} hctrlt).
      exact hctrupper_next.
    have hpairs_next :
      0 <= pairs + 1 <=
        KeygenUniformXofLeafSpec.uniform_first_pairs_i.
    + rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i.
      smt().
    have hpos_next :
      W64.to_uint ((pos0 + W64.one) + W64.one) = 2 * (pairs + 1).
    + rewrite !W64.to_uintD_small 1:/# 1:/# /=.
      smt().
    have hterminal_next :
      live{hr} = W64.of_int 0 =>
      W64.to_uint (ctr{hr} + W64.one) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i \/
      pairs + 1 = KeygenUniformXofLeafSpec.uniform_first_pairs_i.
    + move=> hlive0.
      have hfalse : false.
      + apply hstop.
        exact hlive0.
      by elim hfalse.
    rewrite hpos.
    ring.
    exists (pairs + 1).
    do split; try assumption; try trivial.
    + smt().
    + smt().
    + rewrite /protect_32 hpos hpos1.
      exact hdecoded_next.
    + rewrite /protect_32 hpos hpos1.
      exact hbounded_next.
    + rewrite /protect_32 hpos hpos1.
      exact hframe_next.
  auto => /> &hr pos0 pairs hpairs0 hpairsle hpos hctr
      hacceptedle hdecoded hbounded hframe hbase hcap hbuflen
      hbytelen hprefix hctrle hstop hnotfull hrem
      hrejected.
  have hposle : pos0 \ule W64.of_int 672.
  + rewrite W64.uleE W64.of_uintK /=.
    smt().
  have hremuint :
    W64.to_uint (W64.of_int 672 - pos0) = 672 - 2 * pairs.
  + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
    trivial.
  have hpairslt : pairs < 336.
  + rewrite W64.ultE W64.of_uintK /= in hrem.
    smt().
  have hpos1 :
    W64.to_uint (pos0 + W64.of_int 1) = 2 * pairs + 1.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hpos.
    trivial.
  have hword :
    W32.to_uint
      ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
       ((zeroextu32
           (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
          (W8.of_int 8))) =
    KeygenUniformXofLeafSpec.uniform_le16 bytes pairs.
  + have hstream :
      KeygenShakeStreamSpec.fips_rate_prefix_matches
        bp{hr} 0 bytes 672.
    + exact hbuflen.
    rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches in hstream.
    have hlo := hstream (2 * pairs) _; first smt().
    have hhi := hstream (2 * pairs + 1) _; first smt().
    rewrite /KeygenUniformXofLeafSpec.uniform_le16.
    rewrite -(hlo) -(hhi).
    exact (le16_word_uint
      (BArray1024.get8 bp{hr} (2 * pairs))
      (BArray1024.get8 bp{hr} (2 * pairs + 1))).
  have hcandidate :
    !(KeygenUniformXofLeafSpec.uniform_le16 bytes pairs <
      KeygenUniformXofLeafSpec.uniform_q_i).
  + rewrite W32.ultE W32.of_uintK /= in hrejected.
    rewrite /KeygenUniformXofLeafSpec.uniform_q_i.
    smt().
  have haccepted :=
    KeygenUniformXofLeafSpec.uniform_accepted_snoc bytes pairs hpairs0.
  rewrite hcandidate /= in haccepted.
  have hctr_next :
    W64.to_uint ctr{hr} =
      size (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
  + rewrite haccepted.
    exact hctr.
  have hacceptedle_next :
    size (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)) <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
  + rewrite haccepted.
    exact hacceptedle.
  have hdecoded_next :
    KeygenUniformXofLeafSpec.decoded_prefix32768 ap{hr}
      (W64.to_uint base{hr})
      (KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
  + rewrite haccepted.
    exact hdecoded.
  have hpairs_next :
    0 <= pairs + 1 <=
      KeygenUniformXofLeafSpec.uniform_first_pairs_i.
  + rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i.
    smt().
  have hpos_next :
    W64.to_uint ((pos0 + W64.one) + W64.one) = 2 * (pairs + 1).
  + rewrite !W64.to_uintD_small 1:/# 1:/# /=.
    smt().
  have hterminal_next :
    live{hr} = W64.of_int 0 =>
    W64.to_uint ctr{hr} =
      KeygenUniformXofLeafSpec.uniform_poly_words_i \/
    pairs + 1 = KeygenUniformXofLeafSpec.uniform_first_pairs_i.
  + move=> hlive0.
    have hfalse : false.
    + apply hstop.
      exact hlive0.
    by elim hfalse.
  rewrite hpos.
  ring.
  exists (pairs + 1).
  do split; try assumption; try trivial.
  + smt().
  + smt().
wp.
skip => /> &hr hbase hcap hprefix.
split.
+ exists 0.
  rewrite KeygenUniformXofLeafSpec.uniform_accepted_zero
          /KeygenUniformXofLeafSpec.uniform_first_pairs_i
          /KeygenUniformXofLeafSpec.uniform_poly_words_i.
  have hdecoded0 := KeygenUniformXofLeafSpec.decoded_prefix32768_zero
    ap0 (W64.to_uint base{hr}).
  have hbounded0 := KeygenUniformXofLeafSpec.bounded_prefix32768_zero
    ap0 (W64.to_uint base{hr}).
  have hframe0 := KeygenUniformXofLeafSpec.frame32768_refl
    ap0 (W64.to_uint base{hr}).
  do split; try assumption; try trivial; smt().
+ move=> ap1 ctr0 pos0 pairs hpairs0 hpairsle hpos hctr
      hacceptedle hdecoded hbounded hframe hctrlower hctrupper
      hterminal.
  exists pairs.
  do split.
  + smt().
  + smt().
  + exact hctr.
  + exact hacceptedle.
  + exact hdecoded.
  + exact hterminal.
qed.


lemma consume2048_block168 ap0 bytes values0 base_i :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_consume_2048 :
    ap = ap0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint ctr = size values0 /\
    0 <= W64.to_uint ctr <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    KeygenUniformXofLeafSpec.decoded_prefix8192
      ap base_i values0 /\
    KeygenUniformXofLeafSpec.bounded_prefix8192
      ap base_i (W64.to_uint ctr) /\
    buflen = W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
    size bytes = KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bp 0 bytes KeygenUniformXofLeafSpec.uniform_block_bytes_i
    ==>
    exists pairs,
      0 <= pairs <= KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
      W64.to_uint res.`2 =
        size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
      size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) <=
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      0 <= W64.to_uint res.`2 <=
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      KeygenUniformXofLeafSpec.decoded_prefix8192
        res.`1 base_i
        (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
      KeygenUniformXofLeafSpec.bounded_prefix8192
        res.`1 base_i (W64.to_uint res.`2) /\
      KeygenUniformXofLeafSpec.frame8192 ap0 res.`1 base_i /\
      (W64.to_uint res.`2 =
         KeygenUniformXofLeafSpec.uniform_poly_words_i \/
       pairs = KeygenUniformXofLeafSpec.uniform_block_pairs_i)].
proof.
proc.
while (exists pairs,
         0 <= pairs <=
           KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
         W64.to_uint pos = 2 * pairs /\
         W64.to_uint ctr =
           size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
         size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i /\
         KeygenUniformXofLeafSpec.decoded_prefix8192
           ap base_i
           (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
         KeygenUniformXofLeafSpec.bounded_prefix8192
           ap base_i (W64.to_uint ctr) /\
         KeygenUniformXofLeafSpec.frame8192 ap0 ap base_i /\
         W64.to_uint base = base_i /\
         W64.to_uint base +
           KeygenUniformXofLeafSpec.uniform_poly_words_i <=
           BArray8192.size %/ 4 /\
         buflen = W64.of_int
           KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
         size bytes = KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
         KeygenShakeStreamSpec.fips_rate_prefix_matches
           bp 0 bytes KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
         0 <= W64.to_uint ctr <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i /\
         (live = W64.of_int 0 =>
            W64.to_uint ctr =
              KeygenUniformXofLeafSpec.uniform_poly_words_i \/
            pairs = KeygenUniformXofLeafSpec.uniform_block_pairs_i)).
+ if.
  + auto => /> &hr pairs hpairs0 hpairsle hpos hctr hacceptedle
        hdecoded hbounded hframe hbase hcap hbuflen hbytelen hprefix
        hctrle hstop hfull.
    exists pairs.
    rewrite W64.uleE W64.of_uintK /= in hfull.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /KeygenUniformXofLeafSpec.uniform_block_pairs_i in hprefix.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /KeygenUniformXofLeafSpec.uniform_block_pairs_i in hfull.
    do split; try assumption; smt().
  sp 2.
  if.
  + auto => /> &hr pairs hpairs0 hpairsle hpos hctr hacceptedle
        hdecoded hbounded hframe hbase hcap hbuflen hbytelen hprefix
        hctrle hstop hnotfull hrem.
    have hposle : pos{hr} \ule W64.of_int 168.
    + rewrite W64.uleE W64.of_uintK /=.
      smt().
    have hremuint :
      W64.to_uint (W64.of_int 168 - pos{hr}) = 168 - 2 * pairs.
    + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
      trivial.
    have hpairs336 : pairs = 84.
    + rewrite W64.ultE W64.of_uintK /= in hrem.
      smt().
    smt(W64.to_uint_cmp).
  sp 10.
  if.
  + auto => /> &hr pos0 pairs hpairs0 hpairsle hpos hctr
        hacceptedle hdecoded hbounded hframe hbase hcap hbuflen
        hbytelen hprefix hctrle hstop hnotfull hrem
        haccept.
    have hposle : pos0 \ule W64.of_int 168.
    + rewrite W64.uleE W64.of_uintK /=.
      smt().
    have hremuint :
      W64.to_uint (W64.of_int 168 - pos0) = 168 - 2 * pairs.
    + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
      trivial.
    have hpairslt : pairs < 84.
    + rewrite W64.ultE W64.of_uintK /= in hrem.
      smt().
    have hpos1 :
      W64.to_uint (pos0 + W64.of_int 1) = 2 * pairs + 1.
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hpos.
      trivial.
    have hword :
      W32.to_uint
        ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
         ((zeroextu32
             (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
            (W8.of_int 8))) =
      KeygenUniformXofLeafSpec.uniform_le16 bytes pairs.
    + have hstream :
        KeygenShakeStreamSpec.fips_rate_prefix_matches
          bp{hr} 0 bytes 168.
      + exact hbuflen.
      rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches in hstream.
      have hlo := hstream (2 * pairs) _; first smt().
      have hhi := hstream (2 * pairs + 1) _; first smt().
      rewrite /KeygenUniformXofLeafSpec.uniform_le16.
      rewrite -(hlo) -(hhi).
      exact (le16_word_uint
        (BArray1024.get8 bp{hr} (2 * pairs))
        (BArray1024.get8 bp{hr} (2 * pairs + 1))).
    have hcandidate :
      KeygenUniformXofLeafSpec.uniform_le16 bytes pairs <
        KeygenUniformXofLeafSpec.uniform_q_i.
    + rewrite W32.ultE W32.of_uintK /= in haccept.
      rewrite /KeygenUniformXofLeafSpec.uniform_q_i.
      smt().
    have haccepted :=
      KeygenUniformXofLeafSpec.uniform_accepted_snoc bytes pairs hpairs0.
    rewrite hcandidate /= in haccepted.
    have hctrlt :
      W64.to_uint ctr{hr} <
        KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
              W64.uleE W64.of_uintK /= in hnotfull.
      smt().
    have hdecoded_rcons :
      KeygenUniformXofLeafSpec.decoded_prefix8192
        (BArray8192.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (rcons (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs)
          (KeygenUniformXofLeafSpec.uniform_le16 bytes pairs)).
    + apply (KeygenUniformXofLeafSpec.decoded_prefix8192_set32_word
        ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr}
        (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) _
        (KeygenUniformXofLeafSpec.uniform_le16 bytes pairs)).
      + trivial.
      + exact hbase.
      + exact hctr.
      + exact hctrlt.
      + exact hdecoded.
      exact hword.
    have hdecoded_next :
      KeygenUniformXofLeafSpec.decoded_prefix8192
        (BArray8192.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
    + rewrite haccepted -rcons_cat.
      exact hdecoded_rcons.
    have hbounded_next :
      KeygenUniformXofLeafSpec.bounded_prefix8192
        (BArray8192.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (W64.to_uint (ctr{hr} + W64.one)).
    + apply (KeygenUniformXofLeafSpec.bounded_prefix8192_set32_word
        ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr} _).
      + trivial.
      + exact hbase.
      + exact hctrlt.
      + exact hbounded.
      by rewrite hword.
    have hframe_next :
      KeygenUniformXofLeafSpec.frame8192 ap0
        (BArray8192.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr}).
    + apply (KeygenUniformXofLeafSpec.frame8192_set32_word
        ap0 ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr} _).
      + exact hframe.
      + trivial.
      + exact hbase.
      exact hctrlt.
    have hctrupper_next := uniform_ctr_succ_le ctr{hr} hctrlt.
    have hctrlower_next := uniform_ctr_succ_nonnegative ctr{hr}.
    have hctr_next :
      W64.to_uint (ctr{hr} + W64.one) =
      size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
    + rewrite (uniform_ctr_succ_uint ctr{hr} hctrlt)
              haccepted -rcons_cat size_rcons hctr.
      trivial.
    have hacceptedle_next :
      size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)) <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite haccepted -rcons_cat size_rcons -hctr.
      rewrite -(uniform_ctr_succ_uint ctr{hr} hctrlt).
      exact hctrupper_next.
    have hpairs_next :
      0 <= pairs + 1 <=
        KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
      smt().
    have hpos_next :
      W64.to_uint ((pos0 + W64.one) + W64.one) = 2 * (pairs + 1).
    + rewrite !W64.to_uintD_small 1:/# 1:/# /=.
      smt().
    have hterminal_next :
      live{hr} = W64.of_int 0 =>
      W64.to_uint (ctr{hr} + W64.one) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i \/
      pairs + 1 = KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    + move=> hlive0.
      have hfalse : false.
      + apply hstop.
        exact hlive0.
      by elim hfalse.
    rewrite hpos.
    ring.
    exists (pairs + 1).
    do split; try assumption; try trivial.
    + smt().
    + smt().
    + rewrite /protect_32 hpos hpos1.
      exact hdecoded_next.
    + rewrite /protect_32 hpos hpos1.
      exact hbounded_next.
    + rewrite /protect_32 hpos hpos1.
      exact hframe_next.
  auto => /> &hr pos0 pairs hpairs0 hpairsle hpos hctr
      hacceptedle hdecoded hbounded hframe hbase hcap hbuflen
      hbytelen hprefix hctrle hstop hnotfull hrem
      hrejected.
  have hposle : pos0 \ule W64.of_int 168.
  + rewrite W64.uleE W64.of_uintK /=.
    smt().
  have hremuint :
    W64.to_uint (W64.of_int 168 - pos0) = 168 - 2 * pairs.
  + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
    trivial.
  have hpairslt : pairs < 84.
  + rewrite W64.ultE W64.of_uintK /= in hrem.
    smt().
  have hpos1 :
    W64.to_uint (pos0 + W64.of_int 1) = 2 * pairs + 1.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hpos.
    trivial.
  have hword :
    W32.to_uint
      ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
       ((zeroextu32
           (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
          (W8.of_int 8))) =
    KeygenUniformXofLeafSpec.uniform_le16 bytes pairs.
  + have hstream :
      KeygenShakeStreamSpec.fips_rate_prefix_matches
        bp{hr} 0 bytes 168.
    + exact hbuflen.
    rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches in hstream.
    have hlo := hstream (2 * pairs) _; first smt().
    have hhi := hstream (2 * pairs + 1) _; first smt().
    rewrite /KeygenUniformXofLeafSpec.uniform_le16.
    rewrite -(hlo) -(hhi).
    exact (le16_word_uint
      (BArray1024.get8 bp{hr} (2 * pairs))
      (BArray1024.get8 bp{hr} (2 * pairs + 1))).
  have hcandidate :
    !(KeygenUniformXofLeafSpec.uniform_le16 bytes pairs <
      KeygenUniformXofLeafSpec.uniform_q_i).
  + rewrite W32.ultE W32.of_uintK /= in hrejected.
    rewrite /KeygenUniformXofLeafSpec.uniform_q_i.
    smt().
  have haccepted :=
    KeygenUniformXofLeafSpec.uniform_accepted_snoc bytes pairs hpairs0.
  rewrite hcandidate /= in haccepted.
  have hctr_next :
    W64.to_uint ctr{hr} =
      size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
  + rewrite haccepted.
    exact hctr.
  have hacceptedle_next :
    size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)) <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
  + rewrite haccepted.
    exact hacceptedle.
  have hdecoded_next :
    KeygenUniformXofLeafSpec.decoded_prefix8192 ap{hr}
      (W64.to_uint base{hr})
      (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
  + rewrite haccepted.
    exact hdecoded.
  have hpairs_next :
    0 <= pairs + 1 <=
      KeygenUniformXofLeafSpec.uniform_block_pairs_i.
  + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    smt().
  have hpos_next :
    W64.to_uint ((pos0 + W64.one) + W64.one) = 2 * (pairs + 1).
  + rewrite !W64.to_uintD_small 1:/# 1:/# /=.
    smt().
  have hterminal_next :
    live{hr} = W64.of_int 0 =>
    W64.to_uint ctr{hr} =
      KeygenUniformXofLeafSpec.uniform_poly_words_i \/
    pairs + 1 = KeygenUniformXofLeafSpec.uniform_block_pairs_i.
  + move=> hlive0.
    have hfalse : false.
    + apply hstop.
      exact hlive0.
    by elim hfalse.
  rewrite hpos.
  ring.
  exists (pairs + 1).
  do split; try assumption; try trivial.
  + smt().
  + smt().
wp.
skip => /> &hr hbase hcap hctr0 hctrle hdecoded0 hbounded0 hprefix.
move=> hstream.
split.
+ exists 0.
  rewrite KeygenUniformXofLeafSpec.uniform_accepted_zero
          cats0
          /KeygenUniformXofLeafSpec.uniform_block_pairs_i
          /KeygenUniformXofLeafSpec.uniform_poly_words_i.
  have hframe0 := KeygenUniformXofLeafSpec.frame8192_refl
    ap0 (W64.to_uint base{hr}).
  do split; try assumption; try trivial; smt().
+ move=> ap1 ctr0 pos0 pairs hpairs0 hpairsle hpos hctr
      hacceptedle hdecoded hbounded hframe hctrlower hctrupper
      hterminal.
  exists pairs.
  do split.
  + smt().
  + smt().
  + exact hctr.
  + exact hacceptedle.
  + exact hdecoded.
  + exact hterminal.
qed.



lemma consume8192_block168 ap0 bytes values0 base_i :
  hoare [KeygenSamplerCallersTarget.M.__poly_uniform_consume :
    ap = ap0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    W64.to_uint ctr = size values0 /\
    0 <= W64.to_uint ctr <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    KeygenUniformXofLeafSpec.decoded_prefix32768
      ap base_i values0 /\
    KeygenUniformXofLeafSpec.bounded_prefix32768
      ap base_i (W64.to_uint ctr) /\
    buflen = W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
    size bytes = KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bp 0 bytes KeygenUniformXofLeafSpec.uniform_block_bytes_i
    ==>
    exists pairs,
      0 <= pairs <= KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
      W64.to_uint res.`2 =
        size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
      size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) <=
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      0 <= W64.to_uint res.`2 <=
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      KeygenUniformXofLeafSpec.decoded_prefix32768
        res.`1 base_i
        (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
      KeygenUniformXofLeafSpec.bounded_prefix32768
        res.`1 base_i (W64.to_uint res.`2) /\
      KeygenUniformXofLeafSpec.frame32768 ap0 res.`1 base_i /\
      (W64.to_uint res.`2 =
         KeygenUniformXofLeafSpec.uniform_poly_words_i \/
       pairs = KeygenUniformXofLeafSpec.uniform_block_pairs_i)].
proof.
proc.
while (exists pairs,
         0 <= pairs <=
           KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
         W64.to_uint pos = 2 * pairs /\
         W64.to_uint ctr =
           size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
         size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i /\
         KeygenUniformXofLeafSpec.decoded_prefix32768
           ap base_i
           (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) /\
         KeygenUniformXofLeafSpec.bounded_prefix32768
           ap base_i (W64.to_uint ctr) /\
         KeygenUniformXofLeafSpec.frame32768 ap0 ap base_i /\
         W64.to_uint base = base_i /\
         W64.to_uint base +
           KeygenUniformXofLeafSpec.uniform_poly_words_i <=
           BArray32768.size %/ 4 /\
         buflen = W64.of_int
           KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
         size bytes = KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
         KeygenShakeStreamSpec.fips_rate_prefix_matches
           bp 0 bytes KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
         0 <= W64.to_uint ctr <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i /\
         (live = W64.of_int 0 =>
            W64.to_uint ctr =
              KeygenUniformXofLeafSpec.uniform_poly_words_i \/
            pairs = KeygenUniformXofLeafSpec.uniform_block_pairs_i)).
+ if.
  + auto => /> &hr pairs hpairs0 hpairsle hpos hctr hacceptedle
        hdecoded hbounded hframe hbase hcap hbuflen hbytelen hprefix
        hctrle hstop hfull.
    exists pairs.
    rewrite W64.uleE W64.of_uintK /= in hfull.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /KeygenUniformXofLeafSpec.uniform_block_pairs_i in hprefix.
    rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
            /KeygenUniformXofLeafSpec.uniform_block_pairs_i in hfull.
    do split; try assumption; smt().
  sp 2.
  if.
  + auto => /> &hr pairs hpairs0 hpairsle hpos hctr hacceptedle
        hdecoded hbounded hframe hbase hcap hbuflen hbytelen hprefix
        hctrle hstop hnotfull hrem.
    have hposle : pos{hr} \ule W64.of_int 168.
    + rewrite W64.uleE W64.of_uintK /=.
      smt().
    have hremuint :
      W64.to_uint (W64.of_int 168 - pos{hr}) = 168 - 2 * pairs.
    + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
      trivial.
    have hpairs336 : pairs = 84.
    + rewrite W64.ultE W64.of_uintK /= in hrem.
      smt().
    smt(W64.to_uint_cmp).
  sp 11.
  if.
  + auto => /> &hr pos0 pairs hpairs0 hpairsle hpos hctr
        hacceptedle hdecoded hbounded hframe hbase hcap hbuflen
        hbytelen hprefix hctrle hstop hnotfull hrem
        haccept.
    have hposle : pos0 \ule W64.of_int 168.
    + rewrite W64.uleE W64.of_uintK /=.
      smt().
    have hremuint :
      W64.to_uint (W64.of_int 168 - pos0) = 168 - 2 * pairs.
    + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
      trivial.
    have hpairslt : pairs < 84.
    + rewrite W64.ultE W64.of_uintK /= in hrem.
      smt().
    have hpos1 :
      W64.to_uint (pos0 + W64.of_int 1) = 2 * pairs + 1.
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hpos.
      trivial.
    have hword :
      W32.to_uint
        ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
         ((zeroextu32
             (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
            (W8.of_int 8))) =
      KeygenUniformXofLeafSpec.uniform_le16 bytes pairs.
    + have hstream :
        KeygenShakeStreamSpec.fips_rate_prefix_matches
          bp{hr} 0 bytes 168.
      + exact hbuflen.
      rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches in hstream.
      have hlo := hstream (2 * pairs) _; first smt().
      have hhi := hstream (2 * pairs + 1) _; first smt().
      rewrite /KeygenUniformXofLeafSpec.uniform_le16.
      rewrite -(hlo) -(hhi).
      exact (le16_word_uint
        (BArray1024.get8 bp{hr} (2 * pairs))
        (BArray1024.get8 bp{hr} (2 * pairs + 1))).
    have hcandidate :
      KeygenUniformXofLeafSpec.uniform_le16 bytes pairs <
        KeygenUniformXofLeafSpec.uniform_q_i.
    + rewrite W32.ultE W32.of_uintK /= in haccept.
      rewrite /KeygenUniformXofLeafSpec.uniform_q_i.
      smt().
    have haccepted :=
      KeygenUniformXofLeafSpec.uniform_accepted_snoc bytes pairs hpairs0.
    rewrite hcandidate /= in haccepted.
    have hctrlt :
      W64.to_uint ctr{hr} <
        KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
              W64.uleE W64.of_uintK /= in hnotfull.
      smt().
    have hdecoded_rcons :
      KeygenUniformXofLeafSpec.decoded_prefix32768
        (BArray32768.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (rcons (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs)
          (KeygenUniformXofLeafSpec.uniform_le16 bytes pairs)).
    + apply (KeygenUniformXofLeafSpec.decoded_prefix32768_set32_word
        ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr}
        (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes pairs) _
        (KeygenUniformXofLeafSpec.uniform_le16 bytes pairs)).
      + trivial.
      + exact hbase.
      + exact hctr.
      + exact hctrlt.
      + exact hdecoded.
      exact hword.
    have hdecoded_next :
      KeygenUniformXofLeafSpec.decoded_prefix32768
        (BArray32768.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
    + rewrite haccepted -rcons_cat.
      exact hdecoded_rcons.
    have hbounded_next :
      KeygenUniformXofLeafSpec.bounded_prefix32768
        (BArray32768.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr})
        (W64.to_uint (ctr{hr} + W64.one)).
    + apply (KeygenUniformXofLeafSpec.bounded_prefix32768_set32_word
        ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr} _).
      + trivial.
      + exact hbase.
      + exact hctrlt.
      + exact hbounded.
      by rewrite hword.
    have hframe_next :
      KeygenUniformXofLeafSpec.frame32768 ap0
        (BArray32768.set32 ap{hr}
          (W64.to_uint (base{hr} + ctr{hr}))
          ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
           ((zeroextu32
               (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
              (W8.of_int 8))))
        (W64.to_uint base{hr}).
    + apply (KeygenUniformXofLeafSpec.frame32768_set32_word
        ap0 ap{hr} (W64.to_uint base{hr}) base{hr} ctr{hr} _).
      + exact hframe.
      + trivial.
      + exact hbase.
      exact hctrlt.
    have hctrupper_next := uniform_ctr_succ_le ctr{hr} hctrlt.
    have hctrlower_next := uniform_ctr_succ_nonnegative ctr{hr}.
    have hctr_next :
      W64.to_uint (ctr{hr} + W64.one) =
      size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
    + rewrite (uniform_ctr_succ_uint ctr{hr} hctrlt)
              haccepted -rcons_cat size_rcons hctr.
      trivial.
    have hacceptedle_next :
      size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)) <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite haccepted -rcons_cat size_rcons -hctr.
      rewrite -(uniform_ctr_succ_uint ctr{hr} hctrlt).
      exact hctrupper_next.
    have hpairs_next :
      0 <= pairs + 1 <=
        KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
      smt().
    have hpos_next :
      W64.to_uint ((pos0 + W64.one) + W64.one) = 2 * (pairs + 1).
    + rewrite !W64.to_uintD_small 1:/# 1:/# /=.
      smt().
    have hterminal_next :
      live{hr} = W64.of_int 0 =>
      W64.to_uint (ctr{hr} + W64.one) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i \/
      pairs + 1 = KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    + move=> hlive0.
      have hfalse : false.
      + apply hstop.
        exact hlive0.
      by elim hfalse.
    rewrite hpos.
    ring.
    exists (pairs + 1).
    do split; try assumption; try trivial.
    + smt().
    + smt().
    + rewrite /protect_32 hpos hpos1.
      exact hdecoded_next.
    + rewrite /protect_32 hpos hpos1.
      exact hbounded_next.
    + rewrite /protect_32 hpos hpos1.
      exact hframe_next.
  auto => /> &hr pos0 pairs hpairs0 hpairsle hpos hctr
      hacceptedle hdecoded hbounded hframe hbase hcap hbuflen
      hbytelen hprefix hctrle hstop hnotfull hrem
      hrejected.
  have hposle : pos0 \ule W64.of_int 168.
  + rewrite W64.uleE W64.of_uintK /=.
    smt().
  have hremuint :
    W64.to_uint (W64.of_int 168 - pos0) = 168 - 2 * pairs.
  + rewrite W64.to_uintB 1:hposle W64.of_uintK /= hpos.
    trivial.
  have hpairslt : pairs < 84.
  + rewrite W64.ultE W64.of_uintK /= in hrem.
    smt().
  have hpos1 :
    W64.to_uint (pos0 + W64.of_int 1) = 2 * pairs + 1.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hpos.
    trivial.
  have hword :
    W32.to_uint
      ((zeroextu32 (BArray1024.get8 bp{hr} (2 * pairs))) `|`
       ((zeroextu32
           (BArray1024.get8 bp{hr} (2 * pairs + 1))) `<<`
          (W8.of_int 8))) =
    KeygenUniformXofLeafSpec.uniform_le16 bytes pairs.
  + have hstream :
      KeygenShakeStreamSpec.fips_rate_prefix_matches
        bp{hr} 0 bytes 168.
    + exact hbuflen.
    rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches in hstream.
    have hlo := hstream (2 * pairs) _; first smt().
    have hhi := hstream (2 * pairs + 1) _; first smt().
    rewrite /KeygenUniformXofLeafSpec.uniform_le16.
    rewrite -(hlo) -(hhi).
    exact (le16_word_uint
      (BArray1024.get8 bp{hr} (2 * pairs))
      (BArray1024.get8 bp{hr} (2 * pairs + 1))).
  have hcandidate :
    !(KeygenUniformXofLeafSpec.uniform_le16 bytes pairs <
      KeygenUniformXofLeafSpec.uniform_q_i).
  + rewrite W32.ultE W32.of_uintK /= in hrejected.
    rewrite /KeygenUniformXofLeafSpec.uniform_q_i.
    smt().
  have haccepted :=
    KeygenUniformXofLeafSpec.uniform_accepted_snoc bytes pairs hpairs0.
  rewrite hcandidate /= in haccepted.
  have hctr_next :
    W64.to_uint ctr{hr} =
      size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
  + rewrite haccepted.
    exact hctr.
  have hacceptedle_next :
    size (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)) <=
      KeygenUniformXofLeafSpec.uniform_poly_words_i.
  + rewrite haccepted.
    exact hacceptedle.
  have hdecoded_next :
    KeygenUniformXofLeafSpec.decoded_prefix32768 ap{hr}
      (W64.to_uint base{hr})
      (values0 ++ KeygenUniformXofLeafSpec.uniform_accepted bytes (pairs + 1)).
  + rewrite haccepted.
    exact hdecoded.
  have hpairs_next :
    0 <= pairs + 1 <=
      KeygenUniformXofLeafSpec.uniform_block_pairs_i.
  + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    smt().
  have hpos_next :
    W64.to_uint ((pos0 + W64.one) + W64.one) = 2 * (pairs + 1).
  + rewrite !W64.to_uintD_small 1:/# 1:/# /=.
    smt().
  have hterminal_next :
    live{hr} = W64.of_int 0 =>
    W64.to_uint ctr{hr} =
      KeygenUniformXofLeafSpec.uniform_poly_words_i \/
    pairs + 1 = KeygenUniformXofLeafSpec.uniform_block_pairs_i.
  + move=> hlive0.
    have hfalse : false.
    + apply hstop.
      exact hlive0.
    by elim hfalse.
  rewrite hpos.
  ring.
  exists (pairs + 1).
  do split; try assumption; try trivial.
  + smt().
  + smt().
wp.
skip => /> &hr hbase hcap hctr0 hctrle hdecoded0 hbounded0 hprefix.
move=> hstream.
split.
+ exists 0.
  rewrite KeygenUniformXofLeafSpec.uniform_accepted_zero
          cats0
          /KeygenUniformXofLeafSpec.uniform_block_pairs_i
          /KeygenUniformXofLeafSpec.uniform_poly_words_i.
  have hframe0 := KeygenUniformXofLeafSpec.frame32768_refl
    ap0 (W64.to_uint base{hr}).
  do split; try assumption; try trivial; smt().
+ move=> ap1 ctr0 pos0 pairs hpairs0 hpairsle hpos hctr
      hacceptedle hdecoded hbounded hframe hctrlower hctrupper
      hterminal.
  exists pairs.
  do split.
  + smt().
  + smt().
  + exact hctr.
  + exact hacceptedle.
  + exact hdecoded.
  + exact hterminal.
qed.



(* The generated consumers are bounded independently of acceptance.  The
   variant charges one unit for the explicit live-stop transition and two for
   every remaining byte pair. *)
lemma uniform_consume2048_ll :
  islossless KeygenSamplerCallersTarget.M.__kp_poly_uniform_consume_2048.
proof.
proc.
while (W64.to_uint pos <= W64.to_uint buflen)
      (if live = W64.zero then 0
       else 2 * (W64.to_uint buflen - W64.to_uint pos) + 1).
+ move=> z.
  if.
  + auto => /> &hr hpos hguard hfull.
    smt().
  sp 2.
  if.
  + auto => /> &hr hpos hguard hnotfull hrem.
    smt().
  sp 10.
  if.
  + auto => /> &hr pos0 hpos hguard hnotfull hrem haccept.
    have hposle : pos0 \ule buflen{hr}.
    + by rewrite W64.uleE.
    have hroom : W64.to_uint pos0 + 2 <= W64.to_uint buflen{hr}.
    + move: hrem.
      rewrite W64.ultE W64.of_uintK /=
              W64.to_uintB 1:hposle.
      smt().
    rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    smt().
  auto => /> &hr pos0 hpos hguard hnotfull hrem hrejected.
  have hposle : pos0 \ule buflen{hr}.
  + by rewrite W64.uleE.
  have hroom : W64.to_uint pos0 + 2 <= W64.to_uint buflen{hr}.
  + move: hrem.
    rewrite W64.ultE W64.of_uintK /=
            W64.to_uintB 1:hposle.
    smt().
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  smt().
auto => />; smt().
qed.

lemma uniform_consume8192_ll :
  islossless KeygenSamplerCallersTarget.M.__poly_uniform_consume.
proof.
proc.
while (W64.to_uint pos <= W64.to_uint buflen)
      (if live = W64.zero then 0
       else 2 * (W64.to_uint buflen - W64.to_uint pos) + 1).
+ move=> z.
  if.
  + auto => /> &hr hpos hguard hfull.
    smt().
  sp 2.
  if.
  + auto => /> &hr hpos hguard hnotfull hrem.
    smt().
  sp 11.
  if.
  + auto => /> &hr pos0 hpos hguard hnotfull hrem haccept.
    have hposle : pos0 \ule buflen{hr}.
    + by rewrite W64.uleE.
    have hroom : W64.to_uint pos0 + 2 <= W64.to_uint buflen{hr}.
    + move: hrem.
      rewrite W64.ultE W64.of_uintK /=
              W64.to_uintB 1:hposle.
      smt().
    rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    smt().
  auto => /> &hr pos0 hpos hguard hnotfull hrem hrejected.
  have hposle : pos0 \ule buflen{hr}.
  + by rewrite W64.uleE.
  have hroom : W64.to_uint pos0 + 2 <= W64.to_uint buflen{hr}.
  + move: hrem.
    rewrite W64.ultE W64.of_uintK /=
            W64.to_uintB 1:hposle.
    smt().
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  smt().
auto => />; smt().
qed.

lemma uniform2048_leaf_stream
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4
    ==>
    KeygenUniformXofLeafSpec.bounded_prefix8192
      res base_i KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    (W64.to_uint seedoff0 + 32 <= BArray128.size =>
      exists blocks pairs,
        4 <= blocks /\
        0 <= pairs <=
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
        size (KeygenUniformXofLeafSpec.uniform_accepted
          (KeygenShakeStreamSpec.shake128_squeeze_bytes
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks) pairs) =
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        KeygenUniformXofLeafSpec.decoded_prefix8192
          res base_i
          (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs))].
proof.
proc.
seq 17 :
  (KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
   W64.to_uint base = base_i /\
   base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
     BArray8192.size %/ 4 /\
   seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
   off = W64.of_int 504 /\
   ctr = W64.of_int 0 /\
   buflen = W64.of_int 672 /\
   (W64.to_uint seedoff0 + 32 <= BArray128.size =>
      KeygenShakeStreamSpec.state_bytes_le sp_0 =
        KeygenShakeStreamSpec.squeeze_state_iter
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) 4 /\
      KeygenShakeStreamSpec.squeeze_blocks_matches
        bufp 0
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 168 4 /\
      KeygenShakeStreamSpec.fips_rate_prefix_matches
        bufp 0
        (KeygenShakeStreamSpec.shake128_squeeze_bytes
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) 4) 672 /\
      KeygenShakeStreamSpec.squeeze_region_frame
        buf bufp 0 168 4)).
+ case (W64.to_uint seedoff0 + 32 <= BArray128.size).
  + seq 6 :
      (KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 0 /\
       sp_0 = state /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size).
    + by auto => />; rewrite /KeygenShakeStreamSpec.squeeze_region_frame.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 0 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 0 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 0 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 0).
    + wp.
      call (TargetKeygenShakeStream.shake128_init_seedbuf_padded_state
        seed0 seedoff0 nonce0).
      + auto => /> &hr hregion0 hleafcap hseedcap result.
        move=> hstate.
        do split.
        + by rewrite KeygenShakeStreamSpec.squeeze_state_iter0.
        + exact (KeygenShakeStreamSpec.squeeze_blocks_matches0
            bufp{hr} 0
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) 168).
        + trivial.
      + by auto => />; smt().
    seq 1 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 1 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 1 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 1 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 0).
    + exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 0) before_state).
      auto => /> &hr hstate hmatches hregion0 hprefix hbase hcap hseedcap0
        result hblock hframe hperm.
      have [hstate1 [hmatches1 hregion1]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 0
          _ hstate hmatches hregion0 hblock hframe hperm.
      + smt().
      do split.
      + exact hstate1.
      + exact hmatches1.
      exact hregion1.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 2 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 2 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 2 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 168).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 168) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap hseedcap0
        result hblock hframe hperm.
      have [hstate2 [hmatches2 hregion2]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 1
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      do split.
      + exact hstate2.
      + exact hmatches2.
      exact hregion2.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 3 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 3 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 3 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 336).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 336) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap hseedcap0
        result hblock hframe hperm.
      have [hstate3 [hmatches3 hregion3]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 2
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      do split.
      + exact hstate3.
      + exact hmatches3.
      exact hregion3.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 4 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 4 /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 4) 672 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 4 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 504).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 504) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap hseedcap0
        result hblock hframe hperm.
      have [hstate4 [hmatches4 hregion4]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 3
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      have hflat :=
        KeygenShakeStreamSpec.shake128_squeeze_blocks_fips
          result.`1 0
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) 4 _ hmatches4.
      + smt().
      do split.
      + exact hstate4.
      + exact hmatches4.
      + by rewrite /= in hflat.
      exact hregion4.
    by auto.
  do 5! (wp; call (_ : true); first by auto).
  auto => /> &hr hbase hcap.
  exact (KeygenUniformXofLeafSpec.bounded_prefix8192_zero
    ap{hr} (W64.to_uint base{hr})).
exlim ap => before_ap.
seq 1 :
  (KeygenUniformXofLeafSpec.bounded_prefix8192
     ap base_i (W64.to_uint ctr) /\
   W64.to_uint base = base_i /\
   base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
     BArray8192.size %/ 4 /\
   0 <= W64.to_uint ctr <=
     KeygenUniformXofLeafSpec.uniform_poly_words_i /\
   (W64.to_uint seedoff0 + 32 <= BArray128.size =>
      exists blocks pairs,
        4 <= blocks /\
        0 <= pairs <=
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
        KeygenShakeStreamSpec.state_bytes_le sp_0 =
          KeygenShakeStreamSpec.squeeze_state_iter
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks /\
        (buflen = W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
         buflen = W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
        W64.to_uint ctr =
          size (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs) /\
        size (KeygenUniformXofLeafSpec.uniform_accepted
          (KeygenShakeStreamSpec.shake128_squeeze_bytes
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks) pairs) <=
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        0 <= W64.to_uint ctr <=
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        KeygenUniformXofLeafSpec.decoded_prefix8192
          ap base_i
          (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs) /\
        KeygenUniformXofLeafSpec.bounded_prefix8192
          ap base_i (W64.to_uint ctr) /\
        KeygenUniformXofLeafSpec.frame8192
          before_ap ap base_i /\
        (W64.to_uint ctr =
           KeygenUniformXofLeafSpec.uniform_poly_words_i \/
         pairs =
           blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))).
+ have hbytes :
    size (KeygenShakeStreamSpec.shake128_squeeze_bytes
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 4) =
      KeygenUniformXofLeafSpec.uniform_first_bytes_i.
  + exact (shake128_first_bytes_size
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0)).
  case (W64.to_uint seedoff0 + 32 <= BArray128.size).
  + call (consume2048_first672 before_ap
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 4) base_i).
    + auto => />.
      move=> &hr hbounded0 hcap hstream hseedcap.
      have [hstate [_ [hprefix _]]] := hstream hseedcap.
      split.
      + rewrite /KeygenUniformXofLeafSpec.uniform_first_bytes_i.
        exact hprefix.
      move=> _ _ _ result pairs hpairs0 hpairsle hctr hacceptedle
        _ _ hdecoded _ _ hterminal.
      exists 4.
      exists pairs.
      do split.
      + trivial.
      + rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i
                in hpairsle.
        rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
        smt().
      + exact hstate.
      + exact hctr.
      + exact hacceptedle.
      + exact hdecoded.
      move: hterminal.
      rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i
              /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
      smt().
    + auto => />.
  + call (consume2048_range base_i).
    auto => />.

while (KeygenUniformXofLeafSpec.bounded_prefix8192
         ap base_i (W64.to_uint ctr) /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i /\
       (W64.to_uint seedoff0 + 32 <= BArray128.size =>
         exists blocks pairs,
           4 <= blocks /\
           0 <= pairs <=
             blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
           KeygenShakeStreamSpec.state_bytes_le sp_0 =
             KeygenShakeStreamSpec.squeeze_state_iter
               (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                 seed0 seedoff0 nonce0) blocks /\
           (buflen =
              W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
            buflen =
              W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
           W64.to_uint ctr =
             size (KeygenUniformXofLeafSpec.uniform_accepted
               (KeygenShakeStreamSpec.shake128_squeeze_bytes
                 (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                   seed0 seedoff0 nonce0) blocks) pairs) /\
           size (KeygenUniformXofLeafSpec.uniform_accepted
             (KeygenShakeStreamSpec.shake128_squeeze_bytes
               (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                 seed0 seedoff0 nonce0) blocks) pairs) <=
             KeygenUniformXofLeafSpec.uniform_poly_words_i /\
           0 <= W64.to_uint ctr <=
             KeygenUniformXofLeafSpec.uniform_poly_words_i /\
           KeygenUniformXofLeafSpec.decoded_prefix8192
             ap base_i
             (KeygenUniformXofLeafSpec.uniform_accepted
               (KeygenShakeStreamSpec.shake128_squeeze_bytes
                 (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                   seed0 seedoff0 nonce0) blocks) pairs) /\
           KeygenUniformXofLeafSpec.bounded_prefix8192
             ap base_i (W64.to_uint ctr) /\
           KeygenUniformXofLeafSpec.frame8192 before_ap ap base_i /\
           (W64.to_uint ctr =
              KeygenUniformXofLeafSpec.uniform_poly_words_i \/
            pairs =
              blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))).
+ case (W64.to_uint seedoff0 + 32 <= BArray128.size).
  + conseq (_ :
      (exists blocks pairs,
        KeygenUniformXofLeafSpec.bounded_prefix8192
          ap base_i (W64.to_uint ctr) /\
        W64.to_uint base = base_i /\
        base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
          BArray8192.size %/ 4 /\
        0 <= W64.to_uint ctr <=
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        4 <= blocks /\
        0 <= pairs <=
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
        KeygenShakeStreamSpec.state_bytes_le sp_0 =
          KeygenShakeStreamSpec.squeeze_state_iter
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks /\
        (buflen =
           W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
         buflen =
           W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
        W64.to_uint ctr =
          size (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs) /\
        size (KeygenUniformXofLeafSpec.uniform_accepted
          (KeygenShakeStreamSpec.shake128_squeeze_bytes
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks) pairs) <=
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        KeygenUniformXofLeafSpec.decoded_prefix8192
          ap base_i
          (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs) /\
        KeygenUniformXofLeafSpec.frame8192 before_ap ap base_i /\
        (W64.to_uint ctr =
           KeygenUniformXofLeafSpec.uniform_poly_words_i \/
         pairs =
           blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i) /\
        ctr \ult W64.of_int KeygenUniformXofLeafSpec.uniform_poly_words_i)
      ==> _).
    + auto => />.
      move=> &hr _ _ _ _ hstream hguard hseedcap.
      have [blocks pairs hsemantic] := hstream hseedcap.
      exists blocks.
      exists pairs.
      by move: hsemantic; auto.
    elim* => blocks pairs.
    exlim ap => iteration_ap.
    sp 3.
    rcondf 1.
    + auto => /> &hr _ _ _ _ _ _ _ _ hbuflen.
      have hoff := uniform_even_buflen_and1_zero buflen{hr} hbuflen.
      by rewrite W64.ultE hoff W64.of_uintK /=.
    seq 9 :
      (ap = iteration_ap /\
       KeygenUniformXofLeafSpec.bounded_prefix8192
         ap base_i (W64.to_uint ctr) /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i /\
       4 <= blocks /\
       pairs =
         blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
       KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) (blocks + 1) /\
       buflen =
         W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
       W64.to_uint ctr =
         size (KeygenUniformXofLeafSpec.uniform_accepted
           (KeygenShakeStreamSpec.shake128_squeeze_bytes
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks)
           (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i)) /\
       size (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)
         (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i)) <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i /\
       KeygenUniformXofLeafSpec.decoded_prefix8192
         ap base_i
         (KeygenUniformXofLeafSpec.uniform_accepted
           (KeygenShakeStreamSpec.shake128_squeeze_bytes
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks)
           (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i)) /\
       KeygenUniformXofLeafSpec.frame8192 before_ap ap base_i /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_squeeze_block
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)
         KeygenUniformXofLeafSpec.uniform_block_bytes_i).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 0) before_state).
      auto => />.
      move=> &hr hbounded hcap hctr0 hctrle hblocks hpairs0 hpairsle
        hstate hbuflen hctr hacceptedle hdecoded hframe hterminal
        hguard.
      have hctrlt :
        W64.to_uint ctr{hr} <
          KeygenUniformXofLeafSpec.uniform_poly_words_i.
      + rewrite W64.ultE W64.of_uintK
                /KeygenUniformXofLeafSpec.uniform_poly_words_i
                /= in hguard.
        exact hguard.
      have hoff :=
        uniform_even_buflen_and1_zero buflen{hr} hbuflen.
      split.
      + exact hoff.
      move=> _ _ result hblock _ hperm.
      have [hstate_next hprefix] :=
        shake128_squeeze_overwrite_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          before_state result.`2 result.`1 blocks
          _ hstate _ hperm.
      + smt().
      + rewrite /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
        exact hblock.
      rewrite /protect_64 /protect_ptr hoff
              /KeygenUniformXofLeafSpec.uniform_block_bytes_i /=.
      do split.
      + smt().
      + exact hstate_next.
      + trivial.
      + have <- :
          pairs =
            blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i by smt().
        exact hctr.
      + have <- :
          pairs =
            blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i by smt().
        exact hacceptedle.
      + have <- :
          pairs =
            blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i by smt().
        exact hdecoded.
      + exact hprefix.
    + wp.
      call (consume2048_block168 iteration_ap
        (KeygenShakeStreamSpec.shake128_squeeze_block
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) blocks)
        (KeygenUniformXofLeafSpec.uniform_accepted
          (KeygenShakeStreamSpec.shake128_squeeze_bytes
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks)
          (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))
        base_i).
      + auto => />.
        move=> &hr hbounded hcap hctr0 hctrle hblocks hstate hctr
          hacceptedle hdecoded hframe hprefix.
        split.
        + by rewrite
            KeygenShakeStreamSpec.shake128_squeeze_block_size
            /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
        move=> _ result fresh_pairs hfresh0 hfreshle hresultctr
          hresultsize hresultctr0 hresultctrle hresultdecoded
          hresultbounded hresultframe hterminal _.
        have hcat :=
          uniform_accepted_shake128_succ
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0)
            blocks fresh_pairs _ hfresh0.
        + smt().
        have hframe_next :=
          KeygenUniformXofLeafSpec.frame8192_trans
            before_ap iteration_ap result.`1 (W64.to_uint base{hr})
            hframe hresultframe.
        rewrite /protect_64 /protect_ptr.
        exists (blocks + 1).
        exists (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i +
          fresh_pairs).
        do split.
        + smt().
        + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
          smt().
        + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
          smt().
        + exact hstate.
        + rewrite hcat.
          exact hresultctr.
        + rewrite hcat.
          exact hresultsize.
        + smt().
        + smt().
        + rewrite hcat.
          exact hresultdecoded.
        + exact hresultbounded.
        + exact hframe_next.
        case hterminal => [hfull | hfreshfull].
        + by left.
        right.
        rewrite hfreshfull.
        ring.
  + wp.
    call (consume2048_range base_i).
    wp.
    call (_: true).
    + by auto.
    while (KeygenUniformXofLeafSpec.bounded_prefix8192
             ap base_i (W64.to_uint ctr) /\
           W64.to_uint base = base_i /\
           base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
             BArray8192.size %/ 4 /\
           0 <= W64.to_uint ctr <=
             KeygenUniformXofLeafSpec.uniform_poly_words_i).
    + by auto.
    by auto.
wp.
auto => />.
move=> &hr hbounded hcap hctrlo hctrhi hsemantic.
rewrite /protect_64 /protect_ptr.
split.
+ move=> hseedcap.
  have [blocks pairs hstream] := hsemantic hseedcap.
  exists blocks.
  exists pairs.
  move: hstream =>
    [hblocks [hpairs [hstate [hbuflen [hctr [hsizele
      [hdecoded [hframe hterminal]]]]]]]].
  have [hpairs0 hpairsle] := hpairs.
  do split; try assumption; smt().
move=> ap0 base0 buflen0 ctr0 sp_00 hguard hbounded0 _
  hctr0lo hctr0hi hsemantic0.
have hctrnlt :
    ! (W64.to_uint ctr0 <
       KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ move: hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenUniformXofLeafSpec.uniform_poly_words_i /=.
  trivial.
have hctrfull :
    W64.to_uint ctr0 =
      KeygenUniformXofLeafSpec.uniform_poly_words_i by smt().
split.
+ rewrite -hctrfull.
  exact hbounded0.
move=> hseedcap.
have [blocks pairs hstream] := hsemantic0 hseedcap.
exists blocks.
exists pairs.
move: hstream =>
  [hblocks [hpairs [_ [_ [hctr [_ [hdecoded [_ _]]]]]]]].
have [hpairs0 hpairsle] := hpairs.
do split; try assumption; smt().
qed.

lemma uniform2048_leaf_range base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048 :
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4
    ==>
    KeygenUniformXofLeafSpec.bounded_prefix8192
      res base_i KeygenUniformXofLeafSpec.uniform_poly_words_i].
proof.
exlim seedp => seed0.
exlim seedoff => seedoff0.
exlim nonce => nonce0.
conseq (uniform2048_leaf_stream seed0 seedoff0 nonce0 base_i).
+ auto => />.
+ auto => />.
qed.

lemma uniform8192_leaf_stream
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4
    ==>
    KeygenUniformXofLeafSpec.bounded_prefix32768
      res base_i KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    (W64.to_uint seedoff0 + 32 <= BArray128.size =>
      exists blocks pairs,
        4 <= blocks /\
        0 <= pairs <=
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
        size (KeygenUniformXofLeafSpec.uniform_accepted
          (KeygenShakeStreamSpec.shake128_squeeze_bytes
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks) pairs) =
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        KeygenUniformXofLeafSpec.decoded_prefix32768
          res base_i
          (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs))].
proof.
proc.
seq 17 :
  (KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
   W64.to_uint base = base_i /\
   base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
     BArray32768.size %/ 4 /\
   seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
   off = W64.of_int 504 /\
   ctr = W64.of_int 0 /\
   buflen = W64.of_int 672 /\
   (W64.to_uint seedoff0 + 32 <= BArray128.size =>
      KeygenShakeStreamSpec.state_bytes_le sp_0 =
        KeygenShakeStreamSpec.squeeze_state_iter
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) 4 /\
      KeygenShakeStreamSpec.squeeze_blocks_matches
        bufp 0
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 168 4 /\
      KeygenShakeStreamSpec.fips_rate_prefix_matches
        bufp 0
        (KeygenShakeStreamSpec.shake128_squeeze_bytes
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) 4) 672 /\
      KeygenShakeStreamSpec.squeeze_region_frame
        buf bufp 0 168 4)).
+ case (W64.to_uint seedoff0 + 32 <= BArray128.size).
  + seq 6 :
      (KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 0 /\
       sp_0 = state /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size).
    + by auto => />; rewrite /KeygenShakeStreamSpec.squeeze_region_frame.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 0 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 0 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 0 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 0).
    + wp.
      call (TargetKeygenShakeStream.shake128_init_seedbuf_padded_state
        seed0 seedoff0 nonce0).
      + auto => /> &hr hregion0 hleafcap hseedcap result.
        move=> hstate.
        do split.
        + by rewrite KeygenShakeStreamSpec.squeeze_state_iter0.
        + exact (KeygenShakeStreamSpec.squeeze_blocks_matches0
            bufp{hr} 0
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) 168).
        + trivial.
      + by auto => />; smt().
    seq 1 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 1 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 1 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 1 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 0).
    + exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 0) before_state).
      auto => /> &hr hstate hmatches hregion0 hprefix hbase hcap hseedcap0
        result hblock hframe hperm.
      have [hstate1 [hmatches1 hregion1]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 0
          _ hstate hmatches hregion0 hblock hframe hperm.
      + smt().
      do split.
      + exact hstate1.
      + exact hmatches1.
      exact hregion1.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 2 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 2 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 2 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 168).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 168) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap hseedcap0
        result hblock hframe hperm.
      have [hstate2 [hmatches2 hregion2]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 1
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      do split.
      + exact hstate2.
      + exact hmatches2.
      exact hregion2.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 3 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 3 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 3 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 336).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 336) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap hseedcap0
        result hblock hframe hperm.
      have [hstate3 [hmatches3 hregion3]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 2
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      do split.
      + exact hstate3.
      + exact hmatches3.
      exact hregion3.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 4 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 4 /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 4) 672 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 4 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\
       nonce = nonce0 /\ W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       off = W64.of_int 504).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 504) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap hseedcap0
        result hblock hframe hperm.
      have [hstate4 [hmatches4 hregion4]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 3
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      have hflat :=
        KeygenShakeStreamSpec.shake128_squeeze_blocks_fips
          result.`1 0
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) 4 _ hmatches4.
      + smt().
      do split.
      + exact hstate4.
      + exact hmatches4.
      + by rewrite /= in hflat.
      exact hregion4.
    by auto.
  do 5! (wp; call (_ : true); first by auto).
  auto => /> &hr hbase hcap.
  exact (KeygenUniformXofLeafSpec.bounded_prefix32768_zero
    ap{hr} (W64.to_uint base{hr})).
exlim ap => before_ap.
seq 1 :
  (KeygenUniformXofLeafSpec.bounded_prefix32768
     ap base_i (W64.to_uint ctr) /\
   W64.to_uint base = base_i /\
   base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
     BArray32768.size %/ 4 /\
   0 <= W64.to_uint ctr <=
     KeygenUniformXofLeafSpec.uniform_poly_words_i /\
   (W64.to_uint seedoff0 + 32 <= BArray128.size =>
      exists blocks pairs,
        4 <= blocks /\
        0 <= pairs <=
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
        KeygenShakeStreamSpec.state_bytes_le sp_0 =
          KeygenShakeStreamSpec.squeeze_state_iter
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks /\
        (buflen = W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
         buflen = W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
        W64.to_uint ctr =
          size (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs) /\
        size (KeygenUniformXofLeafSpec.uniform_accepted
          (KeygenShakeStreamSpec.shake128_squeeze_bytes
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks) pairs) <=
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        0 <= W64.to_uint ctr <=
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        KeygenUniformXofLeafSpec.decoded_prefix32768
          ap base_i
          (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs) /\
        KeygenUniformXofLeafSpec.bounded_prefix32768
          ap base_i (W64.to_uint ctr) /\
        KeygenUniformXofLeafSpec.frame32768
          before_ap ap base_i /\
        (W64.to_uint ctr =
           KeygenUniformXofLeafSpec.uniform_poly_words_i \/
         pairs =
           blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))).
+ have hbytes :
    size (KeygenShakeStreamSpec.shake128_squeeze_bytes
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 4) =
      KeygenUniformXofLeafSpec.uniform_first_bytes_i.
  + exact (shake128_first_bytes_size
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0)).
  case (W64.to_uint seedoff0 + 32 <= BArray128.size).
  + call (consume8192_first672 before_ap
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 4) base_i).
    + auto => />.
      move=> &hr hbounded0 hcap hstream hseedcap.
      have [hstate [_ [hprefix _]]] := hstream hseedcap.
      split.
      + rewrite /KeygenUniformXofLeafSpec.uniform_first_bytes_i.
        exact hprefix.
      move=> _ _ _ result pairs hpairs0 hpairsle hctr hacceptedle
        _ _ hdecoded _ _ hterminal.
      exists 4.
      exists pairs.
      do split.
      + trivial.
      + rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i
                in hpairsle.
        rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
        smt().
      + exact hstate.
      + exact hctr.
      + exact hacceptedle.
      + exact hdecoded.
      move: hterminal.
      rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i
              /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
      smt().
    + auto => />.
  + call (consume8192_range base_i).
    auto => />.

while (KeygenUniformXofLeafSpec.bounded_prefix32768
         ap base_i (W64.to_uint ctr) /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i /\
       (W64.to_uint seedoff0 + 32 <= BArray128.size =>
         exists blocks pairs,
           4 <= blocks /\
           0 <= pairs <=
             blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
           KeygenShakeStreamSpec.state_bytes_le sp_0 =
             KeygenShakeStreamSpec.squeeze_state_iter
               (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                 seed0 seedoff0 nonce0) blocks /\
           (buflen =
              W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
            buflen =
              W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
           W64.to_uint ctr =
             size (KeygenUniformXofLeafSpec.uniform_accepted
               (KeygenShakeStreamSpec.shake128_squeeze_bytes
                 (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                   seed0 seedoff0 nonce0) blocks) pairs) /\
           size (KeygenUniformXofLeafSpec.uniform_accepted
             (KeygenShakeStreamSpec.shake128_squeeze_bytes
               (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                 seed0 seedoff0 nonce0) blocks) pairs) <=
             KeygenUniformXofLeafSpec.uniform_poly_words_i /\
           0 <= W64.to_uint ctr <=
             KeygenUniformXofLeafSpec.uniform_poly_words_i /\
           KeygenUniformXofLeafSpec.decoded_prefix32768
             ap base_i
             (KeygenUniformXofLeafSpec.uniform_accepted
               (KeygenShakeStreamSpec.shake128_squeeze_bytes
                 (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                   seed0 seedoff0 nonce0) blocks) pairs) /\
           KeygenUniformXofLeafSpec.bounded_prefix32768
             ap base_i (W64.to_uint ctr) /\
           KeygenUniformXofLeafSpec.frame32768 before_ap ap base_i /\
           (W64.to_uint ctr =
              KeygenUniformXofLeafSpec.uniform_poly_words_i \/
            pairs =
              blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))).
+ case (W64.to_uint seedoff0 + 32 <= BArray128.size).
  + conseq (_ :
      (exists blocks pairs,
        KeygenUniformXofLeafSpec.bounded_prefix32768
          ap base_i (W64.to_uint ctr) /\
        W64.to_uint base = base_i /\
        base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
          BArray32768.size %/ 4 /\
        0 <= W64.to_uint ctr <=
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        4 <= blocks /\
        0 <= pairs <=
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
        KeygenShakeStreamSpec.state_bytes_le sp_0 =
          KeygenShakeStreamSpec.squeeze_state_iter
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks /\
        (buflen =
           W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
         buflen =
           W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
        W64.to_uint ctr =
          size (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs) /\
        size (KeygenUniformXofLeafSpec.uniform_accepted
          (KeygenShakeStreamSpec.shake128_squeeze_bytes
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks) pairs) <=
          KeygenUniformXofLeafSpec.uniform_poly_words_i /\
        KeygenUniformXofLeafSpec.decoded_prefix32768
          ap base_i
          (KeygenUniformXofLeafSpec.uniform_accepted
            (KeygenShakeStreamSpec.shake128_squeeze_bytes
              (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
                seed0 seedoff0 nonce0) blocks) pairs) /\
        KeygenUniformXofLeafSpec.frame32768 before_ap ap base_i /\
        (W64.to_uint ctr =
           KeygenUniformXofLeafSpec.uniform_poly_words_i \/
         pairs =
           blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i) /\
        ctr \ult W64.of_int KeygenUniformXofLeafSpec.uniform_poly_words_i)
      ==> _).
    + auto => />.
      move=> &hr _ _ _ _ hstream hguard hseedcap.
      have [blocks pairs hsemantic] := hstream hseedcap.
      exists blocks.
      exists pairs.
      by move: hsemantic; auto.
    elim* => blocks pairs.
    exlim ap => iteration_ap.
    sp 3.
    rcondf 1.
    + auto => /> &hr _ _ _ _ _ _ _ _ hbuflen.
      have hoff := uniform_even_buflen_and1_zero buflen{hr} hbuflen.
      by rewrite W64.ultE hoff W64.of_uintK /=.
    seq 9 :
      (ap = iteration_ap /\
       KeygenUniformXofLeafSpec.bounded_prefix32768
         ap base_i (W64.to_uint ctr) /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i /\
       4 <= blocks /\
       pairs =
         blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
       KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) (blocks + 1) /\
       buflen =
         W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
       W64.to_uint ctr =
         size (KeygenUniformXofLeafSpec.uniform_accepted
           (KeygenShakeStreamSpec.shake128_squeeze_bytes
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks)
           (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i)) /\
       size (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)
         (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i)) <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i /\
       KeygenUniformXofLeafSpec.decoded_prefix32768
         ap base_i
         (KeygenUniformXofLeafSpec.uniform_accepted
           (KeygenShakeStreamSpec.shake128_squeeze_bytes
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks)
           (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i)) /\
       KeygenUniformXofLeafSpec.frame32768 before_ap ap base_i /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_squeeze_block
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)
         KeygenUniformXofLeafSpec.uniform_block_bytes_i).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 0) before_state).
      auto => />.
      move=> &hr hbounded hcap hctr0 hctrle hblocks hpairs0 hpairsle
        hstate hbuflen hctr hacceptedle hdecoded hframe hterminal
        hguard.
      have hctrlt :
        W64.to_uint ctr{hr} <
          KeygenUniformXofLeafSpec.uniform_poly_words_i.
      + rewrite W64.ultE W64.of_uintK
                /KeygenUniformXofLeafSpec.uniform_poly_words_i
                /= in hguard.
        exact hguard.
      have hoff :=
        uniform_even_buflen_and1_zero buflen{hr} hbuflen.
      split.
      + exact hoff.
      move=> _ _ result hblock _ hperm.
      have [hstate_next hprefix] :=
        shake128_squeeze_overwrite_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          before_state result.`2 result.`1 blocks
          _ hstate _ hperm.
      + smt().
      + rewrite /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
        exact hblock.
      rewrite /protect_64 /protect_ptr hoff
              /KeygenUniformXofLeafSpec.uniform_block_bytes_i /=.
      do split.
      + smt().
      + exact hstate_next.
      + trivial.
      + have <- :
          pairs =
            blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i by smt().
        exact hctr.
      + have <- :
          pairs =
            blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i by smt().
        exact hacceptedle.
      + have <- :
          pairs =
            blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i by smt().
        exact hdecoded.
      + exact hprefix.
    + wp.
      call (consume8192_block168 iteration_ap
        (KeygenShakeStreamSpec.shake128_squeeze_block
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) blocks)
        (KeygenUniformXofLeafSpec.uniform_accepted
          (KeygenShakeStreamSpec.shake128_squeeze_bytes
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks)
          (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))
        base_i).
      + auto => />.
        move=> &hr hbounded hcap hctr0 hctrle hblocks hstate hctr
          hacceptedle hdecoded hframe hprefix.
        split.
        + by rewrite
            KeygenShakeStreamSpec.shake128_squeeze_block_size
            /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
        move=> _ result fresh_pairs hfresh0 hfreshle hresultctr
          hresultsize hresultctr0 hresultctrle hresultdecoded
          hresultbounded hresultframe hterminal _.
        have hcat :=
          uniform_accepted_shake128_succ
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0)
            blocks fresh_pairs _ hfresh0.
        + smt().
        have hframe_next :=
          KeygenUniformXofLeafSpec.frame32768_trans
            before_ap iteration_ap result.`1 (W64.to_uint base{hr})
            hframe hresultframe.
        rewrite /protect_64 /protect_ptr.
        exists (blocks + 1).
        exists (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i +
          fresh_pairs).
        do split.
        + smt().
        + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
          smt().
        + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
          smt().
        + exact hstate.
        + rewrite hcat.
          exact hresultctr.
        + rewrite hcat.
          exact hresultsize.
        + smt().
        + smt().
        + rewrite hcat.
          exact hresultdecoded.
        + exact hresultbounded.
        + exact hframe_next.
        case hterminal => [hfull | hfreshfull].
        + by left.
        right.
        rewrite hfreshfull.
        ring.
  + wp.
    call (consume8192_range base_i).
    wp.
    call (_: true).
    + by auto.
    while (KeygenUniformXofLeafSpec.bounded_prefix32768
             ap base_i (W64.to_uint ctr) /\
           W64.to_uint base = base_i /\
           base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
             BArray32768.size %/ 4 /\
           0 <= W64.to_uint ctr <=
             KeygenUniformXofLeafSpec.uniform_poly_words_i).
    + by auto.
    by auto.
wp.
auto => />.
move=> &hr hbounded hcap hctrlo hctrhi hsemantic.
rewrite /protect_64 /protect_ptr.
split.
+ move=> hseedcap.
  have [blocks pairs hstream] := hsemantic hseedcap.
  exists blocks.
  exists pairs.
  move: hstream =>
    [hblocks [hpairs [hstate [hbuflen [hctr [hsizele
      [hdecoded [hframe hterminal]]]]]]]].
  have [hpairs0 hpairsle] := hpairs.
  do split; try assumption; smt().
move=> ap0 base0 buflen0 ctr0 sp_00 hguard hbounded0 _
  hctr0lo hctr0hi hsemantic0.
have hctrnlt :
    ! (W64.to_uint ctr0 <
       KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ move: hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenUniformXofLeafSpec.uniform_poly_words_i /=.
  trivial.
have hctrfull :
    W64.to_uint ctr0 =
      KeygenUniformXofLeafSpec.uniform_poly_words_i by smt().
split.
+ rewrite -hctrfull.
  exact hbounded0.
move=> hseedcap.
have [blocks pairs hstream] := hsemantic0 hseedcap.
exists blocks.
exists pairs.
move: hstream =>
  [hblocks [hpairs [_ [_ [hctr [_ [hdecoded [_ _]]]]]]]].
have [hpairs0 hpairsle] := hpairs.
do split; try assumption; smt().
qed.

lemma uniform8192_leaf_range base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192 :
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4
    ==>
    KeygenUniformXofLeafSpec.bounded_prefix32768
      res base_i KeygenUniformXofLeafSpec.uniform_poly_words_i].
proof.
exlim seedp => seed0.
exlim seedoff => seedoff0.
exlim nonce => nonce0.
conseq (uniform8192_leaf_stream seed0 seedoff0 nonce0 base_i).
+ auto => />.
+ auto => />.
qed.

lemma uniform2048_leaf_frame ap0 base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048 :
    ap = ap0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4
    ==>
    KeygenUniformXofLeafSpec.frame8192 ap0 res base_i].
proof.
proc.
while (KeygenUniformXofLeafSpec.frame8192 ap0 ap base_i /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ wp.
  call (consume2048_frame ap0 base_i).
  wp.
  call (_: true).
  + by auto.
  while (KeygenUniformXofLeafSpec.frame8192 ap0 ap base_i /\
         W64.to_uint base = base_i /\
         base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i).
  + by auto.
  by auto.
wp.
call (consume2048_frame ap0 base_i).
do 5! (wp; call (_: true); first by auto).
auto => /> &hr hcap.
qed.

lemma uniform8192_leaf_frame ap0 base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192 :
    ap = ap0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4
    ==>
    KeygenUniformXofLeafSpec.frame32768 ap0 res base_i].
proof.
proc.
while (KeygenUniformXofLeafSpec.frame32768 ap0 ap base_i /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       0 <= W64.to_uint ctr <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i).
+ wp.
  call (consume8192_frame ap0 base_i).
  wp.
  call (_: true).
  + by auto.
  while (KeygenUniformXofLeafSpec.frame32768 ap0 ap base_i /\
         W64.to_uint base = base_i /\
         base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
           BArray32768.size %/ 4 /\
         0 <= W64.to_uint ctr <=
           KeygenUniformXofLeafSpec.uniform_poly_words_i).
  + by auto.
  by auto.
wp.
call (consume8192_frame ap0 base_i).
do 5! (wp; call (_: true); first by auto).
auto => /> &hr hcap.
qed.

lemma uniform2048_leaf_progress_ll
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i limit :
  phoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size /\
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      seed0 seedoff0 nonce0 limit
    ==> true] = 1%r.
proof.
proc.
while
  (W64.to_uint base = base_i /\
   base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
     BArray8192.size %/ 4 /\
   KeygenUniformXofLeafSpec.uniform_progress_prefix
     seed0 seedoff0 nonce0 limit /\
   0 <= W64.to_uint ctr <=
     KeygenUniformXofLeafSpec.uniform_poly_words_i /\
   exists blocks pairs,
     4 <= blocks <= limit /\
     0 <= pairs <=
       blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks /\
     (buflen =
        W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
      buflen =
        W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
     W64.to_uint ctr =
       size (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks) pairs) /\
     size (KeygenUniformXofLeafSpec.uniform_accepted
       (KeygenShakeStreamSpec.shake128_squeeze_bytes
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks) pairs) <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     KeygenUniformXofLeafSpec.decoded_prefix8192
       ap base_i
       (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks) pairs) /\
     KeygenUniformXofLeafSpec.bounded_prefix8192
       ap base_i (W64.to_uint ctr) /\
     (W64.to_uint ctr =
        KeygenUniformXofLeafSpec.uniform_poly_words_i \/
      pairs =
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))
  (KeygenUniformXofLeafSpec.uniform_poly_words_i - W64.to_uint ctr).
+ move=> z.
  conseq (_ : _ ==> true : = 1%r)
    (_ : _ ==>
    (W64.to_uint base = base_i /\
     base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
       BArray8192.size %/ 4 /\
     KeygenUniformXofLeafSpec.uniform_progress_prefix
       seed0 seedoff0 nonce0 limit /\
     0 <= W64.to_uint ctr <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     exists blocks pairs,
       4 <= blocks <= limit /\
       0 <= pairs <=
         blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
       KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks /\
       (buflen =
          W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
        buflen =
          W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
       W64.to_uint ctr =
         size (KeygenUniformXofLeafSpec.uniform_accepted
           (KeygenShakeStreamSpec.shake128_squeeze_bytes
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks) pairs) /\
       size (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks) pairs) <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i /\
       KeygenUniformXofLeafSpec.decoded_prefix8192
         ap base_i
         (KeygenUniformXofLeafSpec.uniform_accepted
           (KeygenShakeStreamSpec.shake128_squeeze_bytes
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks) pairs) /\
       KeygenUniformXofLeafSpec.bounded_prefix8192
         ap base_i (W64.to_uint ctr) /\
       (W64.to_uint ctr =
          KeygenUniformXofLeafSpec.uniform_poly_words_i \/
        pairs =
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i) /\
     KeygenUniformXofLeafSpec.uniform_poly_words_i -
       W64.to_uint ctr < z)) => //.
  + smt().
  + smt().
  + elim* => blocks pairs.
  exlim ap => iteration_ap.
  sp 3.
  rcondf 1.
  + auto => /> &hr _ _ _ _ _ _ _ _ _ _ _ hbuflen.
    have hoff := uniform_even_buflen_and1_zero buflen{hr} hbuflen.
    by rewrite W64.ultE hoff W64.of_uintK /=.
  seq 9 :
    (ap = iteration_ap /\
     W64.to_uint base = base_i /\
     base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
       BArray8192.size %/ 4 /\
     KeygenUniformXofLeafSpec.uniform_progress_prefix
       seed0 seedoff0 nonce0 limit /\
     0 <= W64.to_uint ctr <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     4 <= blocks < limit /\
     pairs =
       blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) (blocks + 1) /\
     buflen =
       W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
     W64.to_uint ctr =
       KeygenUniformXofLeafSpec.uniform_prefix_count
         seed0 seedoff0 nonce0 blocks /\
     KeygenUniformXofLeafSpec.uniform_prefix_count
       seed0 seedoff0 nonce0 blocks <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     KeygenUniformXofLeafSpec.decoded_prefix8192
       ap base_i
       (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)
         (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i)) /\
     KeygenUniformXofLeafSpec.bounded_prefix8192
       ap base_i (W64.to_uint ctr) /\
     KeygenShakeStreamSpec.fips_rate_prefix_matches
       bufp 0
       (KeygenShakeStreamSpec.shake128_squeeze_block
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks)
       KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
     W64.to_uint ctr <
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     KeygenUniformXofLeafSpec.uniform_poly_words_i -
       W64.to_uint ctr = z).
  + wp.
    exlim bufp => before_out.
    exlim sp_0 => before_state.
    call (TargetKeygenShakeStream.squeeze128_rate_block
      before_out (W64.of_int 0) before_state).
    auto => />.
    move=> &hr hleafcap hlimit hendpoint hprogress_step
      hctr0 hctrle hblocks0 hblocksle hpairs0 hpairsle
      hstate hbuflen hctr hsizele hdecoded hbounded hterminal hguard.
    have hcert :
      KeygenUniformXofLeafSpec.uniform_progress_prefix
        seed0 seedoff0 nonce0 limit.
    + by rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
                 /KeygenUniformXofLeafSpec.uniform_sufficient_prefix; smt().
    have hctrlt :
      W64.to_uint ctr{hr} <
        KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + by rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i; smt().
    have hpairsfull :
      pairs = blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i
      by smt().
    have hcount :
      W64.to_uint ctr{hr} =
        KeygenUniformXofLeafSpec.uniform_prefix_count
          seed0 seedoff0 nonce0 blocks.
    + rewrite /KeygenUniformXofLeafSpec.uniform_prefix_count
              -hpairsfull.
      exact hctr.
    have hblocklt :=
      KeygenUniformXofLeafSpec.uniform_progress_prefix_before_limit
        seed0 seedoff0 nonce0 limit blocks hcert hblocks0 _.
    + by rewrite -hcount.
    have hoff := uniform_even_buflen_and1_zero buflen{hr} hbuflen.
    split.
    + exact hoff.
    move=> _ _ result hblock _ hperm.
    have [hstate_next hprefix] :=
      shake128_squeeze_overwrite_step
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0)
        before_state result.`2 result.`1 blocks
        _ hstate _ hperm.
    + smt().
    + rewrite /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
      exact hblock.
    rewrite /protect_64 /protect_ptr hoff
            /KeygenUniformXofLeafSpec.uniform_block_bytes_i /=.
    do split.
    + exact hblocklt.
    + exact hpairsfull.
    + exact hstate_next.
    + trivial.
    + rewrite /KeygenUniformXofLeafSpec.uniform_prefix_count
              -hpairsfull.
      exact hsizele.
    + rewrite -hpairsfull.
      exact hdecoded.
    + exact hprefix.
    exact hctrlt.
  wp.
  call (consume2048_block168 iteration_ap
    (KeygenShakeStreamSpec.shake128_squeeze_block
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) blocks)
    (KeygenUniformXofLeafSpec.uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) blocks)
      (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))
    base_i).
  auto => />.
  move=> &hr hbase hcap hcert hctr0 hctrle hblocks0 hblocklt
    hstate hctr hcountle hdecoded hbounded hprefix hctrlt hz.
  split.
  + by rewrite KeygenShakeStreamSpec.shake128_squeeze_block_size
               /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
  move=> _ _ result fresh_pairs hfresh0 hfreshle hresultctr
    hresultsize hresultctr0 hresultctrle hresultdecoded
    hresultbounded _ hterminal.
  have hcat :=
    uniform_accepted_shake128_succ
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0)
      blocks fresh_pairs _ hfresh0.
  + smt().
  have hcert_full :
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      seed0 seedoff0 nonce0 limit.
  + by rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
               /KeygenUniformXofLeafSpec.uniform_sufficient_prefix; smt().
  have hstep :=
    KeygenUniformXofLeafSpec.uniform_progress_prefix_step
      seed0 seedoff0 nonce0 limit blocks hcert_full _ _.
  + smt().
  + by rewrite -hcountle; exact hz.
  rewrite /protect_64 /protect_ptr.
  exists (blocks + 1).
  exists (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i +
    fresh_pairs).
  do split.
  + smt().
  + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    smt().
  + smt().
  + smt().
  + exact hctr.
  + trivial.
  + rewrite hcat.
    exact hresultctr.
  + rewrite hcat.
    exact hresultsize.
  + rewrite hcat.
    exact hresultdecoded.
  + exact hresultbounded.
  + case hterminal => [hfull | hfreshfull].
    + by left.
    right.
    rewrite hfreshfull.
    ring.
  case hterminal => [hfull | hfreshfull]; smt().
  + sp 3.
    rcondf 1.
    + auto => /> &hr *.
      have hoff := uniform_even_buflen_and1_zero buflen{hr} _.
      + assumption.
      by rewrite W64.ultE hoff W64.of_uintK /=.
    wp.
    call uniform_consume2048_ll.
    wp.
    call TargetKeygenShakeStream.squeeze128_ll.
    auto.
conseq (_ : _ ==> true : = 1%r) (_ : _ ==> _) => //.
+ smt().
+ seq 17 :
    (KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
     W64.to_uint base = base_i /\
     base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
       BArray8192.size %/ 4 /\
     seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
     off = W64.of_int 504 /\
     ctr = W64.of_int 0 /\
     buflen = W64.of_int 672 /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 4 /\
     KeygenShakeStreamSpec.squeeze_blocks_matches
       bufp 0
       (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
         seed0 seedoff0 nonce0) 168 4 /\
     KeygenShakeStreamSpec.fips_rate_prefix_matches
       bufp 0
       (KeygenShakeStreamSpec.shake128_squeeze_bytes
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 4) 672 /\
     KeygenShakeStreamSpec.squeeze_region_frame
       buf bufp 0 168 4 /\
     W64.to_uint seedoff0 + 32 <= BArray128.size /\
     KeygenUniformXofLeafSpec.uniform_progress_prefix
       seed0 seedoff0 nonce0 limit).
  + seq 6 :
      (KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 0 /\
       sp_0 = state /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit).
    + by auto => />; rewrite /KeygenShakeStreamSpec.squeeze_region_frame.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 0 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 0 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 0 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 0).
    + wp.
      call (TargetKeygenShakeStream.shake128_init_seedbuf_padded_state
        seed0 seedoff0 nonce0).
      + auto => /> &hr hregion0 hleafcap hseedcap
          hlimit hendpoint hprogress result.
        move=> hstate.
        do split.
        + by rewrite KeygenShakeStreamSpec.squeeze_state_iter0.
        + exact (KeygenShakeStreamSpec.squeeze_blocks_matches0
            bufp{hr} 0
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) 168).
        + trivial.
      + by auto => />; smt().
    seq 1 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 1 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 1 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 1 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 0).
    + exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 0) before_state).
      auto => /> &hr hstate hmatches hregion0 hprefix hbase hcap
        hseedcap0 hlimit hendpoint hprogress result hblock hframe hperm.
      have [hstate1 [hmatches1 hregion1]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 0
          _ hstate hmatches hregion0 hblock hframe hperm.
      + smt().
      do split.
      + exact hstate1.
      + exact hmatches1.
      exact hregion1.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 2 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 2 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 2 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 168).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 168) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap
        hseedcap0 hlimit hendpoint hprogress result hblock hframe hperm.
      have [hstate2 [hmatches2 hregion2]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 1
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      do split.
      + exact hstate2.
      + exact hmatches2.
      exact hregion2.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 3 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 3 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 3 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 336).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 336) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap
        hseedcap0 hlimit hendpoint hprogress result hblock hframe hperm.
      have [hstate3 [hmatches3 hregion3]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 2
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      do split.
      + exact hstate3.
      + exact hmatches3.
      exact hregion3.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 4 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 4 /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 4) 672 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 4 /\
       KeygenUniformXofLeafSpec.bounded_prefix8192 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 504).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 504) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap
        hseedcap0 hlimit hendpoint hprogress result hblock hframe hperm.
      have [hstate4 [hmatches4 hregion4]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 3
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      have hflat :=
        KeygenShakeStreamSpec.shake128_squeeze_blocks_fips
          result.`1 0
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) 4 _ hmatches4.
      + smt().
      do split.
      + exact hstate4.
      + exact hmatches4.
      + by rewrite /= in hflat.
      exact hregion4.
    by auto.
  exlim ap => before_ap.
  have hbytes :
    size (KeygenShakeStreamSpec.shake128_squeeze_bytes
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 4) =
      KeygenUniformXofLeafSpec.uniform_first_bytes_i.
  + exact (shake128_first_bytes_size
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0)).
  wp.
  call (consume2048_first672 before_ap
    (KeygenShakeStreamSpec.shake128_squeeze_bytes
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 4) base_i).
  auto => />.
  move=> &hr hbounded hcap0 hstate0 hmatches hprefix0 hregion
    hseedcap hlimit0 hendpoint hprogress.
  have hcap :
    W64.to_uint base{hr} +
      KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4 by assumption.
  have hstate :
    KeygenShakeStreamSpec.state_bytes_le sp_0{hr} =
      KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 4 by assumption.
  have hprefix :
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bufp{hr} 0
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 4) 672 by assumption.
  have hcert :
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      seed0 seedoff0 nonce0 limit.
  + rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
            /KeygenUniformXofLeafSpec.uniform_sufficient_prefix.
    do split; assumption.
  have hlimit : 4 <= limit.
  + move: hcert.
    rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
            /KeygenUniformXofLeafSpec.uniform_sufficient_prefix.
    smt().
  move=> _ _ _ result fresh_pairs hfresh0 hfreshle hresultctr
    hresultsize hresultctr0 hresultctrle hresultdecoded
    hresultbounded _ hterminal.
  split.
  + rewrite /protect_64 /protect_ptr.
    exists 4.
    exists fresh_pairs.
    do split.
    + smt().
    + exact hfresh0.
    + rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i
                in hfreshle.
      rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
      smt().
    + exact hstate.
    + exact hresultctr.
    + exact hresultsize.
    + exact hresultdecoded.
    + exact hresultbounded.
    move: hterminal.
    rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i
            /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    smt().
  move=> *.
  rewrite W64.ultE W64.of_uintK
          /KeygenUniformXofLeafSpec.uniform_poly_words_i /=.
  smt().
+ wp.
  call uniform_consume2048_ll.
  wp.
  call TargetKeygenShakeStream.squeeze128_ll.
  wp.
  call TargetKeygenShakeStream.squeeze128_ll.
  wp.
  call TargetKeygenShakeStream.squeeze128_ll.
  wp.
  call TargetKeygenShakeStream.squeeze128_ll.
  wp.
  call TargetKeygenShakeStream.shake128_init_seedbuf_ll.
  by auto.
qed.

lemma uniform8192_leaf_progress_ll
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i limit :
  phoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size /\
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      seed0 seedoff0 nonce0 limit
    ==> true] = 1%r.
proof.
proc.
while
  (W64.to_uint base = base_i /\
   base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
     BArray32768.size %/ 4 /\
   KeygenUniformXofLeafSpec.uniform_progress_prefix
     seed0 seedoff0 nonce0 limit /\
   0 <= W64.to_uint ctr <=
     KeygenUniformXofLeafSpec.uniform_poly_words_i /\
   exists blocks pairs,
     4 <= blocks <= limit /\
     0 <= pairs <=
       blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks /\
     (buflen =
        W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
      buflen =
        W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
     W64.to_uint ctr =
       size (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks) pairs) /\
     size (KeygenUniformXofLeafSpec.uniform_accepted
       (KeygenShakeStreamSpec.shake128_squeeze_bytes
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks) pairs) <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     KeygenUniformXofLeafSpec.decoded_prefix32768
       ap base_i
       (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks) pairs) /\
     KeygenUniformXofLeafSpec.bounded_prefix32768
       ap base_i (W64.to_uint ctr) /\
     (W64.to_uint ctr =
        KeygenUniformXofLeafSpec.uniform_poly_words_i \/
      pairs =
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))
  (KeygenUniformXofLeafSpec.uniform_poly_words_i - W64.to_uint ctr).
+ move=> z.
  conseq (_ : _ ==> true : = 1%r)
    (_ : _ ==>
    (W64.to_uint base = base_i /\
     base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
       BArray32768.size %/ 4 /\
     KeygenUniformXofLeafSpec.uniform_progress_prefix
       seed0 seedoff0 nonce0 limit /\
     0 <= W64.to_uint ctr <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     exists blocks pairs,
       4 <= blocks <= limit /\
       0 <= pairs <=
         blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
       KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks /\
       (buflen =
          W64.of_int KeygenUniformXofLeafSpec.uniform_first_bytes_i \/
        buflen =
          W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i) /\
       W64.to_uint ctr =
         size (KeygenUniformXofLeafSpec.uniform_accepted
           (KeygenShakeStreamSpec.shake128_squeeze_bytes
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks) pairs) /\
       size (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks) pairs) <=
         KeygenUniformXofLeafSpec.uniform_poly_words_i /\
       KeygenUniformXofLeafSpec.decoded_prefix32768
         ap base_i
         (KeygenUniformXofLeafSpec.uniform_accepted
           (KeygenShakeStreamSpec.shake128_squeeze_bytes
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks) pairs) /\
       KeygenUniformXofLeafSpec.bounded_prefix32768
         ap base_i (W64.to_uint ctr) /\
       (W64.to_uint ctr =
          KeygenUniformXofLeafSpec.uniform_poly_words_i \/
        pairs =
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i) /\
     KeygenUniformXofLeafSpec.uniform_poly_words_i -
       W64.to_uint ctr < z)) => //.
  + smt().
  + smt().
  + elim* => blocks pairs.
  exlim ap => iteration_ap.
  sp 3.
  rcondf 1.
  + auto => /> &hr _ _ _ _ _ _ _ _ _ _ _ hbuflen.
    have hoff := uniform_even_buflen_and1_zero buflen{hr} hbuflen.
    by rewrite W64.ultE hoff W64.of_uintK /=.
  seq 9 :
    (ap = iteration_ap /\
     W64.to_uint base = base_i /\
     base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
       BArray32768.size %/ 4 /\
     KeygenUniformXofLeafSpec.uniform_progress_prefix
       seed0 seedoff0 nonce0 limit /\
     0 <= W64.to_uint ctr <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     4 <= blocks < limit /\
     pairs =
       blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) (blocks + 1) /\
     buflen =
       W64.of_int KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
     W64.to_uint ctr =
       KeygenUniformXofLeafSpec.uniform_prefix_count
         seed0 seedoff0 nonce0 blocks /\
     KeygenUniformXofLeafSpec.uniform_prefix_count
       seed0 seedoff0 nonce0 blocks <=
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     KeygenUniformXofLeafSpec.decoded_prefix32768
       ap base_i
       (KeygenUniformXofLeafSpec.uniform_accepted
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)
         (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i)) /\
     KeygenUniformXofLeafSpec.bounded_prefix32768
       ap base_i (W64.to_uint ctr) /\
     KeygenShakeStreamSpec.fips_rate_prefix_matches
       bufp 0
       (KeygenShakeStreamSpec.shake128_squeeze_block
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks)
       KeygenUniformXofLeafSpec.uniform_block_bytes_i /\
     W64.to_uint ctr <
       KeygenUniformXofLeafSpec.uniform_poly_words_i /\
     KeygenUniformXofLeafSpec.uniform_poly_words_i -
       W64.to_uint ctr = z).
  + wp.
    exlim bufp => before_out.
    exlim sp_0 => before_state.
    call (TargetKeygenShakeStream.squeeze128_rate_block
      before_out (W64.of_int 0) before_state).
    auto => />.
    move=> &hr hleafcap hlimit hendpoint hprogress_step
      hctr0 hctrle hblocks0 hblocksle hpairs0 hpairsle
      hstate hbuflen hctr hsizele hdecoded hbounded hterminal hguard.
    have hcert :
      KeygenUniformXofLeafSpec.uniform_progress_prefix
        seed0 seedoff0 nonce0 limit.
    + by rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
                 /KeygenUniformXofLeafSpec.uniform_sufficient_prefix; smt().
    have hctrlt :
      W64.to_uint ctr{hr} <
        KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + by rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i; smt().
    have hpairsfull :
      pairs = blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i
      by smt().
    have hcount :
      W64.to_uint ctr{hr} =
        KeygenUniformXofLeafSpec.uniform_prefix_count
          seed0 seedoff0 nonce0 blocks.
    + rewrite /KeygenUniformXofLeafSpec.uniform_prefix_count
              -hpairsfull.
      exact hctr.
    have hblocklt :=
      KeygenUniformXofLeafSpec.uniform_progress_prefix_before_limit
        seed0 seedoff0 nonce0 limit blocks hcert hblocks0 _.
    + by rewrite -hcount.
    have hoff := uniform_even_buflen_and1_zero buflen{hr} hbuflen.
    split.
    + exact hoff.
    move=> _ _ result hblock _ hperm.
    have [hstate_next hprefix] :=
      shake128_squeeze_overwrite_step
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0)
        before_state result.`2 result.`1 blocks
        _ hstate _ hperm.
    + smt().
    + rewrite /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
      exact hblock.
    rewrite /protect_64 /protect_ptr hoff
            /KeygenUniformXofLeafSpec.uniform_block_bytes_i /=.
    do split.
    + exact hblocklt.
    + exact hpairsfull.
    + exact hstate_next.
    + trivial.
    + rewrite /KeygenUniformXofLeafSpec.uniform_prefix_count
              -hpairsfull.
      exact hsizele.
    + rewrite -hpairsfull.
      exact hdecoded.
    + exact hprefix.
    exact hctrlt.
  wp.
  call (consume8192_block168 iteration_ap
    (KeygenShakeStreamSpec.shake128_squeeze_block
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) blocks)
    (KeygenUniformXofLeafSpec.uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) blocks)
      (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i))
    base_i).
  auto => />.
  move=> &hr hbase hcap hcert hctr0 hctrle hblocks0 hblocklt
    hstate hctr hcountle hdecoded hbounded hprefix hctrlt hz.
  split.
  + by rewrite KeygenShakeStreamSpec.shake128_squeeze_block_size
               /KeygenUniformXofLeafSpec.uniform_block_bytes_i.
  move=> _ _ result fresh_pairs hfresh0 hfreshle hresultctr
    hresultsize hresultctr0 hresultctrle hresultdecoded
    hresultbounded _ hterminal.
  have hcat :=
    uniform_accepted_shake128_succ
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0)
      blocks fresh_pairs _ hfresh0.
  + smt().
  have hcert_full :
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      seed0 seedoff0 nonce0 limit.
  + by rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
               /KeygenUniformXofLeafSpec.uniform_sufficient_prefix; smt().
  have hstep :=
    KeygenUniformXofLeafSpec.uniform_progress_prefix_step
      seed0 seedoff0 nonce0 limit blocks hcert_full _ _.
  + smt().
  + by rewrite -hcountle; exact hz.
  rewrite /protect_64 /protect_ptr.
  exists (blocks + 1).
  exists (blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i +
    fresh_pairs).
  do split.
  + smt().
  + rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    smt().
  + smt().
  + smt().
  + exact hctr.
  + trivial.
  + rewrite hcat.
    exact hresultctr.
  + rewrite hcat.
    exact hresultsize.
  + rewrite hcat.
    exact hresultdecoded.
  + exact hresultbounded.
  + case hterminal => [hfull | hfreshfull].
    + by left.
    right.
    rewrite hfreshfull.
    ring.
  case hterminal => [hfull | hfreshfull]; smt().
  + sp 3.
    rcondf 1.
    + auto => /> &hr *.
      have hoff := uniform_even_buflen_and1_zero buflen{hr} _.
      + assumption.
      by rewrite W64.ultE hoff W64.of_uintK /=.
    wp.
    call uniform_consume8192_ll.
    wp.
    call TargetKeygenShakeStream.squeeze128_ll.
    auto.
conseq (_ : _ ==> true : = 1%r) (_ : _ ==> _) => //.
+ smt().
+ seq 17 :
    (KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
     W64.to_uint base = base_i /\
     base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
       BArray32768.size %/ 4 /\
     seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
     off = W64.of_int 504 /\
     ctr = W64.of_int 0 /\
     buflen = W64.of_int 672 /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 4 /\
     KeygenShakeStreamSpec.squeeze_blocks_matches
       bufp 0
       (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
         seed0 seedoff0 nonce0) 168 4 /\
     KeygenShakeStreamSpec.fips_rate_prefix_matches
       bufp 0
       (KeygenShakeStreamSpec.shake128_squeeze_bytes
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 4) 672 /\
     KeygenShakeStreamSpec.squeeze_region_frame
       buf bufp 0 168 4 /\
     W64.to_uint seedoff0 + 32 <= BArray128.size /\
     KeygenUniformXofLeafSpec.uniform_progress_prefix
       seed0 seedoff0 nonce0 limit).
  + seq 6 :
      (KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 0 /\
       sp_0 = state /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit).
    + by auto => />; rewrite /KeygenShakeStreamSpec.squeeze_region_frame.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 0 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 0 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 0 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 0).
    + wp.
      call (TargetKeygenShakeStream.shake128_init_seedbuf_padded_state
        seed0 seedoff0 nonce0).
      + auto => /> &hr hregion0 hleafcap hseedcap
          hlimit hendpoint hprogress result.
        move=> hstate.
        do split.
        + by rewrite KeygenShakeStreamSpec.squeeze_state_iter0.
        + exact (KeygenShakeStreamSpec.squeeze_blocks_matches0
            bufp{hr} 0
            (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
              seed0 seedoff0 nonce0) 168).
        + trivial.
      + by auto => />; smt().
    seq 1 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 1 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 1 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 1 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 0).
    + exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 0) before_state).
      auto => /> &hr hstate hmatches hregion0 hprefix hbase hcap
        hseedcap0 hlimit hendpoint hprogress result hblock hframe hperm.
      have [hstate1 [hmatches1 hregion1]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 0
          _ hstate hmatches hregion0 hblock hframe hperm.
      + smt().
      do split.
      + exact hstate1.
      + exact hmatches1.
      exact hregion1.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 2 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 2 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 2 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 168).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 168) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap
        hseedcap0 hlimit hendpoint hprogress result hblock hframe hperm.
      have [hstate2 [hmatches2 hregion2]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 1
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      do split.
      + exact hstate2.
      + exact hmatches2.
      exact hregion2.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 3 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 3 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 3 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 336).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 336) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap
        hseedcap0 hlimit hendpoint hprogress result hblock hframe hperm.
      have [hstate3 [hmatches3 hregion3]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 2
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      do split.
      + exact hstate3.
      + exact hmatches3.
      exact hregion3.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 4 /\
       KeygenShakeStreamSpec.squeeze_blocks_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 168 4 /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake128_squeeze_bytes
           (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 4) 672 /\
       KeygenShakeStreamSpec.squeeze_region_frame
         buf bufp 0 168 4 /\
       KeygenUniformXofLeafSpec.bounded_prefix32768 ap base_i 0 /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
         BArray32768.size %/ 4 /\
       W64.to_uint seedoff0 + 32 <= BArray128.size /\
       KeygenUniformXofLeafSpec.uniform_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       off = W64.of_int 504).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze128_rate_block
        before_out (W64.of_int 504) before_state).
      auto => /> &hr hstate hmatches hregion hprefix hbase hcap
        hseedcap0 hlimit hendpoint hprogress result hblock hframe hperm.
      have [hstate4 [hmatches4 hregion4]] :=
        shake128_squeeze_block_step
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          buf{hr} before_out result.`1 before_state result.`2 3
          _ hstate hmatches hregion hblock hframe hperm.
      + smt().
      have hflat :=
        KeygenShakeStreamSpec.shake128_squeeze_blocks_fips
          result.`1 0
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) 4 _ hmatches4.
      + smt().
      do split.
      + exact hstate4.
      + exact hmatches4.
      + by rewrite /= in hflat.
      exact hregion4.
    by auto.
  exlim ap => before_ap.
  have hbytes :
    size (KeygenShakeStreamSpec.shake128_squeeze_bytes
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 4) =
      KeygenUniformXofLeafSpec.uniform_first_bytes_i.
  + exact (shake128_first_bytes_size
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0)).
  wp.
  call (consume8192_first672 before_ap
    (KeygenShakeStreamSpec.shake128_squeeze_bytes
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 4) base_i).
  auto => />.
  move=> &hr hbounded hcap0 hstate0 hmatches hprefix0 hregion
    hseedcap hlimit0 hendpoint hprogress.
  have hcap :
    W64.to_uint base{hr} +
      KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 by assumption.
  have hstate :
    KeygenShakeStreamSpec.state_bytes_le sp_0{hr} =
      KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 4 by assumption.
  have hprefix :
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bufp{hr} 0
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 4) 672 by assumption.
  have hcert :
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      seed0 seedoff0 nonce0 limit.
  + rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
            /KeygenUniformXofLeafSpec.uniform_sufficient_prefix.
    do split; assumption.
  have hlimit : 4 <= limit.
  + move: hcert.
    rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
            /KeygenUniformXofLeafSpec.uniform_sufficient_prefix.
    smt().
  move=> _ _ _ result fresh_pairs hfresh0 hfreshle hresultctr
    hresultsize hresultctr0 hresultctrle hresultdecoded
    hresultbounded _ hterminal.
  split.
  + rewrite /protect_64 /protect_ptr.
    exists 4.
    exists fresh_pairs.
    do split.
    + smt().
    + exact hfresh0.
    + rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i
                in hfreshle.
      rewrite /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
      smt().
    + exact hstate.
    + exact hresultctr.
    + exact hresultsize.
    + exact hresultdecoded.
    + exact hresultbounded.
    move: hterminal.
    rewrite /KeygenUniformXofLeafSpec.uniform_first_pairs_i
            /KeygenUniformXofLeafSpec.uniform_block_pairs_i.
    smt().
  move=> *.
  rewrite W64.ultE W64.of_uintK
          /KeygenUniformXofLeafSpec.uniform_poly_words_i /=.
  smt().
+ wp.
  call uniform_consume8192_ll.
  wp.
  call TargetKeygenShakeStream.squeeze128_ll.
  wp.
  call TargetKeygenShakeStream.squeeze128_ll.
  wp.
  call TargetKeygenShakeStream.squeeze128_ll.
  wp.
  call TargetKeygenShakeStream.squeeze128_ll.
  wp.
  call TargetKeygenShakeStream.shake128_init_seedbuf_ll.
  by auto.
qed.

end TargetKeygenUniformXofLeaf.
