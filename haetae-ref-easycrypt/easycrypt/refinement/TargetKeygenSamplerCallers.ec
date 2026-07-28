require import AllCore IntDiv CoreMap List Distr Ring StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenSamplerCallersTarget KeygenSamplerCallersSpec
               KeygenUniformXofLeafSpec KeygenEtaSamplerSpec
               KeygenShakeStreamSpec TargetKeygenUniformXofLeaf
               TargetKeygenEtaSampler.

theory TargetKeygenSamplerCallers.

lemma uniform8192_leaf_self_equiv :
  equiv [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192 ~
         KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192 :
    ={arg} ==> ={res}].
proof. by sim. qed.

lemma uniform2048_leaf_self_equiv :
  equiv [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048 ~
         KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048 :
    ={arg} ==> ={res}].
proof. by sim. qed.

lemma eta2048_leaf_self_equiv :
  equiv [KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 ~
         KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 :
    ={arg} ==> ={res}].
proof. by sim. qed.

lemma uniform2048_leaf_stream_frame
    ap0 (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048 :
    ap = ap0 /\ seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size
    ==>
    KeygenUniformXofLeafSpec.bounded_prefix8192
      res base_i KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    (exists blocks pairs,
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
                seed0 seedoff0 nonce0) blocks) pairs)) /\
    KeygenUniformXofLeafSpec.frame8192 ap0 res base_i].
proof.
conseq
  (TargetKeygenUniformXofLeaf.uniform2048_leaf_stream
    seed0 seedoff0 nonce0 base_i)
  (TargetKeygenUniformXofLeaf.uniform2048_leaf_frame ap0 base_i) => />.
qed.

lemma uniform8192_leaf_stream_frame
    ap0 (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192 :
    ap = ap0 /\ seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size
    ==>
    KeygenUniformXofLeafSpec.bounded_prefix32768
      res base_i KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    (exists blocks pairs,
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
                seed0 seedoff0 nonce0) blocks) pairs)) /\
    KeygenUniformXofLeafSpec.frame32768 ap0 res base_i].
proof.
conseq
  (TargetKeygenUniformXofLeaf.uniform8192_leaf_stream
    seed0 seedoff0 nonce0 base_i)
  (TargetKeygenUniformXofLeaf.uniform8192_leaf_frame ap0 base_i) => />.
qed.

lemma uniform2048_caller_leaf_stream_frame
    ap0 (seed0 : BArray128.t) nonce0 base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048 :
    ap = ap0 /\ seedp = seed0 /\
    seedoff = W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
    nonce = nonce0 /\ W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4
    ==>
    (exists blocks pairs,
      4 <= blocks /\
      0 <= pairs <=
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
      size (KeygenSamplerCallersSpec.caller_uniform_values
        seed0 nonce0 blocks pairs) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      KeygenUniformXofLeafSpec.decoded_prefix8192
        res base_i
          (KeygenSamplerCallersSpec.caller_uniform_values
            seed0 nonce0 blocks pairs)) /\
    KeygenUniformXofLeafSpec.frame8192 ap0 res base_i].
proof.
conseq (uniform2048_leaf_stream_frame ap0 seed0
  (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
  nonce0 base_i).
move=> &hr hpre result [hbounded [hstream hframe]].
split; last exact hframe.
case: hstream => blocks pairs hstream.
exists blocks pairs.
rewrite /KeygenSamplerCallersSpec.caller_uniform_values.
exact hstream.
qed.

lemma uniform8192_caller_leaf_stream_frame
    ap0 (seed0 : BArray128.t) nonce0 base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192 :
    ap = ap0 /\ seedp = seed0 /\
    seedoff = W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
    nonce = nonce0 /\ W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4
    ==>
    (exists blocks pairs,
      4 <= blocks /\
      0 <= pairs <=
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
      size (KeygenSamplerCallersSpec.caller_uniform_values
        seed0 nonce0 blocks pairs) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      KeygenUniformXofLeafSpec.decoded_prefix32768
        res base_i
          (KeygenSamplerCallersSpec.caller_uniform_values
            seed0 nonce0 blocks pairs)) /\
    KeygenUniformXofLeafSpec.frame32768 ap0 res base_i].
proof.
conseq (uniform8192_leaf_stream_frame ap0 seed0
  (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
  nonce0 base_i).
move=> &hr hpre result [hbounded [hstream hframe]].
split; last exact hframe.
case: hstream => blocks pairs hstream.
exists blocks pairs.
rewrite /KeygenSamplerCallersSpec.caller_uniform_values.
exact hstream.
qed.

lemma expand_vecA_relative_orchestration_equiv :
  equiv [KeygenSamplerCallersTarget.M._kp_polyveck_expand_vecA ~
         KeygenSamplerCallersSpec.CallerSpec.expand_vecA :
    ={vp, seedp, k, m} ==> ={res}].
proof.
proc.
while (={vp, seedp, k, m} /\
       seedoff{1} = W64.of_int 0 /\
       i{1} = W64.of_int i{2} /\
       base{1} = KeygenSamplerCallersSpec.linear_base_word i{2} /\
       nonce{1} = KeygenSamplerCallersSpec.vector_nonce_word
                    (W64.to_uint k{2}) (W64.to_uint m{2}) i{2} /\
       0 <= i{2} <= W64.to_uint k{2}).
+ wp.
  call uniform2048_leaf_self_equiv.
  wp.
  skip => />.
  rewrite /SLH64.protect_64.
  by smt(KeygenSamplerCallersSpec.linear_base_word_next
         KeygenSamplerCallersSpec.vector_nonce_word_next
         KeygenSamplerCallersSpec.w64_counter_next
         KeygenSamplerCallersSpec.w64_counter_guard W64.to_uint_cmp).
wp.
skip => />.
by smt(KeygenSamplerCallersSpec.vector_nonce_word_zero_words
       KeygenSamplerCallersSpec.w64_counter_guard W64.to_uint_cmp).
qed.

lemma expand_vecA_stream_correct
    vp0 (seed0 : BArray128.t) k_i m_i :
  hoare [KeygenSamplerCallersTarget.M._kp_polyveck_expand_vecA :
    vp = vp0 /\ seedp = seed0 /\
    W64.to_uint k = k_i /\ W64.to_uint m = m_i /\
    0 <= k_i <= 8
    ==>
    KeygenSamplerCallersSpec.uniform_vector_stream8192
      res seed0 k_i m_i k_i /\
    KeygenSamplerCallersSpec.uniform_vector_range8192 res k_i /\
    KeygenSamplerCallersSpec.uniform_vector_frame8192 vp0 res k_i].
proof.
proc.
while (seedp = seed0 /\
       W64.to_uint k = k_i /\ W64.to_uint m = m_i /\
       0 <= W64.to_uint i <= k_i /\
       W64.to_uint base =
         KeygenSamplerCallersSpec.uniform_vector_words_i (W64.to_uint i) /\
       nonce = KeygenSamplerCallersSpec.vector_nonce_word
         k_i m_i (W64.to_uint i) /\
       seedoff =
         W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
       KeygenSamplerCallersSpec.uniform_vector_stream8192
         vp seed0 k_i m_i (W64.to_uint i) /\
       KeygenSamplerCallersSpec.uniform_prefix_frame8192
         vp0 vp
           (KeygenSamplerCallersSpec.uniform_vector_words_i
             (W64.to_uint i)) /\
       0 <= k_i <= 8).
+ wp.
  exlim vp => vp_before.
  exlim base => base_before.
  exlim i => i_before.
  call (uniform2048_caller_leaf_stream_frame
    vp_before seed0
      (KeygenSamplerCallersSpec.vector_nonce_word
        k_i m_i (W64.to_uint i_before))
      (W64.to_uint base_before)).
  auto => />.
  move=> &hr hi0 hile hbase hstream hframe hk0 hk8 hguard.
  have hilt : W64.to_uint i_before < W64.to_uint k{hr}.
  + by rewrite W64.ultE in hguard.
  have hi_succ :
      W64.to_uint (i_before + W64.one) = W64.to_uint i_before + 1
    by rewrite W64.to_uintD_small 1:/#.
  have hnextcap :
      KeygenSamplerCallersSpec.uniform_vector_words_i
        (W64.to_uint i_before + 1) <= BArray8192.size %/ 4.
  + rewrite /KeygenSamplerCallersSpec.uniform_vector_words_i
            /KeygenUniformXofLeafSpec.uniform_poly_words_i.
    rewrite /BArray8192.size.
    smt().
  have hleafcap :
      W64.to_uint base_before +
        KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4.
  + rewrite hbase
            -KeygenSamplerCallersSpec.uniform_vector_words_i_succ.
    exact hnextcap.
  split; first exact hleafcap.
  move=> _ result blocks pairs hblocks hpairs0 hpairsle hsize
          hdecoded hleafframe.
  have hpairs :
      0 <= pairs <=
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i
    by split.
  have hdecoded_current :
      KeygenUniformXofLeafSpec.decoded_prefix8192 result
        (KeygenSamplerCallersSpec.uniform_vector_words_i
          (W64.to_uint i_before))
        (KeygenSamplerCallersSpec.caller_uniform_values seed0
          (KeygenSamplerCallersSpec.vector_nonce_word
            (W64.to_uint k{hr}) (W64.to_uint m{hr})
            (W64.to_uint i_before)) blocks pairs).
  + rewrite hbase in hdecoded.
    exact hdecoded.
  have hframe_current :
      KeygenUniformXofLeafSpec.frame8192 vp_before result
        (KeygenSamplerCallersSpec.uniform_vector_words_i
          (W64.to_uint i_before)).
  + rewrite hbase in hleafframe.
    exact hleafframe.
  have hstream_next :=
    KeygenSamplerCallersSpec.uniform_vector_stream8192_extend
      vp_before result seed0 (W64.to_uint k{hr}) (W64.to_uint m{hr})
      (W64.to_uint i_before)
      blocks pairs hi0 hnextcap hstream hblocks hpairs hsize
      hdecoded_current hframe_current.
  have hframe_next :=
    KeygenSamplerCallersSpec.uniform_prefix_frame8192_extend
      vp0 vp_before result
      (KeygenSamplerCallersSpec.uniform_vector_words_i
        (W64.to_uint i_before)) _ hframe hframe_current.
  + rewrite /KeygenSamplerCallersSpec.uniform_vector_words_i
            /KeygenUniformXofLeafSpec.uniform_poly_words_i.
    smt().
  have hbase_succ :
      W64.to_uint (base_before + W64.of_int 256) =
      KeygenSamplerCallersSpec.uniform_vector_words_i
        (W64.to_uint i_before + 1).
  + rewrite W64.to_uintD_small 1:/#.
    rewrite W64.to_uint_small 1:/# hbase
            KeygenSamplerCallersSpec.uniform_vector_words_i_succ
            /KeygenUniformXofLeafSpec.uniform_poly_words_i.
    ring.
  rewrite /SLH64.protect_64 /SLH64.protect_ptr hi_succ.
  split; first smt().
  split; first exact hbase_succ.
  split.
  + by rewrite KeygenSamplerCallersSpec.vector_nonce_word_next.
  split; first exact hstream_next.
  rewrite KeygenSamplerCallersSpec.uniform_vector_words_i_succ.
  exact hframe_next.
wp.
auto => /> &hr hk0 hk8.
rewrite KeygenSamplerCallersSpec.vector_nonce_word_zero_words.
split.
+ rewrite /KeygenSamplerCallersSpec.uniform_vector_stream8192.
  smt().
smt(W64.ultE
    KeygenSamplerCallersSpec.uniform_vector_stream8192_range).
qed.

lemma expand_eta_relative_orchestration_equiv :
  equiv [KeygenSamplerCallersTarget.M._kp_polyvec_expand_eta ~
         KeygenSamplerCallersSpec.CallerSpec.expand_eta :
    ={vp, seedp, nonce, count} ==> ={res}].
proof.
proc.
while (={vp, seedp, count} /\
       start{2} = nonce{2} /\
       seedoff{1} = W64.of_int 32 /\
       i{1} = W64.of_int i{2} /\
       base{1} = KeygenSamplerCallersSpec.linear_base_word i{2} /\
       nonce{1} = KeygenSamplerCallersSpec.eta_nonce_word start{2} i{2} /\
       0 <= i{2} <= W64.to_uint count{2}).
+ wp.
  call eta2048_leaf_self_equiv.
  wp.
  skip => />.
  smt(KeygenSamplerCallersSpec.w64_counter_guard
      KeygenSamplerCallersSpec.w64_counter_next
      KeygenSamplerCallersSpec.linear_base_word_next
      KeygenSamplerCallersSpec.eta_nonce_word_next
      W64.to_uint_cmp).
wp.
skip => />.
by smt(KeygenSamplerCallersSpec.linear_base_word_zero
       KeygenSamplerCallersSpec.eta_nonce_word_zero
       KeygenSamplerCallersSpec.w64_counter_guard W64.to_uint_cmp).
qed.

lemma eta2048_leaf_stream_frame
    ap0 (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 :
    ap = ap0 /\ seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size
    ==>
    (exists blocks,
      1 <= blocks /\
      size (KeygenEtaSamplerSpec.eta_fill []
        (KeygenShakeStreamSpec.shake256_squeeze_bytes
          (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
            seed0 seedoff0 nonce0) blocks)) =
        KeygenEtaSamplerSpec.eta_poly_words_i /\
      KeygenEtaSamplerSpec.eta_decoded_prefix8192
        res base_i
        (KeygenEtaSamplerSpec.eta_fill []
          (KeygenShakeStreamSpec.shake256_squeeze_bytes
            (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks))) /\
    KeygenEtaSamplerSpec.poly_frame8192 ap0 res base_i].
proof.
conseq
  (TargetKeygenEtaSampler.eta2048_leaf_stream
    seed0 seedoff0 nonce0 base_i)
  (TargetKeygenEtaSampler.eta2048_leaf_frame ap0 base_i) => />.
qed.

lemma eta2048_caller_leaf_stream_frame
    ap0 (seed0 : BArray128.t) (start : W64.t) slot base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 :
    ap = ap0 /\ seedp = seed0 /\
    seedoff = W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i /\
    nonce = KeygenSamplerCallersSpec.eta_nonce_word start slot /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4
    ==>
    (exists blocks,
      1 <= blocks /\
      size (KeygenSamplerCallersSpec.caller_eta_values
        seed0 start slot blocks) =
        KeygenEtaSamplerSpec.eta_poly_words_i /\
      KeygenEtaSamplerSpec.eta_decoded_prefix8192
        res base_i
          (KeygenSamplerCallersSpec.caller_eta_values
            seed0 start slot blocks)) /\
    KeygenEtaSamplerSpec.poly_frame8192 ap0 res base_i].
proof.
conseq (eta2048_leaf_stream_frame ap0 seed0
  (W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i)
  (KeygenSamplerCallersSpec.eta_nonce_word start slot) base_i).
move=> &hr hpre result [hstream hframe].
split; last exact hframe.
case: hstream => blocks hstream.
exists blocks.
rewrite /KeygenSamplerCallersSpec.caller_eta_values.
exact hstream.
qed.

lemma expand_eta_correct vp0 count_i :
  hoare [KeygenSamplerCallersTarget.M._kp_polyvec_expand_eta :
    vp = vp0 /\
    W64.to_uint count = count_i /\
    0 <= count_i /\
    KeygenSamplerCallersSpec.eta_vector_words_i count_i <=
      BArray8192.size %/ 4
    ==>
    KeygenSamplerCallersSpec.eta_vector_centered8192 res count_i /\
    KeygenSamplerCallersSpec.eta_vector_frame8192 vp0 res count_i].
proof.
proc.
while (W64.to_uint count = count_i /\
       0 <= W64.to_uint i <= count_i /\
       W64.to_uint base =
         KeygenSamplerCallersSpec.eta_vector_words_i (W64.to_uint i) /\
       KeygenSamplerCallersSpec.eta_vector_centered8192
         vp (W64.to_uint i) /\
       KeygenSamplerCallersSpec.eta_vector_frame8192
         vp0 vp (W64.to_uint i) /\
       KeygenSamplerCallersSpec.eta_vector_words_i count_i <=
         BArray8192.size %/ 4).
+ wp.
  exlim vp => vp_before.
  exlim base => base_before.
  call (TargetKeygenEtaSampler.eta2048_leaf_correct
          vp_before (W64.to_uint base_before)).
  auto => />.
  move=> &hr hi0 hile hbase hcenter hframe hcapacity hguard.
  have hilt : W64.to_uint i{hr} < W64.to_uint count{hr}.
  + by rewrite W64.ultE in hguard.
  have hcount_le8 : W64.to_uint count{hr} <= 8.
  + rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
            /KeygenEtaSamplerSpec.eta_poly_words_i in hcapacity.
    smt().
  have hi_succ :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1
    by rewrite W64.to_uintD_small 1:/#.
  have hnextcap :
      KeygenSamplerCallersSpec.eta_vector_words_i
        (W64.to_uint i{hr} + 1) <= BArray8192.size %/ 4.
  + rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
            /KeygenEtaSamplerSpec.eta_poly_words_i in hcapacity.
    rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
            /KeygenEtaSamplerSpec.eta_poly_words_i.
    smt().
  have hleafcap :
      W64.to_uint base_before +
        KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4.
  + rewrite hbase
            -KeygenSamplerCallersSpec.eta_vector_words_i_succ.
    exact hnextcap.
  split; first exact hleafcap.
  move=> _ result hleafcenter hleafframe.
  have hbase_succ :
      W64.to_uint (base_before + W64.of_int 256) =
      KeygenSamplerCallersSpec.eta_vector_words_i
        (W64.to_uint i{hr} + 1).
  + rewrite W64.to_uintD_small 1:/#.
    rewrite W64.to_uint_small 1:/# hbase
            KeygenSamplerCallersSpec.eta_vector_words_i_succ
            /KeygenEtaSamplerSpec.eta_poly_words_i.
    ring.
  have hcenter_next :=
    KeygenSamplerCallersSpec.eta_vector_centered8192_extend
      vp_before result (W64.to_uint i{hr}) hi0 hnextcap hcenter _ _.
  + by rewrite -hbase.
  + by rewrite -hbase.
  have hframe_next :=
    KeygenSamplerCallersSpec.eta_vector_frame8192_extend
      vp0 vp_before result (W64.to_uint i{hr}) hi0 hframe _.
  + by rewrite -hbase.
  rewrite /SLH64.protect_64 /SLH64.protect_ptr hi_succ.
  split.
  + smt().
  split; first exact hbase_succ.
  split; first exact hcenter_next.
  exact hframe_next.
wp.
auto => /> &hr hcount_nonneg hcapacity.
split.
+ exact (KeygenSamplerCallersSpec.eta_vector_centered8192_empty vp0).
move=> base0 count0 i0 vp hnotguard hcounteq hi0 hile hbase
        hcenter hframe.
have hi_eq : W64.to_uint i0 = W64.to_uint count{hr}.
+ rewrite W64.ultE in hnotguard.
  smt().
by rewrite -hi_eq.
qed.

lemma expand_eta_stream
    (seed0 : BArray128.t) (start0 : W64.t) count_i :
  hoare [KeygenSamplerCallersTarget.M._kp_polyvec_expand_eta :
    seedp = seed0 /\ nonce = start0 /\
    W64.to_uint count = count_i /\
    0 <= count_i /\
    KeygenSamplerCallersSpec.eta_vector_words_i count_i <=
      BArray8192.size %/ 4
    ==>
    KeygenSamplerCallersSpec.eta_vector_stream8192
      res seed0 start0 count_i].
proof.
proc.
while (seedp = seed0 /\
       W64.to_uint count = count_i /\
       0 <= W64.to_uint i <= count_i /\
       W64.to_uint base =
         KeygenSamplerCallersSpec.eta_vector_words_i (W64.to_uint i) /\
       nonce = KeygenSamplerCallersSpec.eta_nonce_word
         start0 (W64.to_uint i) /\
       seedoff = W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i /\
       KeygenSamplerCallersSpec.eta_vector_stream8192
         vp seed0 start0 (W64.to_uint i) /\
       KeygenSamplerCallersSpec.eta_vector_words_i count_i <=
         BArray8192.size %/ 4).
+ wp.
  exlim vp => vp_before.
  exlim base => base_before.
  exlim i => i_before.
  call (eta2048_caller_leaf_stream_frame
    vp_before seed0 start0 (W64.to_uint i_before)
    (W64.to_uint base_before)).
  auto => />.
  move=> &hr hi0 hile hbase hstream hcapacity hguard.
  have hilt : W64.to_uint i_before < W64.to_uint count{hr}.
  + by rewrite W64.ultE in hguard.
  have hcount_le8 : W64.to_uint count{hr} <= 8.
  + rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
            /KeygenEtaSamplerSpec.eta_poly_words_i in hcapacity.
    smt().
  have hi_succ :
      W64.to_uint (i_before + W64.one) = W64.to_uint i_before + 1
    by rewrite W64.to_uintD_small 1:/#.
  have hnextcap :
      KeygenSamplerCallersSpec.eta_vector_words_i
        (W64.to_uint i_before + 1) <= BArray8192.size %/ 4.
  + rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
            /KeygenEtaSamplerSpec.eta_poly_words_i in hcapacity.
    rewrite /KeygenSamplerCallersSpec.eta_vector_words_i
            /KeygenEtaSamplerSpec.eta_poly_words_i.
    smt().
  have hleafcap :
      W64.to_uint base_before +
        KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4.
  + rewrite hbase
            -KeygenSamplerCallersSpec.eta_vector_words_i_succ.
    exact hnextcap.
  split; first exact hleafcap.
  move=> _ result blocks hblocks hsize hdecoded hleafframe.
  have hdecoded_current :
      KeygenEtaSamplerSpec.eta_decoded_prefix8192
        result
          (KeygenSamplerCallersSpec.eta_vector_words_i
          (W64.to_uint i_before))
        (KeygenSamplerCallersSpec.caller_eta_values
          seed0 start0 (W64.to_uint i_before) blocks).
  + by rewrite -hbase.
  have hframe_current :
      KeygenEtaSamplerSpec.poly_frame8192 vp_before result
        (KeygenSamplerCallersSpec.eta_vector_words_i
          (W64.to_uint i_before)).
  + by rewrite -hbase.
  have hstream_next :=
    KeygenSamplerCallersSpec.eta_vector_stream8192_extend
      vp_before result seed0 start0 (W64.to_uint i_before) blocks
      hi0 hnextcap hstream hblocks hsize hdecoded_current hframe_current.
  have hbase_succ :
      W64.to_uint (base_before + W64.of_int 256) =
      KeygenSamplerCallersSpec.eta_vector_words_i
        (W64.to_uint i_before + 1).
  + rewrite W64.to_uintD_small 1:/#.
    rewrite W64.to_uint_small 1:/# hbase
            KeygenSamplerCallersSpec.eta_vector_words_i_succ
            /KeygenEtaSamplerSpec.eta_poly_words_i.
    ring.
  rewrite /SLH64.protect_64 /SLH64.protect_ptr hi_succ.
  split; first smt().
  split; first exact hbase_succ.
  split.
  + by rewrite KeygenSamplerCallersSpec.eta_nonce_word_next.
  exact hstream_next.
wp.
auto => /> &hr hcount_nonneg hcapacity.
split.
+ exact (KeygenSamplerCallersSpec.eta_vector_stream8192_empty
           vp{hr} seed0 start0).
smt(W64.ultE).
qed.

lemma expand_eta_stream_correct
    vp0 (seed0 : BArray128.t) (start0 : W64.t) count_i :
  hoare [KeygenSamplerCallersTarget.M._kp_polyvec_expand_eta :
    vp = vp0 /\ seedp = seed0 /\ nonce = start0 /\
    W64.to_uint count = count_i /\
    0 <= count_i /\
    KeygenSamplerCallersSpec.eta_vector_words_i count_i <=
      BArray8192.size %/ 4
    ==>
    KeygenSamplerCallersSpec.eta_vector_stream8192
      res seed0 start0 count_i /\
    KeygenSamplerCallersSpec.eta_vector_centered8192 res count_i /\
    KeygenSamplerCallersSpec.eta_vector_frame8192 vp0 res count_i].
proof.
conseq (expand_eta_stream seed0 start0 count_i)
       (expand_eta_correct vp0 count_i) => />.
qed.

(* This proof-only composition mirrors the two eta-vector calls in mode 2.  It
   deliberately does not model the surrounding keypair retry loop. *)
module CheckedMode2EtaPair = {
  proc expand
      (s1 : BArray8192.t, s2 : BArray8192.t,
       seedp : BArray128.t, start : W64.t)
      : BArray8192.t * BArray8192.t * W64.t = {
    var second_start : W64.t;
    var next : W64.t;

    s1 <@ KeygenSamplerCallersTarget.M._kp_polyvec_expand_eta
      (s1, seedp, start,
       W64.of_int KeygenSamplerCallersSpec.mode2_m_i);
    second_start <- KeygenSamplerCallersSpec.eta_nonce_word
      start KeygenSamplerCallersSpec.mode2_m_i;
    s2 <@ KeygenSamplerCallersTarget.M._kp_polyvec_expand_eta
      (s2, seedp, second_start,
       W64.of_int KeygenSamplerCallersSpec.mode2_k_i);
    next <- KeygenSamplerCallersSpec.eta_nonce_word
      second_start KeygenSamplerCallersSpec.mode2_k_i;
    return (s1, s2, next);
  }
}.

lemma checked_mode2_eta_pair_correct
    s10 s20 (seed0 : BArray128.t) (start0 : W64.t) :
  hoare [CheckedMode2EtaPair.expand :
    s1 = s10 /\ s2 = s20 /\ seedp = seed0 /\ start = start0
    ==>
    KeygenSamplerCallersSpec.eta_vector_stream8192
      res.`1 seed0 start0 KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_centered8192
      res.`1 KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_frame8192
      s10 res.`1 KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_stream8192
      res.`2 seed0
        (KeygenSamplerCallersSpec.eta_nonce_word
          start0 KeygenSamplerCallersSpec.mode2_m_i)
        KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.eta_vector_centered8192
      res.`2 KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.eta_vector_frame8192
      s20 res.`2 KeygenSamplerCallersSpec.mode2_k_i /\
    res.`3 = KeygenSamplerCallersSpec.eta_nonce_word
      (KeygenSamplerCallersSpec.eta_nonce_word
        start0 KeygenSamplerCallersSpec.mode2_m_i)
      KeygenSamplerCallersSpec.mode2_k_i /\
    res.`3 = KeygenSamplerCallersSpec.eta_nonce_word
      start0 KeygenSamplerCallersSpec.mode2_retry_span_i /\
    res.`3 = KeygenSamplerCallersSpec.eta_nonce_word start0 5].
proof.
proc.
wp.
call (expand_eta_stream_correct s20 seed0
  (KeygenSamplerCallersSpec.eta_nonce_word
    start0 KeygenSamplerCallersSpec.mode2_m_i)
  KeygenSamplerCallersSpec.mode2_k_i).
wp.
call (expand_eta_stream_correct s10 seed0 start0
  KeygenSamplerCallersSpec.mode2_m_i).
auto => />.
qed.

lemma expand_matA_relative_orchestration_equiv :
  equiv [KeygenSamplerCallersTarget.M._kp_polymatkm_expand_matA ~
         KeygenSamplerCallersSpec.CallerSpec.expand_matA :
    ={matp, seedp, rows, cols} ==> ={res}].
proof.
proc.
while (={matp, seedp, rows, cols} /\
       seedoff{1} = W64.of_int 0 /\
       i{1} = W64.of_int i{2} /\
       rowbase{1} = W64.of_int (i{2} * W64.to_uint cols{2}) /\
       0 <= i{2} <= W64.to_uint rows{2}).
+ wp.
  while (={matp, seedp, rows, cols} /\
         seedoff{1} = W64.of_int 0 /\
         i{1} = W64.of_int i{2} /\
         rowbase{1} = W64.of_int (i{2} * W64.to_uint cols{2}) /\
         j{1} = W64.of_int j{2} /\
         0 <= i{2} < W64.to_uint rows{2} /\
         0 <= j{2} <= W64.to_uint cols{2}).
  + wp.
    call uniform8192_leaf_self_equiv.
    wp.
    skip => />.
    smt(KeygenSamplerCallersSpec.w64_counter_guard
        KeygenSamplerCallersSpec.w64_counter_next
        KeygenSamplerCallersSpec.matrix_nonce_wordE
        KeygenSamplerCallersSpec.matrix_base_wordE
        W64.to_uint_cmp).
  wp.
  skip => />.
  smt(KeygenSamplerCallersSpec.w64_counter_guard
      KeygenSamplerCallersSpec.w64_counter_next
      KeygenSamplerCallersSpec.rowbase_word_next
      W64.to_uint_cmp).
wp.
skip => />.
rewrite /KeygenSamplerCallersSpec.uniform_seed_offset_i.
by smt(KeygenSamplerCallersSpec.w64_counter_guard W64.to_uint_cmp).
qed.

lemma expand_matA_stream_correct
    mat0 (seed0 : BArray128.t) rows_i cols_i :
  hoare [KeygenSamplerCallersTarget.M._kp_polymatkm_expand_matA :
    matp = mat0 /\ seedp = seed0 /\
    W64.to_uint rows = rows_i /\ W64.to_uint cols = cols_i /\
    0 <= rows_i /\ 0 <= cols_i /\ rows_i * cols_i <= 32
    ==>
    KeygenSamplerCallersSpec.uniform_matrix_stream32768
      res seed0 rows_i cols_i /\
    KeygenSamplerCallersSpec.uniform_matrix_range32768
      res rows_i cols_i /\
    KeygenSamplerCallersSpec.uniform_matrix_frame32768
      mat0 res rows_i cols_i].
proof.
proc.
while (seedp = seed0 /\
       W64.to_uint rows = rows_i /\ W64.to_uint cols = cols_i /\
       0 <= W64.to_uint i <= rows_i /\
       W64.to_uint rowbase = W64.to_uint i * W64.to_uint cols /\
       seedoff =
         W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
       KeygenSamplerCallersSpec.uniform_matrix_stream_prefix32768
         matp seed0 rows_i cols_i (W64.to_uint i) 0 /\
       KeygenSamplerCallersSpec.uniform_prefix_frame32768
         mat0 matp
           (KeygenSamplerCallersSpec.matrix_base_i
             cols_i (W64.to_uint i) 0) /\
       0 <= rows_i /\ 0 <= cols_i /\ rows_i * cols_i <= 32).
+ wp.
  while (seedp = seed0 /\
         W64.to_uint rows = rows_i /\ W64.to_uint cols = cols_i /\
         0 <= W64.to_uint i < rows_i /\
         0 <= W64.to_uint j <= cols_i /\
         W64.to_uint rowbase = W64.to_uint i * W64.to_uint cols /\
         seedoff =
           W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
         KeygenSamplerCallersSpec.uniform_matrix_stream_prefix32768
           matp seed0 rows_i cols_i
             (W64.to_uint i) (W64.to_uint j) /\
         KeygenSamplerCallersSpec.uniform_prefix_frame32768
           mat0 matp
             (KeygenSamplerCallersSpec.matrix_base_i
               cols_i (W64.to_uint i) (W64.to_uint j)) /\
         0 <= rows_i /\ 0 <= cols_i /\ rows_i * cols_i <= 32).
  + wp.
    exlim matp => mat_before.
    exlim rowbase => rowbase_before.
    exlim i => i_before.
    exlim j => j_before.
    call (uniform8192_caller_leaf_stream_frame
      mat_before seed0
        ((i_before `<<` (W8.of_int 8)) + j_before)
        (W64.to_uint
          ((rowbase_before + j_before) * W64.of_int 256))).
    wp.
    auto => />.
    move=> &hr hi0 hilt hj0 hjle hrowbase hstream hframe
            hrows0 hcols0 hproduct hguard.
    have hjlt : W64.to_uint j_before < W64.to_uint cols{hr}.
    + by rewrite W64.ultE in hguard.
    have hi_bounds :
        0 <= W64.to_uint i_before < W64.to_uint rows{hr}
      by smt().
    have hj_bounds :
        0 <= W64.to_uint j_before < W64.to_uint cols{hr}
      by smt().
    have hstream_before :
        KeygenSamplerCallersSpec.uniform_matrix_stream_prefix32768
          mat_before seed0 (W64.to_uint rows{hr}) (W64.to_uint cols{hr})
          (W64.to_uint i_before) (W64.to_uint j_before)
      by exact hstream.
    have hprefix_frame :
        KeygenSamplerCallersSpec.uniform_prefix_frame32768
          mat0 mat_before
          (KeygenSamplerCallersSpec.matrix_base_i
            (W64.to_uint cols{hr})
            (W64.to_uint i_before) (W64.to_uint j_before))
      by exact hframe.
    have hj_succ :
        W64.to_uint (j_before + W64.one) = W64.to_uint j_before + 1
      by rewrite W64.to_uintD_small 1:/#.
    have hcellcap :=
      KeygenSamplerCallersSpec.matrix_capacity
        (W64.to_uint rows{hr}) (W64.to_uint cols{hr})
        (W64.to_uint i_before) (W64.to_uint j_before)
        hrows0 hcols0 hproduct _ _.
    + exact hi_bounds.
    + exact hj_bounds.
    case: hcellcap => hbase_nonneg hbase_last.
    have hnonce_eq :
        (i_before `<<` (W8.of_int 8)) + j_before =
        KeygenSamplerCallersSpec.matrix_nonce_word
          (W64.to_uint i_before) (W64.to_uint j_before).
    + rewrite KeygenSamplerCallersSpec.matrix_nonce_wordE.
      by rewrite !W64.to_uintK'.
    have hbase_word :
        (rowbase_before + j_before) * W64.of_int 256 =
        KeygenSamplerCallersSpec.matrix_base_word
          (W64.to_uint cols{hr})
          (W64.to_uint i_before) (W64.to_uint j_before).
    + have hrowbase_word :
          rowbase_before =
          W64.of_int
            (W64.to_uint i_before * W64.to_uint cols{hr}).
      + rewrite -(W64.to_uintK' rowbase_before) hrowbase.
        by [].
      rewrite hrowbase_word KeygenSamplerCallersSpec.matrix_base_wordE.
      by rewrite !W64.to_uintK'.
    have hbase_eq :
        W64.to_uint
          ((rowbase_before + j_before) * W64.of_int 256) =
        KeygenSamplerCallersSpec.matrix_base_i
          (W64.to_uint cols{hr})
          (W64.to_uint i_before) (W64.to_uint j_before).
    + rewrite hbase_word.
      apply KeygenSamplerCallersSpec.matrix_base_word_uint.
      split; first exact hbase_nonneg.
      smt(W64.to_uint_cmp).
    have hleafcap :
        W64.to_uint
          ((rowbase_before + j_before) * W64.of_int 256) +
          KeygenUniformXofLeafSpec.uniform_poly_words_i <=
        BArray32768.size %/ 4.
    + rewrite hbase_eq /KeygenUniformXofLeafSpec.uniform_poly_words_i
              /BArray32768.size.
      smt().
    split; first exact hleafcap.
    move=> _ result blocks pairs hblocks hpairs0 hpairsle hsize
            hdecoded hleafframe.
    have hpairs :
        0 <= pairs <=
          blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i
      by split.
    have hdecoded_current :
        KeygenUniformXofLeafSpec.decoded_prefix32768 result
          (KeygenSamplerCallersSpec.matrix_base_i
            (W64.to_uint cols{hr})
            (W64.to_uint i_before) (W64.to_uint j_before))
          (KeygenSamplerCallersSpec.caller_uniform_values seed0
            (KeygenSamplerCallersSpec.matrix_nonce_word
              (W64.to_uint i_before) (W64.to_uint j_before))
            blocks pairs).
    + rewrite -hbase_eq -hnonce_eq.
      exact hdecoded.
    have hframe_current :
        KeygenUniformXofLeafSpec.frame32768 mat_before result
          (KeygenSamplerCallersSpec.matrix_base_i
            (W64.to_uint cols{hr})
            (W64.to_uint i_before) (W64.to_uint j_before)).
    + by rewrite -hbase_eq.
    have hsize_current :
        size
          (KeygenSamplerCallersSpec.caller_uniform_values seed0
            (KeygenSamplerCallersSpec.matrix_nonce_word
              (W64.to_uint i_before) (W64.to_uint j_before))
            blocks pairs) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i.
    + rewrite -hnonce_eq.
      exact hsize.
    have hstream_next :=
      KeygenSamplerCallersSpec.uniform_matrix_stream_prefix32768_extend
        mat_before result seed0
        (W64.to_uint rows{hr}) (W64.to_uint cols{hr})
        (W64.to_uint i_before) (W64.to_uint j_before)
        blocks pairs hcols0 _ _ _ hstream_before hblocks hpairs hsize_current
        hdecoded_current hframe_current.
    + by split.
    + by split.
    + rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
              /BArray32768.size.
      smt().
    have hframe_next :=
      KeygenSamplerCallersSpec.uniform_prefix_frame32768_extend
        mat0 mat_before result
        (KeygenSamplerCallersSpec.matrix_base_i
          (W64.to_uint cols{hr})
          (W64.to_uint i_before) (W64.to_uint j_before))
        hbase_nonneg hprefix_frame hframe_current.
    rewrite /SLH64.protect_64 /SLH64.protect_ptr hj_succ.
    do split; try assumption.
    + smt().
    + smt().
    + smt().
  wp.
  auto => />.
  move=> &hr hi0 hile hrowbase hstream hframe
          hrows0 hcols0 hproduct hguard.
  have hilt : W64.to_uint i{hr} < W64.to_uint rows{hr}.
  + by rewrite W64.ultE in hguard.
  split.
  + smt().
  move=> cols0 i0 j0 matp0 rowbase0 rows0 seedoff0 seedp0
          hnotguard h0 h1 h2 h3 h4 h5 h6.
  have hj_eq : W64.to_uint j0 = W64.to_uint cols{hr}.
  + smt().
  have hrolled_stream :=
    KeygenSamplerCallersSpec.uniform_matrix_stream_prefix32768_rollover
      matp0 seed0 (W64.to_uint rows{hr}) (W64.to_uint cols{hr})
      (W64.to_uint i0) _.
  + have hstream_end := h5.
    rewrite hj_eq in hstream_end.
    exact hstream_end.
  have hi_lt_rows : W64.to_uint i0 < W64.to_uint rows{hr}.
  + exact h1.
  have hi_succ :
      W64.to_uint (i0 + W64.one) = W64.to_uint i0 + 1.
  + rewrite W64.to_uintD_small.
    + smt(W64.to_uint_cmp).
    by rewrite W64.to_uint1.
  rewrite /SLH64.protect_64 /SLH64.protect_ptr hi_succ.
  split; first smt().
  split.
  + rewrite W64.to_uintD_small 1:/# h4.
    ring.
  split; first exact hrolled_stream.
  have hframe_end := h6.
  rewrite hj_eq in hframe_end.
  rewrite -KeygenSamplerCallersSpec.matrix_base_i_rollover.
  exact hframe_end.
wp.
auto => /> &hr hrows0 hcols0 hproduct.
rewrite /KeygenSamplerCallersSpec.uniform_seed_offset_i.
split.
+ apply KeygenSamplerCallersSpec.uniform_matrix_stream_prefix32768_empty.
smt(W64.ultE
    KeygenSamplerCallersSpec.uniform_matrix_stream32768_range
    KeygenSamplerCallersSpec.uniform_matrix_words_base).
qed.

(* This proof-only composition mirrors the matrix and vector uniform-sampler
   calls in mode 2.  Both calls consume the same raw seed buffer. *)
module CheckedMode2UniformPair = {
  proc expand
      (mat : BArray32768.t, vec : BArray8192.t,
       seedp : BArray128.t)
      : BArray32768.t * BArray8192.t = {
    mat <@ KeygenSamplerCallersTarget.M._kp_polymatkm_expand_matA
      (mat, seedp,
       W64.of_int KeygenSamplerCallersSpec.mode2_k_i,
       W64.of_int KeygenSamplerCallersSpec.mode2_m_i);
    vec <@ KeygenSamplerCallersTarget.M._kp_polyveck_expand_vecA
      (vec, seedp,
       W64.of_int KeygenSamplerCallersSpec.mode2_k_i,
       W64.of_int KeygenSamplerCallersSpec.mode2_m_i);
    return (mat, vec);
  }
}.

lemma checked_mode2_uniform_pair_correct
    mat0 vec0 (seed0 : BArray128.t) :
  hoare [CheckedMode2UniformPair.expand :
    mat = mat0 /\ vec = vec0 /\ seedp = seed0
    ==>
    KeygenSamplerCallersSpec.uniform_matrix_stream32768
      res.`1 seed0 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.uniform_matrix_range32768
      res.`1 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.uniform_matrix_frame32768
      mat0 res.`1 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.uniform_vector_stream8192
      res.`2 seed0 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i
        KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.uniform_vector_range8192
      res.`2 KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.uniform_vector_frame8192
      vec0 res.`2 KeygenSamplerCallersSpec.mode2_k_i].
proof.
proc.
wp.
call (expand_vecA_stream_correct
  vec0 seed0 KeygenSamplerCallersSpec.mode2_k_i
    KeygenSamplerCallersSpec.mode2_m_i).
wp.
call (expand_matA_stream_correct
  mat0 seed0 KeygenSamplerCallersSpec.mode2_k_i
    KeygenSamplerCallersSpec.mode2_m_i).
auto => />.
qed.

end TargetKeygenSamplerCallers.
