require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import
  KeygenSamplerCallersTarget KeygenMode2ParentTarget
  KeygenSeedXofSpec KeygenSamplerCallersSpec
  KeygenUniformXofLeafSpec KeygenEtaSamplerSpec
  TargetKeygenSeedXof TargetKeygenSamplerCallers
  TargetKeygenUniformXofLeaf TargetKeygenEtaSampler.

theory TargetKeygenMode2Parent.

module Sampler = KeygenSamplerCallersTarget.M.
module Parent = KeygenMode2ParentTarget.M.

lemma kp_expand_seedbuf_cross_equiv :
  equiv [Parent._kp_expand_seedbuf ~ Sampler._kp_expand_seedbuf :
    ={outp, seedp} ==> ={res}].
proof.
proc.
sim.
qed.

lemma uniform8192_leaf_cross_equiv :
  equiv [Parent._kp_poly_uniform_at_seedbuf_8192 ~
         Sampler._kp_poly_uniform_at_seedbuf_8192 :
    ={ap, base, seedp, seedoff, nonce} ==> ={res}].
proof.
proc.
sim.
qed.

lemma uniform2048_leaf_cross_equiv :
  equiv [Parent._kp_poly_uniform_at_seedbuf_2048 ~
         Sampler._kp_poly_uniform_at_seedbuf_2048 :
    ={ap, base, seedp, seedoff, nonce} ==> ={res}].
proof.
proc.
sim.
qed.

lemma eta2048_leaf_cross_equiv :
  equiv [Parent._kp_poly_uniform_eta_at_seedbuf_2048 ~
         Sampler._kp_poly_uniform_eta_at_seedbuf_2048 :
    ={ap, base, seedp, seedoff, nonce} ==> ={res}].
proof.
proc.
sim.
qed.

lemma expand_matA_cross_equiv :
  equiv [Parent._kp_polymatkm_expand_matA ~
         Sampler._kp_polymatkm_expand_matA :
    ={matp, seedp, rows, cols} ==> ={res}].
proof.
proc.
sim.
qed.

lemma expand_vecA_cross_equiv :
  equiv [Parent._kp_polyveck_expand_vecA ~
         Sampler._kp_polyveck_expand_vecA :
    ={vp, seedp, k, m} ==> ={res}].
proof.
proc.
sim.
qed.

lemma expand_eta_cross_equiv :
  equiv [Parent._kp_polyvec_expand_eta ~
         Sampler._kp_polyvec_expand_eta :
    ={vp, seedp, nonce, count} ==> ={res}].
proof.
proc.
sim.
qed.

lemma kp_expand_seedbuf_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [Parent._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.output_matches res seed0].
proof.
conseq kp_expand_seedbuf_cross_equiv
  (TargetKeygenSeedXof.kp_expand_seedbuf_correct out0 seed0) => //=.
move=> &1 [hout hseed].
exists (out0, seed0) => />.
qed.

lemma kp_expand_seedbuf_uniform_slice_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [Parent._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.uniform_seed_slice_matches res seed0].
proof.
conseq kp_expand_seedbuf_cross_equiv
  (TargetKeygenSeedXof.kp_expand_seedbuf_uniform_slice_correct
    out0 seed0) => //=.
move=> &1 [hout hseed].
exists (out0, seed0) => />.
qed.

lemma kp_expand_seedbuf_eta_slice_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [Parent._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.eta_seed_slice_matches res seed0].
proof.
conseq kp_expand_seedbuf_cross_equiv
  (TargetKeygenSeedXof.kp_expand_seedbuf_eta_slice_correct
    out0 seed0) => //=.
move=> &1 [hout hseed].
exists (out0, seed0) => />.
qed.

lemma kp_expand_seedbuf_key_slice_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [Parent._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.key_seed_slice_matches res seed0].
proof.
conseq kp_expand_seedbuf_cross_equiv
  (TargetKeygenSeedXof.kp_expand_seedbuf_key_slice_correct
    out0 seed0) => //=.
move=> &1 [hout hseed].
exists (out0, seed0) => />.
qed.

lemma expand_matA_stream_correct
    mat0 (seed0 : BArray128.t) rows_i cols_i :
  hoare [Parent._kp_polymatkm_expand_matA :
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
conseq expand_matA_cross_equiv
  (TargetKeygenSamplerCallers.expand_matA_stream_correct
    mat0 seed0 rows_i cols_i) => //=.
move=> &1 [hmat [hseed hpre]].
exists (mat0, seed0, rows{1}, cols{1}) => />.
qed.

lemma expand_vecA_stream_correct
    vp0 (seed0 : BArray128.t) k_i m_i :
  hoare [Parent._kp_polyveck_expand_vecA :
    vp = vp0 /\ seedp = seed0 /\
    W64.to_uint k = k_i /\ W64.to_uint m = m_i /\
    0 <= k_i <= 8
    ==>
    KeygenSamplerCallersSpec.uniform_vector_stream8192
      res seed0 k_i m_i k_i /\
    KeygenSamplerCallersSpec.uniform_vector_range8192 res k_i /\
    KeygenSamplerCallersSpec.uniform_vector_frame8192 vp0 res k_i].
proof.
conseq expand_vecA_cross_equiv
  (TargetKeygenSamplerCallers.expand_vecA_stream_correct
    vp0 seed0 k_i m_i) => //=.
move=> &1 [hvp [hseed hpre]].
exists (vp0, seed0, k{1}, m{1}) => />.
qed.

lemma expand_eta_stream_correct
    vp0 (seed0 : BArray128.t) (start0 : W64.t) count_i :
  hoare [Parent._kp_polyvec_expand_eta :
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
conseq expand_eta_cross_equiv
  (TargetKeygenSamplerCallers.expand_eta_stream_correct
    vp0 seed0 start0 count_i) => //=.
move=> &1 [hvp [hseed [hnonce hpre]]].
exists (vp0, seed0, start0, count{1}) => />.
qed.

lemma uniform2048_leaf_progress_ll
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i limit :
  phoare [Parent._kp_poly_uniform_at_seedbuf_2048 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size /\
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      seed0 seedoff0 nonce0 limit
    ==> true] = 1%r.
proof.
conseq uniform2048_leaf_cross_equiv
  (TargetKeygenUniformXofLeaf.uniform2048_leaf_progress_ll
    seed0 seedoff0 nonce0 base_i limit) => //=.
move=> &1 [hseed [hseedoff [hnonce hpre]]].
exists (ap{1}, base{1}, seed0, seedoff0, nonce0) => />.
qed.

lemma uniform8192_leaf_progress_ll
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i limit :
  phoare [Parent._kp_poly_uniform_at_seedbuf_8192 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
      BArray32768.size %/ 4 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size /\
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      seed0 seedoff0 nonce0 limit
    ==> true] = 1%r.
proof.
conseq uniform8192_leaf_cross_equiv
  (TargetKeygenUniformXofLeaf.uniform8192_leaf_progress_ll
    seed0 seedoff0 nonce0 base_i limit) => //=.
move=> &1 [hseed [hseedoff [hnonce hpre]]].
exists (ap{1}, base{1}, seed0, seedoff0, nonce0) => />.
qed.

lemma eta2048_leaf_progress_ll
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i limit :
  phoare [Parent._kp_poly_uniform_eta_at_seedbuf_2048 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size /\
    KeygenEtaSamplerSpec.eta_progress_prefix
      seed0 seedoff0 nonce0 limit
    ==> true] = 1%r.
proof.
conseq eta2048_leaf_cross_equiv
  (TargetKeygenEtaSampler.eta2048_leaf_progress_ll
    seed0 seedoff0 nonce0 base_i limit) => //=.
move=> &1 [hseed [hseedoff [hnonce hpre]]].
exists (ap{1}, base{1}, seed0, seedoff0, nonce0) => />.
qed.

end TargetKeygenMode2Parent.
