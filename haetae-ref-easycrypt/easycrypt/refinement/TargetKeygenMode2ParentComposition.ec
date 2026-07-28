require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import
  KeygenMode2ParentTarget
  KeygenMode2ParentSpec KeygenSeedXofSpec KeygenSamplerCallersSpec
  KeygenUniformXofLeafSpec KeygenEtaSamplerSpec
  TargetKeygenKeccak1600 TargetKeygenMode2Parent.

theory TargetKeygenMode2ParentComposition.

module Sampler = KeygenSamplerCallersTarget.M.
module Parent = KeygenMode2ParentTarget.M.

lemma kp_expand_seedbuf_all_correct
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  hoare [Parent._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.output_matches res seed0 /\
    KeygenSeedXofSpec.uniform_seed_slice_matches res seed0 /\
    KeygenSeedXofSpec.eta_seed_slice_matches res seed0 /\
    KeygenSeedXofSpec.key_seed_slice_matches res seed0].
proof.
conseq (TargetKeygenMode2Parent.kp_expand_seedbuf_correct out0 seed0).
move=> &hr hpre result hmatches.
do split.
+ exact hmatches.
+ exact (KeygenSeedXofSpec.output_matches_uniform_slice
    result seed0 hmatches).
+ exact (KeygenSeedXofSpec.output_matches_eta_slice
    result seed0 hmatches).
+ exact (KeygenSeedXofSpec.output_matches_key_slice
    result seed0 hmatches).
qed.

lemma sampler_kp_expand_seedbuf_ll :
  islossless Sampler._kp_expand_seedbuf.
proof.
proc.
while (W64.to_uint idx <= 128) (128 - W64.to_uint idx).
+ move=> z.
  auto => /> &hr hidx hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  smt().
wp.
call TargetKeygenKeccak1600.keccakf1600_ll.
wp.
call (_ : true); first by auto.
wp.
while (W64.to_uint pos <= 32) (32 - W64.to_uint pos).
+ move=> z.
  auto => /> &hr hpos hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  smt().
wp.
call TargetKeygenKeccak1600.keccak_init_state_ll.
auto => />.
move=> pos; split.
+ move=> hpos hvariant.
  rewrite W64.ultE W64.of_uintK /=.
  smt(W64.to_uint_cmp).
+ move=> hdone hpos idx hidx hvariant.
  rewrite W64.ultE W64.of_uintK /=.
  smt(W64.ultE W64.to_uint_cmp).
qed.

lemma parent_kp_expand_seedbuf_ll :
  islossless Parent._kp_expand_seedbuf.
proof.
conseq TargetKeygenMode2Parent.kp_expand_seedbuf_cross_equiv
       sampler_kp_expand_seedbuf_ll => //=.
move=> &1.
exists (outp{1}, seedp{1}) => />.
qed.

lemma parent_kp_expand_seedbuf_output_matches_pr
    (out0 : BArray128.t) (seed0 : BArray32.t) :
  phoare [Parent._kp_expand_seedbuf :
    outp = out0 /\ seedp = seed0
    ==>
    KeygenSeedXofSpec.output_matches res seed0] = 1%r.
proof.
conseq parent_kp_expand_seedbuf_ll
       (TargetKeygenMode2Parent.kp_expand_seedbuf_correct out0 seed0)
  => //=.
qed.

lemma mode2_matrix_uniform_leaf_ll
    (seed0 : BArray128.t) (mat_limit : int -> int -> int) row col :
  phoare [Parent._kp_poly_uniform_at_seedbuf_8192 :
    seedp = seed0 /\
    seedoff =
      W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
    nonce = KeygenSamplerCallersSpec.matrix_nonce_word row col /\
    base = KeygenSamplerCallersSpec.matrix_base_word
      KeygenSamplerCallersSpec.mode2_m_i row col /\
    0 <= row < KeygenSamplerCallersSpec.mode2_k_i /\
    0 <= col < KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenMode2ParentSpec.mode2_matrix_uniform_progress seed0 mat_limit
    ==> true] = 1%r.
proof.
conseq (TargetKeygenMode2Parent.uniform8192_leaf_progress_ll
  seed0
  (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
  (KeygenSamplerCallersSpec.matrix_nonce_word row col)
  (KeygenSamplerCallersSpec.matrix_base_i
    KeygenSamplerCallersSpec.mode2_m_i row col)
  (mat_limit row col)) => //=.
move=> &hr
  [hseed [hseedoff [hnonce [hbase [hrow [hcol hprogress]]]]]].
have hcapacity :=
  KeygenSamplerCallersSpec.matrix_capacity
    KeygenSamplerCallersSpec.mode2_k_i
    KeygenSamplerCallersSpec.mode2_m_i row col _ _ _ hrow hcol.
+ by rewrite /KeygenSamplerCallersSpec.mode2_k_i.
+ by rewrite /KeygenSamplerCallersSpec.mode2_m_i.
+ by rewrite /KeygenSamplerCallersSpec.mode2_k_i
              /KeygenSamplerCallersSpec.mode2_m_i.
case: hcapacity => hbase0 hbaselast.
have hbaseuint :
    W64.to_uint
      (KeygenSamplerCallersSpec.matrix_base_word
        KeygenSamplerCallersSpec.mode2_m_i row col) =
      KeygenSamplerCallersSpec.matrix_base_i
        KeygenSamplerCallersSpec.mode2_m_i row col.
+ apply KeygenSamplerCallersSpec.matrix_base_word_uint.
  split; first exact hbase0.
  rewrite /KeygenSamplerCallersSpec.mode2_k_i in hrow.
  rewrite /KeygenSamplerCallersSpec.mode2_m_i in hcol.
  smt(W64.to_uint_cmp).
have hcert :=
  KeygenMode2ParentSpec.mode2_matrix_uniform_progress_at
    seed0 mat_limit row col hprogress hrow hcol.
rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
        /KeygenUniformXofLeafSpec.uniform_sufficient_prefix in hcert.
case: hcert => [[hlimit hsize] hstep].
do split.
+ exact hseed.
+ exact hseedoff.
+ exact hnonce.
+ by rewrite hbase hbaseuint.
+ rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
           /BArray32768.size.
  smt().
+ rewrite /KeygenSamplerCallersSpec.uniform_seed_offset_i
           /BArray128.size.
  smt().
+ exact hsize.
+ exact hstep.
qed.

lemma mode2_matrix_uniform_progress_ll
    (seed0 : BArray128.t) (mat_limit : int -> int -> int) :
  phoare [Parent._kp_polymatkm_expand_matA :
    seedp = seed0 /\
    rows = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
    cols = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenMode2ParentSpec.mode2_matrix_uniform_progress seed0 mat_limit
    ==> true] = 1%r.
proof.
proc.
while
  (seedp = seed0 /\
   rows = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
   cols = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
   KeygenMode2ParentSpec.mode2_matrix_uniform_progress seed0 mat_limit /\
   seedoff =
     W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
   0 <= W64.to_uint i <= KeygenSamplerCallersSpec.mode2_k_i /\
   rowbase =
     W64.of_int
       (W64.to_uint i * KeygenSamplerCallersSpec.mode2_m_i))
  (KeygenSamplerCallersSpec.mode2_k_i - W64.to_uint i).
+ move=> z.
  exlim i => i_outer.
  wp.
  while
    (seedp = seed0 /\
     rows = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
     cols = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
     KeygenMode2ParentSpec.mode2_matrix_uniform_progress seed0 mat_limit /\
     seedoff =
       W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
     i = i_outer /\
     0 <= W64.to_uint i < KeygenSamplerCallersSpec.mode2_k_i /\
     0 <= W64.to_uint j <= KeygenSamplerCallersSpec.mode2_m_i /\
     rowbase =
       W64.of_int
         (W64.to_uint i * KeygenSamplerCallersSpec.mode2_m_i))
    (KeygenSamplerCallersSpec.mode2_m_i - W64.to_uint j).
  + move=> zinner.
    wp.
    exlim i => i_before.
    exlim j => j_before.
    call (mode2_matrix_uniform_leaf_ll
      seed0 mat_limit (W64.to_uint i_before) (W64.to_uint j_before)).
    auto => />.
    move=> hprogress hi0 hilt hj0 hjle hguard.
    have hjlt :
        W64.to_uint j_before < KeygenSamplerCallersSpec.mode2_m_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    split.
    + split.
      - by rewrite KeygenSamplerCallersSpec.matrix_nonce_wordE
                   !W64.to_uintK'.
      - split.
        * by rewrite KeygenSamplerCallersSpec.matrix_base_wordE
                     !W64.to_uintK'.
        * exact hjlt.
    move=> _ _ _.
    rewrite /SLH64.protect_64 /SLH64.protect_ptr.
    have hj_succ :
        W64.to_uint (j_before + W64.one) =
          W64.to_uint j_before + 1
      by rewrite W64.to_uintD_small 1:/#.
    rewrite hj_succ.
    smt().
  wp.
  auto => />.
  move=> hprogress_outer hi0 hile hguard.
  have hilt :
      W64.to_uint i_outer < KeygenSamplerCallersSpec.mode2_k_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  split; first exact hilt.
  move=> j0.
  split.
  + move=> hi0' hilt' hj0 hjle hvariant.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  + move=> hnotguard hi0' hilt' hj0 hjle.
    have hj_eq :
        W64.to_uint j0 = KeygenSamplerCallersSpec.mode2_m_i.
    + rewrite W64.ultE W64.of_uintK /= in hnotguard.
      smt(W64.to_uint_cmp).
    have hi_succ :
        W64.to_uint (i_outer + W64.one) = W64.to_uint i_outer + 1
      by rewrite W64.to_uintD_small 1:/#.
    rewrite hi_succ.
    split.
    + split; first smt().
      congr.
      ring.
    + smt().
wp.
auto => />.
move=> i0 hi hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma mode2_vector_uniform_leaf_ll
    (seed0 : BArray128.t) (vec_limit : int -> int) slot :
  phoare [Parent._kp_poly_uniform_at_seedbuf_2048 :
    seedp = seed0 /\
    seedoff =
      W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
    nonce = KeygenSamplerCallersSpec.vector_nonce_word
      KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i slot /\
    W64.to_uint base =
      KeygenSamplerCallersSpec.uniform_vector_words_i slot /\
    0 <= slot < KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenMode2ParentSpec.mode2_vector_uniform_progress seed0 vec_limit
    ==> true] = 1%r.
proof.
conseq (TargetKeygenMode2Parent.uniform2048_leaf_progress_ll
  seed0
  (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
  (KeygenSamplerCallersSpec.vector_nonce_word
    KeygenSamplerCallersSpec.mode2_k_i
    KeygenSamplerCallersSpec.mode2_m_i slot)
  (KeygenSamplerCallersSpec.uniform_vector_words_i slot)
  (vec_limit slot)) => //=.
move=> &hr [hseed [hseedoff [hnonce [hbase [hslot hprogress]]]]].
have hcert :=
  KeygenMode2ParentSpec.mode2_vector_uniform_progress_at
    seed0 vec_limit slot hprogress hslot.
rewrite /KeygenUniformXofLeafSpec.uniform_progress_prefix
        /KeygenUniformXofLeafSpec.uniform_sufficient_prefix in hcert.
case: hcert => [[hlimit hsize] hstep].
do split.
+ exact hseed.
+ exact hseedoff.
+ exact hnonce.
+ exact hbase.
+ rewrite /KeygenSamplerCallersSpec.uniform_vector_words_i
           /KeygenUniformXofLeafSpec.uniform_poly_words_i
           /BArray8192.size.
  smt().
+ rewrite /KeygenSamplerCallersSpec.uniform_seed_offset_i
           /BArray128.size.
  smt().
+ exact hsize.
+ exact hstep.
qed.

lemma mode2_expand_vecA_progress_ll
    (seed0 : BArray128.t) (vec_limit : int -> int) :
  phoare [Parent._kp_polyveck_expand_vecA :
    seedp = seed0 /\
    k = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
    m = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenMode2ParentSpec.mode2_vector_uniform_progress
      seed0 vec_limit
    ==> true] = 1%r.
proof.
proc.
while
  (seedp = seed0 /\
   k = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
   m = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
   KeygenMode2ParentSpec.mode2_vector_uniform_progress
     seed0 vec_limit /\
   seedoff =
     W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i /\
   0 <= W64.to_uint i <= KeygenSamplerCallersSpec.mode2_k_i /\
   W64.to_uint base =
     KeygenSamplerCallersSpec.uniform_vector_words_i (W64.to_uint i) /\
   nonce = KeygenSamplerCallersSpec.vector_nonce_word
     KeygenSamplerCallersSpec.mode2_k_i
     KeygenSamplerCallersSpec.mode2_m_i (W64.to_uint i))
  (KeygenSamplerCallersSpec.mode2_k_i - W64.to_uint i).
+ move=> z.
  wp.
  exlim i => i_before.
  exlim base => base_before.
  call (mode2_vector_uniform_leaf_ll
    seed0 vec_limit (W64.to_uint i_before)).
  auto => />.
  move=> hprogress hi0 hile hbase hguard.
  have hilt :
      W64.to_uint i_before <
        KeygenSamplerCallersSpec.mode2_k_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hslot :
      0 <= W64.to_uint i_before <
        KeygenSamplerCallersSpec.mode2_k_i by smt().
  split.
  + smt().
  move=> _.
  rewrite /SLH64.protect_64 /SLH64.protect_ptr.
  have hi_succ :
      W64.to_uint (i_before + W64.one) =
        W64.to_uint i_before + 1
    by rewrite W64.to_uintD_small 1:/#.
  have hbase_succ :
      W64.to_uint (base_before + W64.of_int 256) =
      KeygenSamplerCallersSpec.uniform_vector_words_i
        (W64.to_uint i_before + 1).
  + rewrite W64.to_uintD_small 1:/#.
    rewrite W64.to_uint_small 1:/# hbase
            KeygenSamplerCallersSpec.uniform_vector_words_i_succ
            /KeygenUniformXofLeafSpec.uniform_poly_words_i.
    ring.
  have hvariant_succ :
      KeygenSamplerCallersSpec.mode2_k_i -
        W64.to_uint (i_before + W64.one) <
      KeygenSamplerCallersSpec.mode2_k_i -
        W64.to_uint i_before
    by rewrite hi_succ; smt().
  do split.
  + smt().
  + rewrite hi_succ; smt().
  + rewrite hi_succ; exact hbase_succ.
  + rewrite hi_succ KeygenSamplerCallersSpec.vector_nonce_word_next; trivial.
  + exact hvariant_succ.
auto => />.
move=> _.
split.
+ by rewrite KeygenSamplerCallersSpec.vector_nonce_wordE W64.addr0_s.
+ move=> base0 i0 hi0 hile hbase hvariant.
  rewrite W64.ultE W64.of_uintK /=.
  smt(W64.to_uint_cmp).
qed.

lemma mode2_eta_first_attempt_leaf_ll
    (seed0 : BArray128.t) (eta_limit : int -> int)
    global_slot local_slot :
  phoare [Parent._kp_poly_uniform_eta_at_seedbuf_2048 :
    seedp = seed0 /\
    seedoff =
      W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i /\
    nonce = W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i 0 global_slot) /\
    base = KeygenSamplerCallersSpec.linear_base_word local_slot /\
    0 <= global_slot < KeygenSamplerCallersSpec.mode2_retry_span_i /\
    0 <= local_slot < 8 /\
    KeygenMode2ParentSpec.mode2_first_attempt_eta_progress
      seed0 eta_limit
    ==> true] = 1%r.
proof.
conseq (TargetKeygenMode2Parent.eta2048_leaf_progress_ll
  seed0
  (W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i)
  (W64.of_int
    (KeygenSamplerCallersSpec.mode2_eta_nonce_i 0 global_slot))
  (KeygenSamplerCallersSpec.linear_base_i local_slot)
  (eta_limit global_slot)) => //=.
move=> &hr
  [hseed [hseedoff [hnonce [hbase [hglobal [hlocal hprogress]]]]]].
have hcapacity :=
  KeygenSamplerCallersSpec.linear_capacity 8 local_slot _ hlocal.
+ by smt().
case: hcapacity => hbase0 hbaselast.
have hbaseuint :
    W64.to_uint (KeygenSamplerCallersSpec.linear_base_word local_slot) =
      KeygenSamplerCallersSpec.linear_base_i local_slot.
+ rewrite /KeygenSamplerCallersSpec.linear_base_word.
  apply W64.to_uint_small.
  split; first exact hbase0.
  smt(W64.to_uint_cmp).
have hcert :=
  KeygenMode2ParentSpec.mode2_first_attempt_eta_progress_at
    seed0 eta_limit global_slot hprogress hglobal.
rewrite /KeygenEtaSamplerSpec.eta_progress_prefix
        /KeygenEtaSamplerSpec.eta_sufficient_prefix in hcert.
case: hcert => [[hlimit hsize] hstep].
do split.
+ exact hseed.
+ exact hseedoff.
+ exact hnonce.
+ by rewrite hbase hbaseuint.
+ rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
           /BArray8192.size.
  smt().
+ rewrite /KeygenSamplerCallersSpec.eta_seed_offset_i
           /BArray128.size.
  smt().
+ exact hsize.
+ exact hstep.
qed.

lemma mode2_eta_segment_progress_ll
    (seed0 : BArray128.t) (eta_limit : int -> int)
    start_slot count_i :
  phoare [Parent._kp_polyvec_expand_eta :
    seedp = seed0 /\
    nonce = W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i 0 start_slot) /\
    count = W64.of_int count_i /\
    0 <= start_slot /\
    0 <= count_i <= 8 /\
    start_slot + count_i <=
      KeygenSamplerCallersSpec.mode2_retry_span_i /\
    KeygenMode2ParentSpec.mode2_first_attempt_eta_progress
      seed0 eta_limit
    ==> true] = 1%r.
proof.
proc.
while
  (seedp = seed0 /\
   count = W64.of_int count_i /\
   0 <= start_slot /\
   0 <= count_i <= 8 /\
   start_slot + count_i <=
     KeygenSamplerCallersSpec.mode2_retry_span_i /\
   KeygenMode2ParentSpec.mode2_first_attempt_eta_progress
     seed0 eta_limit /\
   seedoff =
     W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i /\
   0 <= W64.to_uint i <= count_i /\
   base =
     KeygenSamplerCallersSpec.linear_base_word (W64.to_uint i) /\
   nonce = W64.of_int
     (KeygenSamplerCallersSpec.mode2_eta_nonce_i
       0 (start_slot + W64.to_uint i)))
  (count_i - W64.to_uint i).
+ move=> z.
  wp.
  exlim i => i_before.
  call (mode2_eta_first_attempt_leaf_ll
    seed0 eta_limit
    (start_slot + W64.to_uint i_before)
    (W64.to_uint i_before)).
  auto => />.
  move=> hstart0 hcount0 hcountle hspan hprogress
          hi0 hile hguard.
  have hilt : W64.to_uint i_before < count_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hglobal :
      0 <= start_slot + W64.to_uint i_before <
        KeygenSamplerCallersSpec.mode2_retry_span_i by smt().
  have hlocal :
      0 <= W64.to_uint i_before < 8 by smt().
  split.
  + smt().
  move=> _.
  rewrite /SLH64.protect_64 /SLH64.protect_ptr.
  have hi_succ :
      W64.to_uint (i_before + W64.one) =
        W64.to_uint i_before + 1
    by rewrite W64.to_uintD_small 1:/#.
  have hbase_succ :
      KeygenSamplerCallersSpec.linear_base_word
        (W64.to_uint i_before) + W64.of_int 256 =
        KeygenSamplerCallersSpec.linear_base_word
          (W64.to_uint i_before + 1).
  + by rewrite KeygenSamplerCallersSpec.linear_base_word_next.
  have hnonce_succ :
      W64.of_int
        (KeygenSamplerCallersSpec.mode2_eta_nonce_i
          0 (start_slot + W64.to_uint i_before)) +
        W64.of_int 1 =
      W64.of_int
        (KeygenSamplerCallersSpec.mode2_eta_nonce_i
          0 (start_slot + W64.to_uint i_before + 1)).
  + rewrite /KeygenSamplerCallersSpec.mode2_eta_nonce_i
            /KeygenSamplerCallersSpec.mode2_retry_counter_i
            /KeygenSamplerCallersSpec.mode2_retry_span_i
            -W64.of_intD.
    by congr; ring.
  have hvariant_succ :
      count_i - W64.to_uint (i_before + W64.one) <
        count_i - W64.to_uint i_before
    by rewrite hi_succ; smt().
  smt().
auto => />.
move=> hstart0 hcount0 hcountle hspan hprogress.
rewrite /KeygenSamplerCallersSpec.mode2_eta_nonce_i
        /KeygenSamplerCallersSpec.mode2_retry_counter_i.
move=> i0 hi0 hile hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma mode2_eta_nonce0_count3_progress_ll
    (seed0 : BArray128.t) (eta_limit : int -> int) :
  phoare [Parent._kp_polyvec_expand_eta :
    seedp = seed0 /\
    nonce = W64.of_int 0 /\
    count = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenMode2ParentSpec.mode2_first_attempt_eta_progress
      seed0 eta_limit
    ==> true] = 1%r.
proof.
conseq (mode2_eta_segment_progress_ll
  seed0 eta_limit 0 KeygenSamplerCallersSpec.mode2_m_i) => //=.
qed.

lemma mode2_eta_nonce3_count2_progress_ll
    (seed0 : BArray128.t) (eta_limit : int -> int) :
  phoare [Parent._kp_polyvec_expand_eta :
    seedp = seed0 /\
    nonce = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
    count = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenMode2ParentSpec.mode2_first_attempt_eta_progress
      seed0 eta_limit
    ==> true] = 1%r.
proof.
conseq (mode2_eta_segment_progress_ll
  seed0 eta_limit
  KeygenSamplerCallersSpec.mode2_m_i
  KeygenSamplerCallersSpec.mode2_k_i) => //=.
qed.

(* This is a proof-only sampler-prefix observer.  It calls procedures from
   the actual parent module, but it is not [Parent._keypair_full_m23].  In
   particular, it stops before [_kp_m23_matrix] and the singularity retry. *)
module CheckedMode2ParentSamplerPrefix = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       raw_seed : BArray32.t)
      : BArray128.t * BArray32768.t * BArray8192.t *
        BArray8192.t * BArray8192.t * W64.t = {
    var counter : W64.t;
    var nonce : W64.t;

    seedbuf <@ Parent._kp_expand_seedbuf (seedbuf, raw_seed);
    mat <@ Parent._kp_polymatkm_expand_matA
      (mat, seedbuf,
       W64.of_int KeygenSamplerCallersSpec.mode2_k_i,
       W64.of_int KeygenSamplerCallersSpec.mode2_m_i);
    avec <@ Parent._kp_polyveck_expand_vecA
      (avec, seedbuf,
       W64.of_int KeygenSamplerCallersSpec.mode2_k_i,
       W64.of_int KeygenSamplerCallersSpec.mode2_m_i);
    counter <- W64.of_int 0;
    s1 <@ Parent._kp_polyvec_expand_eta
      (s1, seedbuf, counter,
       W64.of_int KeygenSamplerCallersSpec.mode2_m_i);
    nonce <- counter;
    nonce <- nonce + W64.of_int KeygenSamplerCallersSpec.mode2_m_i;
    s2 <@ Parent._kp_polyvec_expand_eta
      (s2, seedbuf, nonce,
       W64.of_int KeygenSamplerCallersSpec.mode2_k_i);
    counter <- counter + W64.of_int KeygenSamplerCallersSpec.mode2_m_i;
    counter <- counter + W64.of_int KeygenSamplerCallersSpec.mode2_k_i;
    return (seedbuf, mat, avec, s1, s2, counter);
  }
}.

lemma checked_mode2_parent_sampler_prefix_correct
    seedbuf0 mat0 avec0 s10 s20 (raw_seed0 : BArray32.t) :
  hoare [CheckedMode2ParentSamplerPrefix.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ raw_seed = raw_seed0
    ==>
    KeygenSeedXofSpec.output_matches res.`1 raw_seed0 /\
    KeygenSeedXofSpec.uniform_seed_slice_matches res.`1 raw_seed0 /\
    KeygenSeedXofSpec.eta_seed_slice_matches res.`1 raw_seed0 /\
    KeygenSeedXofSpec.key_seed_slice_matches res.`1 raw_seed0 /\
    KeygenSamplerCallersSpec.uniform_matrix_stream32768
      res.`2 res.`1 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.uniform_matrix_range32768
      res.`2 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.uniform_matrix_frame32768
      mat0 res.`2 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.uniform_vector_stream8192
      res.`3 res.`1 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i
        KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.uniform_vector_range8192
      res.`3 KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.uniform_vector_frame8192
      avec0 res.`3 KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.eta_vector_stream8192
      res.`4 res.`1 (W64.of_int 0)
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_centered8192
      res.`4 KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_frame8192
      s10 res.`4 KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_stream8192
      res.`5 res.`1 (W64.of_int KeygenSamplerCallersSpec.mode2_m_i)
        KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.eta_vector_centered8192
      res.`5 KeygenSamplerCallersSpec.mode2_k_i /\
    KeygenSamplerCallersSpec.eta_vector_frame8192
      s20 res.`5 KeygenSamplerCallersSpec.mode2_k_i /\
    res.`6 = W64.of_int KeygenSamplerCallersSpec.mode2_retry_span_i /\
    res.`6 = W64.of_int 5].
proof.
proc.
seq 1 :
  (KeygenSeedXofSpec.output_matches seedbuf raw_seed0 /\
   KeygenSeedXofSpec.uniform_seed_slice_matches seedbuf raw_seed0 /\
   KeygenSeedXofSpec.eta_seed_slice_matches seedbuf raw_seed0 /\
   KeygenSeedXofSpec.key_seed_slice_matches seedbuf raw_seed0 /\
   mat = mat0 /\ avec = avec0 /\ s1 = s10 /\ s2 = s20).
+ call (kp_expand_seedbuf_all_correct seedbuf0 raw_seed0).
  auto => />.
exlim seedbuf => expanded.
wp.
call (TargetKeygenMode2Parent.expand_eta_stream_correct
  s20 expanded
  (W64.of_int KeygenSamplerCallersSpec.mode2_m_i)
  KeygenSamplerCallersSpec.mode2_k_i).
wp.
call (TargetKeygenMode2Parent.expand_eta_stream_correct
  s10 expanded (W64.of_int 0)
  KeygenSamplerCallersSpec.mode2_m_i).
wp.
call (TargetKeygenMode2Parent.expand_vecA_stream_correct
  avec0 expanded KeygenSamplerCallersSpec.mode2_k_i
    KeygenSamplerCallersSpec.mode2_m_i).
wp.
call (TargetKeygenMode2Parent.expand_matA_stream_correct
  mat0 expanded KeygenSamplerCallersSpec.mode2_k_i
    KeygenSamplerCallersSpec.mode2_m_i).
auto => />.
qed.

lemma checked_mode2_parent_sampler_prefix_progress_ll
    (seedbuf0 : BArray128.t) (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  phoare [CheckedMode2ParentSamplerPrefix.run :
    seedbuf = seedbuf0 /\ raw_seed = raw_seed0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit
    ==> true] = 1%r.
proof.
proc.
seq 1 :
  (KeygenSeedXofSpec.output_matches seedbuf raw_seed0 /\
   KeygenMode2ParentSpec.mode2_matrix_uniform_progress
     seedbuf mat_limit /\
   KeygenMode2ParentSpec.mode2_vector_uniform_progress
     seedbuf vec_limit /\
   KeygenMode2ParentSpec.mode2_first_attempt_eta_progress
     seedbuf eta_limit)
  1%r 1%r 0%r _ => //=.
+ call (parent_kp_expand_seedbuf_output_matches_pr seedbuf0 raw_seed0).
  auto => /> hprogress hmatches.
  rewrite /KeygenMode2ParentSpec.mode2_sampler_prefix_progress
    in hprogress.
  by apply hprogress.
exlim seedbuf => expanded.
wp.
call (mode2_eta_nonce3_count2_progress_ll expanded eta_limit).
wp.
call (mode2_eta_nonce0_count3_progress_ll expanded eta_limit).
wp.
call (mode2_expand_vecA_progress_ll expanded vec_limit).
wp.
call (mode2_matrix_uniform_progress_ll expanded mat_limit).
auto => />.
hoare.
call (kp_expand_seedbuf_all_correct seedbuf0 raw_seed0).
auto => /> hprogress hmatches *.
rewrite /KeygenMode2ParentSpec.mode2_sampler_prefix_progress
  in hprogress.
by apply hprogress.
qed.

end TargetKeygenMode2ParentComposition.
