require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray128.
require import KeygenMode2ParentTarget
               KeygenMode2ParentSpec
               KeygenSamplerCallersSpec
               KeygenEtaSamplerSpec
               TargetKeygenMode2Parent.

theory Mode2FaithfulSecurityRetryEtaProgressPostFreeze.

module Parent = KeygenMode2ParentTarget.M.

op mode2_retry_eta_nowrap (retry : int) : bool =
  0 <= retry /\
  KeygenSamplerCallersSpec.mode2_eta_nonce_i retry
    (KeygenSamplerCallersSpec.mode2_retry_span_i - 1) < 65536.

op mode2_retry_eta_progress
    (expanded : BArray128.t) (retry : int) (eta_limit : int -> int) : bool =
  forall slot,
    0 <= slot < KeygenSamplerCallersSpec.mode2_retry_span_i =>
    KeygenEtaSamplerSpec.eta_progress_prefix
      expanded
      (W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i)
      (W64.of_int
        (KeygenSamplerCallersSpec.mode2_eta_nonce_i retry slot))
      (eta_limit slot).

lemma mode2_retry_eta_progress_at expanded retry eta_limit slot :
  mode2_retry_eta_progress expanded retry eta_limit =>
  0 <= slot < KeygenSamplerCallersSpec.mode2_retry_span_i =>
  KeygenEtaSamplerSpec.eta_progress_prefix
    expanded
    (W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i)
    (W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i retry slot))
    (eta_limit slot).
proof.
rewrite /mode2_retry_eta_progress.
by move=> hprogress hslot; apply hprogress.
qed.

lemma mode2_retry_eta_nonce_lt65536 retry slot :
  mode2_retry_eta_nowrap retry =>
  0 <= slot < KeygenSamplerCallersSpec.mode2_retry_span_i =>
  KeygenSamplerCallersSpec.mode2_eta_nonce_i retry slot < 65536.
proof.
rewrite /mode2_retry_eta_nowrap.
move=> [hretry htop] hslot.
rewrite /KeygenSamplerCallersSpec.mode2_eta_nonce_i
        /KeygenSamplerCallersSpec.mode2_retry_counter_i
        /KeygenSamplerCallersSpec.mode2_retry_span_i
        /KeygenSamplerCallersSpec.mode2_k_i
        /KeygenSamplerCallersSpec.mode2_m_i.
smt().
qed.

lemma mode2_retry_eta_nonce_w64_range retry slot :
  mode2_retry_eta_nowrap retry =>
  0 <= slot < KeygenSamplerCallersSpec.mode2_retry_span_i =>
  0 <= KeygenSamplerCallersSpec.mode2_eta_nonce_i retry slot < W64.modulus.
proof.
move=> [hretry htop] hslot.
have hnowrap : mode2_retry_eta_nowrap retry by split.
apply
  (KeygenSamplerCallersSpec.mode2_eta_nonce_bounds retry slot).
+ exact hretry.
+ exact hslot.
exact (mode2_retry_eta_nonce_lt65536 retry slot hnowrap hslot).
qed.

lemma mode2_retry_counter_plus5_range retry :
  mode2_retry_eta_nowrap retry =>
  0 <= KeygenSamplerCallersSpec.mode2_retry_counter_i retry +
      KeygenSamplerCallersSpec.mode2_retry_span_i < W64.modulus.
proof.
rewrite /mode2_retry_eta_nowrap.
move=> [hretry htop].
rewrite /KeygenSamplerCallersSpec.mode2_retry_counter_i
        /KeygenSamplerCallersSpec.mode2_retry_span_i
        /KeygenSamplerCallersSpec.mode2_k_i
        /KeygenSamplerCallersSpec.mode2_m_i.
smt(KeygenSamplerCallersSpec.low16_lt_w64_modulus).
qed.

lemma mode2_retry_counter_plus5E retry :
  mode2_retry_eta_nowrap retry =>
  W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i retry) +
    W64.of_int KeygenSamplerCallersSpec.mode2_retry_span_i =
  W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i (retry + 1)).
proof.
move=> _.
rewrite /KeygenSamplerCallersSpec.mode2_retry_counter_i
        /KeygenSamplerCallersSpec.mode2_retry_span_i
        /KeygenSamplerCallersSpec.mode2_k_i
        /KeygenSamplerCallersSpec.mode2_m_i
        -W64.of_intD.
congr.
ring.
qed.

lemma mode2_retry_eta_nonce_splitE retry :
  mode2_retry_eta_nowrap retry =>
  KeygenSamplerCallersSpec.eta_nonce_word
    (KeygenSamplerCallersSpec.eta_nonce_word
      (W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i retry))
      KeygenSamplerCallersSpec.mode2_m_i)
    KeygenSamplerCallersSpec.mode2_k_i =
  W64.of_int (KeygenSamplerCallersSpec.mode2_retry_counter_i (retry + 1)).
proof.
move=> hnowrap.
rewrite KeygenSamplerCallersSpec.mode2_eta_nonce_split.
exact (mode2_retry_counter_plus5E retry hnowrap).
qed.

lemma mode2_retry_eta_loop_step
    retry start_slot count_i (i_before : W64.t) :
  W64.to_uint i_before < count_i =>
  W64.to_uint (i_before + W64.one) = W64.to_uint i_before + 1 =>
  KeygenSamplerCallersSpec.linear_base_word (W64.to_uint i_before) +
      W64.of_int 256 =
    KeygenSamplerCallersSpec.linear_base_word (W64.to_uint i_before + 1) =>
  W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i
        retry (start_slot + W64.to_uint i_before)) + W64.one =
    W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i
        retry (start_slot + W64.to_uint i_before + 1)) =>
  ((0 <= W64.to_uint (i_before + W64.one) /\
    (0 <= W64.to_uint (i_before + W64.one) =>
     W64.to_uint (i_before + W64.one) <= count_i)) /\
   KeygenSamplerCallersSpec.linear_base_word (W64.to_uint i_before) +
       W64.of_int 256 =
     KeygenSamplerCallersSpec.linear_base_word
       (W64.to_uint (i_before + W64.one)) /\
   W64.of_int
       (KeygenSamplerCallersSpec.mode2_eta_nonce_i
         retry (start_slot + W64.to_uint i_before)) + W64.one =
     W64.of_int
       (KeygenSamplerCallersSpec.mode2_eta_nonce_i
         retry (start_slot + W64.to_uint (i_before + W64.one))) /\
   count_i - W64.to_uint (i_before + W64.one) <
     count_i - W64.to_uint i_before).
proof.
move=> hilt hi_succ hbase_succ hnonce_succ.
rewrite hi_succ.
split.
+ split.
  + smt(W64.to_uint_cmp).
  + move=> _; smt().
+ smt().
qed.

lemma mode2_eta_retry_leaf_ll
    (seed0 : BArray128.t) retry (eta_limit : int -> int)
    global_slot local_slot :
  phoare [Parent._kp_poly_uniform_eta_at_seedbuf_2048 :
    seedp = seed0 /\
    seedoff =
      W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i /\
    nonce = W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i retry global_slot) /\
    base = KeygenSamplerCallersSpec.linear_base_word local_slot /\
    mode2_retry_eta_progress seed0 retry eta_limit /\
    0 <= global_slot < KeygenSamplerCallersSpec.mode2_retry_span_i /\
    0 <= local_slot < 8
    ==> true] = 1%r.
proof.
conseq (TargetKeygenMode2Parent.eta2048_leaf_progress_ll
  seed0
  (W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i)
  (W64.of_int
    (KeygenSamplerCallersSpec.mode2_eta_nonce_i retry global_slot))
  (KeygenSamplerCallersSpec.linear_base_i local_slot)
  (eta_limit global_slot)) => //=.
move=> &hr
  [hseed [hseedoff [hnonce [hbase [hprogress [hglobal hlocal]]]]]].
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
  mode2_retry_eta_progress_at seed0 retry eta_limit global_slot
    hprogress hglobal.
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

lemma mode2_eta_retry_segment_progress_ll
    (seed0 : BArray128.t) retry (eta_limit : int -> int)
    start_slot count_i :
  phoare [Parent._kp_polyvec_expand_eta :
    seedp = seed0 /\
    nonce = W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i retry start_slot) /\
    count = W64.of_int count_i /\
    0 <= retry /\
    0 <= start_slot /\
    0 <= count_i <= 8 /\
    start_slot + count_i <=
      KeygenSamplerCallersSpec.mode2_retry_span_i /\
    mode2_retry_eta_progress seed0 retry eta_limit
    ==> true] = 1%r.
proof.
proc.
while
  (seedp = seed0 /\
   count = W64.of_int count_i /\
   0 <= retry /\
   0 <= start_slot /\
   0 <= count_i <= 8 /\
   start_slot + count_i <=
     KeygenSamplerCallersSpec.mode2_retry_span_i /\
   mode2_retry_eta_progress seed0 retry eta_limit /\
   seedoff =
     W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i /\
   0 <= W64.to_uint i <= count_i /\
   base =
     KeygenSamplerCallersSpec.linear_base_word (W64.to_uint i) /\
   nonce = W64.of_int
     (KeygenSamplerCallersSpec.mode2_eta_nonce_i
       retry (start_slot + W64.to_uint i)))
  (count_i - W64.to_uint i).
+ move=> z.
  wp.
  exlim i => i_before.
  call (mode2_eta_retry_leaf_ll
    seed0 retry eta_limit
    (start_slot + W64.to_uint i_before)
    (W64.to_uint i_before)).
  auto => />.
  move=> hretry0 hstart0 hcount0 hcountle hspan hprogress
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
          retry (start_slot + W64.to_uint i_before)) +
        W64.of_int 1 =
      W64.of_int
        (KeygenSamplerCallersSpec.mode2_eta_nonce_i
          retry (start_slot + W64.to_uint i_before + 1)).
  + rewrite /KeygenSamplerCallersSpec.mode2_eta_nonce_i
            /KeygenSamplerCallersSpec.mode2_retry_counter_i
            /KeygenSamplerCallersSpec.mode2_retry_span_i
            -W64.of_intD.
    by congr; ring.
  move=> _ _.
  move:
    (mode2_retry_eta_loop_step
      retry start_slot count_i i_before
      hilt hi_succ hbase_succ hnonce_succ).
  smt().
auto => />.
move=> hretry0 hstart0 hcount0 hcountle hspan hprogress.
rewrite /KeygenSamplerCallersSpec.mode2_eta_nonce_i
        /KeygenSamplerCallersSpec.mode2_retry_counter_i.
move=> i0 hi0 hile hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma mode2_eta_retry_s1_count3_progress_ll
    (seed0 : BArray128.t) retry (eta_limit : int -> int) :
  phoare [Parent._kp_polyvec_expand_eta :
    seedp = seed0 /\
    nonce = W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i retry 0) /\
    count = W64.of_int KeygenSamplerCallersSpec.mode2_m_i /\
    mode2_retry_eta_nowrap retry /\
    mode2_retry_eta_progress seed0 retry eta_limit
    ==> true] = 1%r.
proof.
conseq (mode2_eta_retry_segment_progress_ll
  seed0 retry eta_limit 0 KeygenSamplerCallersSpec.mode2_m_i) => //=.
move=> &hr [hseed [hnonce [hcount [hnowrap hprogress]]]].
rewrite /mode2_retry_eta_nowrap in hnowrap.
smt().
qed.

lemma mode2_eta_retry_s2_count2_progress_ll
    (seed0 : BArray128.t) retry (eta_limit : int -> int) :
  phoare [Parent._kp_polyvec_expand_eta :
    seedp = seed0 /\
    nonce = W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i
        retry KeygenSamplerCallersSpec.mode2_m_i) /\
    count = W64.of_int KeygenSamplerCallersSpec.mode2_k_i /\
    mode2_retry_eta_nowrap retry /\
    mode2_retry_eta_progress seed0 retry eta_limit
    ==> true] = 1%r.
proof.
conseq (mode2_eta_retry_segment_progress_ll
  seed0 retry eta_limit
  KeygenSamplerCallersSpec.mode2_m_i
  KeygenSamplerCallersSpec.mode2_k_i) => //=.
move=> &hr [hseed [hnonce [hcount [hnowrap hprogress]]]].
rewrite /mode2_retry_eta_nowrap in hnowrap.
smt().
qed.

end Mode2FaithfulSecurityRetryEtaProgressPostFreeze.
