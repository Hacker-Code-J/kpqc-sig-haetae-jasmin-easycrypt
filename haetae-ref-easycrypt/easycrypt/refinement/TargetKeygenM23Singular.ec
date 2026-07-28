require import AllCore IntDiv Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import
  SBArray8192_1024
  KeygenMode2ParentTarget
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  TargetKeygenM23SingularHelpers
  TargetKeygenM23SingularFFT.

theory TargetKeygenM23Singular.

module Parent = KeygenMode2ParentTarget.M.

lemma mode2_slice_s1E
    (s1 s2 : BArray8192.t) (slot : int) :
  0 <= slot < KeygenM23SingularFFTSpec.mode2_s1_count_i =>
  KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot =
  SBArray8192_1024.get_sub32 s1
    (slot * KeygenM23SingularSpec.singular_words_i).
proof.
rewrite /KeygenM23SingularFFTSpec.mode2_slice.
by move=> [_ hlt]; rewrite hlt.
qed.

lemma mode2_slice_s2E
    (s1 s2 : BArray8192.t) (slot : int) :
  KeygenM23SingularFFTSpec.mode2_s1_count_i <= slot <
    KeygenM23SingularFFTSpec.mode2_slice_count_i =>
  KeygenM23SingularFFTSpec.mode2_slice s1 s2 slot =
  SBArray8192_1024.get_sub32 s2
    ((slot - KeygenM23SingularFFTSpec.mode2_s1_count_i) *
      KeygenM23SingularSpec.singular_words_i).
proof.
rewrite /KeygenM23SingularFFTSpec.mode2_slice.
move=> [hge _].
rewrite (_ : !(slot < KeygenM23SingularFFTSpec.mode2_s1_count_i)) 1:/#.
trivial.
qed.

lemma mode2_singular_guardE (sv : W64.t) :
  (! (W64.of_int 611098 \ult sv)) <=>
  W64.to_uint sv <= 611098.
proof.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma singular_full_mode2_word_exact
    (s10 s20 : BArray8192.t) :
  hoare [Parent._singular_full :
    s1p = s10 /\ s2p = s20 /\
    mcount = 3 /\ kcount = 2 /\
    best_count = 5 /\ tau = 58 /\ rem = 24
    ==>
    res =
      KeygenM23SingularFFTSpec.mode2_singular_word
        s10 s20
        KeygenMode2ParentTarget.jfft_roots
        KeygenMode2ParentTarget.jfft_brv8].
proof.
proc.
seq 12 :
  (s1p = s10 /\ s2p = s20 /\
   mcount = 3 /\ kcount = 2 /\
   best_count = 5 /\ tau = 58 /\ rem = 24 /\
   inputp = witness /\
   sump = KeygenM23SingularSpec.clear_sum witness /\
   rootsp = KeygenMode2ParentTarget.jfft_roots /\
   brvp = KeygenMode2ParentTarget.jfft_brv8).
+ ecall
    (TargetKeygenM23SingularHelpers.singular_clear_sum_correct
       witness<:BArray1024.t>).
  auto => />.
seq 3 :
  (s1p = s10 /\ s2p = s20 /\
   mcount = 3 /\ kcount = 2 /\
   best_count = 5 /\ tau = 58 /\ rem = 24 /\
   rootsp = KeygenMode2ParentTarget.jfft_roots /\
   brvp = KeygenMode2ParentTarget.jfft_brv8 /\
   (inputp, sump) =
     KeygenM23SingularFFTSpec.mode2_accumulate_prefix
       s10 s20
       KeygenMode2ParentTarget.jfft_roots
       KeygenMode2ParentTarget.jfft_brv8
       KeygenM23SingularFFTSpec.mode2_s1_count_i).
+ while
    (s1p = s10 /\ s2p = s20 /\
     mcount = 3 /\ kcount = 2 /\
     best_count = 5 /\ tau = 58 /\ rem = 24 /\
     rootsp = KeygenMode2ParentTarget.jfft_roots /\
     brvp = KeygenMode2ParentTarget.jfft_brv8 /\
     0 <= W64.to_uint i <=
       KeygenM23SingularFFTSpec.mode2_s1_count_i /\
     W64.to_uint base =
       W64.to_uint i * KeygenM23SingularSpec.singular_words_i /\
     (inputp, sump) =
       KeygenM23SingularFFTSpec.mode2_accumulate_prefix
         s10 s20
         KeygenMode2ParentTarget.jfft_roots
         KeygenMode2ParentTarget.jfft_brv8
         (W64.to_uint i)).
  + wp.
    ecall
      (TargetKeygenM23SingularHelpers.sk_singular_value_accumulate_fft_sqabs_correct
         sump inputp).
    ecall
      (TargetKeygenM23SingularFFT.fft_full_correct
         inputp rootsp).
    ecall
      (TargetKeygenM23SingularFFT.fft_init_and_bitrev_correct
         inputp xp rootsp brvp).
    auto => /> &hr hi0 hile hbase hpipe hguard.
    have hilt :
        W64.to_uint i{hr} <
          KeygenM23SingularFFTSpec.mode2_s1_count_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23SingularFFTSpec.mode2_s1_count_i /=.
      trivial.
    have hisucc :
        W64.to_uint (i{hr} + W64.one) =
          W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hbasesucc :
        W64.to_uint (base{hr} + W64.of_int 256) =
          (W64.to_uint i{hr} + 1) *
            KeygenM23SingularSpec.singular_words_i.
    + rewrite W64.to_uintD_small 1:/#.
      rewrite W64.to_uint_small 1:/# hbase
              /KeygenM23SingularSpec.singular_words_i.
      ring.
    have hslice :
        SBArray8192_1024.get_sub32 s10 (W64.to_uint base{hr}) =
        KeygenM23SingularFFTSpec.mode2_slice
          s10 s20 (W64.to_uint i{hr}).
    + rewrite mode2_slice_s1E 1:/#.
      by rewrite hbase.
    rewrite /SLH64.protect_ptr /SLH64.protect_64
            hisucc hbasesucc.
    split.
    + split; smt().
    split; first ring.
    rewrite KeygenM23SingularFFTSpec.mode2_accumulate_prefixS 1:hi0.
    rewrite /KeygenM23SingularFFTSpec.mode2_accumulate_step
            /KeygenM23SingularFFTSpec.mode2_fft -hpipe -hslice.
    trivial.
  auto => />.
  split.
  + by rewrite KeygenM23SingularFFTSpec.mode2_accumulate_prefix0.
  move=> base0 i0 input0 sum0 hdone hi0 hile hbase hpipe.
  have hieq :
      W64.to_uint i0 =
        KeygenM23SingularFFTSpec.mode2_s1_count_i.
  + move: hdone hile.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularFFTSpec.mode2_s1_count_i /=.
    smt(W64.to_uint_cmp).
  by rewrite -hieq.
seq 3 :
  (s1p = s10 /\ s2p = s20 /\
   best_count = 5 /\ tau = 58 /\ rem = 24 /\
   rootsp = KeygenMode2ParentTarget.jfft_roots /\
   brvp = KeygenMode2ParentTarget.jfft_brv8 /\
   (inputp, sump) =
     KeygenM23SingularFFTSpec.mode2_accumulate_prefix
       s10 s20
       KeygenMode2ParentTarget.jfft_roots
       KeygenMode2ParentTarget.jfft_brv8
       KeygenM23SingularFFTSpec.mode2_slice_count_i).
+ while
    (s1p = s10 /\ s2p = s20 /\
     kcount = 2 /\
     best_count = 5 /\ tau = 58 /\ rem = 24 /\
     rootsp = KeygenMode2ParentTarget.jfft_roots /\
     brvp = KeygenMode2ParentTarget.jfft_brv8 /\
     0 <= W64.to_uint i <=
       KeygenM23SingularFFTSpec.mode2_s2_count_i /\
     W64.to_uint base =
       W64.to_uint i * KeygenM23SingularSpec.singular_words_i /\
     (inputp, sump) =
       KeygenM23SingularFFTSpec.mode2_accumulate_prefix
         s10 s20
         KeygenMode2ParentTarget.jfft_roots
         KeygenMode2ParentTarget.jfft_brv8
         (KeygenM23SingularFFTSpec.mode2_s1_count_i +
          W64.to_uint i)).
  + wp.
    ecall
      (TargetKeygenM23SingularHelpers.sk_singular_value_accumulate_fft_sqabs_correct
         sump inputp).
    ecall
      (TargetKeygenM23SingularFFT.fft_full_correct
         inputp rootsp).
    ecall
      (TargetKeygenM23SingularFFT.fft_init_and_bitrev_correct
         inputp xp rootsp brvp).
    auto => /> &hr hi0 hile hbase hpipe hguard.
    have hilt :
        W64.to_uint i{hr} <
          KeygenM23SingularFFTSpec.mode2_s2_count_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23SingularFFTSpec.mode2_s2_count_i /=.
      trivial.
    have hisucc :
        W64.to_uint (i{hr} + W64.one) =
          W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hbasesucc :
        W64.to_uint (base{hr} + W64.of_int 256) =
          (W64.to_uint i{hr} + 1) *
            KeygenM23SingularSpec.singular_words_i.
    + rewrite W64.to_uintD_small 1:/#.
      rewrite W64.to_uint_small 1:/# hbase
              /KeygenM23SingularSpec.singular_words_i.
      ring.
    have hslice :
        SBArray8192_1024.get_sub32 s20 (W64.to_uint base{hr}) =
        KeygenM23SingularFFTSpec.mode2_slice
          s10 s20
          (KeygenM23SingularFFTSpec.mode2_s1_count_i +
           W64.to_uint i{hr}).
    + rewrite mode2_slice_s2E 1:/#.
      rewrite hbase
              /KeygenM23SingularFFTSpec.mode2_s1_count_i
              /KeygenM23SingularSpec.singular_words_i.
      congr; ring.
    rewrite /SLH64.protect_ptr /SLH64.protect_64
            hisucc hbasesucc.
    split.
    + split; smt().
    split; first ring.
    rewrite
      (_ :
        KeygenM23SingularFFTSpec.mode2_s1_count_i +
          (W64.to_uint i{hr} + 1) =
        (KeygenM23SingularFFTSpec.mode2_s1_count_i +
          W64.to_uint i{hr}) + 1) 1:/#.
    rewrite KeygenM23SingularFFTSpec.mode2_accumulate_prefixS 1:/#.
    rewrite /KeygenM23SingularFFTSpec.mode2_accumulate_step
            /KeygenM23SingularFFTSpec.mode2_fft -hpipe -hslice.
    trivial.
  auto => /> &hr hinit base1 i0 input0 sum0
              hdone hi0 hile hbase hpipe.
  have hieq :
      W64.to_uint i0 =
        KeygenM23SingularFFTSpec.mode2_s2_count_i.
  + move: hdone hile.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularFFTSpec.mode2_s2_count_i /=.
    smt(W64.to_uint_cmp).
  have hcount :
      KeygenM23SingularFFTSpec.mode2_s1_count_i +
        W64.to_uint i0 =
      KeygenM23SingularFFTSpec.mode2_slice_count_i.
  + rewrite hieq
            /KeygenM23SingularFFTSpec.mode2_s1_count_i
            /KeygenM23SingularFFTSpec.mode2_s2_count_i
            /KeygenM23SingularFFTSpec.mode2_slice_count_i.
    trivial.
  by rewrite -hcount.
ecall
  (TargetKeygenM23SingularHelpers.singular_finish_typed_mode2_correct
     (KeygenM23SingularFFTSpec.mode2_accumulate_prefix
        s10 s20
        KeygenMode2ParentTarget.jfft_roots
        KeygenMode2ParentTarget.jfft_brv8
        KeygenM23SingularFFTSpec.mode2_slice_count_i).`2).
auto => />.
rewrite /KeygenM23SingularFFTSpec.mode2_singular_word
        /KeygenM23SingularFFTSpec.mode2_accumulate.
trivial.
move=> &hr hpipe.
smt().
qed.

end TargetKeygenM23Singular.
