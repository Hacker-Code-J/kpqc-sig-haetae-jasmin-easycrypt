require import AllCore IntDiv List Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenMode2ParentTarget KeygenM23SingularSpec.

theory TargetKeygenM23SingularHelpers.

module Parent = KeygenMode2ParentTarget.M.

lemma sk_singular_value_minmax_correct (a0 b0 : W32.t) :
  hoare [Parent.__sk_singular_value_minmax :
    a = a0 /\ b = b0
    ==>
    res = KeygenM23SingularSpec.minmax_word a0 b0].
proof.
proc.
auto => />.
qed.

lemma sk_singular_value_minmax_ll :
  islossless Parent.__sk_singular_value_minmax.
proof.
proc.
islossless.
qed.

lemma sk_singular_value_mulrnd16_correct (x0 y0 : W32.t) :
  hoare [Parent.__sk_singular_value_mulrnd16 :
    x = x0 /\ y = y0
    ==>
    res = KeygenM23SingularSpec.mulrnd16_word x0 y0].
proof.
proc.
auto => />.
qed.

lemma sk_singular_value_mulrnd16_ll :
  islossless Parent.__sk_singular_value_mulrnd16.
proof.
proc.
islossless.
qed.

lemma singular_clear_sum_correct (sum0 : BArray1024.t) :
  hoare [Parent._singular_clear_sum :
    sump = sum0
    ==>
    res = KeygenM23SingularSpec.clear_sum sum0].
proof.
proc.
while
  (0 <= W64.to_uint i <= KeygenM23SingularSpec.singular_words_i /\
   sump =
     KeygenM23SingularSpec.clear_prefix sum0 (W64.to_uint i)).
+ auto => /> &hr hile hsum hguard.
  have hilt :
      W64.to_uint i{hr} < KeygenM23SingularSpec.singular_words_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.singular_words_i /=.
    trivial.
  have hsucc :
      W64.to_uint (i{hr} + W64.one) =
        W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  rewrite hsucc.
  split; first smt().
  rewrite KeygenM23SingularSpec.clear_prefixS 1:/#.
  by rewrite /KeygenM23SingularSpec.clear_step.
auto => />.
split.
+ by rewrite KeygenM23SingularSpec.clear_prefix0.
move=> i0 sum1 hdone hile.
have hieq :
    W64.to_uint i0 = KeygenM23SingularSpec.singular_words_i.
+ move: hdone hile.
  rewrite /KeygenM23SingularSpec.singular_words_i /=.
  smt(W64.to_uint_cmp).
by rewrite /KeygenM23SingularSpec.clear_sum -hieq.
qed.

lemma singular_clear_sum_ll :
  islossless Parent._singular_clear_sum.
proof.
proc.
while
  (W64.to_uint i <= KeygenM23SingularSpec.singular_words_i)
  (KeygenM23SingularSpec.singular_words_i - W64.to_uint i).
+ move=> z.
  auto => /> &hr hle hguard.
  have hilt :
      W64.to_uint i{hr} < KeygenM23SingularSpec.singular_words_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.singular_words_i /=.
    trivial.
  have hsucc :
      W64.to_uint (i{hr} + W64.one) =
        W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  rewrite hsucc.
  split.
  + smt().
  + smt().
auto => />.
rewrite /KeygenM23SingularSpec.singular_words_i.
move=> i0 hle hvariant.
move: hvariant; rewrite subz_le0 => hge.
by rewrite W64.ultE W64.of_uintK /=; smt().
qed.

lemma sk_singular_value_accumulate_fft_sqabs_correct
    (sum0 : BArray1024.t) (input0 : BArray2048.t) :
  hoare [Parent._sk_singular_value_accumulate_fft_sqabs :
    sump = sum0 /\ inputp = input0
    ==>
    res =
      KeygenM23SingularSpec.accumulate_fft_sqabs sum0 input0].
proof.
proc.
while
  (inputp = input0 /\
   0 <= W64.to_uint i <= KeygenM23SingularSpec.singular_words_i /\
   W64.to_uint idx = 2 * W64.to_uint i /\
   sump =
     KeygenM23SingularSpec.accumulate_prefix
       sum0 input0 (W64.to_uint i)).
+ wp.
  ecall (sk_singular_value_mulrnd16_correct imag imag).
  ecall (sk_singular_value_mulrnd16_correct real real).
  auto => /> &hr hile hidx hsum hguard.
  have hilt :
      W64.to_uint i{hr} < KeygenM23SingularSpec.singular_words_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.singular_words_i /=.
    trivial.
  have hidx1 :
      W64.to_uint (idx{hr} + W64.one) =
        W64.to_uint idx{hr} + 1.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  have hidx2 :
      W64.to_uint (idx{hr} + W64.one + W64.one) =
        W64.to_uint idx{hr} + 2.
  + rewrite W64.to_uintD_small 1:/# hidx1 W64.to_uint1.
    trivial.
  have hisucc :
      W64.to_uint (i{hr} + W64.one) =
        W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  rewrite hidx1 hidx2 hisucc.
  do split.
  + smt().
  + smt().
  rewrite /KeygenM23SingularSpec.accumulate_step
          /KeygenM23SingularSpec.fft_sqabs_at.
  ring.
auto => />.
smt().
rewrite KeygenM23SingularSpec.accumulate_prefixS 1:/#.
rewrite /KeygenM23SingularSpec.accumulate_step
        /KeygenM23SingularSpec.fft_sqabs_at.
congr.
rewrite hsum /=.
trivial.
auto => />.
split.
+ by rewrite KeygenM23SingularSpec.accumulate_prefix0.
move=> i0 idx0 hdone hi0 hile hidx.
have hieq :
    W64.to_uint i0 = KeygenM23SingularSpec.singular_words_i.
+ move: hdone hile.
  rewrite /KeygenM23SingularSpec.singular_words_i /=.
  smt(W64.to_uint_cmp).
by rewrite /KeygenM23SingularSpec.accumulate_fft_sqabs -hieq.
qed.

lemma sk_singular_value_accumulate_fft_sqabs_ll :
  islossless Parent._sk_singular_value_accumulate_fft_sqabs.
proof.
proc.
while
  (W64.to_uint i <= KeygenM23SingularSpec.singular_words_i)
  (KeygenM23SingularSpec.singular_words_i - W64.to_uint i).
+ move=> z.
  wp.
  call sk_singular_value_mulrnd16_ll.
  call sk_singular_value_mulrnd16_ll.
  auto => /> &hr hle hguard.
  have hilt :
      W64.to_uint i{hr} < KeygenM23SingularSpec.singular_words_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.singular_words_i /=.
    trivial.
  have hsucc :
      W64.to_uint (i{hr} + W64.one) =
        W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  rewrite hsucc.
  split; smt().
auto => />.
rewrite /KeygenM23SingularSpec.singular_words_i.
move=> i0 hle hvariant.
move: hvariant; rewrite subz_le0 => hge.
by rewrite W64.ultE W64.of_uintK /=; smt().
qed.

lemma singular_finish_typed_mode2_correct (sum0 : BArray1024.t) :
  hoare [Parent._singular_finish_typed :
    sump = sum0 /\
    best_count = KeygenM23SingularSpec.mode2_best_count_i /\
    tau = KeygenM23SingularSpec.mode2_tau_i /\
    rem = KeygenM23SingularSpec.mode2_rem_i
    ==>
    res = KeygenM23SingularSpec.finish_mode2 sum0].
proof.
proc.
seq 3 :
  (sump = sum0 /\
   best_count = KeygenM23SingularSpec.mode2_best_count_i /\
   tau = KeygenM23SingularSpec.mode2_tau_i /\
   rem = KeygenM23SingularSpec.mode2_rem_i /\
   bestm = KeygenM23SingularSpec.best_init sum0).
+ while
    (sump = sum0 /\
     best_count = KeygenM23SingularSpec.mode2_best_count_i /\
     tau = KeygenM23SingularSpec.mode2_tau_i /\
     rem = KeygenM23SingularSpec.mode2_rem_i /\
     0 <= W64.to_uint i <=
       KeygenM23SingularSpec.mode2_best_count_i /\
     bestm =
       KeygenM23SingularSpec.best_init_prefix sum0 (W64.to_uint i)).
  + auto => /> &hr hile hibound hguard.
    have hilt :
        W64.to_uint i{hr} <
          KeygenM23SingularSpec.mode2_best_count_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23SingularSpec.mode2_best_count_i /=.
      trivial.
    have hsucc :
        W64.to_uint (i{hr} + W64.one) =
          W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small 1:/#.
      trivial.
    rewrite hsucc.
    split.
    + split; smt().
    rewrite KeygenM23SingularSpec.best_init_prefixS 1:/#.
    by rewrite /KeygenM23SingularSpec.best_init_step.
  auto => />.
  split.
  + by rewrite KeygenM23SingularSpec.best_init_prefix0.
  move=> i0 hdone hi0 hile.
  have hieq :
      W64.to_uint i0 =
        KeygenM23SingularSpec.mode2_best_count_i.
  + move: hdone hile.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.mode2_best_count_i /=.
    smt(W64.to_uint_cmp).
  by rewrite /KeygenM23SingularSpec.best_init -hieq.
seq 2 :
  (sump = sum0 /\
   best_count = KeygenM23SingularSpec.mode2_best_count_i /\
   tau = KeygenM23SingularSpec.mode2_tau_i /\
   rem = KeygenM23SingularSpec.mode2_rem_i /\
   bestm = KeygenM23SingularSpec.best_scan sum0).
+ while
    (sump = sum0 /\
     best_count = KeygenM23SingularSpec.mode2_best_count_i /\
     tau = KeygenM23SingularSpec.mode2_tau_i /\
     rem = KeygenM23SingularSpec.mode2_rem_i /\
     KeygenM23SingularSpec.mode2_best_count_i <= W64.to_uint i <=
       KeygenM23SingularSpec.singular_words_i /\
     bestm =
       KeygenM23SingularSpec.best_scan_prefix sum0 (W64.to_uint i)).
  + wp.
    while
      (sump = sum0 /\
       best_count = KeygenM23SingularSpec.mode2_best_count_i /\
       tau = KeygenM23SingularSpec.mode2_tau_i /\
       rem = KeygenM23SingularSpec.mode2_rem_i /\
       KeygenM23SingularSpec.mode2_best_count_i <= W64.to_uint i <
         KeygenM23SingularSpec.singular_words_i /\
       0 <= W64.to_uint j <=
         KeygenM23SingularSpec.mode2_best_count_i /\
       (x, bestm) =
         KeygenM23SingularSpec.best_insert_prefix
           (BArray1024.get32 sum0 (W64.to_uint i))
           (KeygenM23SingularSpec.best_scan_prefix
             sum0 (W64.to_uint i))
           (W64.to_uint j)).
    + wp.
      ecall (sk_singular_value_minmax_correct x y).
      auto => /> &hr hi0 hi1 hj0 hj1 hpair hguard.
      have hjlt :
          W64.to_uint j{hr} <
            KeygenM23SingularSpec.mode2_best_count_i.
      + move: hguard.
        rewrite W64.ultE W64.of_uintK
                /KeygenM23SingularSpec.mode2_best_count_i /=.
        trivial.
      have hjsucc :
          W64.to_uint (j{hr} + W64.one) =
            W64.to_uint j{hr} + 1.
      + rewrite W64.to_uintD_small 1:/#.
        trivial.
      rewrite hjsucc.
      split.
      + split; smt().
      rewrite KeygenM23SingularSpec.best_insert_prefixS 1:/#.
      by rewrite /KeygenM23SingularSpec.best_insert_step -hpair.
    auto => />.
    move=> &hr hi0 hi1 hguard.
    have hilt :
        W64.to_uint i{hr} <
          KeygenM23SingularSpec.singular_words_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23SingularSpec.singular_words_i /=.
      trivial.
    have hisucc :
        W64.to_uint (i{hr} + W64.one) =
          W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small 1:/#.
      trivial.
    split.
    + split; first exact hilt.
      by rewrite KeygenM23SingularSpec.best_insert_prefix0.
    move=> bestm0 j0 x0 hdone hi2 hj0 hj1 hpair.
    have hjeq :
        W64.to_uint j0 =
          KeygenM23SingularSpec.mode2_best_count_i.
    + move: hdone hj1.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23SingularSpec.mode2_best_count_i /=.
      smt(W64.to_uint_cmp).
    rewrite hisucc.
    split.
    + split; smt().
    rewrite KeygenM23SingularSpec.best_scan_prefixS 1:hi0.
    rewrite /KeygenM23SingularSpec.best_scan_step
            /KeygenM23SingularSpec.best_insert -hjeq.
    by rewrite -hpair.
  auto => />.
  split.
  + by rewrite KeygenM23SingularSpec.best_scan_prefix_start.
  move=> i0 hdone hi0 hile.
  have hieq :
      W64.to_uint i0 = KeygenM23SingularSpec.singular_words_i.
  + move: hdone hile.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.singular_words_i /=.
    smt(W64.to_uint_cmp).
  by rewrite /KeygenM23SingularSpec.best_scan -hieq.
seq 3 :
  (sump = sum0 /\
   best_count = KeygenM23SingularSpec.mode2_best_count_i /\
   tau = KeygenM23SingularSpec.mode2_tau_i /\
   rem = KeygenM23SingularSpec.mode2_rem_i /\
   bestm = KeygenM23SingularSpec.best_scan sum0 /\
   min = KeygenM23SingularSpec.best_min bestm).
+ while
    (sump = sum0 /\
     best_count = KeygenM23SingularSpec.mode2_best_count_i /\
     tau = KeygenM23SingularSpec.mode2_tau_i /\
     rem = KeygenM23SingularSpec.mode2_rem_i /\
     bestm = KeygenM23SingularSpec.best_scan sum0 /\
     1 <= W64.to_uint i <=
       KeygenM23SingularSpec.mode2_best_count_i /\
     min =
       KeygenM23SingularSpec.best_min_prefix bestm (W64.to_uint i)).
  + wp.
    ecall (sk_singular_value_minmax_correct min tmp).
    auto => /> &hr hi0 hi1 hguard.
    have hilt :
        W64.to_uint i{hr} <
          KeygenM23SingularSpec.mode2_best_count_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23SingularSpec.mode2_best_count_i /=.
      trivial.
    have hisucc :
        W64.to_uint (i{hr} + W64.one) =
          W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small 1:/#.
      trivial.
    rewrite hisucc.
    split.
    + split; smt().
    rewrite KeygenM23SingularSpec.best_min_prefixS 1:hi0.
    by rewrite /KeygenM23SingularSpec.best_min_step.
  auto => />.
  split.
  + by rewrite KeygenM23SingularSpec.best_min_prefix_start.
  move=> i0 hdone hi0 hile.
  have hieq :
      W64.to_uint i0 =
        KeygenM23SingularSpec.mode2_best_count_i.
  + move: hdone hile.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.mode2_best_count_i /=.
    smt(W64.to_uint_cmp).
  by rewrite /KeygenM23SingularSpec.best_min -hieq.
seq 3 :
  (sump = sum0 /\
   best_count = KeygenM23SingularSpec.mode2_best_count_i /\
   tau = KeygenM23SingularSpec.mode2_tau_i /\
   rem = KeygenM23SingularSpec.mode2_rem_i /\
   bestm = KeygenM23SingularSpec.best_scan sum0 /\
   min = KeygenM23SingularSpec.best_min bestm /\
   res_0 = KeygenM23SingularSpec.finish_acc bestm min).
+ while
    (sump = sum0 /\
     best_count = KeygenM23SingularSpec.mode2_best_count_i /\
     tau = KeygenM23SingularSpec.mode2_tau_i /\
     rem = KeygenM23SingularSpec.mode2_rem_i /\
     bestm = KeygenM23SingularSpec.best_scan sum0 /\
     min = KeygenM23SingularSpec.best_min bestm /\
     0 <= W64.to_uint i <=
       KeygenM23SingularSpec.mode2_best_count_i /\
     res_0 =
       KeygenM23SingularSpec.finish_acc_prefix
         bestm min (W64.to_uint i)).
  + auto => /> &hr hi0 hile hguard.
    have hilt :
        W64.to_uint i{hr} <
          KeygenM23SingularSpec.mode2_best_count_i.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK
              /KeygenM23SingularSpec.mode2_best_count_i /=.
      trivial.
    have hisucc :
        W64.to_uint (i{hr} + W64.one) =
          W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small 1:/#.
      trivial.
    rewrite hisucc.
    split.
    + split; smt().
    rewrite KeygenM23SingularSpec.finish_acc_prefixS 1:hi0.
    by rewrite /KeygenM23SingularSpec.finish_acc_step
               /KeygenM23SingularSpec.finish_term_word
               /KeygenM23SingularSpec.finish_factor_word.
  auto => />.
  split.
  + by rewrite KeygenM23SingularSpec.finish_acc_prefix0.
  move=> i0 hdone hi0 hile.
  have hieq :
      W64.to_uint i0 =
        KeygenM23SingularSpec.mode2_best_count_i.
  + move: hdone hile.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.mode2_best_count_i /=.
    smt(W64.to_uint_cmp).
  by rewrite /KeygenM23SingularSpec.finish_acc -hieq.
auto => />.
qed.

lemma singular_finish_typed_mode2_ll (sum0 : BArray1024.t) :
  phoare [Parent._singular_finish_typed :
    sump = sum0 /\
    best_count = KeygenM23SingularSpec.mode2_best_count_i /\
    tau = KeygenM23SingularSpec.mode2_tau_i /\
    rem = KeygenM23SingularSpec.mode2_rem_i
    ==> true] = 1%r.
proof.
proc.
wp.
while
  (best_count = KeygenM23SingularSpec.mode2_best_count_i /\
   W64.to_uint i <= KeygenM23SingularSpec.mode2_best_count_i)
  (KeygenM23SingularSpec.mode2_best_count_i - W64.to_uint i).
+ move=> z.
  auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23SingularSpec.mode2_best_count_i /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
wp.
while
  (best_count = KeygenM23SingularSpec.mode2_best_count_i /\
   1 <= W64.to_uint i <=
     KeygenM23SingularSpec.mode2_best_count_i)
  (KeygenM23SingularSpec.mode2_best_count_i - W64.to_uint i).
+ move=> z.
  wp.
  call sk_singular_value_minmax_ll.
  auto => /> &hr hi0 hi1 hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23SingularSpec.mode2_best_count_i /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
wp.
while
  (best_count = KeygenM23SingularSpec.mode2_best_count_i /\
   KeygenM23SingularSpec.mode2_best_count_i <= W64.to_uint i <=
     KeygenM23SingularSpec.singular_words_i)
  (KeygenM23SingularSpec.singular_words_i - W64.to_uint i).
+ move=> z.
  wp.
  while
    (best_count = KeygenM23SingularSpec.mode2_best_count_i /\
     KeygenM23SingularSpec.mode2_best_count_i <= W64.to_uint i <
       KeygenM23SingularSpec.singular_words_i /\
     W64.to_uint j <= KeygenM23SingularSpec.mode2_best_count_i)
    (KeygenM23SingularSpec.mode2_best_count_i - W64.to_uint j).
  + move=> z0.
    wp.
    call sk_singular_value_minmax_ll.
    auto => /> &hr hi0 hi1 hj hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularSpec.mode2_best_count_i /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  auto => /> &hr hi0 hi1 hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23SingularSpec.singular_words_i /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
wp.
while
  (best_count = KeygenM23SingularSpec.mode2_best_count_i /\
   W64.to_uint i <= KeygenM23SingularSpec.mode2_best_count_i)
  (KeygenM23SingularSpec.mode2_best_count_i - W64.to_uint i).
+ move=> z.
  auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23SingularSpec.mode2_best_count_i /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
auto => />.
move=> i0.
split.
+ move=> hi0 hvariant0.
  move: hvariant0; rewrite subz_le0 => hge0.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23SingularSpec.mode2_best_count_i /=.
  smt().
move=> _ _ i1.
split.
+ move=> _ hi1 hvariant1.
  move: hvariant1; rewrite subz_le0 => hge1.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23SingularSpec.singular_words_i /=.
  smt().
move=> _ _ _ i2.
split.
+ move=> _ hi2 hvariant2.
  move: hvariant2; rewrite subz_le0 => hge2.
  rewrite W64.ultE W64.of_uintK
          /KeygenM23SingularSpec.mode2_best_count_i /=.
  smt().
move=> _ _ _ i3 hi3 hvariant3.
move: hvariant3; rewrite subz_le0 => hge3.
rewrite W64.ultE W64.of_uintK
        /KeygenM23SingularSpec.mode2_best_count_i /=.
smt().
qed.

end TargetKeygenM23SingularHelpers.
