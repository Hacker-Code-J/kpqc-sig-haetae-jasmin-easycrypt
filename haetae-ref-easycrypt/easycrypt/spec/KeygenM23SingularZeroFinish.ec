require import AllCore IntDiv List Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray20 BArray1024.
require import KeygenM23SingularSpec KeygenM23SingularBoundary
               KeygenM23FixedPointSemantics KeygenM23FinalizeSemantics.

theory KeygenM23SingularZeroFinish.

op zero_sum_256 (sum : BArray1024.t) : bool =
  forall i, 0 <= i < KeygenM23SingularSpec.singular_words_i =>
    BArray1024.get32 sum i = W32.zero.

op zero_best_5 (best : BArray20.t) : bool =
  forall i, 0 <= i < KeygenM23SingularSpec.mode2_best_count_i =>
    BArray20.get32 best i = W32.zero.

lemma minmax_zero_exact :
  KeygenM23SingularSpec.minmax_word W32.zero W32.zero =
    (W32.zero, W32.zero).
proof.
by rewrite /KeygenM23SingularSpec.minmax_word /=.
qed.

lemma zero_best_set_zero best at :
  zero_best_5 best =>
  0 <= at < KeygenM23SingularSpec.mode2_best_count_i =>
  zero_best_5 (BArray20.set32 best at W32.zero).
proof.
rewrite /zero_best_5
        /KeygenM23SingularSpec.mode2_best_count_i.
move=> hbest hat i hi.
rewrite BArray20.get_set32E 1:/# 1:/#.
case: (at = i) => heq.
+ trivial.
+ exact (hbest i hi).
qed.

lemma best_init_zero_prefix sum processed :
  zero_sum_256 sum =>
  0 <= processed =>
  processed <= KeygenM23SingularSpec.mode2_best_count_i =>
  forall i, 0 <= i < processed =>
    BArray20.get32
      (KeygenM23SingularSpec.best_init_prefix sum processed) i =
      W32.zero.
proof.
move=> hsum.
move: processed.
apply intind.
+ move=> _ i hi.
  smt().
+ move=> processed hprocessed ih hcap i hi.
  rewrite KeygenM23SingularSpec.best_init_prefixS 1://
          /KeygenM23SingularSpec.best_init_step.
  rewrite BArray20.get_set32E 1:/# 1:/#.
  case: (processed = i) => heq.
  + apply hsum.
    rewrite /KeygenM23SingularSpec.mode2_best_count_i in hcap.
    rewrite /KeygenM23SingularSpec.singular_words_i.
    smt().
  + apply ih.
    + smt().
    + smt().
qed.

lemma best_init_zero sum :
  zero_sum_256 sum =>
  zero_best_5 (KeygenM23SingularSpec.best_init sum).
proof.
move=> hsum.
rewrite /zero_best_5 /KeygenM23SingularSpec.best_init.
exact (best_init_zero_prefix sum
         KeygenM23SingularSpec.mode2_best_count_i hsum _ _).
qed.

lemma best_insert_zero_prefix best processed :
  zero_best_5 best =>
  0 <= processed =>
  processed <= KeygenM23SingularSpec.mode2_best_count_i =>
  (KeygenM23SingularSpec.best_insert_prefix
     W32.zero best processed).`1 = W32.zero /\
  zero_best_5
    (KeygenM23SingularSpec.best_insert_prefix
       W32.zero best processed).`2.
proof.
move=> hbest.
move: processed.
apply intind.
+ move=> _.
  rewrite KeygenM23SingularSpec.best_insert_prefix0 /=.
  exact hbest.
+ move=> processed hprocessed ih hcap.
  rewrite KeygenM23SingularSpec.best_insert_prefixS 1://.
  have hprev := ih _.
  + smt().
  move: hprev => [hx hbestprev].
  rewrite /KeygenM23SingularSpec.best_insert_step /= hx.
  rewrite hbestprev 1:/# minmax_zero_exact /=.
  apply zero_best_set_zero.
  + exact hbestprev.
  + smt().
qed.

lemma best_insert_zero best :
  zero_best_5 best =>
  zero_best_5
    (KeygenM23SingularSpec.best_insert W32.zero best).
proof.
move=> hbest.
rewrite /KeygenM23SingularSpec.best_insert.
have hnonnegative :
    0 <= KeygenM23SingularSpec.mode2_best_count_i.
+ by rewrite /KeygenM23SingularSpec.mode2_best_count_i.
have hself :
    KeygenM23SingularSpec.mode2_best_count_i <=
    KeygenM23SingularSpec.mode2_best_count_i by smt().
have hprefix :=
  best_insert_zero_prefix best
    KeygenM23SingularSpec.mode2_best_count_i
    hbest hnonnegative hself.
move: hprefix => [_ hzero].
exact hzero.
qed.

lemma best_scan_zero_offset sum count :
  zero_sum_256 sum =>
  0 <= count =>
  KeygenM23SingularSpec.mode2_best_count_i + count <=
    KeygenM23SingularSpec.singular_words_i =>
  zero_best_5
    (KeygenM23SingularSpec.best_scan_prefix sum
      (KeygenM23SingularSpec.mode2_best_count_i + count)).
proof.
move=> hsum.
move: count.
apply intind.
+ move=> _.
  rewrite (_ :
      KeygenM23SingularSpec.mode2_best_count_i + 0 =
      KeygenM23SingularSpec.mode2_best_count_i) 1:/#.
  rewrite KeygenM23SingularSpec.best_scan_prefix_start.
  exact (best_init_zero sum hsum).
+ move=> count hcount ih hcap.
  rewrite (_ :
      KeygenM23SingularSpec.mode2_best_count_i + (count + 1) =
      (KeygenM23SingularSpec.mode2_best_count_i + count) + 1) 1:/#.
  rewrite KeygenM23SingularSpec.best_scan_prefixS 1:/#.
  rewrite /KeygenM23SingularSpec.best_scan_step.
  rewrite hsum 1:/#.
  apply best_insert_zero.
  apply ih.
  smt().
qed.

lemma best_scan_zero sum :
  zero_sum_256 sum =>
  zero_best_5 (KeygenM23SingularSpec.best_scan sum).
proof.
move=> hsum.
rewrite /KeygenM23SingularSpec.best_scan.
have h :=
  best_scan_zero_offset sum
    (KeygenM23SingularSpec.singular_words_i -
     KeygenM23SingularSpec.mode2_best_count_i) hsum _ _.
+ rewrite /KeygenM23SingularSpec.singular_words_i
           /KeygenM23SingularSpec.mode2_best_count_i.
  smt().
+ smt().
rewrite (_ :
    KeygenM23SingularSpec.mode2_best_count_i +
      (KeygenM23SingularSpec.singular_words_i -
       KeygenM23SingularSpec.mode2_best_count_i) =
    KeygenM23SingularSpec.singular_words_i) in h.
+ rewrite /KeygenM23SingularSpec.singular_words_i
           /KeygenM23SingularSpec.mode2_best_count_i.
  smt().
+ exact h.
qed.

lemma best_min_zero_offset best count :
  zero_best_5 best =>
  0 <= count =>
  1 + count <= KeygenM23SingularSpec.mode2_best_count_i =>
  KeygenM23SingularSpec.best_min_prefix best (1 + count) =
    W32.zero.
proof.
move=> hbest.
move: count.
apply intind.
+ move=> _.
  rewrite (_ : 1 + 0 = 1) 1:/#.
  rewrite KeygenM23SingularSpec.best_min_prefix_start.
  apply hbest.
  rewrite /KeygenM23SingularSpec.mode2_best_count_i.
  smt().
+ move=> count hcount ih hcap.
  rewrite (_ : 1 + (count + 1) = (1 + count) + 1) 1:/#.
  rewrite KeygenM23SingularSpec.best_min_prefixS 1:/#.
  rewrite /KeygenM23SingularSpec.best_min_step.
  rewrite ih 1:/#.
  rewrite hbest 1:/# minmax_zero_exact /=.
  trivial.
qed.

lemma best_min_zero best :
  zero_best_5 best =>
  KeygenM23SingularSpec.best_min best = W32.zero.
proof.
move=> hbest.
rewrite /KeygenM23SingularSpec.best_min.
have h :=
  best_min_zero_offset best
    (KeygenM23SingularSpec.mode2_best_count_i - 1) hbest _ _.
+ rewrite /KeygenM23SingularSpec.mode2_best_count_i.
  smt().
+ smt().
rewrite (_ :
    1 + (KeygenM23SingularSpec.mode2_best_count_i - 1) =
    KeygenM23SingularSpec.mode2_best_count_i) in h.
+ rewrite /KeygenM23SingularSpec.mode2_best_count_i.
  smt().
+ exact h.
qed.

lemma finish_term_zero_exact :
  KeygenM23SingularSpec.finish_term_word W32.zero W32.zero =
    W32.of_int 1536.
proof.
rewrite /KeygenM23SingularSpec.finish_term_word
        KeygenM23SingularBoundary.finish_factor_zero_exact /=.
rewrite /(`|>>`) W8.of_uintK /=.
have hs32 :
    W32.sar (W32.of_int 66048) 10 = W32.of_int 64.
+ rewrite KeygenM23FinalizeSemantics.w32_sar_nonnegative_of_int
          1,2:/#.
  done.
by rewrite hs32 W32.of_intM'.
qed.

lemma finish_acc_zero_prefix best processed :
  zero_best_5 best =>
  0 <= processed =>
  processed <= KeygenM23SingularSpec.mode2_best_count_i =>
  KeygenM23SingularSpec.finish_acc_prefix
    best W32.zero processed =
    W32.of_int (processed * 1536).
proof.
move=> hbest.
move: processed.
apply intind.
+ move=> _.
  by rewrite KeygenM23SingularSpec.finish_acc_prefix0.
+ move=> processed hprocessed ih hcap.
  rewrite KeygenM23SingularSpec.finish_acc_prefixS 1://
          /KeygenM23SingularSpec.finish_acc_step.
  rewrite ih 1:/# hbest 1:/# finish_term_zero_exact
          W32.of_intD'.
  congr.
  ring.
qed.

lemma finish_acc_zero best :
  zero_best_5 best =>
  KeygenM23SingularSpec.finish_acc best W32.zero =
    W32.of_int 7680.
proof.
move=> hbest.
rewrite /KeygenM23SingularSpec.finish_acc.
rewrite finish_acc_zero_prefix 1://.
+ rewrite /KeygenM23SingularSpec.mode2_best_count_i.
  smt().
+ rewrite /KeygenM23SingularSpec.mode2_best_count_i.
  smt().
+ rewrite /KeygenM23SingularSpec.mode2_best_count_i /=.
  trivial.
qed.

lemma finish_mode2_zero_sum sum :
  zero_sum_256 sum =>
  KeygenM23SingularSpec.finish_mode2 sum = W64.of_int 120.
proof.
move=> hsum.
have hbest := best_scan_zero sum hsum.
have hmin := best_min_zero
  (KeygenM23SingularSpec.best_scan sum) hbest.
have hacc := finish_acc_zero
  (KeygenM23SingularSpec.best_scan sum) hbest.
change (
  (sigextu64
      (KeygenM23SingularSpec.finish_acc
        (KeygenM23SingularSpec.best_scan sum)
        (KeygenM23SingularSpec.best_min
          (KeygenM23SingularSpec.best_scan sum))) +
    W64.of_int 32) `|>>` W8.of_int 6 = W64.of_int 120).
rewrite hmin hacc.
rewrite KeygenM23FixedPointSemantics.sigextu64_semantics
        W32.to_sintK_small 1:/# W64.of_intD'.
rewrite /(`|>>`) W8.of_uintK /=.
rewrite KeygenM23FinalizeSemantics.w64_sar_nonnegative_of_int
        1,2:/#.
done.
qed.

lemma clear_prefix_zero_entries sum processed :
  0 <= processed =>
  processed <= KeygenM23SingularSpec.singular_words_i =>
  forall i, 0 <= i < processed =>
    BArray1024.get32
      (KeygenM23SingularSpec.clear_prefix sum processed) i =
      W32.zero.
proof.
move: processed.
apply intind.
+ move=> _ i hi.
  smt().
+ move=> processed hprocessed ih hcap i hi.
  rewrite KeygenM23SingularSpec.clear_prefixS 1://
          /KeygenM23SingularSpec.clear_step.
  rewrite BArray1024.get_set32E 1:/# 1:/#.
  case: (processed = i) => heq.
  + trivial.
  + apply ih.
    + smt().
    + smt().
qed.

lemma clear_sum_zero_entries sum :
  zero_sum_256 (KeygenM23SingularSpec.clear_sum sum).
proof.
rewrite /zero_sum_256 /KeygenM23SingularSpec.clear_sum.
apply clear_prefix_zero_entries.
rewrite /KeygenM23SingularSpec.singular_words_i.
smt().
rewrite /KeygenM23SingularSpec.singular_words_i.
smt().
qed.

lemma finish_mode2_clear_sum sum :
  KeygenM23SingularSpec.finish_mode2
    (KeygenM23SingularSpec.clear_sum sum) = W64.of_int 120.
proof.
apply finish_mode2_zero_sum.
exact (clear_sum_zero_entries sum).
qed.

end KeygenM23SingularZeroFinish.
