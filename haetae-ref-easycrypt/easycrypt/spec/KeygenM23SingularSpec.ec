require import AllCore IntDiv List Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray20 BArray1024 BArray2048.

theory KeygenM23SingularSpec.

op singular_words_i : int = 256.
op mode2_best_count_i : int = 5.
op mode2_tau_i : int = 58.
op mode2_rem_i : int = 24.

op minmax_word (a b : W32.t) : W32.t * W32.t =
  let ab = b `^` a in
  let c0 = b - a in
  let t = (c0 `^` b) `&` ab in
  let c1 = (c0 `^` t) `|>>` W8.of_int 31 in
  let c2 = c1 `&` ab in
  (a `^` c2, b `^` c2).

op mulrnd16_word (x y : W32.t) : W32.t =
  truncateu32
    (((sigextu64 x * sigextu64 y) + W64.of_int 32768)
      `|>>` W8.of_int 16).

op fft_sqabs_at (input : BArray2048.t) (i : int) : W32.t =
  let real = BArray2048.get32 input (2 * i) in
  let imag = BArray2048.get32 input (2 * i + 1) in
  mulrnd16_word real real + mulrnd16_word imag imag.

op accumulate_step
    (input : BArray2048.t) (sum : BArray1024.t) (i : int)
    : BArray1024.t =
  BArray1024.set32 sum i
    (BArray1024.get32 sum i + fft_sqabs_at input i).

op accumulate_prefix
    (sum : BArray1024.t) (input : BArray2048.t) (processed : int)
    : BArray1024.t =
  foldl (accumulate_step input) sum (iota_ 0 processed).

op accumulate_fft_sqabs
    (sum : BArray1024.t) (input : BArray2048.t) : BArray1024.t =
  accumulate_prefix sum input singular_words_i.

op clear_step (sum : BArray1024.t) (i : int) : BArray1024.t =
  BArray1024.set32 sum i W32.zero.

op clear_prefix (sum : BArray1024.t) (processed : int) : BArray1024.t =
  foldl clear_step sum (iota_ 0 processed).

op clear_sum (sum : BArray1024.t) : BArray1024.t =
  clear_prefix sum singular_words_i.

op best_init_step
    (sum : BArray1024.t) (best : BArray20.t) (i : int) : BArray20.t =
  BArray20.set32 best i (BArray1024.get32 sum i).

op best_init_prefix
    (sum : BArray1024.t) (processed : int) : BArray20.t =
  foldl (best_init_step sum) witness (iota_ 0 processed).

op best_init (sum : BArray1024.t) : BArray20.t =
  best_init_prefix sum mode2_best_count_i.

type insert_state = W32.t * BArray20.t.

op best_insert_step (st : insert_state) (j : int) : insert_state =
  let mm = minmax_word st.`1 (BArray20.get32 st.`2 j) in
  (mm.`1, BArray20.set32 st.`2 j mm.`2).

op best_insert_prefix
    (x : W32.t) (best : BArray20.t) (processed : int) : insert_state =
  foldl best_insert_step (x, best) (iota_ 0 processed).

op best_insert (x : W32.t) (best : BArray20.t) : BArray20.t =
  (best_insert_prefix x best mode2_best_count_i).`2.

op best_scan_step
    (sum : BArray1024.t) (best : BArray20.t) (i : int) : BArray20.t =
  best_insert (BArray1024.get32 sum i) best.

op best_scan_prefix
    (sum : BArray1024.t) (processed : int) : BArray20.t =
  foldl (best_scan_step sum) (best_init sum)
    (iota_ mode2_best_count_i (processed - mode2_best_count_i)).

op best_scan (sum : BArray1024.t) : BArray20.t =
  best_scan_prefix sum singular_words_i.

op best_min_step
    (best : BArray20.t) (minimum : W32.t) (i : int) : W32.t =
  (minmax_word minimum (BArray20.get32 best i)).`1.

op best_min_prefix (best : BArray20.t) (processed : int) : W32.t =
  foldl (best_min_step best) (BArray20.get32 best 0)
    (iota_ 1 (processed - 1)).

op best_min (best : BArray20.t) : W32.t =
  best_min_prefix best mode2_best_count_i.

op finish_factor_word (minimum value : W32.t) : W32.t =
  let fac0 = (minimum - value) `|>>` W8.of_int 31 in
  let notfac =
    (fac0 `^` W32.of_int 4294967295) `&` W32.of_int mode2_rem_i in
  (fac0 `&` W32.of_int mode2_tau_i) `^` notfac.

op finish_term_word (minimum value : W32.t) : W32.t =
  ((value + W32.of_int 66048) `|>>` W8.of_int 10) *
    finish_factor_word minimum value.

op finish_acc_step
    (best : BArray20.t) (minimum acc : W32.t) (i : int) : W32.t =
  acc + finish_term_word minimum (BArray20.get32 best i).

op finish_acc_prefix
    (best : BArray20.t) (minimum : W32.t) (processed : int) : W32.t =
  foldl (finish_acc_step best minimum) W32.zero (iota_ 0 processed).

op finish_acc (best : BArray20.t) (minimum : W32.t) : W32.t =
  finish_acc_prefix best minimum mode2_best_count_i.

op finish_mode2 (sum : BArray1024.t) : W64.t =
  let best = best_scan sum in
  let minimum = best_min best in
  let acc = finish_acc best minimum in
  (sigextu64 acc + W64.of_int 32) `|>>` W8.of_int 6.

lemma accumulate_prefix0 sum input :
  accumulate_prefix sum input 0 = sum.
proof. by rewrite /accumulate_prefix iota0. qed.

lemma accumulate_prefixS sum input processed :
  0 <= processed =>
  accumulate_prefix sum input (processed + 1) =
    accumulate_step input (accumulate_prefix sum input processed) processed.
proof.
move=> hprocessed.
by rewrite /accumulate_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma clear_prefix0 sum :
  clear_prefix sum 0 = sum.
proof. by rewrite /clear_prefix iota0. qed.

lemma clear_prefixS sum processed :
  0 <= processed =>
  clear_prefix sum (processed + 1) =
    clear_step (clear_prefix sum processed) processed.
proof.
move=> hprocessed.
by rewrite /clear_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma best_init_prefix0 sum :
  best_init_prefix sum 0 = witness.
proof. by rewrite /best_init_prefix iota0. qed.

lemma best_init_prefixS sum processed :
  0 <= processed =>
  best_init_prefix sum (processed + 1) =
    best_init_step sum (best_init_prefix sum processed) processed.
proof.
move=> hprocessed.
by rewrite /best_init_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma best_insert_prefix0 x best :
  best_insert_prefix x best 0 = (x, best).
proof. by rewrite /best_insert_prefix iota0. qed.

lemma best_insert_prefixS x best processed :
  0 <= processed =>
  best_insert_prefix x best (processed + 1) =
    best_insert_step (best_insert_prefix x best processed) processed.
proof.
move=> hprocessed.
by rewrite /best_insert_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma best_scan_prefix_start sum :
  best_scan_prefix sum mode2_best_count_i = best_init sum.
proof.
by rewrite /best_scan_prefix /mode2_best_count_i iota0.
qed.

lemma best_scan_prefixS sum processed :
  mode2_best_count_i <= processed =>
  best_scan_prefix sum (processed + 1) =
    best_scan_step sum (best_scan_prefix sum processed) processed.
proof.
move=> hprocessed.
rewrite /best_scan_prefix.
have hcount : 0 <= processed - mode2_best_count_i by smt().
rewrite (_ : processed + 1 - mode2_best_count_i =
             (processed - mode2_best_count_i) + 1) 1:/#.
rewrite iotaSr 1:hcount foldl_rcons /=.
congr.
by rewrite /mode2_best_count_i; ring.
qed.

lemma best_min_prefix_start best :
  best_min_prefix best 1 = BArray20.get32 best 0.
proof. by rewrite /best_min_prefix iota0. qed.

lemma best_min_prefixS best processed :
  1 <= processed =>
  best_min_prefix best (processed + 1) =
    best_min_step best (best_min_prefix best processed) processed.
proof.
move=> hprocessed.
rewrite /best_min_prefix.
have hcount : 0 <= processed - 1 by smt().
rewrite (_ : processed + 1 - 1 = (processed - 1) + 1) 1:/#.
by rewrite iotaSr 1:hcount foldl_rcons.
qed.

lemma finish_acc_prefix0 best minimum :
  finish_acc_prefix best minimum 0 = W32.zero.
proof. by rewrite /finish_acc_prefix iota0. qed.

lemma finish_acc_prefixS best minimum processed :
  0 <= processed =>
  finish_acc_prefix best minimum (processed + 1) =
    finish_acc_step best minimum
      (finish_acc_prefix best minimum processed) processed.
proof.
move=> hprocessed.
by rewrite /finish_acc_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

end KeygenM23SingularSpec.
