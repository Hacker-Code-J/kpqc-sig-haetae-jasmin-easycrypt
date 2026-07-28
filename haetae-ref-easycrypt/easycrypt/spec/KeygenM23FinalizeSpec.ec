require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8192 KeygenM23MatrixSpec.

theory KeygenM23FinalizeSpec.

(* These operations intentionally stay at the extracted word level.  In
   particular, [freeze_word] records the exact instruction sequence used by
   the target without assigning it an unproved canonical-residue meaning. *)
op freeze_word (a : W32.t) : W32.t =
  let x0 = sigextu64 a in
  let t0 = x0 * W64.of_int 66575 in
  let t1 = t0 `|>>` W8.of_int 32 in
  let t2 = t1 * W64.of_int 64513 in
  let x1 = x0 - t2 in
  let mask0 = (x1 `|>>` W8.of_int 31) `&` W64.of_int 129026 in
  let x2 = x1 + mask0 in
  let mask1 = (x2 - W64.of_int 64513) `|>>` W8.of_int 31 in
  let mask32 = (truncateu32 mask1 + W32.one) * W32.of_int 64513 in
  truncateu32 (x2 - zeroextu64 mask32).

op frozen_sum_word (b s2 a : W32.t) : W32.t =
  freeze_word ((b + s2) + a).

op egen_low_word (b : W32.t) : W32.t =
  let low0 = b `&` W32.one in
  let tmp = ((b `|>>` W8.of_int 1) `&` low0) `<<` W8.of_int 1 in
  low0 - tmp.

op egen_high_word (b : W32.t) : W32.t =
  (b - egen_low_word b) `|>>` W8.of_int 1.

op finalize_b_word (b s2 a : W32.t) : W32.t =
  egen_high_word (frozen_sum_word b s2 a).

op finalize_s2_word (b s2 a : W32.t) : W32.t =
  s2 - egen_low_word (frozen_sum_word b s2 a).

op finalize_prefix
    (bp0 s2p0 ap0 bp s2p : BArray8192.t) (processed : int) : bool =
  0 <= processed <= KeygenM23MatrixSpec.mode2_b_words_i /\
  (forall i,
    0 <= i < processed =>
    BArray8192.get32 bp i =
      finalize_b_word
        (BArray8192.get32 bp0 i)
        (BArray8192.get32 s2p0 i)
        (BArray8192.get32 ap0 i)) /\
  (forall i,
    0 <= i < processed =>
    BArray8192.get32 s2p i =
      finalize_s2_word
        (BArray8192.get32 bp0 i)
        (BArray8192.get32 s2p0 i)
        (BArray8192.get32 ap0 i)) /\
  KeygenM23MatrixSpec.word_tail_frame
    bp0 bp processed /\
  KeygenM23MatrixSpec.word_tail_frame
    s2p0 s2p processed.

op finalize_output
    (bp0 s2p0 ap0 bp s2p : BArray8192.t) : bool =
  finalize_prefix
    bp0 s2p0 ap0 bp s2p KeygenM23MatrixSpec.mode2_b_words_i.

lemma finalize_prefix_refl bp0 s2p0 ap0 :
  finalize_prefix bp0 s2p0 ap0 bp0 s2p0 0.
proof.
rewrite /finalize_prefix.
do split.
+ rewrite /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i.
  smt().
+ by smt().
qed.

lemma word_tail_frame_advance_set32 before current processed w :
  0 <= processed < KeygenM23MatrixSpec.array_words_i =>
  KeygenM23MatrixSpec.word_tail_frame before current processed =>
  KeygenM23MatrixSpec.word_tail_frame
    before (BArray8192.set32 current processed w) (processed + 1).
proof.
rewrite /KeygenM23MatrixSpec.word_tail_frame
        /KeygenM23MatrixSpec.array_words_i.
move=> hprocessed hframe i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : processed <> i by smt().
rewrite ifF 1:/#.
by apply hframe; smt().
qed.

lemma finalize_prefix_step bp0 s2p0 ap0 bp s2p processed :
  finalize_prefix bp0 s2p0 ap0 bp s2p processed =>
  processed < KeygenM23MatrixSpec.mode2_b_words_i =>
  finalize_prefix
    bp0 s2p0 ap0
    (BArray8192.set32 bp processed
      (finalize_b_word
        (BArray8192.get32 bp0 processed)
        (BArray8192.get32 s2p0 processed)
        (BArray8192.get32 ap0 processed)))
    (BArray8192.set32 s2p processed
      (finalize_s2_word
        (BArray8192.get32 bp0 processed)
        (BArray8192.get32 s2p0 processed)
        (BArray8192.get32 ap0 processed)))
    (processed + 1).
proof.
rewrite /finalize_prefix.
move=> [hdone [hbp [hs2 [hbpframe hs2frame]]]] hlt.
have harray :
    0 <= processed < KeygenM23MatrixSpec.array_words_i.
+ move: hdone hlt.
  rewrite /KeygenM23MatrixSpec.array_words_i
          /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i
          /BArray8192.size /=.
  smt().
split; first smt().
split.
+ move=> i hi.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (processed = i) => heq.
  + by rewrite -heq.
  by apply hbp; smt().
split.
+ move=> i hi.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (processed = i) => heq.
  + by rewrite -heq.
  by apply hs2; smt().
split.
+ apply (word_tail_frame_advance_set32 bp0 bp processed).
  + exact harray.
  + exact hbpframe.
+ apply (word_tail_frame_advance_set32 s2p0 s2p processed).
  + exact harray.
  + exact hs2frame.
qed.

lemma finalize_prefix_final bp0 s2p0 ap0 bp s2p :
  finalize_prefix
    bp0 s2p0 ap0 bp s2p KeygenM23MatrixSpec.mode2_b_words_i =>
  finalize_output bp0 s2p0 ap0 bp s2p.
proof.
by rewrite /finalize_output.
qed.

end KeygenM23FinalizeSpec.
