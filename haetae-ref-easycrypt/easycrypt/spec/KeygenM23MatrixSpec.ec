require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray8192.

theory KeygenM23MatrixSpec.

(* Structural mode-2 footprint constants and relations.  These predicates
   describe copied/active words only; they do not assign algebraic NTT
   semantics to the coefficients. *)
op mode2_rows_i : int = 2.
op mode2_cols_i : int = 3.
op poly_words_i : int = 256.

op mode2_s1_words_i : int = mode2_cols_i * poly_words_i.
op mode2_b_words_i : int = mode2_rows_i * poly_words_i.
op array_words_i : int = BArray8192.size %/ 4.

op ntt_stage_len (len : int) : bool =
     len = 1   \/ len = 2   \/ len = 4   \/ len = 8
  \/ len = 16  \/ len = 32  \/ len = 64  \/ len = 128
  \/ len = 256.

op m23_fwd_len_schedule (len : int) : bool =
     len = 0   \/ len = 1   \/ len = 2   \/ len = 4
  \/ len = 8   \/ len = 16  \/ len = 32  \/ len = 64
  \/ len = 128.

op m23_fwd_block_start (len start : int) : bool =
     (len = 128 /\ exists block, 0 <= block <= 1   /\ start = 256 * block)
  \/ (len = 64  /\ exists block, 0 <= block <= 2   /\ start = 128 * block)
  \/ (len = 32  /\ exists block, 0 <= block <= 4   /\ start = 64 * block)
  \/ (len = 16  /\ exists block, 0 <= block <= 8   /\ start = 32 * block)
  \/ (len = 8   /\ exists block, 0 <= block <= 16  /\ start = 16 * block)
  \/ (len = 4   /\ exists block, 0 <= block <= 32  /\ start = 8 * block)
  \/ (len = 2   /\ exists block, 0 <= block <= 64  /\ start = 4 * block)
  \/ (len = 1   /\ exists block, 0 <= block <= 128 /\ start = 2 * block).

op word_prefix_eq
    (left right : BArray8192.t) (words : int) : bool =
  forall i,
    0 <= i < words =>
    BArray8192.get32 left i = BArray8192.get32 right i.

op word_tail_frame
    (before after : BArray8192.t) (words : int) : bool =
  forall i,
    words <= i < array_words_i =>
    BArray8192.get32 after i = BArray8192.get32 before i.

op copy_index_bounds (copied words : int) : bool =
  0 <= copied /\ copied <= words /\ words <= array_words_i.

op copy_prefix_state
    (before source current : BArray8192.t) (copied words : int) : bool =
  copy_index_bounds copied words /\
  word_prefix_eq current source copied /\
  word_tail_frame before current words.

lemma word_tail_frame_refl a words :
  word_tail_frame a a words.
proof.
by rewrite /word_tail_frame.
qed.

lemma word_tail_frame_trans before middle after words :
  word_tail_frame before middle words =>
  word_tail_frame middle after words =>
  word_tail_frame before after words.
proof.
rewrite /word_tail_frame.
move=> hleft hright i hi.
by rewrite (hright i hi) (hleft i hi).
qed.

lemma ntt_stage_len_one :
  ntt_stage_len 1.
proof. by rewrite /ntt_stage_len. qed.

lemma ntt_stage_len_active_bounds len :
  ntt_stage_len len =>
  len < 256 =>
  1 <= len <= 128.
proof.
rewrite /ntt_stage_len.
by move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]]; smt().
qed.

lemma ntt_stage_len_double len :
  ntt_stage_len len =>
  len < 256 =>
  ntt_stage_len (2 * len).
proof.
rewrite /ntt_stage_len.
by move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]] //=.
qed.

lemma ntt_block_next_bound len block :
  ntt_stage_len len =>
  len < 256 =>
  0 <= block =>
  2 * block * len < 256 =>
  2 * (block + 1) * len <= 256.
proof.
rewrite /ntt_stage_len.
by move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]] //; smt().
qed.

lemma m23_fwd_len_schedule_shr1 len :
  m23_fwd_len_schedule len =>
  m23_fwd_len_schedule (len %/ 2).
proof.
rewrite /m23_fwd_len_schedule.
by move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]];
   rewrite /m23_fwd_len_schedule /=.
qed.

lemma m23_fwd_block_start_zero len :
  m23_fwd_len_schedule len =>
  0 < len =>
  m23_fwd_block_start len 0.
proof.
rewrite /m23_fwd_len_schedule /m23_fwd_block_start.
move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]] // _.
+ right; right; right; right; right; right; right.
  split; first trivial.
  by exists 0.
+ right; right; right; right; right; right.
  left; split; first trivial.
  by exists 0.
+ right; right; right; right; right.
  left; split; first trivial.
  by exists 0.
+ right; right; right; right.
  left; split; first trivial.
  by exists 0.
+ right; right; right.
  left; split; first trivial.
  by exists 0.
+ right; right.
  left; split; first trivial.
  by exists 0.
+ right.
  left; split; first trivial.
  by exists 0.
+ left.
  split; first trivial.
  by exists 0.
qed.

lemma m23_fwd_block_active_bound len start :
  m23_fwd_len_schedule len =>
  0 < len =>
  m23_fwd_block_start len start =>
  start < poly_words_i =>
  start + 2 * len <= poly_words_i.
proof.
rewrite /m23_fwd_block_start /poly_words_i.
move=> _ _.
by move=> [[-> [block [hblock hstart]]] |
          [[-> [block [hblock hstart]]] |
          [[-> [block [hblock hstart]]] |
          [[-> [block [hblock hstart]]] |
          [[-> [block [hblock hstart]]] |
          [[-> [block [hblock hstart]]] |
          [[-> [block [hblock hstart]]] |
           [-> [block [hblock hstart]]]]]]]]]]; smt().
qed.

lemma m23_fwd_block_start_step len start :
  m23_fwd_len_schedule len =>
  0 < len =>
  m23_fwd_block_start len start =>
  start < poly_words_i =>
  m23_fwd_block_start len (start + 2 * len).
proof.
move=> hsched hpos hstart hactive.
have hcap :=
  m23_fwd_block_active_bound len start hsched hpos hstart hactive.
move: hstart.
rewrite /m23_fwd_block_start.
move=> [[-> [block [hblock hstart]]] |
        [[-> [block [hblock hstart]]] |
        [[-> [block [hblock hstart]]] |
        [[-> [block [hblock hstart]]] |
        [[-> [block [hblock hstart]]] |
        [[-> [block [hblock hstart]]] |
        [[-> [block [hblock hstart]]] |
         [-> [block [hblock hstart]]]]]]]]]].
+ rewrite /m23_fwd_block_start /=.
  by exists (block + 1); smt().
+ rewrite /m23_fwd_block_start /=.
  by exists (block + 1); smt().
+ rewrite /m23_fwd_block_start /=.
  by exists (block + 1); smt().
+ rewrite /m23_fwd_block_start /=.
  by exists (block + 1); smt().
+ rewrite /m23_fwd_block_start /=.
  by exists (block + 1); smt().
+ rewrite /m23_fwd_block_start /=.
  by exists (block + 1); smt().
+ rewrite /m23_fwd_block_start /=.
  by exists (block + 1); smt().
+ rewrite /m23_fwd_block_start /=.
  by exists (block + 1); smt().
qed.

lemma invntt_counter_next_bound len z0 block :
  ntt_stage_len len =>
  len < 256 =>
  0 <= z0 =>
  z0 * len = 256 * (len - 1) =>
  0 <= block =>
  2 * block * len < 256 =>
  z0 + block + 1 <= 255.
proof.
rewrite /ntt_stage_len.
by move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]] //; smt().
qed.

lemma word_prefix_eq_get32 lhs rhs words i :
  word_prefix_eq lhs rhs words =>
  0 <= i < words =>
  BArray8192.get32 lhs i = BArray8192.get32 rhs i.
proof.
by rewrite /word_prefix_eq; move=> hprefix; apply hprefix.
qed.

lemma word_prefix_eq_set32_same
    lhs rhs words i left_word right_word :
  0 <= i < words =>
  words <= array_words_i =>
  word_prefix_eq lhs rhs words =>
  left_word = right_word =>
  word_prefix_eq
    (BArray8192.set32 lhs i left_word)
    (BArray8192.set32 rhs i right_word)
    words.
proof.
rewrite /word_prefix_eq /array_words_i.
move=> hi hwords hprefix heq j hj.
rewrite !BArray8192.get_set32E 1:/# 1:/# 1:/# 1:/#.
case (i = j) => hij.
+ by rewrite heq.
+ by apply hprefix.
qed.

lemma word_prefix_eq_extend_set32
    current source copied words :
  0 <= copied < words =>
  words <= array_words_i =>
  word_prefix_eq current source copied =>
  word_prefix_eq
    (BArray8192.set32 current copied (BArray8192.get32 source copied))
    source (copied + 1).
proof.
rewrite /word_prefix_eq /array_words_i.
move=> hcopied hwords hprefix i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (copied = i) => heq.
+ by rewrite -heq.
by apply hprefix; smt().
qed.

lemma word_prefix_eq_extend_same_set32
    left0 right0 copied w :
  0 <= copied < array_words_i =>
  word_prefix_eq left0 right0 copied =>
  word_prefix_eq
    (BArray8192.set32 left0 copied w)
    (BArray8192.set32 right0 copied w)
    (copied + 1).
proof.
rewrite /word_prefix_eq /array_words_i.
move=> hcopied hprefix i hi.
rewrite !BArray8192.get_set32E 1:/# 1:/# 1:/# 1:/#.
case (copied = i) => heq.
+ trivial.
by apply hprefix; smt().
qed.

lemma word_tail_frame_set32_before
    before current copied words w :
  0 <= copied < words =>
  words <= array_words_i =>
  word_tail_frame before current words =>
  word_tail_frame before (BArray8192.set32 current copied w) words.
proof.
rewrite /word_tail_frame /array_words_i.
move=> hcopied hwords hframe i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : copied <> i by smt().
rewrite ifF 1:/#.
by apply hframe.
qed.

lemma copy_prefix_state_step before source current copied words :
  copy_prefix_state before source current copied words =>
  copied < words =>
  copy_prefix_state
    before source
    (BArray8192.set32 current copied (BArray8192.get32 source copied))
    (copied + 1) words.
proof.
rewrite /copy_prefix_state.
move=> [hbounds [hprefix hframe]] hlt.
split.
+ move: hbounds.
  rewrite /copy_index_bounds.
  smt().
split.
+ apply (word_prefix_eq_extend_set32 current source copied words);
     move: hbounds; rewrite /copy_index_bounds; smt().
+ apply (word_tail_frame_set32_before
           before current copied words
           (BArray8192.get32 source copied));
     move: hbounds; rewrite /copy_index_bounds; smt().
qed.

end KeygenM23MatrixSpec.
