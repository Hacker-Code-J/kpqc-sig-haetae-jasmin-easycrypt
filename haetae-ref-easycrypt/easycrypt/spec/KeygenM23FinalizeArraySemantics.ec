require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray8192 Fq KeygenM23MatrixSpec.
require import KeygenM23FinalizeSpec KeygenM23FinalizeSemantics.

theory KeygenM23FinalizeArraySemantics.

(* The finalizer receives a signed inverse-NTT output [b], a centered
   secret coefficient [s2], and a canonical uniform coefficient [a].
   This definition records the mathematical integer before the target
   performs its two word additions. *)
op raw_sum_int (b s2 a : W32.t) : int =
  W32.to_sint b + W32.to_sint s2 + W32.to_uint a.

op raw_residue (b s2 a : W32.t) : int =
  raw_sum_int b s2 a %% KeygenM23FinalizeSemantics.q.

op reachable_word_inputs (b s2 a : W32.t) : bool =
  Fq.bw32 b 16 /\
  -1 <= W32.to_sint s2 <= 1 /\
  W32.to_uint a < KeygenM23FinalizeSemantics.q.

lemma mode2_b_words_eq512 :
  KeygenM23MatrixSpec.mode2_b_words_i = 512.
proof.
by rewrite /KeygenM23MatrixSpec.mode2_b_words_i
           /KeygenM23MatrixSpec.mode2_rows_i
           /KeygenM23MatrixSpec.poly_words_i.
qed.

lemma reachable_s2_bw1 (s2 : W32.t) :
  -1 <= W32.to_sint s2 <= 1 =>
  Fq.bw32 s2 1.
proof.
rewrite /Fq.bw32 /=.
smt().
qed.

lemma reachable_uniform_to_sint (a : W32.t) :
  W32.to_uint a < KeygenM23FinalizeSemantics.q =>
  W32.to_sint a = W32.to_uint a.
proof.
move=> ha.
apply W32.to_sint_unsigned.
rewrite W32.to_sintE /W32.smod
        /KeygenM23FinalizeSemantics.q /=.
have hu := W32.to_uint_cmp a.
smt().
qed.

lemma reachable_uniform_bw16 (a : W32.t) :
  W32.to_uint a < KeygenM23FinalizeSemantics.q =>
  Fq.bw32 a 16.
proof.
move=> ha.
rewrite /Fq.bw32 (reachable_uniform_to_sint a ha)
        /KeygenM23FinalizeSemantics.q /=.
have hu := W32.to_uint_cmp a.
smt().
qed.

lemma reachable_sum_bw18 (b s2 a : W32.t) :
  reachable_word_inputs b s2 a =>
  Fq.bw32 ((b + s2) + a) 18.
proof.
rewrite /reachable_word_inputs.
move=> [hb [hs2 ha]].
have hs2bw : Fq.bw32 s2 1 by exact (reachable_s2_bw1 s2 hs2).
have habw : Fq.bw32 a 16 by exact (reachable_uniform_bw16 a ha).
have hbs : Fq.bw32 (b + s2) 17.
+ exact (Fq.add_corr b s2 16 1 _ _ hb hs2bw); smt().
exact (Fq.add_corr (b + s2) a 17 16 _ _ hbs habw); smt().
qed.

lemma reachable_sum_to_sint (b s2 a : W32.t) :
  reachable_word_inputs b s2 a =>
  W32.to_sint ((b + s2) + a) = raw_sum_int b s2 a.
proof.
rewrite /reachable_word_inputs.
move=> [hb [hs2 ha]].
have haeq := reachable_uniform_to_sint a ha.
rewrite /raw_sum_int W32.to_sintD_small.
+ have hs2bw : Fq.bw32 s2 1 by
    exact (reachable_s2_bw1 s2 hs2).
  have hbsbw : Fq.bw32 (b + s2) 17.
  + exact (Fq.add_corr b s2 16 1 _ _ hb hs2bw); smt().
  move: hbsbw.
  rewrite /Fq.bw32 /= haeq.
  rewrite /KeygenM23FinalizeSemantics.q in ha.
  have hu := W32.to_uint_cmp a.
  smt().
+ rewrite W32.to_sintD_small.
  + move: hb.
    rewrite /Fq.bw32 /=.
    smt().
  + by rewrite haeq.
qed.

lemma reachable_sum_exact_and_bw18 (b s2 a : W32.t) :
  reachable_word_inputs b s2 a =>
  W32.to_sint ((b + s2) + a) = raw_sum_int b s2 a /\
  Fq.bw32 ((b + s2) + a) 18.
proof.
move=> hreachable.
split.
+ exact (reachable_sum_to_sint b s2 a hreachable).
+ exact (reachable_sum_bw18 b s2 a hreachable).
qed.

lemma reachable_finalize_words_decode (b s2 a : W32.t) :
  reachable_word_inputs b s2 a =>
  W32.to_uint (KeygenM23FinalizeSpec.finalize_b_word b s2 a) =
    KeygenM23FinalizeSemantics.vk_high_int (raw_residue b s2 a) /\
  W32.to_sint (KeygenM23FinalizeSpec.finalize_s2_word b s2 a) =
    W32.to_sint s2 -
      KeygenM23FinalizeSemantics.vk_low_int (raw_residue b s2 a).
proof.
move=> hreachable.
have hsum := reachable_sum_bw18 b s2 a hreachable.
have hfinal :=
  KeygenM23FinalizeSemantics.finalize_words_semantics b s2 a hsum.
rewrite (reachable_sum_to_sint b s2 a hreachable) in hfinal.
rewrite /raw_residue in hfinal.
move: hfinal => [hb hs2].
split.
+ have hx :
      0 <= raw_residue b s2 a <
        KeygenM23FinalizeSemantics.q.
  + rewrite /raw_residue.
    apply modz_cmp.
    rewrite /KeygenM23FinalizeSemantics.q.
    smt().
  have hh :=
    KeygenM23FinalizeSemantics.vk_high_int_range
      (raw_residue b s2 a) hx.
  have hcast :
      W32.to_uint
        (W32.of_int
          (KeygenM23FinalizeSemantics.vk_high_int
            (raw_residue b s2 a))) =
      KeygenM23FinalizeSemantics.vk_high_int
        (raw_residue b s2 a).
  + apply W32.to_uint_small.
    smt().
  by rewrite hb hcast.
+ have hl :=
    KeygenM23FinalizeSemantics.vk_low_int_range
      (raw_residue b s2 a).
  have hlcast :
      W32.to_sint
        (W32.of_int
          (KeygenM23FinalizeSemantics.vk_low_int
            (raw_residue b s2 a))) =
      KeygenM23FinalizeSemantics.vk_low_int
        (raw_residue b s2 a).
  + apply W32.to_sintK_small.
    smt().
  have hdiff :
      W32.min_sint <=
        W32.to_sint s2 -
          W32.to_sint
            (W32.of_int
              (KeygenM23FinalizeSemantics.vk_low_int
                (raw_residue b s2 a))) <=
      W32.max_sint.
  + rewrite hlcast.
    rewrite /reachable_word_inputs in hreachable.
    smt().
  have hsub :=
    W32.to_sintB_small
      s2
      (W32.of_int
        (KeygenM23FinalizeSemantics.vk_low_int
          (raw_residue b s2 a)))
      hdiff.
  rewrite hs2 hsub hlcast.
  trivial.
qed.

(* [mode2_b_words_i] is 2 * 256 = 512.  The semantic predicate covers
   exactly that active prefix and retains the exact finalizer's two tail
   frame guarantees. *)
op finalize_reachable_inputs
    (bp0 s2p0 ap0 : BArray8192.t) : bool =
  forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    reachable_word_inputs
      (BArray8192.get32 bp0 i)
      (BArray8192.get32 s2p0 i)
      (BArray8192.get32 ap0 i).

op finalize_semantic_output
    (bp0 s2p0 ap0 bp s2p : BArray8192.t) : bool =
  (forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    W32.to_uint (BArray8192.get32 bp i) =
      KeygenM23FinalizeSemantics.vk_high_int
        (raw_residue
          (BArray8192.get32 bp0 i)
          (BArray8192.get32 s2p0 i)
          (BArray8192.get32 ap0 i)) /\
    W32.to_sint (BArray8192.get32 s2p i) =
      W32.to_sint (BArray8192.get32 s2p0 i) -
        KeygenM23FinalizeSemantics.vk_low_int
          (raw_residue
            (BArray8192.get32 bp0 i)
            (BArray8192.get32 s2p0 i)
            (BArray8192.get32 ap0 i))) /\
  KeygenM23MatrixSpec.word_tail_frame
    bp0 bp KeygenM23MatrixSpec.mode2_b_words_i /\
  KeygenM23MatrixSpec.word_tail_frame
    s2p0 s2p KeygenM23MatrixSpec.mode2_b_words_i.

lemma finalize_output_semantics
    (bp0 s2p0 ap0 bp s2p : BArray8192.t) :
  finalize_reachable_inputs bp0 s2p0 ap0 =>
  KeygenM23FinalizeSpec.finalize_output bp0 s2p0 ap0 bp s2p =>
  finalize_semantic_output bp0 s2p0 ap0 bp s2p.
proof.
move=> hreachable.
rewrite /KeygenM23FinalizeSpec.finalize_output
        /KeygenM23FinalizeSpec.finalize_prefix.
move=> [_ [hbp [hs2 [hbptail hs2tail]]]].
rewrite /finalize_semantic_output.
split.
+ move=> i hi.
  have hword :=
    reachable_finalize_words_decode
      (BArray8192.get32 bp0 i)
      (BArray8192.get32 s2p0 i)
      (BArray8192.get32 ap0 i)
      (hreachable i hi).
  rewrite (hbp i hi) (hs2 i hi).
  exact hword.
+ split.
  + exact hbptail.
  + exact hs2tail.
qed.

end KeygenM23FinalizeArraySemantics.
