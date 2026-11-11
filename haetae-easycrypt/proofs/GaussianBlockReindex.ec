require import AllCore IntDiv StdRing StdOrder RealSeries.
import IntOrder RField RealOrder.

lemma gb_translation_bijective (offset : int) :
  bijective (fun y : int => offset+y).
proof.
  exists (fun y : int => y-offset); split.
  + by move=> y; ring.
  by move=> y; ring.
qed.

lemma gb_quotient_translate (N x y : int) : 0 < N =>
  (x = (N*x+y) %/ N) <=> (0 <= y < N).
proof.
  move=> hN.
  have he : N*x+y = x*N+y by ring.
  have hz := divz_eq0 y N hN.
  rewrite he divzMDl 1:/#; smt().
qed.

(* Restricting a translated summable series preserves summability. This
   proves the condition for every inner block before any sum is moved. *)
lemma gb_block_inner_summable (N : int) (f : int -> real) (x : int) :
  RealSeries.summable f =>
  RealSeries.summable (fun y =>
    if 0 <= x /\ 0 <= y < N then f (N*x+y) else 0%r).
proof.
  move=> hs.
  have ht := RealSeries.summable_bij (fun y : int => N*x+y) f
    (gb_translation_bijective (N*x)) hs.
  have hc := RealSeries.summable_cond (f \o (fun y : int => N*x+y))
    (fun y => 0 <= x /\ 0 <= y < N) ht.
  exact hc.
qed.

(* A quotient fibre is reindexed by one translation Z -> Z. Negative
   fibres carry zero because f itself vanishes at negative integers. *)
lemma gb_block_fibre (N : int) (f : int -> real) (x : int) :
  0 < N => RealSeries.summable f =>
  (forall z, z < 0 => f z = 0%r) =>
  RealSeries.sum (fun y =>
    if 0 <= x /\ 0 <= y < N then f (N*x+y) else 0%r) =
  RealSeries.sum (fun z => if x = z %/ N then f z else 0%r).
proof.
  move=> hN hs hnegative.
  have hf := RealSeries.summable_cond f (fun z => x = z %/ N) hs.
  have ht := RealSeries.sum_reindex (fun y : int => N*x+y)
    (fun z => if x = z %/ N then f z else 0%r)
    (gb_translation_bijective (N*x)) hf.
  rewrite -ht; apply RealSeries.eq_sum => y /=.
  rewrite /(\o) /= (gb_quotient_translate N x y hN).
  case (0 <= x) => hx /=; first trivial.
  case (0 <= y < N) => hy /=; last trivial.
  have hquot : x = (N*x+y) %/ N by rewrite gb_quotient_translate.
  have hsign := divz_ge0 (N*x+y) N hN.
  have hz : N*x+y < 0 by smt().
  by rewrite (hnegative (N*x+y) hz).
qed.

lemma gb_block_outer_summable (N : int) (f : int -> real) :
  0 < N => RealSeries.summable f =>
  (forall z, z < 0 => f z = 0%r) =>
  RealSeries.summable (fun x => RealSeries.sum (fun y =>
    if 0 <= x /\ 0 <= y < N then f (N*x+y) else 0%r)).
proof.
  move=> hN hs hnegative.
  have hp := RealSeries.summable_partition (fun z : int => z %/ N) f hs.
  apply (RealSeries.eqL_summable _ _ hp) => x /=.
  by rewrite (gb_block_fibre N f x hN hs hnegative).
qed.

lemma gb_block_sum (N : int) (f : int -> real) :
  0 < N => RealSeries.summable f =>
  (forall z, z < 0 => f z = 0%r) =>
  RealSeries.sum (fun x => RealSeries.sum (fun y =>
    if 0 <= x /\ 0 <= y < N then f (N*x+y) else 0%r)) = RealSeries.sum f.
proof.
  move=> hN hs hnegative.
  rewrite (RealSeries.sum_partition (fun z : int => z %/ N) f hs).
  apply RealSeries.eq_sum => x /=.
  exact (gb_block_fibre N f x hN hs hnegative).
qed.
