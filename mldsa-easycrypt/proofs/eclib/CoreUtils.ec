(* -------------------------------------------------------------------- *)
require import AllCore.

(* -------------------------------------------------------------------- *)
op pairxmap ['a 'b] (f : 'a -> 'a -> 'b) (xy1 xy2 : 'a * 'a) =
  (f xy1.`1 xy2.`1, f xy1.`2 xy2.`2).

(* -------------------------------------------------------------------- *)
lemma pairxmapE ['a 'b] (f : 'a -> 'a -> 'b) (x1 y1 x2 y2 : 'a) :
  pairxmap f (x1, y1) (x2, y2) = (f x1 x2, f y1 y2).
proof. done. qed.

hint simplify pairxmapE.

(* -------------------------------------------------------------------- *)
lemma compE ['a 'b 'c] (g : 'b -> 'c) (f : 'a -> 'b) :
  forall x, (g \o f) x = g (f x).
proof. by done. qed.

hint simplify compE.
