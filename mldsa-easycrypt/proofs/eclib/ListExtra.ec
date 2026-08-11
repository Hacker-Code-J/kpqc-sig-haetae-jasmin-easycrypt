require import AllCore List.

(* move to list theory *)
lemma in_map_id ['a] (f : 'a -> 'a) (s : 'a list) :
  (forall x, x \in s => f x = x) => map f s = s.
proof. by move=> id_f; rewrite -{2}[s]map_id &(eq_in_map). qed.

lemma in_map_cancel ['a 'b] (f : 'a -> 'b) (g : 'b -> 'a) (s : 'a list) :
  (forall x, x \in s => g (f x) = x) => map g (map f s) = s.
proof. by move=> can_fg; rewrite -map_comp in_map_id. qed.

lemma flatten_map_seq1 ['a 'b] (f : 'a -> 'b) (s : 'a list) :
  flatten (map (fun x => [f x]) s) = map f s.
proof. by elim: s. qed.

lemma flatten_mkseq_seq1 ['a] (f : int -> 'a) (n : int) :
  flatten (mkseq (fun i => [f i]) n) = mkseq f n.
proof. by apply: flatten_map_seq1. qed.
(* *)

(* -------------------------------------------------------------------- *)
lemma take_mkseqE ['a] (x0 : 'a) (s : 'a list) (i : int) : 0 <= i <= size s =>
  take i s = mkseq (fun j => nth x0 s j) i.
proof.
move=> ?; apply/eq_sym/(eq_from_nth x0).
- by rewrite size_take ~-1:/# size_mkseq /#.
rewrite size_mkseq lez_maxr 1:/# => j rgj.
by rewrite nth_mkseq //= nth_take //#.
qed.

(* -------------------------------------------------------------------- *)
lemma drop_mkseqE ['a] (x0 : 'a) (s : 'a list) (i : int) : 0 <= i <= size s =>
  drop i s = mkseq (fun j => nth x0 s (i + j)) (size s - i).
proof.
move=> ?; apply/eq_sym/(eq_from_nth x0).
- by rewrite size_drop ~-1:/# size_mkseq /#.
rewrite size_mkseq lez_maxr 1:/# => j rgj.
by rewrite nth_mkseq //= nth_drop //#.
qed.
