require import AllCore List.
require import Array256.

(* Move to array theory *)
lemma all_tolist ['a] (p : 'a -> bool) (a : 'a Array256.t) :
  (Array256.all p a) <=> (List.all p (to_list a)) by 
  rewrite /all !allP /to_list /mkseq /=;split => H x Hx; 
   [have /# := mapP ("_.[_]" a) (iota_ 0 256) x | smt(mapP)].
   
lemma all_imply ['a] (p q : 'a -> bool) (s : 'a Array256.t) :
  (forall x, p x => q x) => all p s => all q s
  by rewrite /all !allP /= => H x Hx;smt(mapP).

lemma array256_mapE ['a 'b] (f : 'a -> 'b) (a : 'a Array256.t) :
  Array256.to_list (Array256.map f a) = List.map f (Array256.to_list a).
  rewrite /to_list /mkseq /= -{1}map_comp /(\o) /=.
  apply (eq_from_nth witness);1: by rewrite !size_map.
  move => i;rewrite !size_map size_iota /max /= => ib.
  rewrite !(nth_map witness) /=;1,2:smt(size_map size_iota).
  by rewrite /map initiE /=;1:by rewrite nth_iota /#.
qed.
  
lemma array256_map_comp ['a 'b 'c] (f : 'a -> 'b) (g : 'b -> 'c) (a : 'a Array256.t) :
  Array256.map g ((Array256.map f a)) = Array256.map (fun x => g (f x)) a
  by rewrite /map tP => i ib;smt(Array256.initiE).

lemma array256_allP ['a] (p : 'a -> bool) (a : 'a Array256.t) :
  Array256.all p a <=> (forall x, x \in Array256.to_list a => p x).
proof. by rewrite all_tolist allP. qed.
(* *)

(* move to list theory *)
lemma in_map_id ['a] (f : 'a -> 'a) (s : 'a list) :
  (forall x, x \in s => f x = x) => map f s = s.
proof. by move=> id_f; rewrite -{2}[s]map_id &(eq_in_map). qed.

lemma in_map_cancel ['a 'b] (f : 'a -> 'b) (g : 'b -> 'a) (s : 'a list) :
  (forall x, x \in s => g (f x) = x) => map g (map f s) = s.
proof. by move=> can_fg; rewrite -map_comp in_map_id. qed.

(* *)
