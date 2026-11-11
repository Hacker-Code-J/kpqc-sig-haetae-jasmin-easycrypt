require import AllCore List IntDiv.

(* A concrete finite maximum, with 48 as the empty-set default. *)
op grr_max (indices : int list) : int =
  foldr (fun b m => if m < b then b else m) 48 indices.

op [opaque] grr_candidates (P : int -> bool) (cap : int) : int list =
  filter P (range 49 (cap+1)).

op [opaque] grr_index (P : int -> bool) (cap : int) : int =
  grr_max (grr_candidates P cap).

op [opaque] grr_rank (P : int -> bool) (cap : int) : int =
  cap - grr_index P cap.

lemma grr_max_cons b indices :
  grr_max (b::indices) =
    if grr_max indices < b then b else grr_max indices.
proof. by rewrite /grr_max /=. qed.

lemma grr_max_properties (indices : int list) :
  48 <= grr_max indices /\
  (grr_max indices = 48 \/ grr_max indices \in indices) /\
  (forall b, b \in indices => b <= grr_max indices).
proof.
  elim: indices => [|b indices ih].
  + rewrite /grr_max /=; smt().
  rewrite grr_max_cons !in_cons.
  case (grr_max indices < b); smt().
qed.

lemma grr_candidates_mem (P : int -> bool) (cap b : int) :
  (b \in grr_candidates P cap) = (49 <= b <= cap /\ P b).
proof. rewrite /grr_candidates mem_filter mem_range; smt(). qed.

lemma grr_index_ge48 (P : int -> bool) (cap : int) :
  48 <= grr_index P cap.
proof.
  have [h _] := grr_max_properties (grr_candidates P cap).
  by rewrite /grr_index.
qed.

lemma grr_index_dominates (P : int -> bool) (cap b : int) :
  49 <= b <= cap => P b => b <= grr_index P cap.
proof.
  move=> hb hp.
  have hm : b \in grr_candidates P cap by rewrite grr_candidates_mem; smt().
  have [_ [_ h]] := grr_max_properties (grr_candidates P cap).
  rewrite /grr_index; exact (h b hm).
qed.

lemma grr_index_witness (P : int -> bool) (cap : int) :
  (exists b, 49 <= b <= cap /\ P b) =>
  49 <= grr_index P cap <= cap /\ P (grr_index P cap).
proof.
  move=> [b [hb hp]].
  have hd := grr_index_dominates P cap b hb hp.
  have [_ [hm _]] := grr_max_properties (grr_candidates P cap).
  have hi : grr_index P cap \in grr_candidates P cap.
  + rewrite /grr_index; move: hd; rewrite /grr_index; smt().
  by move: hi; rewrite grr_candidates_mem.
qed.

lemma grr_rank_nonnegative (P : int -> bool) (cap : int) :
  (exists b, 49 <= b <= cap /\ P b) => 0 <= grr_rank P cap.
proof.
  move=> hp; have h := grr_index_witness P cap hp.
  rewrite /grr_rank; smt().
qed.

lemma grr_index_strict_cap (P : int -> bool) (cap : int) :
  (exists b, 49 <= b <= cap /\ P b) =>
  (forall b, 49 <= b <= cap => P b => b < cap) =>
  grr_index P cap < cap.
proof.
  move=> hp hall; have [hb hP] := grr_index_witness P cap hp.
  exact (hall (grr_index P cap) hb hP).
qed.

lemma grr_index_successor (P Q : int -> bool) (cap : int) :
  (exists b, 49 <= b <= cap /\ P b) =>
  grr_index P cap < cap => Q (grr_index P cap + 1) =>
  (exists b, 49 <= b <= cap /\ Q b) /\
  grr_index P cap + 1 <= grr_index Q cap.
proof.
  move=> hp hcap hq; have [hb _] := grr_index_witness P cap hp.
  have hn : 49 <= grr_index P cap + 1 <= cap by smt().
  split.
  + exists (grr_index P cap + 1); smt().
  exact (grr_index_dominates Q cap (grr_index P cap + 1) hn hq).
qed.

(* Only one compatible successor is needed. Other compatible indices may
   coexist, and the next predicate need not contain the previous witnesses. *)
lemma grr_rank_step (P Q : int -> bool) (cap : int) :
  (exists b, 49 <= b <= cap /\ P b) =>
  grr_index P cap < cap => Q (grr_index P cap + 1) =>
  (exists b, 49 <= b <= cap /\ Q b) /\
  0 <= grr_rank Q cap /\ grr_rank Q cap < grr_rank P cap.
proof.
  move=> hp hcap hq.
  have [hne hinc] := grr_index_successor P Q cap hp hcap hq.
  have hnonneg := grr_rank_nonnegative Q cap hne.
  rewrite /grr_rank in hnonneg.
  rewrite /grr_rank; smt().
qed.

lemma grr_rank_step_bounded (P Q : int -> bool) (cap : int) :
  (exists b, 49 <= b <= cap /\ P b) =>
  (forall b, 49 <= b <= cap => P b => b < cap) =>
  Q (grr_index P cap + 1) =>
  (exists b, 49 <= b <= cap /\ Q b) /\
  0 <= grr_rank Q cap /\ grr_rank Q cap < grr_rank P cap.
proof.
  move=> hp hall hq.
  exact (grr_rank_step P Q cap hp (grr_index_strict_cap P cap hp hall) hq).
qed.
