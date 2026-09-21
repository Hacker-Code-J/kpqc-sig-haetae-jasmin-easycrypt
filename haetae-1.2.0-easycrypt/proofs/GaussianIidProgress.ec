require import AllCore IntDiv List Distr DList StdRing StdOrder.
from Jasmin require import JModel_x86.
require import SigmaSpec SigmaCorrectness GaussianTraceSpec GaussianTraceProperties GaussianRetryInputs
  GaussianUniformBytes GaussianByteCarryDistribution GaussianIidBufferSpec.
import RField RealOrder.

lemma gip_chunk_of_list (bytes : W8.t list) (i : int) :
  0 <= i => 26*(i+1) <= size bytes => size bytes <= 8192 =>
  gauss_chunk (BArray8192.of_list bytes) (26*i) =
    BArray26.of_list (take 26 (drop (26*i) bytes)).
proof.
  move=> hi hs hb; apply BArray26.ext_eq => j hj.
  rewrite /gauss_chunk BArray26.initiE 1:hj /=
    BArray8192.get_of_list 1:/# BArray26.get_of_list 1:hj
    nth_take 1:// 1:/# nth_drop 1:/# 1:/#.
  trivial.
qed.

lemma gip_events_chunks_count (bytes : W8.t list) (count : int) :
  0 <= count => 26*count <= size bytes => size bytes <= 8192 =>
  gauss_events (BArray8192.of_list bytes) count = map sigma76_spec (gbc_chunks count bytes).
proof.
  move=> hc hs hb; rewrite /gauss_events /gbc_chunks -map_comp.
  apply eq_in_map => i; rewrite mem_iota /= => hi.
  rewrite /gauss_event_at gip_chunk_of_list 1:/# 1:/# 1:hb.
  trivial.
qed.

lemma gip_events_chunks (bytes : W8.t list) : size bytes <= 8192 =>
  gauss_events (BArray8192.of_list bytes) (size bytes %/ 26) =
    map sigma76_spec (gbc_chunks (size bytes %/ 26) bytes).
proof.
  move=> hb; have hs := size_ge0 bytes.
  have hd := divz_eq (size bytes) 26.
  have hr := modz_cmp (size bytes) 26 _; first trivial.
  apply gip_events_chunks_count; smt().
qed.

lemma gip_accepted_chunks (bytes : W8.t list) : size bytes <= 8192 =>
  gib_accepted bytes =
    map fst (filter snd (map gr_candidate_observer (gbc_chunks (size bytes %/ 26) bytes))).
proof.
  move=> hb.
  have h := gr_candidate_stream_accepted (gbc_chunks (size bytes %/ 26) bytes).
  rewrite gr_candidate_stream_events in h.
  by rewrite /gib_accepted gip_events_chunks 1:hb.
qed.

lemma gip_bytes_drop (m n : int) : 0 <= m => 0 <= n =>
  dmap (gbc_bytes (m+n)) (drop m) = gbc_bytes n.
proof.
  move=> hm hn.
  have h := congr1 (fun (d : (W8.t list * W8.t list) distr) =>
    dmap d (fun (p : W8.t list * W8.t list) => p.`2)) _ _ (gbc_bytes_split m n hm hn).
  rewrite /= dmap_comp /= dmap_dprodE /= dmap_id dlet_cst 1:gbc_bytes_ll in h.
  exact h.
qed.

lemma gip_bytes_take (m n : int) : 0 <= m => 0 <= n =>
  dmap (gbc_bytes (m+n)) (take m) = gbc_bytes m.
proof.
  move=> hm hn.
  have h := congr1 (fun (d : (W8.t list * W8.t list) distr) =>
    dmap d (fun (p : W8.t list * W8.t list) => p.`1)) _ _ (gbc_bytes_split m n hm hn).
  rewrite /= dmap_comp /= dmap_dprodE_swap /= dmap_id dlet_cst 1:gbc_bytes_ll in h.
  exact h.
qed.

lemma gip_uniform_candidate_slice (offset total : int) :
  0 <= offset => offset+26 <= total =>
  dmap (gbc_bytes total)
    (fun bytes => BArray26.of_list (take 26 (drop offset bytes))) = gbc_candidate.
proof.
  move=> ho ht.
  have hd : dmap (gbc_bytes total) (drop offset) = gbc_bytes (total-offset).
  + have he : total = offset+(total-offset) by ring.
    rewrite {1}he; apply gip_bytes_drop; smt().
  have hh : dmap (gbc_bytes (total-offset)) (take 26) = gbc_bytes 26.
  + have he : total-offset = 26+(total-offset-26) by ring.
    rewrite {1}he; apply gip_bytes_take; smt().
  have he : dmap (gbc_bytes total)
      (fun bytes => BArray26.of_list (take 26 (drop offset bytes))) =
      dmap (dmap (dmap (gbc_bytes total) (drop offset)) (take 26)) BArray26.of_list.
  + by rewrite !dmap_comp.
  by rewrite he hd hh /gbc_candidate /gbc_bytes /BArray26.darray.
qed.

op [opaque] gip_fresh_candidate (tail block : W8.t list) : BArray26.t =
  BArray26.of_list (take 26 (drop (26-size tail) block)).

lemma gip_fresh_candidate_uniform (tail : W8.t list) : size tail < 26 =>
  dmap (gbc_bytes 136) (gip_fresh_candidate tail) = gbc_candidate.
proof.
  move=> ht; rewrite /gip_fresh_candidate.
  apply gip_uniform_candidate_slice; smt(size_ge0).
qed.

(* Candidate index1 lies entirely in the fresh block, even if candidate0
   starts with a fixed, adversarially chosen carry. *)
lemma gip_fresh_candidate_member (tail block : W8.t list) :
  size tail < 26 => size block = 136 =>
  gip_fresh_candidate tail block \in
    gbc_chunks (size (tail++block) %/ 26) (tail++block).
proof.
  move=> ht hb.
  have hr : 0 <= size tail < 26 by smt(size_ge0).
  have [hq _] := gbc_refill_arithmetic (size tail) hr.
  have hc : 1 < size (tail++block) %/ 26.
  + rewrite size_cat hb; move: hq; rewrite /gbc_refill_count; smt().
  rewrite /gbc_chunks; apply/mapP; exists 1.
  split; first by rewrite mem_iota /=; smt().
  by rewrite /= /gip_fresh_candidate drop_catr 1:/#.
qed.

lemma gip_fresh_acceptance_progress (tail block : W8.t list) :
  size tail < 26 => size block = 136 =>
  (gr_candidate_observer (gip_fresh_candidate tail block)).`2 =>
  gib_accepted (tail++block) <> [].
proof.
  move=> ht hb ha.
  have hbound : size (tail++block) <= 8192 by rewrite size_cat hb; smt(size_ge0).
  rewrite (gip_accepted_chunks (tail++block) hbound).
  have hc := gip_fresh_candidate_member tail block ht hb.
  have ho := map_f gr_candidate_observer _ _ hc.
  have hf : gr_candidate_observer (gip_fresh_candidate tail block) \in
      filter snd (map gr_candidate_observer (gbc_chunks (size (tail++block) %/ 26) (tail++block))).
  + rewrite mem_filter; smt().
  have hm := map_f fst _ _ hf.
  smt().
qed.

lemma gip_refill_progress_from_candidate (tail : W8.t list) :
  size tail < 26 =>
  1%r/7%r <= mu gbc_candidate (fun p => (gr_candidate_observer p).`2) =>
  1%r/7%r <= mu gib_block (fun block => gib_accepted (tail++block) <> []).
proof.
  move=> ht ha.
  have hslice : mu (gbc_bytes 136)
      (fun block => (gr_candidate_observer (gip_fresh_candidate tail block)).`2) =
      mu gbc_candidate (fun p => (gr_candidate_observer p).`2).
  + by rewrite -(gip_fresh_candidate_uniform tail ht) dmapE /(\o).
  have hle := mu_le (gbc_bytes 136)
    (fun block => (gr_candidate_observer (gip_fresh_candidate tail block)).`2)
    (fun block => gib_accepted (tail++block) <> []) _.
  + move=> block hb hacc.
    have hs := supp_dlist_size W8.dword 136 block _ hb; first trivial.
    exact (gip_fresh_acceptance_progress tail block ht hs hacc).
  rewrite hslice in hle.
  rewrite /gib_block; move: hle; rewrite /gbc_bytes; smt().
qed.

(* Uniform progress holds for every fixed carry, including values selected
   by the complete prior execution. No fresh-randomness claim about that
   carry is needed; candidate1 uses only bytes from the new136-byte block. *)
lemma gip_refill_progress (tail : W8.t list) &m : size tail < 26 =>
  1%r/7%r <= mu gib_block (fun block => gib_accepted (tail++block) <> []).
proof.
  move=> ht; apply (gip_refill_progress_from_candidate tail ht).
  have h := gbc_candidate_acceptance_lower &m.
  by move: h; rewrite /gr_candidate_observer /=.
qed.
