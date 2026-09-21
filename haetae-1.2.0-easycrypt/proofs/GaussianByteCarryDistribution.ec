require import AllCore IntDiv List Distr DList DProd.
from Jasmin require import JModel_x86.
require import GaussianTraceSpec GaussianUniformBytes.

op [opaque] gbc_refill_count (remaining : int) : int = (remaining + 136) %/ 26.
op [opaque] gbc_refill_tail (remaining : int) : int = (remaining + 136) %% 26.

lemma gbc_refill_arithmetic (remaining : int) : 0 <= remaining < 26 =>
  5 <= gbc_refill_count remaining <= 6 /\
  0 <= gbc_refill_tail remaining < 26 /\
  26 * gbc_refill_count remaining + gbc_refill_tail remaining = remaining + 136.
proof.
  move=> hr.
  have hd := divz_eq (remaining + 136) 26.
  have hm := modz_cmp (remaining + 136) 26 _; first trivial.
  rewrite /gbc_refill_count /gbc_refill_tail; smt().
qed.

lemma gbc_refill_concat (remaining : int) : 0 <= remaining < 26 =>
  dmap (dlist W8.dword remaining `*` dlist W8.dword 136)
    (fun (p : W8.t list * W8.t list) => p.`1 ++ p.`2) =
  dlist W8.dword (remaining + 136).
proof. move=> hr; apply eq_sym; apply dlist_add; smt(). qed.

(* This exact finite-distribution identity also permits a randomized
   consumer. Neither the consumer nor its continuation guard receives the
   independently sampled tail. The tail is discarded only on stopping. *)
lemma gbc_defer_unused_tail ['chunk 'tail 'state 'result]
    (chunks : 'chunk distr) (tail : 'tail distr)
    (consume : 'chunk -> 'state distr) (more : 'state -> bool)
    (on_more : 'state -> 'tail -> 'result distr) (on_stop : 'state -> 'result distr) :
  is_lossless tail =>
  dlet chunks (fun c => dlet tail (fun t => dlet (consume c)
    (fun s => if more s then on_more s t else on_stop s))) =
  dlet chunks (fun c => dlet (consume c)
    (fun s => if more s then dlet tail (on_more s) else on_stop s)).
proof.
  move=> ht; apply eq_dlet => // c.
  rewrite dlet_swap; apply eq_dlet => // s.
  case (more s) => hm.
  + by rewrite hm.
  by rewrite hm /= dlet_cst.
qed.

lemma gbc_events_prefix_equal (buf1 buf2 : BArray8192.t) (count : int) :
  0 <= count =>
  (forall j, 0 <= j < 26*count => BArray8192.get8 buf1 j = BArray8192.get8 buf2 j) =>
  gauss_events buf1 count = gauss_events buf2 count.
proof.
  move=> hc he; rewrite /gauss_events.
  apply List.eq_in_map => i; rewrite mem_iota /=; move=> hi.
  rewrite /gauss_event_at /gauss_chunk.
  congr; apply BArray26.init_ext => j hj /=.
  apply he; smt().
qed.

(* The actual consumer specification observes complete 26-byte candidates
   only. Its returned values, square buffer and accepted count all ignore
   the remaining bytes. *)
lemma gbc_trace_tail_irrelevant (buf1 buf2 : BArray8192.t)
    (requested available : int) (dont : bool) (values : BArray4096.t)
    (squares : BArray16.t) (count0 : BArray8.t) :
  0 <= available =>
  (forall j, 0 <= j < 26*(available %/ 26) =>
    BArray8192.get8 buf1 j = BArray8192.get8 buf2 j) =>
  gauss_trace_result buf1 requested available dont values squares count0 =
  gauss_trace_result buf2 requested available dont values squares count0.
proof.
  move=> ha he.
  have hq : 0 <= available %/ 26 by rewrite divz_ge0.
  have h := gbc_events_prefix_equal buf1 buf2 (available %/ 26) hq he.
  by rewrite /gauss_trace_result /gauss_trace_prefix h.
qed.

lemma gbc_chunks_prefix (count : int) (bytes : W8.t list) :
  0 <= count => gbc_chunks count (take (26*count) bytes) = gbc_chunks count bytes.
proof.
  move=> hc; rewrite /gbc_chunks.
  apply eq_in_map => i; rewrite mem_iota /= => hi.
  rewrite drop_take 1:/# 1:/# take_take.
  have -> : 26 <= 26*count - 26*i by smt().
  trivial.
qed.

(* The pair distribution exposes independence of all complete candidates
   from the unused tail, rather than just the marginal law of each part. *)
lemma gbc_grouped_split (count remaining : int) :
  0 <= count => 0 <= remaining =>
  dmap (gbc_bytes (26*count + remaining))
    (fun bytes => (gbc_chunks count bytes, drop (26*count) bytes)) =
  dlist gbc_candidate count `*` gbc_bytes remaining.
proof.
  move=> hc hr.
  rewrite -(gbc_chunks_iid count hc) dmap_dprodL
    -(gbc_bytes_split (26*count) remaining _ hr) 1:/# dmap_comp.
  apply eq_dmap => bytes; by rewrite /(\o) /= gbc_chunks_prefix.
qed.

lemma gbc_refill_factor (remaining : int) : 0 <= remaining < 26 =>
  dmap (gbc_bytes (remaining + 136))
    (fun bytes => (gbc_chunks (gbc_refill_count remaining) bytes,
      drop (26*gbc_refill_count remaining) bytes)) =
  dlist gbc_candidate (gbc_refill_count remaining) `*`
    gbc_bytes (gbc_refill_tail remaining).
proof.
  move=> hr; have [hq [ht he]] := gbc_refill_arithmetic remaining hr.
  rewrite -he; apply gbc_grouped_split; smt().
qed.

lemma gbc_chunks_append_unused (count : int) (bytes suffix : W8.t list) :
  0 <= count => 26*count <= size bytes =>
  gbc_chunks count (bytes ++ suffix) = gbc_chunks count bytes.
proof.
  move=> hc hb; rewrite /gbc_chunks.
  apply eq_in_map => i; rewrite mem_iota /= => hi.
  rewrite drop_catl 1:/# take_catl //.
  rewrite size_drop 1:/# /max; smt().
qed.

lemma gbc_chunks_complete_tail (count : int) (bytes suffix : W8.t list) :
  0 <= count => 26*count <= size bytes =>
  size bytes + size suffix = 26*(count+1) =>
  gbc_chunks (count+1) (bytes ++ suffix) =
    gbc_chunks count bytes ++ [BArray26.of_list (drop (26*count) bytes ++ suffix)].
proof.
  move=> hc hb hs.
  rewrite /gbc_chunks iotaSr 1:hc map_rcons -cats1 /=.
  have hprefix : map (fun i => BArray26.of_list
      (take 26 (drop (26*i) (bytes++suffix)))) (iota_ 0 count) = gbc_chunks count bytes.
  + exact (gbc_chunks_append_unused count bytes suffix hc hb).
  rewrite hprefix drop_catl 1:hb take_oversize //.
  rewrite size_cat size_drop 1:/# /max; smt().
qed.

lemma gbc_bytes_bind_cat ['a] (m n : int) (F : W8.t list -> 'a distr) :
  0 <= m => 0 <= n =>
  dlet (gbc_bytes (m+n)) F =
    dlet (gbc_bytes m) (fun xs => dlet (gbc_bytes n) (fun ys => F (xs++ys))).
proof.
  move=> hm hn.
  rewrite /gbc_bytes dlist_add 1:hm 1:hn dlet_dmap dprod_dlet dlet_dlet.
  apply eq_dlet => // xs.
  by rewrite dlet_dmap.
qed.

(* The carried bytes below are a literal known prefix. Only the bytes that
   complete its next candidate are sampled by this continuation kernel. *)
op [opaque] gbc_carry_kernel ['state 'result]
    (step : 'state -> BArray26.t -> 'state) (complete : 'state -> 'result distr)
    (state : 'state) (tail : W8.t list) : 'result distr =
  dlet (gbc_bytes (26 - size tail))
    (fun suffix => complete (step state (BArray26.of_list (tail ++ suffix)))).

lemma gbc_fixed_tail_groups ['state 'result]
    (step : 'state -> BArray26.t -> 'state) (complete : 'state -> 'result distr)
    (state : 'state) (tail : W8.t list) (count : int) :
  size tail < 26 => 0 <= count =>
  (forall head, size head = 26 =>
    dlet (dlist gbc_candidate count)
      (fun cs => complete (foldl step (step state (BArray26.of_list head)) cs)) =
    complete (step state (BArray26.of_list head))) =>
  dlet (gbc_bytes (26 - size tail + 26*count))
    (fun fresh => complete (foldl step state (gbc_chunks (count+1) (tail++fresh)))) =
  gbc_carry_kernel step complete state tail.
proof.
  move=> ht hc hgroup.
  have hf : 0 <= 26 - size tail by smt(size_ge0).
  have hcount : 0 <= 26*count by smt().
  rewrite (gbc_bytes_bind_cat (26-size tail) (26*count) _ hf hcount)
    /gbc_carry_kernel.
  apply in_eq_dlet => prefix hp.
  have hsize := supp_dlist_size W8.dword (26-size tail) prefix hf hp.
  have hhead : size (tail++prefix) = 26 by rewrite size_cat; smt().
  have he : dlet (gbc_bytes (26*count))
      (fun rest => complete (foldl step state
        (gbc_chunks (count+1) (tail++(prefix++rest))))) =
      dlet (dlist gbc_candidate count)
        (fun cs => complete (foldl step (step state (BArray26.of_list (tail++prefix))) cs)).
  + rewrite -(gbc_chunks_iid count hc) dlet_dmap.
    apply eq_dlet => // rest.
    by rewrite catA gbc_chunks_cons 1:hc 1:hhead /=.
  rewrite /= he; exact (hgroup (tail++prefix) hhead).
qed.

lemma gbc_fixed_tail_refill ['state 'result]
    (step : 'state -> BArray26.t -> 'state) (complete : 'state -> 'result distr)
    (state : 'state) (tail : W8.t list) :
  size tail < 26 =>
  (forall head, size head = 26 =>
    dlet (dlist gbc_candidate (gbc_refill_count (size tail)))
      (fun cs => complete (foldl step (step state (BArray26.of_list head)) cs)) =
    complete (step state (BArray26.of_list head))) =>
  dlet (gbc_bytes 136) (fun block =>
    gbc_carry_kernel step complete
      (foldl step state (gbc_chunks (gbc_refill_count (size tail)) (tail++block)))
      (drop (26*gbc_refill_count (size tail)) (tail++block))) =
  gbc_carry_kernel step complete state tail.
proof.
  move=> ht hgroup.
  have htr : 0 <= size tail < 26 by smt(size_ge0).
  have [hq [hr hlen]] := gbc_refill_arithmetic (size tail) htr.
  pose q := gbc_refill_count (size tail).
  pose r := gbc_refill_tail (size tail).
  have hq0 : 0 <= q by smt().
  have hf : 0 <= 26-r by smt().
  have he : dlet (gbc_bytes 136) (fun block =>
      gbc_carry_kernel step complete
        (foldl step state (gbc_chunks q (tail++block)))
        (drop (26*q) (tail++block))) =
      dlet (gbc_bytes 136) (fun block => dlet (gbc_bytes (26-r))
        (fun suffix => complete
          (foldl step state (gbc_chunks (q+1) (tail++(block++suffix)))))).
  + apply in_eq_dlet => block hb.
    have hbs := supp_dlist_size W8.dword 136 block _ hb; first trivial.
    have htail : size (drop (26*q) (tail++block)) = r.
    - rewrite size_drop 1:/# size_cat hbs /max; smt().
    rewrite /= /gbc_carry_kernel htail.
    apply in_eq_dlet => suffix hs.
    have hss := supp_dlist_size W8.dword (26-r) suffix hf hs.
    have hbase : 26*q <= size (tail++block) by rewrite size_cat hbs; smt().
    have hsum : size (tail++block) + size suffix = 26*(q+1).
    - rewrite size_cat hbs hss; smt().
    rewrite /= catA (gbc_chunks_complete_tail q (tail++block) suffix hq0 hbase hsum)
      foldl_cat /=.
    trivial.
  rewrite -/q he.
  have hcat := gbc_bytes_bind_cat 136 (26-r)
    (fun fresh => complete (foldl step state (gbc_chunks (q+1) (tail++fresh)))) _ hf;
    first trivial.
  rewrite /= in hcat.
  rewrite -hcat.
  have htotal : 136 + (26-r) = 26 - size tail + 26*q by smt().
  rewrite htotal.
  exact (gbc_fixed_tail_groups step complete state tail q ht hq0 hgroup).
qed.
