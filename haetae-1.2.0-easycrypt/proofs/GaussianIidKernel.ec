require import AllCore IntDiv List Distr DList DProd Xreal StdOrder StdRing.
from Jasmin require import JModel_x86.
require import BArray26 GaussianRetryInputs GaussianUniformBytes
  GaussianByteCarryDistribution GaussianBlockSampling GaussianRetryCore.
import RField RealOrder.

op gik_pairs : (int * bool) distr = dmap gbc_candidate gr_candidate_observer.
op gik_step (values : int list) (candidate : BArray26.t) : int list =
  gbs_step 256 values (gr_candidate_observer candidate).
op gik_scan (values : int list) (candidates : BArray26.t list) : int list =
  foldl gik_step values candidates.
op gik_complete (values : int list) : int list distr = gbs_complete gik_pairs 256 values.
op gik_kernel (values : int list) (tail : W8.t list) : int list distr =
  gbc_carry_kernel gik_step gik_complete values tail.

lemma gik_pairs_law p : gik_pairs = SigmaConditionalSpec.sc_actual_pair p.
proof. by rewrite /gik_pairs (gbc_candidate_observer_law p). qed.

lemma gik_pairs_ll : is_lossless gik_pairs.
proof. rewrite /gik_pairs; apply dmap_ll; exact gbc_candidate_ll. qed.

lemma gik_acceptance_lower : 1%r/7%r <= mu gik_pairs gr_accept.
proof.
  rewrite /gik_pairs dmapE /(\o) /gr_accept /gr_candidate_observer /=.
  have h := gbc_candidate_acceptance_lower.
  smt().
qed.

lemma gik_acceptance_positive : 0%r < mu gik_pairs gr_accept.
proof. have := gik_acceptance_lower; smt(). qed.

lemma gik_complete_ll values : is_lossless (gik_complete values).
proof. exact (gbs_complete_ll gik_pairs 256 values gik_acceptance_positive). qed.

lemma gik_complete_full values : size values = 256 => gik_complete values = dunit values.
proof. exact (gbs_complete_full gik_pairs 256 values). qed.

lemma gik_step_size values candidate : size values <= 256 =>
  size values <= size (gik_step values candidate) <= 256.
proof. exact (gbs_step_size 256 values (gr_candidate_observer candidate)). qed.

lemma gik_scan_observers values candidates :
  gik_scan values candidates = gbs_scan 256 values (map gr_candidate_observer candidates).
proof.
  elim: candidates values => [|candidate tail ih] values.
  + by rewrite /gik_scan gbs_scan_nil.
  by rewrite /gik_scan /= -/(gik_scan _ _) ih gbs_scan_cons /gik_step.
qed.

lemma gik_scan_size values candidates : size values <= 256 =>
  size values <= size (gik_scan values candidates) <= 256.
proof. rewrite gik_scan_observers; exact (gbs_scan_size 256 values _). qed.

lemma gik_step_complete values : size values <= 256 =>
  dlet gbc_candidate (fun candidate => gik_complete (gik_step values candidate)) =
    gik_complete values.
proof.
  move=> hv.
  have h := gbs_complete_step gik_pairs 256 values gik_pairs_ll gik_acceptance_positive hv.
  by move: h; rewrite /gik_pairs dlet_dmap /gik_complete /gik_step.
qed.

lemma gik_group_complete values count : size values <= 256 => 0 <= count =>
  dlet (dlist gbc_candidate count) (fun candidates => gik_complete (gik_scan values candidates)) =
    gik_complete values.
proof.
  move=> hv hc.
  have h := gbs_complete_group gik_pairs 256 values count
    gik_pairs_ll gik_acceptance_positive hv hc.
  rewrite /gik_pairs dlist_dmap dlet_dmap in h.
  have he : (fun candidates => gik_complete (gik_scan values candidates)) =
    (fun candidates => gbs_complete (dmap gbc_candidate gr_candidate_observer) 256
      (gbs_scan 256 values (map gr_candidate_observer candidates))).
  + apply fun_ext => candidates.
    by rewrite /gik_complete /gik_pairs gik_scan_observers.
  by rewrite he /gik_complete /gik_pairs.
qed.

lemma gik_group_event values count (event : int list -> bool) :
  size values <= 256 => 0 <= count =>
  Ep (dlist gbc_candidate count) (fun candidates =>
    (mu (gik_complete (gik_scan values candidates)) event)%xr) =
    (mu (gik_complete values) event)%xr.
proof.
  move=> hv hc; have h := gik_group_complete values count hv hc.
  rewrite -(Ep_mu (gik_complete values) event) -h Ep_dlet.
  apply eq_Ep => candidates hcs /=; by rewrite Ep_mu.
qed.

lemma gik_kernel_ll values tail : is_lossless (gik_kernel values tail).
proof.
  rewrite /gik_kernel /gbc_carry_kernel; apply dlet_ll; first exact (gbc_bytes_ll _).
  move=> suffix hs; exact (gik_complete_ll _).
qed.

lemma gik_kernel_full values tail : size values = 256 =>
  gik_kernel values tail = dunit values.
proof.
  move=> hv; rewrite /gik_kernel /gbc_carry_kernel.
  have he : (fun suffix => gik_complete (gik_step values (BArray26.of_list (tail++suffix)))) =
    (fun _ => dunit values).
  + apply fun_ext => suffix; rewrite /gik_step /gbs_step hv /=.
    exact (gik_complete_full values hv).
  rewrite he; exact (dlet_cst _ _ (gbc_bytes_ll _)).
qed.

(* tail is a fixed, already observed byte list. Only block is sampled. *)
lemma gik_refill_complete values tail : size values <= 256 => size tail < 26 =>
  dlet (gbc_bytes 136) (fun block =>
    gik_kernel
      (gik_scan values (gbc_chunks (gbc_refill_count (size tail)) (tail++block)))
      (drop (26*gbc_refill_count (size tail)) (tail++block))) =
    gik_kernel values tail.
proof.
  move=> hv ht; rewrite /gik_kernel /gik_scan.
  apply gbc_fixed_tail_refill; first exact ht.
  move=> head hh.
  have hs := gik_step_size values (BArray26.of_list head) hv.
  have [hq _] := gbc_refill_arithmetic (size tail) _; first smt(size_ge0).
  apply gik_group_complete; smt().
qed.

lemma gik_refill_event values tail (event : int list -> bool) :
  size values <= 256 => size tail < 26 =>
  Ep (gbc_bytes 136) (fun block =>
    (mu (gik_kernel
      (gik_scan values (gbc_chunks (gbc_refill_count (size tail)) (tail++block)))
      (drop (26*gbc_refill_count (size tail)) (tail++block))) event)%xr) =
    (mu (gik_kernel values tail) event)%xr.
proof.
  move=> hv ht; have h := gik_refill_complete values tail hv ht.
  rewrite -(Ep_mu (gik_kernel values tail) event) -h Ep_dlet.
  apply eq_Ep => block hb /=; by rewrite Ep_mu.
qed.

lemma gik_average_tail values remaining :
  size values <= 256 => 0 <= remaining < 26 =>
  dlet (gbc_bytes remaining) (fun tail => gik_kernel values tail) = gik_complete values.
proof.
  move=> hv hr.
  have hf : 0 <= 26-remaining by smt().
  have he : dlet (gbc_bytes remaining) (fun tail => gik_kernel values tail) =
    dlet (gbc_bytes remaining) (fun tail => dlet (gbc_bytes (26-remaining))
      (fun suffix => gik_complete (gik_step values (BArray26.of_list (tail++suffix))))).
  + apply in_eq_dlet => tail ht /=.
    have hs := supp_dlist_size W8.dword remaining tail _ ht; first smt().
    by rewrite /gik_kernel /gbc_carry_kernel hs.
  rewrite he.
  have hc := gbc_bytes_bind_cat remaining (26-remaining)
    (fun bytes => gik_complete (gik_step values (BArray26.of_list bytes))) _ hf;
    first smt().
  rewrite /= in hc; rewrite -hc.
  have -> : remaining+(26-remaining) = 26 by ring.
  have hstep := gik_step_complete values hv.
  by move: hstep; rewrite /gbc_candidate /BArray26.darray dlet_dmap /gbc_bytes.
qed.

lemma gik_average_tail_event values remaining (event : int list -> bool) :
  size values <= 256 => 0 <= remaining < 26 =>
  Ep (gbc_bytes remaining) (fun tail => (mu (gik_kernel values tail) event)%xr) =
    (mu (gik_complete values) event)%xr.
proof.
  move=> hv hr; have h := gik_average_tail values remaining hv hr.
  rewrite -(Ep_mu (gik_complete values) event) -h Ep_dlet.
  apply eq_Ep => tail ht /=; by rewrite Ep_mu.
qed.

lemma gik_group_with_tail values count remaining :
  size values <= 256 => 0 <= count => 0 <= remaining < 26 =>
  dlet (gbc_bytes (26*count+remaining)) (fun bytes =>
    gik_kernel (gik_scan values (gbc_chunks count bytes)) (drop (26*count) bytes)) =
    gik_complete values.
proof.
  move=> hv hc hr.
  have he : dlet (gbc_bytes (26*count+remaining)) (fun bytes =>
      gik_kernel (gik_scan values (gbc_chunks count bytes)) (drop (26*count) bytes)) =
    dlet (dlist gbc_candidate count `*` gbc_bytes remaining)
      (fun (parts : BArray26.t list * W8.t list) =>
        gik_kernel (gik_scan values parts.`1) parts.`2).
  + rewrite -(gbc_grouped_split count remaining hc _) 1:/# dlet_dmap.
    trivial.
  rewrite he dprod_dlet dlet_dlet -(gik_group_complete values count hv hc).
  apply eq_dlet => // candidates /=; rewrite dlet_dmap /=.
  apply gik_average_tail; last exact hr.
  have hs := gik_scan_size values candidates hv; smt().
qed.

lemma gik_group_with_tail_event values count remaining (event : int list -> bool) :
  size values <= 256 => 0 <= count => 0 <= remaining < 26 =>
  Ep (gbc_bytes (26*count+remaining)) (fun bytes =>
    (mu (gik_kernel (gik_scan values (gbc_chunks count bytes))
      (drop (26*count) bytes)) event)%xr) =
    (mu (gik_complete values) event)%xr.
proof.
  move=> hv hc hr; have h := gik_group_with_tail values count remaining hv hc hr.
  rewrite -(Ep_mu (gik_complete values) event) -h Ep_dlet.
  apply eq_Ep => bytes hb /=; by rewrite Ep_mu.
qed.

(* The first 32 sign bytes are independent of the following candidate
   bytes. They are omitted only from this visible-magnitude observer. *)
lemma gik_initial_drop32 :
  dmap (gbc_bytes 6664) (drop 32) = gbc_bytes 6632.
proof.
  have hs := gbc_bytes_split 32 6632 _ _; first 2 trivial.
  rewrite /= in hs.
  have he : dmap (gbc_bytes 6664) (drop 32) =
    dmap (gbc_bytes 32 `*` gbc_bytes 6632) snd.
  + rewrite -hs dmap_comp; apply eq_dmap => bytes.
    by rewrite /(\o) /=.
  rewrite he dmap_dprodE.
  have hconst : (fun signs => dmap (gbc_bytes 6632)
      (fun bytes => snd (signs,bytes))) = (fun (_ : W8.t list) => gbc_bytes 6632).
  + apply fun_ext => signs; by rewrite /= dmap_id.
  rewrite hconst; exact (dlet_cst _ _ (gbc_bytes_ll 32)).
qed.

lemma gik_initial_complete :
  dlet (gbc_bytes 6664) (fun bytes =>
    gik_kernel (gik_scan [] (gbc_chunks 255 (drop 32 bytes)))
      (drop 6630 (drop 32 bytes))) =
    dlist (gr_output gik_pairs) 256.
proof.
  rewrite -(dlet_dmap (gbc_bytes 6664) (drop 32)
    (fun bytes => gik_kernel (gik_scan [] (gbc_chunks 255 bytes)) (drop 6630 bytes)))
    gik_initial_drop32.
  have h := gik_group_with_tail [] 255 2 _ _ _; first 3 trivial.
  by move: h; rewrite /= /gik_complete gbs_complete_empty.
qed.

lemma gik_initial_event (event : int list -> bool) :
  Ep (gbc_bytes 6664) (fun bytes =>
    (mu (gik_kernel (gik_scan [] (gbc_chunks 255 (drop 32 bytes)))
      (drop 6630 (drop 32 bytes))) event)%xr) =
    (mu (dlist (gr_output gik_pairs) 256) event)%xr.
proof.
  rewrite -(Ep_mu (dlist (gr_output gik_pairs) 256) event) -gik_initial_complete Ep_dlet.
  apply eq_Ep => bytes hb /=; by rewrite Ep_mu.
qed.
