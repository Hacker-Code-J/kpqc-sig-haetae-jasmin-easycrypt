require import AllCore IntDiv List Distr DList DProd Xreal StdOrder StdRing.
from Jasmin require import JModel_x86.
require import BArray26 GaussianPayloadSpec GaussianPayloadEncoding GaussianUniformBytes
  GaussianByteCarryDistribution GaussianBlockSampling GaussianRetryCore GaussianIidKernel.
import RField RealOrder.

op gpk_step (n : int) (history : int list) (candidate : BArray26.t) : int list =
  gbs_step n history (gpd_observer candidate).
op gpk_fold (n : int) (history : int list) (candidates : BArray26.t list) : int list =
  foldl (gpk_step n) history candidates.
op gpk_complete (n : int) (history : int list) : int list distr =
  gbs_complete gpd_trial n history.
op gpk_kernel (n : int) (history : int list) (tail : W8.t list) : int list distr =
  gbc_carry_kernel (gpk_step n) (gpk_complete n) history tail.

lemma gpk_complete_ll n history : is_lossless (gpk_complete n history).
proof. exact (gbs_complete_ll gpd_trial n history gpd_trial_acceptance_positive). qed.

lemma gpk_complete_full n history : size history = n =>
  gpk_complete n history = dunit history.
proof. exact (gbs_complete_full gpd_trial n history). qed.

lemma gpk_step_size n history candidate : size history <= n =>
  size history <= size (gpk_step n history candidate) <= n.
proof. exact (gbs_step_size n history (gpd_observer candidate)). qed.

lemma gpk_fold_observers n history candidates :
  gpk_fold n history candidates = gbs_scan n history (map gpd_observer candidates).
proof.
  elim: candidates history => [|candidate tail ih] history.
  + by rewrite /gpk_fold gbs_scan_nil.
  by rewrite /gpk_fold /= -/(gpk_fold _ _ _) ih gbs_scan_cons /gpk_step.
qed.

lemma gpk_fold_size n history candidates : size history <= n =>
  size history <= size (gpk_fold n history candidates) <= n.
proof. rewrite gpk_fold_observers; exact (gbs_scan_size n history _). qed.

lemma gpk_pending_fold n history pending :
  gpd_scan n history pending = gpk_fold n history (gbc_chunks (size pending %/ 26) pending).
proof. by rewrite /gpd_scan gpk_fold_observers. qed.

lemma gpk_pending_size n history pending : size history <= n =>
  size history <= size (gpd_scan n history pending) <= n.
proof. rewrite gpk_pending_fold; exact (gpk_fold_size n history _). qed.

lemma gpk_step_complete n history : size history <= n =>
  dlet gbc_candidate (fun candidate => gpk_complete n (gpk_step n history candidate)) =
    gpk_complete n history.
proof.
  move=> hh.
  have h := gbs_complete_step gpd_trial n history
    gpd_trial_ll gpd_trial_acceptance_positive hh.
  by move: h; rewrite /gpd_trial dlet_dmap /gpk_complete /gpk_step.
qed.

lemma gpk_group_complete n history count : size history <= n => 0 <= count =>
  dlet (dlist gbc_candidate count)
    (fun candidates => gpk_complete n (gpk_fold n history candidates)) = gpk_complete n history.
proof.
  move=> hh hc.
  have h := gbs_complete_group gpd_trial n history count
    gpd_trial_ll gpd_trial_acceptance_positive hh hc.
  rewrite /gpd_trial dlist_dmap dlet_dmap in h.
  have he : (fun candidates => gpk_complete n (gpk_fold n history candidates)) =
    (fun candidates => gbs_complete (dmap gbc_candidate gpd_observer) n
      (gbs_scan n history (map gpd_observer candidates))).
  + apply fun_ext => candidates; by rewrite /gpk_complete /gpd_trial gpk_fold_observers.
  by rewrite he /gpk_complete /gpd_trial.
qed.

lemma gpk_group_event n history count (event : int list -> bool) :
  size history <= n => 0 <= count =>
  Ep (dlist gbc_candidate count) (fun candidates =>
    (mu (gpk_complete n (gpk_fold n history candidates)) event)%xr) =
    (mu (gpk_complete n history) event)%xr.
proof.
  move=> hh hc; have h := gpk_group_complete n history count hh hc.
  rewrite -(Ep_mu (gpk_complete n history) event) -h Ep_dlet.
  apply eq_Ep => candidates hcs /=; by rewrite Ep_mu.
qed.

lemma gpk_kernel_ll n history tail : is_lossless (gpk_kernel n history tail).
proof.
  rewrite /gpk_kernel /gbc_carry_kernel; apply dlet_ll; first exact (gbc_bytes_ll _).
  move=> suffix hs; exact (gpk_complete_ll _ _).
qed.

lemma gpk_kernel_full n history tail : size history = n =>
  gpk_kernel n history tail = dunit history.
proof.
  move=> hh; rewrite /gpk_kernel /gbc_carry_kernel.
  have he : (fun suffix => gpk_complete n
      (gpk_step n history (BArray26.of_list (tail++suffix)))) = (fun _ => dunit history).
  + apply fun_ext => suffix; rewrite /gpk_step /gbs_step hh ltzz /=.
    exact (gpk_complete_full n history hh).
  rewrite he; exact (dlet_cst _ _ (gbc_bytes_ll _)).
qed.

(* tail is fixed. Only the newly supplied block is averaged. *)
lemma gpk_refill_complete n history tail : size history <= n => size tail < 26 =>
  dlet (gbc_bytes 136) (fun block =>
    gpk_kernel n
      (gpk_fold n history (gbc_chunks (gbc_refill_count (size tail)) (tail++block)))
      (drop (26*gbc_refill_count (size tail)) (tail++block))) =
    gpk_kernel n history tail.
proof.
  move=> hh ht; rewrite /gpk_kernel /gpk_fold.
  apply gbc_fixed_tail_refill; first exact ht.
  move=> head hhead.
  have hs := gpk_step_size n history (BArray26.of_list head) hh.
  have [hq _] := gbc_refill_arithmetic (size tail) _; first smt(size_ge0).
  apply gpk_group_complete; smt().
qed.

lemma gpk_refill_event n history tail (event : int list -> bool) :
  size history <= n => size tail < 26 =>
  Ep (gbc_bytes 136) (fun block =>
    (mu (gpk_kernel n
      (gpk_fold n history (gbc_chunks (gbc_refill_count (size tail)) (tail++block)))
      (drop (26*gbc_refill_count (size tail)) (tail++block))) event)%xr) =
    (mu (gpk_kernel n history tail) event)%xr.
proof.
  move=> hh ht; have h := gpk_refill_complete n history tail hh ht.
  rewrite -(Ep_mu (gpk_kernel n history tail) event) -h Ep_dlet.
  apply eq_Ep => block hb /=; by rewrite Ep_mu.
qed.

lemma gpk_average_tail n history remaining :
  size history <= n => 0 <= remaining < 26 =>
  dlet (gbc_bytes remaining) (fun tail => gpk_kernel n history tail) = gpk_complete n history.
proof.
  move=> hh hr; have hf : 0 <= 26-remaining by smt().
  have he : dlet (gbc_bytes remaining) (fun tail => gpk_kernel n history tail) =
    dlet (gbc_bytes remaining) (fun tail => dlet (gbc_bytes (26-remaining))
      (fun suffix => gpk_complete n (gpk_step n history (BArray26.of_list (tail++suffix))))).
  + apply in_eq_dlet => tail ht /=.
    have hs := supp_dlist_size W8.dword remaining tail _ ht; first smt().
    by rewrite /gpk_kernel /gbc_carry_kernel hs.
  rewrite he.
  have hc := gbc_bytes_bind_cat remaining (26-remaining)
    (fun bytes => gpk_complete n (gpk_step n history (BArray26.of_list bytes))) _ hf;
    first smt().
  rewrite /= in hc; rewrite -hc.
  have -> : remaining+(26-remaining) = 26 by ring.
  have hstep := gpk_step_complete n history hh.
  by move: hstep; rewrite /gbc_candidate /BArray26.darray dlet_dmap /gbc_bytes.
qed.

lemma gpk_average_tail_event n history remaining (event : int list -> bool) :
  size history <= n => 0 <= remaining < 26 =>
  Ep (gbc_bytes remaining) (fun tail => (mu (gpk_kernel n history tail) event)%xr) =
    (mu (gpk_complete n history) event)%xr.
proof.
  move=> hh hr; have h := gpk_average_tail n history remaining hh hr.
  rewrite -(Ep_mu (gpk_complete n history) event) -h Ep_dlet.
  apply eq_Ep => tail ht /=; by rewrite Ep_mu.
qed.

lemma gpk_group_with_tail n history count remaining :
  size history <= n => 0 <= count => 0 <= remaining < 26 =>
  dlet (gbc_bytes (26*count+remaining)) (fun bytes =>
    gpk_kernel n (gpk_fold n history (gbc_chunks count bytes)) (drop (26*count) bytes)) =
    gpk_complete n history.
proof.
  move=> hh hc hr.
  have he : dlet (gbc_bytes (26*count+remaining)) (fun bytes =>
      gpk_kernel n (gpk_fold n history (gbc_chunks count bytes)) (drop (26*count) bytes)) =
    dlet (dlist gbc_candidate count `*` gbc_bytes remaining)
      (fun (parts : BArray26.t list * W8.t list) =>
        gpk_kernel n (gpk_fold n history parts.`1) parts.`2).
  + rewrite -(gbc_grouped_split count remaining hc _) 1:/# dlet_dmap; trivial.
  rewrite he dprod_dlet dlet_dlet -(gpk_group_complete n history count hh hc).
  apply eq_dlet => // candidates /=; rewrite dlet_dmap /=.
  apply gpk_average_tail; last exact hr.
  have hs := gpk_fold_size n history candidates hh; smt().
qed.

lemma gpk_initial_complete n : 0 <= n =>
  dlet (gbc_bytes 6664) (fun bytes =>
    gpk_kernel n (gpk_fold n [] (gbc_chunks 255 (drop 32 bytes)))
      (drop 6630 (drop 32 bytes))) = dlist gpd_accepted n.
proof.
  move=> hn.
  rewrite -(dlet_dmap (gbc_bytes 6664) (drop 32)
    (fun bytes => gpk_kernel n (gpk_fold n [] (gbc_chunks 255 bytes)) (drop 6630 bytes)))
    gik_initial_drop32.
  have h := gpk_group_with_tail n [] 255 2 _ _ _; first 3 smt().
  by move: h; rewrite /= /gpk_complete gbs_complete_empty /gpd_accepted.
qed.

lemma gpk_initial_event n (event : int list -> bool) : 0 <= n =>
  Ep (gbc_bytes 6664) (fun bytes =>
    (mu (gpk_kernel n (gpk_fold n [] (gbc_chunks 255 (drop 32 bytes)))
      (drop 6630 (drop 32 bytes))) event)%xr) = (mu (dlist gpd_accepted n) event)%xr.
proof.
  move=> hn.
  rewrite -(Ep_mu (dlist gpd_accepted n) event) -(gpk_initial_complete n hn) Ep_dlet.
  apply eq_Ep => bytes hb /=; by rewrite Ep_mu.
qed.
