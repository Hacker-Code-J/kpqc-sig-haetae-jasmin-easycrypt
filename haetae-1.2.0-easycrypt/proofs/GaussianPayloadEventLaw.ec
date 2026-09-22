require import AllCore IntDiv List Distr DList Xreal StdOrder.
from Jasmin require import JModel_x86.
require import GaussianPayloadSpec GaussianPayloadEncoding GaussianPayloadKernel
  GaussianPayloadBufferSpec GaussianPayloadBufferPath GaussianIidBufferSpec GaussianIidBufferPath
  GaussianUniformBytes GaussianByteCarryDistribution.
import RealOrder.

lemma gpe_refill_shape n history tail bytes : size bytes = 136 =>
  gpd_scan n history (tail++bytes) =
    gpk_fold n history (gbc_chunks (gbc_refill_count (size tail)) (tail++bytes)) /\
  gib_remainder (tail++bytes) = drop (26*gbc_refill_count (size tail)) (tail++bytes).
proof.
  move=> hb.
  have hq : size (tail++bytes) %/ 26 = gbc_refill_count (size tail) by
    rewrite size_cat hb /gbc_refill_count.
  split; first by rewrite gpk_pending_fold hq.
  by rewrite /gib_remainder hq.
qed.

lemma gpe_initial_shape n bytes : size bytes = 6664 =>
  gpd_scan n [] (drop 32 bytes) = gpk_fold n [] (gbc_chunks 255 (drop 32 bytes)) /\
  gib_remainder (drop 32 bytes) = drop 6630 (drop 32 bytes).
proof.
  move=> hb.
  have hs : size (drop 32 bytes) = 6632 by rewrite size_drop 1:// hb.
  split; first by rewrite gpk_pending_fold hs.
  by rewrite /gib_remainder hs.
qed.

(* The invariant keeps the exact already observed tail. The expectation
   rule averages only the next independent byte block. *)
lemma gpe_history_event_hoare (n0 : int) (event : int list -> bool) : 0 <= n0 =>
  ehoare [GaussianPayloadHistory.sample :
    (n=n0) `|` (mu (dlist gpd_accepted n0) event)%xr ==> (event res)%xr].
proof.
  move=> hn; proc.
  while ((n=n0 /\ size history <= n0)
    `|` (mu (gpk_kernel n0 history (gib_remainder pending)) event)%xr).
  + move=> &hr; apply xle_cxr_r => hstop; apply xle_cxr_r => hinv.
    have hsize : size history{hr} = n0 by smt().
    by rewrite (gpk_kernel_full n0 _ _ hsize) dunitE.
  + wp; skip => &hr.
    apply xle_cxr_r => hloop; apply xle_cxr_r => -[hn0 hh].
    pose tail := gib_remainder pending{hr}.
    have [_ hrem] := gib_remainder_size pending{hr}.
    have ht : size tail < 26 by rewrite /tail; smt().
    rewrite hn0 -/tail /gib_block -/(gbc_bytes 136) /= Ep_cxr.
    apply xle_cxr_l.
    + move=> bytes hbytes /=.
      have hsize := gpk_pending_size n0 history{hr} (tail++bytes) hh; smt().
    rewrite -(gpk_refill_event n0 history{hr} tail event hh ht).
    apply le_Ep => bytes hbytes /=.
    have hsize := supp_dlist_size W8.dword 136 bytes _ hbytes; first trivial.
    have [hscan htail] := gpe_refill_shape n0 history{hr} tail bytes hsize.
    by rewrite hscan htail.
  wp; skip => &hr; apply xle_cxr_r => hn0.
  rewrite hn0 /= Ep_cxr.
  apply xle_cxr_l.
  + move=> bytes hbytes /=.
    have hsize := gpk_pending_size n0 [] (drop 32 bytes) _; first smt().
    smt().
  rewrite -(gpk_initial_event n0 event hn).
  apply le_Ep => bytes hbytes /=.
  have hsize := supp_dlist_size W8.dword 6664 bytes _ hbytes; first trivial.
  have [hscan htail] := gpe_initial_shape n0 bytes hsize.
  by rewrite hscan htail.
qed.

lemma gpe_history_upper (n : int) (event : int list -> bool) &m : 0 <= n =>
  Pr[GaussianPayloadHistory.sample(n) @ &m : event res] <=
    mu (dlist gpd_accepted n) event.
proof.
  move=> hn; by byehoare (gpe_history_event_hoare n event hn).
qed.

(* Equality uses the independently proved losslessness of the controller;
   the upper-bound invariant alone is not a termination argument. *)
lemma gpe_history_law (n : int) (event : int list -> bool) &m : 0 <= n <= 512 =>
  Pr[GaussianPayloadHistory.sample(n) @ &m : event res] =
    mu (dlist gpd_accepted n) event.
proof.
  move=> hn.
  have hu := gpe_history_upper n event &m _; first smt().
  have hc := gpe_history_upper n (predC event) &m _; first smt().
  have ht : Pr[GaussianPayloadHistory.sample(n) @ &m : true] = 1%r.
  + by byphoare (gpb_history_total n hn).
  have hl := dlist_ll gpd_accepted n gpd_accepted_ll.
  move: hc; rewrite /predC Pr [mu_not] ht mu_not hl => hc.
  smt().
qed.

lemma gpe_history_phoare (n0 : int) (event : int list -> bool) : 0 <= n0 <= 512 =>
  phoare [GaussianPayloadHistory.sample : n=n0 ==> event res] =
    (mu (dlist gpd_accepted n0) event).
proof.
  move=> hn; bypr => &m ->.
  exact (gpe_history_law n0 event &m hn).
qed.
