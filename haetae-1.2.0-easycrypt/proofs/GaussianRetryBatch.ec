require import AllCore IntDiv List Distr DProd DList StdOrder StdRing.
require import GaussianRetryCore GaussianBatchDistance.
import RField RealOrder.

(* Dropping a suffix of independent lossless samples preserves the full
   joint distribution of the retained prefix. *)
lemma grb_dlist_take ['a] (d : 'a distr) (n k : int) :
  is_lossless d => 0 <= k <= n =>
  dmap (dlist d n) (take k) = dlist d k.
proof.
  move=> hd [hk hkn].
  have hn : 0 <= n-k by smt().
  have -> : n = k+(n-k) by smt().
  exact (gb_dlist_prefix d k (n-k) hd hk hn).
qed.

lemma grb_dlist_257_take256 ['a] (d : 'a distr) :
  is_lossless d => dmap (dlist d 257) (take 256) = dlist d 256.
proof. move=> hd; exact (grb_dlist_take d 257 256 hd _); trivial. qed.

(* Appending after each successful retry preserves acceptance order.
   Calling sample with n=257 retains the final dummy in the full vector. *)
module GaussianRetryBatch = {
  proc sample(d : (int * bool) distr, n : int) : int list = {
    var i : int;
    var x : int;
    var values : int list;
    i <- 0;
    values <- [];
    while (i < n) {
      x <@ GaussianRetry.sample(d);
      values <- values ++ [x];
      i <- i + 1;
    }
    return values;
  }

  proc prefix256(d : (int * bool) distr) : int list = {
    var full : int list;
    full <@ sample(d, 257);
    return take 256 full;
  }
}.

(* Proof observer of one completed retry call. *)
module GaussianRetryAccepted = {
  proc sample(d : (int * bool) distr) : int = {
    var x : int;
    x <$ gr_output d;
    return x;
  }
}.

lemma grb_retry_draw_equiv (d0 : (int * bool) distr) :
  is_lossless d0 => 0%r < mu d0 gr_accept =>
  equiv [GaussianRetry.sample ~ GaussianRetryAccepted.sample :
    d{1} = d0 /\ ={d} ==> ={res}].
proof.
  move=> hd ha.
  bypr (res{1}) (res{2}) => //= &1 &2 x [h1 h2].
  have h2' : d{2} = d0 by smt().
  rewrite h1 h2' (gr_retry_law d0 (fun y => y = x) &1 hd ha).
  byphoare (_ : d = d0 ==> res = x) => //.
  proc; rnd; skip; auto => />.
qed.

section.
declare op d0 : (int * bool) distr.

local clone DList.Program as GRList with
  type t <- int,
  op d <- gr_output d0.

local lemma grb_loop_equiv :
  is_lossless d0 => 0%r < mu d0 gr_accept =>
  equiv [GaussianRetryBatch.sample ~ GRList.LoopSnoc.sample :
    d{1} = d0 /\ ={n} ==> ={res}].
proof.
  move=> hd ha; proc.
  while (d{1} = d0 /\ ={i, n} /\ values{1} = l{2}).
  + wp.
    outline {2} 1 ~ GaussianRetryAccepted.sample.
    call (grb_retry_draw_equiv d0 hd ha); skip; auto => />.
  by auto => />.
qed.

lemma grb_batch_joint_law (n0 : int) (event : int list -> bool) &m :
  is_lossless d0 => 0%r < mu d0 gr_accept => 0 <= n0 =>
  Pr[GaussianRetryBatch.sample(d0, n0) @ &m : event res] =
    mu (dlist (gr_output d0) n0) event.
proof.
  move=> hd ha hn.
  have he : Pr[GaussianRetryBatch.sample(d0, n0) @ &m : event res] =
    Pr[GRList.LoopSnoc.sample(n0) @ &m : event res].
  + by byequiv (grb_loop_equiv hd ha).
  rewrite he.
  have hs : Pr[GRList.Sample.sample(n0) @ &m : event res] =
    Pr[GRList.LoopSnoc.sample(n0) @ &m : event res].
  + by byequiv GRList.Sample_LoopSnoc_eq.
  rewrite -hs.
  byphoare (_ : n = n0 ==> event res) => //.
  proc; rnd; skip; auto => />.
qed.

end section.

lemma grb_batch_phoare (d0 : (int * bool) distr) (n0 : int)
    (event : int list -> bool) :
  is_lossless d0 => 0%r < mu d0 gr_accept => 0 <= n0 =>
  phoare [GaussianRetryBatch.sample : d = d0 /\ n = n0 ==> event res] =
    (mu (dlist (gr_output d0) n0) event).
proof.
  move=> hd ha hn; bypr => &m [-> ->].
  exact (grb_batch_joint_law d0 n0 event &m hd ha hn).
qed.

lemma grb_batch_total (d0 : (int * bool) distr) (n0 : int) :
  is_lossless d0 => 0%r < mu d0 gr_accept => 0 <= n0 =>
  phoare [GaussianRetryBatch.sample : d = d0 /\ n = n0 ==> true] = 1%r.
proof.
  move=> hd ha hn.
  have h := grb_batch_phoare d0 n0 (fun _ => true) hd ha hn.
  have hw : mu (dlist (gr_output d0) n0) (fun _ => true) = 1%r.
  + exact (dlist_ll _ _ (gr_output_ll d0 ha)).
  by move: h; rewrite hw.
qed.

lemma grb_batch_lossless :
  phoare [GaussianRetryBatch.sample :
    is_lossless d /\ 0%r < mu d gr_accept /\ 0 <= n ==> true] = 1%r.
proof.
  bypr => &m [hd [ha hn]].
  rewrite (grb_batch_joint_law d{m} n{m} (fun _ => true) &m hd ha hn).
  exact (dlist_ll _ _ (gr_output_ll d{m} ha)).
qed.

lemma grb_batch_size_total (d0 : (int * bool) distr) (n0 : int) :
  is_lossless d0 => 0%r < mu d0 gr_accept => 0 <= n0 =>
  phoare [GaussianRetryBatch.sample : d = d0 /\ n = n0 ==> size res = n0] = 1%r.
proof.
  move=> hd ha hn; bypr => &m [-> ->].
  rewrite (grb_batch_joint_law d0 n0 (fun xs => size xs = n0) &m hd ha hn).
  apply eq1_mu; first exact (dlist_ll _ _ (gr_output_ll d0 ha)).
  move=> xs hxs; exact (supp_dlist_size _ _ _ hn hxs).
qed.

lemma grb_batch_prefix_law (d0 : (int * bool) distr) (n0 k : int)
    (event : int list -> bool) &m :
  is_lossless d0 => 0%r < mu d0 gr_accept => 0 <= k <= n0 =>
  Pr[GaussianRetryBatch.sample(d0, n0) @ &m : event (take k res)] =
    mu (dlist (gr_output d0) k) event.
proof.
  move=> hd ha hk.
  have hn : 0 <= n0 by smt().
  rewrite (grb_batch_joint_law d0 n0 (fun xs => event (take k xs)) &m hd ha hn).
  rewrite -(dmapE _ (take k) event).
  by rewrite (grb_dlist_take _ n0 k (gr_output_ll d0 ha) hk).
qed.

lemma grb_batch_257_take256_law (d0 : (int * bool) distr)
    (event : int list -> bool) &m :
  is_lossless d0 => 0%r < mu d0 gr_accept =>
  Pr[GaussianRetryBatch.sample(d0, 257) @ &m : event (take 256 res)] =
    mu (dlist (gr_output d0) 256) event.
proof.
  move=> hd ha; exact (grb_batch_prefix_law d0 257 256 event &m hd ha _); trivial.
qed.

lemma grb_prefix256_law (d0 : (int * bool) distr)
    (event : int list -> bool) &m :
  is_lossless d0 => 0%r < mu d0 gr_accept =>
  Pr[GaussianRetryBatch.prefix256(d0) @ &m : event res] =
    mu (dlist (gr_output d0) 256) event.
proof.
  move=> hd ha.
  have he : mu (dlist (gr_output d0) 257)
      (fun xs => event (take 256 xs)) = mu (dlist (gr_output d0) 256) event.
  + rewrite -(dmapE _ (take 256) event).
    by rewrite (grb_dlist_257_take256 _ (gr_output_ll d0 ha)).
  rewrite -he.
  byphoare (_ : d = d0 ==> event res) => //.
  proc; wp.
  call (grb_batch_phoare d0 257 (fun xs => event (take 256 xs)) hd ha _);
    first trivial.
qed.

lemma grb_prefix256_lossless :
  phoare [GaussianRetryBatch.prefix256 :
    is_lossless d /\ 0%r < mu d gr_accept ==> true] = 1%r.
proof.
  bypr => &m [hd ha].
  rewrite (grb_prefix256_law d{m} (fun _ => true) &m hd ha).
  exact (dlist_ll _ _ (gr_output_ll d{m} ha)).
qed.
