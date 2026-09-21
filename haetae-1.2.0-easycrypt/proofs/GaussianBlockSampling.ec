require import AllCore IntDiv List Distr DList DProd RealSeries Xreal StdRing StdOrder.
require import GaussianRetryCore.
import RField RealOrder.

op gbs_step (n : int) (values : int list) (candidate : int * bool) : int list =
  if size values < n /\ candidate.`2 then values ++ [candidate.`1] else values.

op gbs_scan (n : int) (values : int list) (candidates : (int * bool) list) : int list =
  foldl (gbs_step n) values candidates.

op [opaque] gbs_complete (d : (int * bool) distr) (n : int)
    (values : int list) : int list distr =
  dmap (dlist (gr_output d) (n-size values)) (fun suffix => values ++ suffix).

(* The schedule describes complete candidates, including the initial group.
   The production schedule starts with 255 and subsequently uses 5 or 6. *)
op gbs_schedule_valid (q : int -> int) : bool =
  forall block, 0 <= block => 1 <= q block.

module GaussianBlockSampling = {
  proc sample(d : (int * bool) distr, n : int, q : int -> int) : int list = {
    var block : int;
    var values : int list;
    var candidates : (int * bool) list;
    block <- 0;
    values <- [];
    while (size values < n) {
      candidates <$ dlist d (q block);
      values <- gbs_scan n values candidates;
      block <- block + 1;
    }
    return values;
  }
}.

lemma gbs_step_size n values candidate : size values <= n =>
  size values <= size (gbs_step n values candidate) <= n.
proof.
  move=> hv; rewrite /gbs_step.
  case (size values < n /\ candidate.`2); rewrite ?size_cat /=; smt().
qed.

lemma gbs_scan_nil n values : gbs_scan n values [] = values.
proof. by rewrite /gbs_scan. qed.

lemma gbs_scan_cons n values candidate tail :
  gbs_scan n values (candidate::tail) = gbs_scan n (gbs_step n values candidate) tail.
proof. by rewrite /gbs_scan. qed.

lemma gbs_scan_size n values candidates : size values <= n =>
  size values <= size (gbs_scan n values candidates) <= n.
proof.
  elim: candidates values => [|candidate tail ih] values hv.
  + by rewrite gbs_scan_nil.
  rewrite gbs_scan_cons.
  have hs := gbs_step_size n values candidate hv.
  have hi := ih (gbs_step n values candidate) _; smt().
qed.

lemma gbs_scan_full n values candidates : size values = n =>
  gbs_scan n values candidates = values.
proof.
  move=> hv; elim: candidates => [|candidate tail ih].
  + by rewrite gbs_scan_nil.
  by rewrite gbs_scan_cons /gbs_step hv ltzz /= ih.
qed.

lemma gbs_scan_filter n values candidates : size values <= n =>
  gbs_scan n values candidates = take n (values ++ map fst (filter snd candidates)).
proof.
  elim: candidates values => [|[x accepted] tail ih] values hv.
  + by rewrite gbs_scan_nil /= cats0 take_oversize.
  rewrite gbs_scan_cons.
  case accepted => haccepted /=; last first.
  + rewrite /gbs_step /=; exact (ih values hv).
  case (size values < n) => hlt.
  + rewrite /gbs_step hlt /=.
    have hnext : size (values ++ [x]) <= n by rewrite size_cat /=; smt().
    by rewrite (ih (values ++ [x]) hnext) -catA /=.
  have hfull : size values = n by smt().
  rewrite /gbs_step hlt /= (gbs_scan_full n values tail hfull).
  by rewrite (take_size_cat n values (x::map fst (filter snd tail)) hfull).
qed.

lemma gbs_scan_first_progress n values (candidate : int * bool) tail :
  size values < n => candidate.`2 =>
  size values < size (gbs_scan n values (candidate::tail)).
proof.
  move=> hv ha; rewrite gbs_scan_cons /gbs_step hv ha /=.
  have hsize : size (values ++ [candidate.`1]) = size values+1 by rewrite size_cat /=.
  have h := gbs_scan_size n (values ++ [candidate.`1]) tail _; first smt().
  smt().
qed.

lemma gbs_complete_empty d n : gbs_complete d n [] = dlist (gr_output d) n.
proof. by rewrite /gbs_complete /= dmap_id. qed.

lemma gbs_complete_full d n values : size values = n =>
  gbs_complete d n values = dunit values.
proof. by move=> hv; rewrite /gbs_complete hv subzz dlist0 // dmap_dunit /= cats0. qed.

lemma gbs_complete_ll d n values :
  0%r < mu d gr_accept => is_lossless (gbs_complete d n values).
proof.
  move=> ha; rewrite /gbs_complete; apply dmap_ll.
  exact (dlist_ll _ _ (gr_output_ll d ha)).
qed.

lemma gbs_complete_next d n values : size values < n =>
  dlet (gr_output d) (fun x => gbs_complete d n (values ++ [x])) =
    gbs_complete d n values.
proof.
  move=> hv; pose k := n-size values-1.
  have hk : 0 <= k by rewrite /k; smt().
  have hn : n-size values = k+1 by rewrite /k; ring.
  have hm : n-(size values+1) = k by rewrite /k; ring.
  rewrite {2}/gbs_complete hn dlistS 1:hk /= dmap_comp dmap_dprodE.
  apply eq_dlet => // x /=.
  rewrite /gbs_complete size_cat /= hm.
  apply eq_dmap => suffix /=.
  by rewrite /(\o) /= -catA /=.
qed.

lemma gbs_complete_step d n values :
  is_lossless d => 0%r < mu d gr_accept => size values <= n =>
  dlet d (fun candidate => gbs_complete d n (gbs_step n values candidate)) =
    gbs_complete d n values.
proof.
  move=> hd ha hv.
  case (size values < n) => hlt; last first.
  + have hsame : forall candidate, gbs_step n values candidate = values
      by move=> candidate; rewrite /gbs_step hlt.
    rewrite (eq_dlet _ (fun _ => gbs_complete d n values) d d) 1:// 1:/#.
    exact (dlet_cst d _ hd).
  rewrite {1}(marginal_sampling d gr_accept) dlet_dlet.
  have he :
    dlet (dmap d gr_accept) (fun b =>
      dlet (dcond d (fun candidate => gr_accept candidate = b))
        (fun candidate => gbs_complete d n (gbs_step n values candidate))) =
    dlet (dmap d gr_accept) (fun _ => gbs_complete d n values).
  + apply in_eq_dlet => b hb /=.
    have hpos : 0%r < mu d (fun candidate => gr_accept candidate = b).
    + move: hb; rewrite supportP dmap1E /(\o) /pred1 /=.
      have := ge0_mu d (fun candidate => gr_accept candidate = b); smt().
    case b => hbool.
    + have hecond : dcond d (fun candidate => gr_accept candidate = true) =
        dcond d gr_accept by apply eq_dcond; smt().
      rewrite hecond.
      have hs : dlet (dcond d gr_accept)
          (fun candidate => gbs_complete d n (gbs_step n values candidate)) =
        dlet (dcond d gr_accept)
          (fun (candidate : int * bool) => gbs_complete d n (values ++ [candidate.`1])).
      + apply in_eq_dlet => candidate hc /=.
        move: hc; rewrite dcond_supp /gr_accept => -[_ hc].
        by rewrite /gbs_step hlt ?hc.
      rewrite hs -(dlet_dmap (dcond d gr_accept) fst
        (fun x => gbs_complete d n (values ++ [x]))) -/(gr_output d).
      exact (gbs_complete_next d n values hlt).
    have hs : dlet (dcond d (fun candidate => gr_accept candidate = false))
        (fun candidate => gbs_complete d n (gbs_step n values candidate)) =
      dlet (dcond d (fun candidate => gr_accept candidate = false))
        (fun _ => gbs_complete d n values).
    + apply in_eq_dlet => candidate hc /=.
      move: hc; rewrite dcond_supp /gr_accept => -[_ hc].
      by rewrite /gbs_step hlt ?hc.
    rewrite hs; apply dlet_cst; apply dcond_ll.
    by move: hpos; rewrite hbool.
  rewrite he; apply dlet_cst; exact (dmap_ll d gr_accept hd).
qed.

lemma gbs_complete_group d n values q :
  is_lossless d => 0%r < mu d gr_accept => size values <= n => 0 <= q =>
  dlet (dlist d q) (fun candidates => gbs_complete d n (gbs_scan n values candidates)) =
    gbs_complete d n values.
proof.
  move=> hd ha hv hq; move: values hv.
  elim: q hq => [|q hq ih] values hv.
  + by rewrite dlist0 // dlet_unit /= gbs_scan_nil.
  rewrite dlistS 1:hq /= dmap_dprodE dlet_dlet.
  have he :
    dlet d (fun candidate =>
      dlet (dmap (dlist d q) (fun tail => candidate::tail))
        (fun candidates => gbs_complete d n (gbs_scan n values candidates))) =
    dlet d (fun candidate => gbs_complete d n (gbs_step n values candidate)).
  + apply eq_dlet => // candidate /=.
    rewrite dlet_dmap.
    have heq : (fun tail => gbs_complete d n (gbs_scan n values (candidate::tail))) =
      (fun tail => gbs_complete d n (gbs_scan n (gbs_step n values candidate) tail)).
    + apply fun_ext => tail; by rewrite gbs_scan_cons.
    rewrite /= heq; apply ih.
    have hs := gbs_step_size n values candidate hv; smt().
  rewrite he; exact (gbs_complete_step d n values hd ha hv).
qed.

lemma gbs_complete_group_event d n values q (event : int list -> bool) :
  is_lossless d => 0%r < mu d gr_accept => size values <= n => 0 <= q =>
  Ep (dlist d q) (fun candidates =>
    (mu (gbs_complete d n (gbs_scan n values candidates)) event)%xr) =
    (mu (gbs_complete d n values) event)%xr.
proof.
  move=> hd ha hv hq.
  have h := gbs_complete_group d n values q hd ha hv hq.
  rewrite -(Ep_mu (gbs_complete d n values) event) -h Ep_dlet.
  apply eq_Ep => candidates hc /=.
  by rewrite Ep_mu.
qed.

lemma gbs_group_progress d n values q :
  is_lossless d => size values < n => 1 <= q =>
  mu d gr_accept <= mu (dlist d q)
    (fun candidates => size values < size (gbs_scan n values candidates)).
proof.
  move=> hd hv hq.
  have htail : 0 <= q-1 by smt().
  have hhead : mu (dlist d q)
      (fun candidates => gr_accept (head witness candidates)) = mu d gr_accept.
  + have -> : q = (q-1)+1 by ring.
    rewrite dlistS 1:htail /= dmapE /(\o) /=.
    by rewrite (dprodEl _ _ gr_accept) (dlist_ll d (q-1) hd) /=.
  rewrite -hhead; apply mu_le => candidates hc haccept.
  have hsize := supp_dlist_size d q candidates _ hc; first smt().
  case: candidates hc haccept hsize => [|candidate tail] hc haccept hsize; first smt().
  apply gbs_scan_first_progress; first exact hv.
  by move: haccept; rewrite /= /gr_accept.
qed.

lemma gbs_event_hoare (d0 : (int * bool) distr) (n0 : int)
    (q0 : int -> int) (event : int list -> bool) :
  is_lossless d0 => 0%r < mu d0 gr_accept => 0 <= n0 => gbs_schedule_valid q0 =>
  ehoare [GaussianBlockSampling.sample :
    (d=d0 /\ n=n0 /\ q=q0) `|` (mu (dlist (gr_output d0) n0) event)%xr
    ==> (event res)%xr].
proof.
  move=> hd ha hn hq; proc.
  while ((d=d0 /\ n=n0 /\ q=q0 /\ 0 <= block /\ size values <= n0)
    `|` (mu (gbs_complete d0 n0 values) event)%xr).
  + move=> &hr; apply xle_cxr_r => hstop; apply xle_cxr_r => hinv.
    have hfull : size values{hr} = n0 by smt().
    by rewrite (gbs_complete_full d0 n0 values{hr} hfull) dunitE.
  + wp; skip => &hr.
    apply xle_cxr_r => hloop; apply xle_cxr_r => hinv.
    have [hd0 [hn0 [hq0 [hb hv]]]] := hinv.
    rewrite hd0 hn0 hq0 /= Ep_cxr.
    apply xle_cxr_l.
    + move=> candidates hc /=.
      have hs := gbs_scan_size n0 values{hr} candidates hv.
      smt().
    have hqb : 0 <= q0 block{hr} by move: hq; rewrite /gbs_schedule_valid; smt().
    by rewrite (gbs_complete_group_event d0 n0 values{hr} (q0 block{hr}) event hd ha hv hqb).
  wp; skip => &hr; apply xle_cxr_r => hinv.
  apply xle_cxr_l; first smt().
  by rewrite gbs_complete_empty.
qed.

lemma gbs_event_upper (d0 : (int * bool) distr) (n0 : int)
    (q0 : int -> int) (event : int list -> bool) &m :
  is_lossless d0 => 0%r < mu d0 gr_accept => 0 <= n0 => gbs_schedule_valid q0 =>
  Pr[GaussianBlockSampling.sample(d0,n0,q0) @ &m : event res] <=
    mu (dlist (gr_output d0) n0) event.
proof.
  move=> hd ha hn hq.
  by byehoare (gbs_event_hoare d0 n0 q0 event hd ha hn hq).
qed.

lemma gbs_total (d0 : (int * bool) distr) (n0 : int) (q0 : int -> int) :
  is_lossless d0 => 1%r/7%r <= mu d0 gr_accept => 0 <= n0 => gbs_schedule_valid q0 =>
  phoare [GaussianBlockSampling.sample : d=d0 /\ n=n0 /\ q=q0 ==> true] = 1%r.
proof.
  move=> hd ha hn hq; proc.
  seq 2 : (d=d0 /\ n=n0 /\ q=q0 /\ 0 <= block /\ size values <= n0) => //.
  + by auto => />; smt().
  while (d=d0 /\ n=n0 /\ q=q0 /\ 0 <= block /\ size values <= n0)
    (n0-size values) n0 (1%r/7%r) => //=.
  + smt(size_ge0).
  + move=> ih.
    seq 3 : (d=d0 /\ n=n0 /\ q=q0 /\ 0 <= block /\ size values <= n0) => //.
    + wp; rnd; skip; auto => />.
      move=> &hr hb hv hlt; apply eq1_mu; first exact (dlist_ll _ _ hd).
      move=> candidates hc /=.
      have hs := gbs_scan_size n0 values{hr} candidates hv; smt().
    + wp; rnd; skip; auto => />.
      move=> &hr hb hv hlt; apply mu0_false => candidates hc /=.
      have hs := gbs_scan_size n0 values{hr} candidates hv; smt().
  + wp; rnd; skip; auto => />.
    move=> &hr hb hv hlt; apply eq1_mu; first exact (dlist_ll _ _ hd).
    move=> candidates hc /=.
    have hs := gbs_scan_size n0 values{hr} candidates hv; smt().
  split; first smt().
  move=> z; wp; rnd; skip; auto => />.
  move=> &hr hb hv hlt.
  have hqb : 1 <= q0 block{hr} by apply hq; exact hb.
  have hp := gbs_group_progress d0 n0 values{hr} (q0 block{hr}) hd hlt hqb.
  have he : mu (dlist d0 (q0 block{hr}))
      (fun candidates => n0-size (gbs_scan n0 values{hr} candidates) < n0-size values{hr}) =
    mu (dlist d0 (q0 block{hr}))
      (fun candidates => size values{hr} < size (gbs_scan n0 values{hr} candidates)).
  + apply mu_eq => candidates; smt().
  rewrite he; exact (ler_trans _ _ _ ha hp).
  by hoare; auto => />; smt().
qed.

lemma gbs_joint_law (d0 : (int * bool) distr) (n0 : int)
    (q0 : int -> int) (event : int list -> bool) &m :
  is_lossless d0 => 1%r/7%r <= mu d0 gr_accept => 0 <= n0 => gbs_schedule_valid q0 =>
  Pr[GaussianBlockSampling.sample(d0,n0,q0) @ &m : event res] =
    mu (dlist (gr_output d0) n0) event.
proof.
  move=> hd ha hn hq.
  have hp : 0%r < mu d0 gr_accept by smt().
  have hu := gbs_event_upper d0 n0 q0 event &m hd hp hn hq.
  have hc := gbs_event_upper d0 n0 q0 (predC event) &m hd hp hn hq.
  have ht : Pr[GaussianBlockSampling.sample(d0,n0,q0) @ &m : true] = 1%r.
  + by byphoare (gbs_total d0 n0 q0 hd ha hn hq).
  have hl := dlist_ll (gr_output d0) n0 (gr_output_ll d0 hp).
  move: hc; rewrite /predC Pr [mu_not] ht mu_not hl => hc.
  smt().
qed.

lemma gbs_joint_phoare (d0 : (int * bool) distr) (n0 : int)
    (q0 : int -> int) (event : int list -> bool) :
  is_lossless d0 => 1%r/7%r <= mu d0 gr_accept => 0 <= n0 => gbs_schedule_valid q0 =>
  phoare [GaussianBlockSampling.sample : d=d0 /\ n=n0 /\ q=q0 ==> event res] =
    (mu (dlist (gr_output d0) n0) event).
proof.
  move=> hd ha hn hq; bypr => &m [-> [-> ->]].
  exact (gbs_joint_law d0 n0 q0 event &m hd ha hn hq).
qed.

lemma gbs_lossless :
  phoare [GaussianBlockSampling.sample :
    is_lossless d /\ 1%r/7%r <= mu d gr_accept /\ 0 <= n /\ gbs_schedule_valid q
    ==> true] = 1%r.
proof.
  bypr => &m [hd [ha [hn hq]]].
  by byphoare (gbs_total d{m} n{m} q{m} hd ha hn hq).
qed.

lemma gbs_size_total (d0 : (int * bool) distr) (n0 : int) (q0 : int -> int) :
  is_lossless d0 => 1%r/7%r <= mu d0 gr_accept => 0 <= n0 => gbs_schedule_valid q0 =>
  phoare [GaussianBlockSampling.sample : d=d0 /\ n=n0 /\ q=q0 ==> size res=n0] = 1%r.
proof.
  move=> hd ha hn hq; bypr => &m [-> [-> ->]].
  rewrite (gbs_joint_law d0 n0 q0 (fun xs => size xs=n0) &m hd ha hn hq).
  apply eq1_mu.
  + apply dlist_ll; apply gr_output_ll; smt().
  move=> xs hxs; exact (supp_dlist_size _ _ _ hn hxs).
qed.

lemma gbs_initial_refill_schedule (q : int -> int) :
  q 0 = 255 => (forall block, 1 <= block => 5 <= q block <= 6) =>
  gbs_schedule_valid q.
proof.
  move=> h0 hr; rewrite /gbs_schedule_valid => block hb.
  case (block=0) => hz; first by rewrite hz h0.
  have h := hr block _; smt().
qed.
