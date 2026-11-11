require import AllCore IntDiv List Real Distr RealSeries StdRing StdOrder StdBigop Xreal.
from Jasmin require import JModel_x86.
require import BArray26 HalfGaussianProperties GaussianRetryCore GaussianRetryActual
  GaussianRetryAttempt SigmaConditionalSpec SigmaConditionalActual SigmaJoint203Bridge
  GaussianAcceptanceActual.
import RField RealOrder Bigreal Bigreal.BRA HalfGaussianProperties.

op gae_pmf (success : real) (count : int) : real =
  if 1<=count then success*(1%r-success)^(count-1) else 0%r.
op gae_geometric (success : real) : int distr = mk (gae_pmf success).
op gae_shift (success : real) (offset : int) : int distr =
  dmap (gae_geometric success) (fun count => offset+count).
op gae_ipow (ratio : real) (k : int) : real =
  if 0<=k then k%r*ratio^k else 0%r.

(* The count includes the first candidate and the final accepted candidate.
   The actual observer executes the extracted Jasmin attempt on every draw. *)
module GaussianCountedRetry = {
  proc sample(d : (int * bool) distr) : int * int = {
    var r : int * bool;
    var count : int;
    count <- 1;
    r <$ d;
    while (!r.`2) {
      count <- count+1;
      r <$ d;
    }
    return (r.`1,count);
  }
}.

module GaussianCountedActual = {
  proc sample(p : BArray26.t) : int * int = {
    var r : int * bool;
    var count : int;
    count <- 1;
    r <@ SigmaJoint203Experiment.sample(p);
    while (!r.`2) {
      count <- count+1;
      r <@ SigmaJoint203Experiment.sample(p);
    }
    return (r.`1,count);
  }
}.

module GaussianCountedObserved = {
  proc sample(p : BArray26.t) : int * int = {
    var r : int * bool;
    var count : int;
    count <- 1;
    r <@ GaussianActualPair.sample(p);
    while (!r.`2) {
      count <- count+1;
      r <@ GaussianActualPair.sample(p);
    }
    return (r.`1,count);
  }
}.

lemma gae_shift_bij offset : bijective (fun k : int => k+offset).
proof. exists (fun k : int => k-offset); split; smt(). qed.

lemma gae_geom_sum ratio : 0%r<=ratio<1%r =>
  RealSeries.sum (hg_geom ratio)=1%r/(1%r-ratio).
proof.
  move=> hr; have [hs _] := hg_geom_summable_bound ratio hr.
  pose positive := fun k => if k<>0 then hg_geom ratio k else 0%r.
  have hp : RealSeries.summable positive by
    exact (RealSeries.summable_cond (hg_geom ratio) (fun k => k<>0) hs).
  have hshift := RealSeries.sum_reindex (fun k : int => k+1) positive (gae_shift_bij 1) hp.
  have he : positive \o (fun k : int => k+1) = (fun k => ratio*hg_geom ratio k).
  + apply fun_ext => k; rewrite /(\o) /positive /hg_geom.
    case (0<=k) => hk.
    - have [hneq hpos] : k+1<>0 /\ 0<=k+1 by smt().
      rewrite ?hk ?hneq ?hpos /= exprS 1:hk; ring.
    have hk1 : k+1=0 \/ k+1<0 by smt().
    smt().
  move: hshift; rewrite he RealSeries.sumZ => hshift.
  have hsplit := RealSeries.sumD1 (hg_geom ratio) 0 hs.
  have hzero : hg_geom ratio 0=1%r by rewrite /hg_geom /= expr0.
  move: hsplit; rewrite hzero -/positive => hsplit.
  have hn : 1%r-ratio<>0%r by smt().
  apply (mulIf (1%r-ratio) hn).
  have heq : RealSeries.sum (hg_geom ratio)*(1%r-ratio)=1%r.
  + rewrite mulrBr mulr1 (mulrC _ ratio) hshift hsplit; ring.
  rewrite heq; field; smt().
qed.

lemma gae_pmf_shift success count :
  gae_pmf success count=success*hg_geom (1%r-success) (count-1).
proof. rewrite /gae_pmf /hg_geom; smt(). qed.

lemma gae_pmf_nonnegative success count : 0%r<success<=1%r =>
  0%r<=gae_pmf success count.
proof.
  move=> hs; rewrite gae_pmf_shift.
  apply mulr_ge0; first smt().
  apply hg_geom_ge0; smt().
qed.

lemma gae_pmf_summable success : 0%r<success<=1%r =>
  RealSeries.summable (gae_pmf success).
proof.
  move=> hs; have hr : 0%r<=1%r-success<1%r by smt().
  have [hg _] := hg_geom_summable_bound (1%r-success) hr.
  have hz := RealSeries.summableZ (hg_geom (1%r-success)) success hg.
  have h := RealSeries.summable_bij (fun k : int => k+(-1))
    (fun k => success*hg_geom (1%r-success) k) (gae_shift_bij (-1)) hz.
  apply (RealSeries.eqL_summable _ _ h) => k /=.
  by rewrite gae_pmf_shift.
qed.

lemma gae_pmf_sum success : 0%r<success<=1%r =>
  RealSeries.sum (gae_pmf success)=1%r.
proof.
  move=> hs; have hr : 0%r<=1%r-success<1%r by smt().
  have [hg _] := hg_geom_summable_bound (1%r-success) hr.
  have hz := RealSeries.summableZ (hg_geom (1%r-success)) success hg.
  have h := RealSeries.sum_reindex (fun k : int => k+(-1))
    (fun k => success*hg_geom (1%r-success) k) (gae_shift_bij (-1)) hz.
  have he : gae_pmf success =
      (fun k => success*hg_geom (1%r-success) k) \o (fun k : int => k+(-1)).
  + apply fun_ext => k; by rewrite /= gae_pmf_shift.
  rewrite he h RealSeries.sumZ (gae_geom_sum _ hr).
  field; smt().
qed.

lemma gae_pmf_isdistr success : 0%r<success<=1%r => isdistr (gae_pmf success).
proof.
  move=> hs.
  have hp : forall k, 0%r<=gae_pmf success k by
    move=> k; exact (gae_pmf_nonnegative success k hs).
  split; first exact hp.
  move=> values hu.
  have h := RealSeries.ler_big_sum (gae_pmf success) values
    hp hu (gae_pmf_summable success hs).
  by move: h; rewrite (gae_pmf_sum success hs).
qed.

lemma gae_geometric_mu1 success count : 0%r<success<=1%r =>
  mu1 (gae_geometric success) count=gae_pmf success count.
proof. move=> hs; by rewrite /gae_geometric muK 1:(gae_pmf_isdistr success hs). qed.

lemma gae_geometric_ll success : 0%r<success<=1%r => is_lossless (gae_geometric success).
proof.
  move=> hs; rewrite /is_lossless weightE.
  have -> : (fun k => mu1 (gae_geometric success) k)=gae_pmf success by
    apply fun_ext => k; exact (gae_geometric_mu1 success k hs).
  exact (gae_pmf_sum success hs).
qed.

lemma gae_counted_retry_erasure :
  equiv [GaussianCountedRetry.sample ~ GaussianRetry.sample :
    ={d} ==> res{1}.`1=res{2}].
proof.
  proc; while (={d,r}); auto.
qed.

lemma gae_counted_retry_total (d0 : (int * bool) distr) :
  is_lossless d0 => 0%r<mu d0 gr_accept =>
  phoare [GaussianCountedRetry.sample : d=d0 ==> true] = 1%r.
proof.
  move=> hd ha.
  by conseq gae_counted_retry_erasure (gr_retry_total d0 hd ha) => /#.
qed.

lemma gae_actual_observed_equiv :
  equiv [GaussianCountedActual.sample ~ GaussianCountedObserved.sample :
    ={p} ==> ={res}].
proof.
  proc; while (={p,r,count}).
  + call gr_actual_pair_equiv; auto.
  call gr_actual_pair_equiv; auto.
qed.

lemma gae_observed_core_equiv :
  equiv [GaussianCountedObserved.sample ~ GaussianCountedRetry.sample :
    d{2}=sc_actual_pair p{1} ==> ={res}].
proof.
  proc; inline GaussianActualPair.sample; wp.
  while (d{2}=sc_actual_pair p{1} /\ ={r,count}); auto.
qed.

lemma gae_ipow_nonnegative ratio k : 0%r<=ratio => 0%r<=gae_ipow ratio k.
proof.
  move=> hr; rewrite /gae_ipow; case (0<=k) => hk; last trivial.
  apply mulr_ge0; first smt().
  exact (expr_ge0 k ratio hr).
qed.

lemma gae_ipow_summable ratio : 0%r<=ratio<1%r => RealSeries.summable (gae_ipow ratio).
proof.
  move=> hr.
  have [hs _] := hg_nat_summable_bound (gae_ipow ratio) (1%r/(1%r-ratio)^2) _ _ _.
  + move=> k hk; by rewrite /gae_ipow; smt().
  + move=> k; apply gae_ipow_nonnegative; smt().
  + move=> n hn.
    rewrite (@eq_big_int _ _ _ (fun k : int => k%r*ratio^k)).
    - move=> k hk; rewrite /gae_ipow; smt().
    exact (Bigreal.sum_ipow_le ratio n hr).
  exact hs.
qed.

lemma gae_ipow_succ ratio k :
  gae_ipow ratio (k+1)=ratio*(gae_ipow ratio k+hg_geom ratio k).
proof.
  case (0<=k) => hk.
  + have hk1 : 0<=k+1 by smt().
    rewrite /gae_ipow /hg_geom hk hk1 /= fromintD /= exprS 1:hk; ring.
  case (k = -1) => [->|hne]; first by rewrite /gae_ipow /hg_geom /=.
  have hk1 : !(0<=k+1) by smt().
  by rewrite /gae_ipow /hg_geom hk hk1 /=.
qed.

lemma gae_ipow_sum_relation ratio : 0%r<=ratio<1%r =>
  (1%r-ratio)*(RealSeries.sum (gae_ipow ratio)+RealSeries.sum (hg_geom ratio))=
    RealSeries.sum (hg_geom ratio).
proof.
  move=> hr.
  have hs := gae_ipow_summable ratio hr.
  have [hg _] := hg_geom_summable_bound ratio hr.
  have he : gae_ipow ratio \o (fun k : int => k+1) =
    (fun k => ratio*(gae_ipow ratio k+hg_geom ratio k)) by
    apply fun_ext => k; exact (gae_ipow_succ ratio k).
  have h := RealSeries.sum_reindex (fun k : int => k+1) (gae_ipow ratio)
    (gae_shift_bij 1) hs.
  move: h; rewrite he RealSeries.sumZ (RealSeries.sumD _ _ hs hg) => h.
  rewrite mulrBl mul1r h; ring.
qed.

lemma gae_moment_shift success count :
  count%r*gae_pmf success count = success*
    (gae_ipow (1%r-success) (count-1)+hg_geom (1%r-success) (count-1)).
proof.
  case (1<=count) => hc.
  + have hk : 0<=count-1 by smt().
    rewrite /gae_pmf /gae_ipow /hg_geom hc hk /= fromintB /=; ring.
  have hk : !(0<=count-1) by smt().
  by rewrite /gae_pmf /gae_ipow /hg_geom hc hk /=.
qed.

lemma gae_geometric_hasE success : 0%r<success<=1%r =>
  hasE (gae_geometric success) (fun count => count%r).
proof.
  move=> ha; have hr : 0%r<=1%r-success<1%r by smt().
  have hw := gae_ipow_summable (1%r-success) hr.
  have [hg _] := hg_geom_summable_bound (1%r-success) hr.
  have hd := RealSeries.summableD _ _ hw hg.
  have hz := RealSeries.summableZ _ success hd.
  have hs := RealSeries.summable_bij (fun k : int => k+(-1)) _ (gae_shift_bij (-1)) hz.
  rewrite /hasE; apply (RealSeries.eqL_summable _ _ hs) => k /=.
  by rewrite (gae_geometric_mu1 success k ha) gae_moment_shift.
qed.

lemma gae_geometric_expectation success : 0%r<success<=1%r =>
  E (gae_geometric success) (fun count => count%r)=1%r/success.
proof.
  move=> ha; have hr : 0%r<=1%r-success<1%r by smt().
  have hw := gae_ipow_summable (1%r-success) hr.
  have [hg _] := hg_geom_summable_bound (1%r-success) hr.
  have hd := RealSeries.summableD _ _ hw hg.
  have hz := RealSeries.summableZ _ success hd.
  have hs := RealSeries.sum_reindex (fun k : int => k+(-1)) _ (gae_shift_bij (-1)) hz.
  have he : (fun k => k%r*mu1 (gae_geometric success) k) =
    (fun k => success*(gae_ipow (1%r-success) k+hg_geom (1%r-success) k)) \o
      (fun k : int => k+(-1)).
  + apply fun_ext => k; by rewrite /= (gae_geometric_mu1 success k ha) gae_moment_shift.
  rewrite /E he hs RealSeries.sumZ (RealSeries.sumD _ _ hw hg).
  have hrel := gae_ipow_sum_relation (1%r-success) hr.
  have heq : 1%r-(1%r-success)=success by ring.
  move: hrel; rewrite heq => hrel.
  by rewrite hrel (gae_geom_sum _ hr) heq.
qed.

lemma gae_pmf_unfold success count : gae_pmf success count =
  success*b2r (count=1)+(1%r-success)*gae_pmf success (count-1).
proof.
  case (count=1) => [->|hne]; first by rewrite /gae_pmf /b2r /= expr0.
  case (1<=count) => hc.
  + have hc1 : 1<=count-1 by smt().
    rewrite /gae_pmf /b2r ?hne ?hc ?hc1 /=.
    have he : count-1=(count-2)+1 by ring.
    rewrite {1}he exprS 1:/#; ring.
  have hc1 : !(1<=count-1) by smt().
  by rewrite /gae_pmf /b2r ?hne ?hc ?hc1 /=.
qed.

lemma gae_shift_mu1 success offset count : 0%r<success<=1%r =>
  mu1 (gae_shift success offset) count=gae_pmf success (count-offset).
proof.
  move=> hs; rewrite /gae_shift.
  rewrite (dmap1E_can _ _ (fun k => k-offset)) 1:/# 1:/#.
  exact (gae_geometric_mu1 success (count-offset) hs).
qed.

lemma gae_branch_expectation (d : (int * bool) distr) (x y : real) :
  is_lossless d => E d (fun r => if gr_accept r then x else y) =
    mu d gr_accept*x+(1%r-mu d gr_accept)*y.
proof.
  move=> hd.
  have he : (fun r => if gr_accept r then x else y) =
    (fun r => (if gr_accept r then x else 0%r)+(if !gr_accept r then y else 0%r)) by
    apply fun_ext => r; case (gr_accept r); smt().
  rewrite he expD 1:(hasE_cond d (fun _ => x) gr_accept (hasEC d x))
    1:(hasE_cond d (fun _ => y) (predC gr_accept) (hasEC d y)).
  rewrite !expC_cond -/(predC gr_accept) mu_not hd; ring.
qed.

op gae_completion (success : real) (count : int) (accepted : bool) : int distr =
  if accepted then dunit count else gae_shift success count.

lemma gae_completion_step (d : (int * bool) distr) count :
  is_lossless d => 0%r<mu d gr_accept =>
  dlet d (fun (r : int * bool) => gae_completion (mu d gr_accept) (count+1) r.`2) =
    gae_shift (mu d gr_accept) count.
proof.
  move=> hd ha; have hr : 0%r<mu d gr_accept<=1%r by smt(mu_bounded).
  apply eq_distr => k.
  rewrite sj203_dlet_expectation.
  have he : (fun (r : int * bool) => mu1 (gae_completion (mu d gr_accept) (count+1) r.`2) k) =
    (fun r => if gr_accept r then b2r (k=count+1)
      else gae_pmf (mu d gr_accept) (k-(count+1))).
  + apply fun_ext => r; rewrite /gae_completion /gr_accept.
    case r.`2 => hcase /=; first by rewrite dunit1E /pred1; smt().
    exact (gae_shift_mu1 _ (count+1) k hr).
  rewrite he (gae_branch_expectation d _ _ hd) (gae_shift_mu1 _ count k hr).
  rewrite (gae_pmf_unfold (mu d gr_accept) (k-count)).
  have heq : (k=count+1)=(k-count=1) by smt().
  have hi : k-(count+1)=k-count-1 by ring.
  by rewrite heq hi.
qed.

lemma gae_completion_step_event (d : (int * bool) distr) count (event : int -> bool) :
  is_lossless d => 0%r<mu d gr_accept =>
  Ep d (fun (r : int * bool) => (mu (gae_completion (mu d gr_accept) (count+1) r.`2) event)%xr) =
    (mu (gae_shift (mu d gr_accept) count) event)%xr.
proof.
  move=> hd ha; have h := gae_completion_step d count hd ha.
  rewrite -(Ep_mu (gae_shift (mu d gr_accept) count) event) -h Ep_dlet.
  by apply eq_Ep => r _ /=; rewrite Ep_mu.
qed.

lemma gae_shift_zero success : gae_shift success 0=gae_geometric success.
proof. by rewrite /gae_shift /= dmap_id. qed.

lemma gae_retry_count_event_hoare (d0 : (int * bool) distr) (event : int -> bool) :
  is_lossless d0 => 0%r<mu d0 gr_accept =>
  ehoare [GaussianCountedRetry.sample :
    (d=d0) `|` (mu (gae_geometric (mu d0 gr_accept)) event)%xr ==> (event res.`2)%xr].
proof.
  move=> hd ha; proc.
  while ((d=d0) `|` (mu (gae_completion (mu d0 gr_accept) count r.`2) event)%xr).
  + move=> &hr; apply xle_cxr_r => hstop; apply xle_cxr_r => heq.
    have hacc : r{hr}.`2 by smt().
    rewrite /gae_completion hacc /= dunitE /=.
    by rewrite to_pos_pos 1:b2r_ge0.
  + wp; skip => &hr.
    apply xle_cxr_r => hloop; apply xle_cxr_r => heq.
    rewrite heq /= (gae_completion_step_event d0 count{hr} event hd ha).
    by rewrite /gae_completion hloop /=.
  wp; skip => &hr; apply xle_cxr_r => heq.
  rewrite heq /= -(gae_shift_zero (mu d0 gr_accept)).
  by rewrite (gae_completion_step_event d0 0 event hd ha).
qed.

lemma gae_retry_count_upper (d0 : (int * bool) distr) (event : int -> bool) &m :
  is_lossless d0 => 0%r<mu d0 gr_accept =>
  Pr[GaussianCountedRetry.sample(d0) @ &m : event res.`2] <=
    mu (gae_geometric (mu d0 gr_accept)) event.
proof. move=> hd ha; by byehoare (gae_retry_count_event_hoare d0 event hd ha). qed.

lemma gae_retry_count_law (d0 : (int * bool) distr) (event : int -> bool) &m :
  is_lossless d0 => 0%r<mu d0 gr_accept =>
  Pr[GaussianCountedRetry.sample(d0) @ &m : event res.`2] =
    mu (gae_geometric (mu d0 gr_accept)) event.
proof.
  move=> hd ha.
  have hu := gae_retry_count_upper d0 event &m hd ha.
  have hc := gae_retry_count_upper d0 (predC event) &m hd ha.
  have ht : Pr[GaussianCountedRetry.sample(d0) @ &m : true]=1%r by
    byphoare (gae_counted_retry_total d0 hd ha).
  have hr : 0%r<mu d0 gr_accept<=1%r by smt(mu_bounded).
  have hl := gae_geometric_ll (mu d0 gr_accept) hr.
  move: hc; rewrite /predC Pr[mu_not] ht mu_not hl => hc.
  smt().
qed.

(* These laws concern fresh independent candidate bits. They make no
   independence or termination assertion for a fixed concrete SHAKE seed. *)
op gae_actual_count_distribution (p : BArray26.t) : int distr =
  gae_geometric (mu (sc_actual_pair p) sc_accepted).

lemma gae_actual_success_range (p : BArray26.t) :
  0%r<mu (sc_actual_pair p) sc_accepted<=1%r.
proof.
  have h := gaa_acceptance_lower p.
  have hb := mu_bounded (sc_actual_pair p) sc_accepted.
  smt().
qed.

lemma gae_actual_count_law (p : BArray26.t) (event : int -> bool) &m :
  Pr[GaussianCountedActual.sample(p) @ &m : event res.`2] =
    mu (gae_actual_count_distribution p) event.
proof.
  have h1 : Pr[GaussianCountedActual.sample(p) @ &m : event res.`2] =
    Pr[GaussianCountedObserved.sample(p) @ &m : event res.`2] by
    byequiv gae_actual_observed_equiv.
  have h2 : Pr[GaussianCountedObserved.sample(p) @ &m : event res.`2] =
    Pr[GaussianCountedRetry.sample(sc_actual_pair p) @ &m : event res.`2] by
    byequiv gae_observed_core_equiv.
  have ha : 0%r<mu (sc_actual_pair p) gr_accept.
  + have h := gae_actual_success_range p; move: h; rewrite /gr_accept /sc_accepted; smt().
  rewrite h1 h2 (gae_retry_count_law (sc_actual_pair p) event &m (sc_actual_pair_ll p) ha).
  by rewrite /gae_actual_count_distribution /gr_accept /sc_accepted.
qed.

lemma gae_actual_count_geometric (p : BArray26.t) count &m :
  Pr[GaussianCountedActual.sample(p) @ &m : res.`2=count] =
    gae_pmf (mu (sc_actual_pair p) sc_accepted) count.
proof.
  rewrite (gae_actual_count_law p (pred1 count) &m) /gae_actual_count_distribution.
  exact (gae_geometric_mu1 _ count (gae_actual_success_range p)).
qed.

lemma gae_actual_counted_ll : islossless GaussianCountedActual.sample.
proof.
  bypr => &m _; rewrite (gae_actual_count_law p{m} (fun _ => true) &m)
    /gae_actual_count_distribution.
  exact (gae_geometric_ll _ (gae_actual_success_range p{m})).
qed.

lemma gae_actual_erasure :
  equiv [GaussianCountedActual.sample ~ GaussianRetryActual.sample :
    ={p} ==> res{1}.`1=res{2}].
proof.
  proc; while (={p,r}).
  + call (_ : ={p} ==> ={res}); first by proc; sim.
    auto.
  call (_ : ={p} ==> ={res}); first by proc; sim.
  auto.
qed.

lemma gae_actual_count_hasE (p : BArray26.t) :
  hasE (gae_actual_count_distribution p) (fun count => count%r).
proof. exact (gae_geometric_hasE _ (gae_actual_success_range p)). qed.

lemma gae_actual_expected_count (p : BArray26.t) :
  E (gae_actual_count_distribution p) (fun count => count%r) =
    1%r/mu (sc_actual_pair p) sc_accepted.
proof. exact (gae_geometric_expectation _ (gae_actual_success_range p)). qed.

lemma gae_actual_expected_count_bound (p : BArray26.t) :
  E (gae_actual_count_distribution p) (fun count => count%r)<20%r/19%r.
proof.
  rewrite gae_actual_expected_count.
  have [ha _] := gae_actual_success_range p.
  have h := gaa_acceptance_lower p.
  rewrite ltr_pdivr_mulr 1:ha; smt().
qed.
