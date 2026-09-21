require import AllCore IntDiv List StdRing StdOrder Distr DList RealSeq.
import RField RealOrder.

(* DList.dlist is the recursively sampled independent-trial distribution.
   This law is derived from its sampling equation, not a defined tail. *)
lemma gaussian_retry_iid_all ['a] (d : 'a distr) (P : 'a -> bool) (t : int) :
  0 <= t => mu (dlist d t) (all P) = (mu d P)^t.
proof.
  elim: t => [|t ht ih].
  + by rewrite dlist0 1:// dunitE /= expr0.
  rewrite dlistS 1:ht /= dmapE /(\o) /=.
  rewrite (Distr.dprodE P (all P) d (dlist d t)) ih exprS 1:ht; ring.
qed.

lemma gaussian_retry_tail_exact (d : (int * bool) distr) (t : int) :
  is_lossless d => 0 <= t =>
  mu (dlist d t) (all (predC snd)) = (1%r - mu d snd)^t.
proof.
  move=> hll ht.
  have hw : weight d = 1%r by exact hll.
  by rewrite gaussian_retry_iid_all 1:ht mu_not hw.
qed.

lemma gaussian_retry_tail_bound (d : (int * bool) distr) (t : int) :
  is_lossless d => 1%r/7%r <= mu d snd => 0 <= t =>
  mu (dlist d t) (all (predC snd)) <= (6%r/7%r)^t.
proof.
  move=> hll hsuccess ht.
  rewrite (gaussian_retry_tail_exact d t hll ht).
  have hmass := mu_bounded d snd.
  apply (ler_pexp t (1%r-mu d snd) (6%r/7%r) ht); smt().
qed.

lemma gaussian_retry_tail_limit (d : (int * bool) distr) :
  is_lossless d => 1%r/7%r <= mu d snd =>
  RealSeq.convergeto (fun t => mu (dlist d t) (all (predC snd))) 0%r.
proof.
  move=> hll hsuccess; have hmass := mu_bounded d snd.
  have hr : -1%r < 1%r-mu d snd < 1%r by smt().
  have hc := RealSeq.cnvto_pow (1%r-mu d snd) hr.
  apply (RealSeq.eq_cnvto_from 0 _ _ _ _ hc) => t ht.
  by rewrite /= (gaussian_retry_tail_exact d t hll ht).
qed.

(* An executable finite-trial experiment exposes the same no-acceptance
   event. It draws the entire iid list, so t=0 returns true. *)
module GaussianRetryTrials = {
  proc exhausted(d : (int * bool) distr, t : int) : bool = {
    var trials : (int * bool) list;
    trials <$ dlist d t;
    return all (predC snd) trials;
  }
}.

lemma gaussian_retry_trials_law (d0 : (int * bool) distr) (t0 : int) &m :
  Pr[GaussianRetryTrials.exhausted(d0,t0) @ &m : res] =
    mu (dlist d0 t0) (all (predC snd)).
proof.
  byphoare (_ : d=d0 /\ t=t0 ==> res) => //.
  proc; wp; rnd; skip; auto => />.
qed.

lemma gaussian_retry_trials_total (d0 : (int * bool) distr) (t0 : int) :
  is_lossless d0 =>
  phoare [GaussianRetryTrials.exhausted : d=d0 /\ t=t0 ==> true] = 1%r.
proof.
  move=> hll; proc; wp; rnd; skip; auto => />.
  exact (dlist_ll d0 t0 hll).
qed.

lemma gaussian_retry_trials_bound (d0 : (int * bool) distr) (t0 : int) &m :
  is_lossless d0 => 1%r/7%r <= mu d0 snd => 0 <= t0 =>
  Pr[GaussianRetryTrials.exhausted(d0,t0) @ &m : res] <= (6%r/7%r)^t0.
proof.
  move=> hll hsuccess ht.
  rewrite gaussian_retry_trials_law.
  exact (gaussian_retry_tail_bound d0 t0 hll hsuccess ht).
qed.
