require import AllCore List Distr DList SDist StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 GaussianRetryCore GaussianRetryAttempt GaussianRetryActual
  GaussianRetryBatch GaussianBatchDistance SigmaConditionalSpec
  SigmaConditionalActual SigmaConditionalCorrectness Gaussian76Spec
  Gaussian76Identification GaussianRetryTail.
import RealOrder.

module GaussianRetryActualBatch = {
  proc sample(p : BArray26.t, n : int) : int list = {
    var i : int;
    var x : int;
    var values : int list;
    i <- 0;
    values <- [];
    while (i < n) {
      x <@ GaussianRetryActual.sample(p);
      values <- values ++ [x];
      i <- i + 1;
    }
    return values;
  }

  proc prefix256(p : BArray26.t) : int list = {
    var full : int list;
    full <@ sample(p, 257);
    return take 256 full;
  }
}.

lemma gra_retry_core_equiv :
  equiv [GaussianRetryActual.sample ~ GaussianRetry.sample :
    d{2} = sc_actual_pair p{1} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 r hd.
  have hl := sc_actual_pair_ll p{1}.
  have ha : 0%r < mu (sc_actual_pair p{1}) gr_accept.
  + have h := gr_actual_acceptance_positive p{1} &1.
    by move: h; rewrite /sc_accepted /gr_accept.
  rewrite (gr_actual_retry_law p{1} (pred1 r) &1) hd.
  by rewrite (gr_retry_law (sc_actual_pair p{1}) (pred1 r) &2 hl ha)
    gr_actual_output_identity.
qed.

lemma gra_batch_core_equiv :
  equiv [GaussianRetryActualBatch.sample ~ GaussianRetryBatch.sample :
    d{2} = sc_actual_pair p{1} /\ ={n} ==> ={res}].
proof.
  proc; while (d{2} = sc_actual_pair p{1} /\ ={i,n,values}).
  + wp; call gra_retry_core_equiv; skip; auto.
  by auto.
qed.

(* This is the joint law of the whole ordered list, not a collection of
   one-coordinate claims. Every retry invokes the extracted attempt. *)
lemma gra_batch_joint_law (p : BArray26.t) (n : int)
    (event : int list -> bool) &m :
  0 <= n =>
  Pr[GaussianRetryActualBatch.sample(p,n) @ &m : event res] =
    mu (dlist (sc_actual_conditioned p) n) event.
proof.
  move=> hn.
  have he : Pr[GaussianRetryActualBatch.sample(p,n) @ &m : event res] =
    Pr[GaussianRetryBatch.sample(sc_actual_pair p,n) @ &m : event res] by
    byequiv gra_batch_core_equiv.
  have ha : 0%r < mu (sc_actual_pair p) gr_accept.
  + have h := gr_actual_acceptance_positive p &m.
    by move: h; rewrite /sc_accepted /gr_accept.
  rewrite he (grb_batch_joint_law (sc_actual_pair p) n event &m
    (sc_actual_pair_ll p) ha hn).
  by rewrite gr_actual_output_identity.
qed.

lemma gra_batch_phoare (p0 : BArray26.t) (n0 : int)
    (event : int list -> bool) :
  0 <= n0 =>
  phoare [GaussianRetryActualBatch.sample : p=p0 /\ n=n0 ==> event res] =
    (mu (dlist (sc_actual_conditioned p0) n0) event).
proof.
  move=> hn; bypr => &m [-> ->].
  exact (gra_batch_joint_law p0 n0 event &m hn).
qed.

lemma gra_batch_total :
  phoare [GaussianRetryActualBatch.sample : 0 <= n ==> true] = 1%r.
proof.
  bypr => &m hn.
  rewrite (gra_batch_joint_law p{m} n{m} (fun _ => true) &m hn).
  exact (dlist_ll _ _ (sc_actual_distribution_ll p{m} &m)).
qed.

lemma gra_batch_size_total (p0 : BArray26.t) (n0 : int) :
  0 <= n0 =>
  phoare [GaussianRetryActualBatch.sample : p=p0 /\ n=n0 ==> size res=n0] = 1%r.
proof.
  move=> hn; bypr => &m [-> ->].
  rewrite (gra_batch_joint_law p0 n0 (fun xs => size xs=n0) &m hn).
  apply eq1_mu; first exact (dlist_ll _ _ (sc_actual_distribution_ll p0 &m)).
  move=> xs hxs; exact (supp_dlist_size _ _ _ hn hxs).
qed.

lemma gra_batch_gaussian_sdist (p : BArray26.t) (n : int) &m :
  0 < n =>
  sdist (dlist (sc_actual_conditioned p) n) (dlist g76_rounded n) <
    n%r / (2^39)%r.
proof.
  move=> hn.
  have h := gb_batch_distance_strict (sc_actual_conditioned p) g76_rounded
    n (1%r/(2^39)%r) hn (g76_actual_conditioned_sdist p &m).
  have he : n%r * (1%r/(2^39)%r) = n%r/(2^39)%r by ring.
  by move: h; rewrite he.
qed.

lemma gra_batch_gaussian_event (p : BArray26.t) (n : int)
    (event : int list -> bool) &m :
  0 < n =>
  `|Pr[GaussianRetryActualBatch.sample(p,n) @ &m : event res] -
    mu (dlist g76_rounded n) event| < n%r / (2^39)%r.
proof.
  move=> hn; rewrite gra_batch_joint_law 1:/#.
  exact (ler_lt_trans _ _ _ (sdist_upper_bound _ _ event)
    (gra_batch_gaussian_sdist p n &m hn)).
qed.

lemma gra_batch_256_gaussian (p : BArray26.t) &m :
  Pr[GaussianRetryActualBatch.sample(p,256) @ &m : size res=256] = 1%r /\
  sdist (dlist (sc_actual_conditioned p) 256) (dlist g76_rounded 256) <
    1%r / (2^31)%r.
proof.
  split; first by byphoare (gra_batch_size_total p 256 _).
  exact (gb_batch_256_2m39 _ _ (g76_actual_conditioned_sdist p &m)).
qed.

lemma gra_batch_257_gaussian (p : BArray26.t) &m :
  Pr[GaussianRetryActualBatch.sample(p,257) @ &m : size res=257] = 1%r /\
  sdist (dlist (sc_actual_conditioned p) 257) (dlist g76_rounded 257) <
    257%r / (2^39)%r.
proof.
  split; first by byphoare (gra_batch_size_total p 257 _).
  exact (gb_batch_257_2m39 _ _ (g76_actual_conditioned_sdist p &m)).
qed.

lemma gra_prefix256_law (p0 : BArray26.t) (event : int list -> bool) &m :
  Pr[GaussianRetryActualBatch.prefix256(p0) @ &m : event res] =
    mu (dlist (sc_actual_conditioned p0) 256) event.
proof.
  have he : mu (dlist (sc_actual_conditioned p0) 257)
      (fun xs => event (take 256 xs)) =
    mu (dlist (sc_actual_conditioned p0) 256) event.
  + rewrite -(dmapE _ (take 256) event)
      (gb_first256_of257 _ (sc_actual_distribution_ll p0 &m)).
    trivial.
  rewrite -he.
  byphoare (_ : p = p0 ==> event res) => //.
  proc; wp.
  call (gra_batch_phoare p0 257 (fun xs => event (take 256 xs)) _);
    first trivial.
qed.

lemma gra_prefix256_ll : islossless GaussianRetryActualBatch.prefix256.
proof.
  bypr => &m _.
  rewrite (gra_prefix256_law p{m} (fun _ => true) &m).
  exact (dlist_ll _ _ (sc_actual_distribution_ll p{m} &m)).
qed.

lemma gra_prefix256_gaussian_event (p : BArray26.t)
    (event : int list -> bool) &m :
  `|Pr[GaussianRetryActualBatch.prefix256(p) @ &m : event res] -
    mu (dlist g76_rounded 256) event| < 1%r / (2^31)%r.
proof.
  rewrite gra_prefix256_law.
  exact (ler_lt_trans _ _ _ (sdist_upper_bound _ _ event)
    (gb_batch_256_2m39 _ _ (g76_actual_conditioned_sdist p &m))).
qed.
