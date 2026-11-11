require import AllCore IntDiv List Distr DList RealSeq StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 GaussianRetryAttempt GaussianRetryInputs
  GaussianRetryBatchTail GaussianRetryStreamBridge GaussianStreamBuffer
  SigmaConditionalSpec SigmaConditionalActual.
import RealOrder.

(* Each finite prefix uses actual candidate bytes and the exact stream
   adequacy predicate consumed by the concrete buffer-loop proof. *)
op gr_prefix_failure (p : BArray26.t) (n length : int) : real =
  mu (dlist (gr_candidate_distribution p) length)
    (fun candidates => !gr_adequate (gr_candidate_stream candidates) n length).

lemma gr_prefix_failure_law (p : BArray26.t) (n length : int) :
  0 <= n => 0 <= length =>
  gr_prefix_failure p n length =
    mu (dlist (sc_actual_pair p) length) (fun pairs => count snd pairs < n).
proof.
  move=> hn hl; rewrite /gr_prefix_failure -(gr_candidate_pairs_iid p length)
    dmapE /(\o).
  apply mu_eq_support => candidates hc.
  have hs := supp_dlist_size (gr_candidate_distribution p) length candidates hl hc.
  rewrite /gr_adequate hn hl /= -hs gr_candidate_stream_accept_count.
  smt().
qed.

lemma gr_prefix_failure_bound (p : BArray26.t) (n t : int) &m :
  0 <= n => 0 <= t =>
  gr_prefix_failure p n (n*t) <= n%r * (6%r/7%r)^t.
proof.
  move=> hn ht.
  have hnt : 0 <= n*t by apply IntOrder.mulr_ge0; smt().
  rewrite (gr_prefix_failure_law p n (n*t) hn hnt).
  apply (grbt_prefix_shortfall_1m7 (sc_actual_pair p) n t
    (sc_actual_pair_ll p) _ hn ht).
  exact (gr_actual_acceptance_lower p &m).
qed.

lemma gr_prefix_failure_limit (p : BArray26.t) (n : int) &m :
  0 <= n => RealSeq.convergeto (fun length => gr_prefix_failure p n length) 0%r.
proof.
  move=> hn.
  have hc := grbt_all_prefix_shortfall_limit (sc_actual_pair p) snd n
    (sc_actual_pair_ll p) (gr_actual_acceptance_positive p &m) hn.
  apply (RealSeq.eq_cnvto_from 0 _ _ _ _ hc) => length hl.
  by rewrite /= (gr_prefix_failure_law p n length hn hl).
qed.

(* Actual buffering offers floor((136*blocks-32)/26) complete candidates.
   As more blocks become available, the probability of an inadequate
   canonical iid prefix tends to zero, including requests256 and257. *)
lemma gr_block_prefix_failure_limit (p : BArray26.t) (n : int) &m :
  0 <= n => RealSeq.convergeto
    (fun blocks => gr_prefix_failure p n (gs_stream_attempts blocks)) 0%r.
proof.
  move=> hn epsilon hepsilon.
  have hc := gr_prefix_failure_limit p n &m hn.
  have [L hL] := hc epsilon hepsilon.
  pose length0 := max 0 L.
  have [hl0 hlL] : 0 <= length0 /\ L <= length0 by rewrite /length0 /max; smt().
  exists (gr_block_cap length0) => blocks hb.
  have [_ ha] := gr_block_cap_bounds length0 hl0.
  have hm := gr_attempts_monotone (gr_block_cap length0) blocks hb.
  apply hL; smt().
qed.

module GaussianRetryPrefix = {
  proc inadequate(p : BArray26.t, n : int, length : int) : bool = {
    var candidates : BArray26.t list;
    candidates <$ dlist (gr_candidate_distribution p) length;
    return !gr_adequate (gr_candidate_stream candidates) n length;
  }
}.

lemma gr_prefix_experiment_law (p0 : BArray26.t) (n0 length0 : int) &m :
  Pr[GaussianRetryPrefix.inadequate(p0,n0,length0) @ &m : res] =
    gr_prefix_failure p0 n0 length0.
proof.
  byphoare (_ : p=p0 /\ n=n0 /\ length=length0 ==> res) => //.
  proc; wp; rnd; skip; auto => />.
qed.

lemma gr_prefix_experiment_ll : islossless GaussianRetryPrefix.inadequate.
proof.
  proc; wp; rnd; skip; auto => />.
  move=> &hr; exact (dlist_ll _ _ (gr_candidate_distribution_ll p{hr})).
qed.

lemma gr_prefix_experiment_bound (p : BArray26.t) (n t : int) &m :
  0 <= n => 0 <= t =>
  Pr[GaussianRetryPrefix.inadequate(p,n,n*t) @ &m : res] <= n%r*(6%r/7%r)^t.
proof.
  move=> hn ht; rewrite gr_prefix_experiment_law.
  exact (gr_prefix_failure_bound p n t &m hn ht).
qed.

lemma gr_prefix_256_bound (p : BArray26.t) (t : int) &m :
  0 <= t =>
  Pr[GaussianRetryPrefix.inadequate(p,256,256*t) @ &m : res] <= 256%r*(6%r/7%r)^t.
proof. by move=> ht; exact (gr_prefix_experiment_bound p 256 t &m _ ht). qed.

lemma gr_prefix_257_bound (p : BArray26.t) (t : int) &m :
  0 <= t =>
  Pr[GaussianRetryPrefix.inadequate(p,257,257*t) @ &m : res] <= 257%r*(6%r/7%r)^t.
proof. by move=> ht; exact (gr_prefix_experiment_bound p 257 t &m _ ht). qed.
