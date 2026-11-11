require import AllCore Distr SDist StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 GaussianRetryCore GaussianRetryAttempt
  SigmaConditionalSpec SigmaConditionalActual SigmaConditionalCorrectness
  SigmaJoint203Bridge SigmaAcceptanceLowerBound Gaussian76Spec
  Gaussian76Identification.
import RealOrder.

(* Each iteration makes a fresh independent 83/72/48-bit input and calls
   the actual extracted Jasmin attempt. The source is explicit; this is not
   a claim that a fixed concrete SHAKE seed supplies independent draws. *)
module GaussianRetryActual = {
  proc sample(p : BArray26.t) : int = {
    var r : int * bool;
    r <@ SigmaJoint203Experiment.sample(p);
    while (!r.`2) {
      r <@ SigmaJoint203Experiment.sample(p);
    }
    return r.`1;
  }
}.

module GaussianRetryObserved = {
  proc sample(p : BArray26.t) : int = {
    var r : int * bool;
    r <@ GaussianActualPair.sample(p);
    while (!r.`2) {
      r <@ GaussianActualPair.sample(p);
    }
    return r.`1;
  }
}.

lemma gr_actual_retry_observed :
  equiv [GaussianRetryActual.sample ~ GaussianRetryObserved.sample :
    ={p} ==> ={res}].
proof.
  proc; while (={p,r}).
  + call gr_actual_pair_equiv; skip; auto.
  call gr_actual_pair_equiv; skip; auto.
qed.

lemma gr_observed_retry_core :
  equiv [GaussianRetryObserved.sample ~ GaussianRetry.sample :
    d{2} = sc_actual_pair p{1} ==> ={res}].
proof.
  proc; inline GaussianActualPair.sample; wp.
  while (d{2} = sc_actual_pair p{1} /\ r{1} = r{2}).
  + by auto.
  by auto.
qed.

lemma gr_actual_output_identity (p : BArray26.t) :
  gr_output (sc_actual_pair p) = sc_actual_conditioned p.
proof.
  by rewrite /gr_output /sc_actual_conditioned /gr_accept /sc_accepted /sc_output.
qed.

lemma gr_actual_retry_law (p : BArray26.t) (event : int -> bool) &m :
  Pr[GaussianRetryActual.sample(p) @ &m : event res] =
    mu (sc_actual_conditioned p) event.
proof.
  have h1 : Pr[GaussianRetryActual.sample(p) @ &m : event res] =
    Pr[GaussianRetryObserved.sample(p) @ &m : event res] by
    byequiv gr_actual_retry_observed.
  have h2 : Pr[GaussianRetryObserved.sample(p) @ &m : event res] =
    Pr[GaussianRetry.sample(sc_actual_pair p) @ &m : event res] by
    byequiv gr_observed_retry_core.
  rewrite h1 h2 (gr_retry_law (sc_actual_pair p) event &m)
    1:(sc_actual_pair_ll p).
  + have h := gr_actual_acceptance_positive p &m.
    by move: h; rewrite /sc_accepted /gr_accept.
  by rewrite gr_actual_output_identity.
qed.

lemma gr_actual_retry_ll : islossless GaussianRetryActual.sample.
proof.
  bypr => &m _.
  rewrite (gr_actual_retry_law p{m} (fun _ => true) &m).
  have [h _] := g76_actual_gaussian_correct p{m} &m.
  exact h.
qed.

lemma gr_actual_retry_gaussian_event (p : BArray26.t) (event : int -> bool) &m :
  `|Pr[GaussianRetryActual.sample(p) @ &m : event res] - mu g76_rounded event|
    < 1%r / (2^39)%r.
proof.
  rewrite gr_actual_retry_law.
  exact (g76_actual_conditioned_event_error p event &m).
qed.

lemma gr_actual_retry_gaussian (p : BArray26.t) &m :
  Pr[GaussianRetryActual.sample(p) @ &m : true] = 1%r /\
  (forall event, Pr[GaussianRetryActual.sample(p) @ &m : event res] =
    mu (sc_actual_conditioned p) event) /\
  SDist.sdist (sc_actual_conditioned p) g76_rounded < 1%r / (2^39)%r.
proof.
  split; first by byphoare gr_actual_retry_ll.
  split; first by move=> event; exact (gr_actual_retry_law p event &m).
  exact (g76_actual_conditioned_sdist p &m).
qed.
