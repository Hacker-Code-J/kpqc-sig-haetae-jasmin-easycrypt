require import AllCore Distr StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 GaussianAcceptanceProduction GaussianAttemptExpectation
  GaussianRetryAttempt SigmaJoint203Bridge SigmaConditionalSpec.
import RealOrder.

lemma gap_hyperball_attempt_equiv :
  equiv [GaussianAcceptanceProduction.hyperball ~ SigmaJoint203Experiment.sample :
    true ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 r.
  by rewrite (gap_hyperball_pair_law p{2} (pred1 r) &1)
    (gr_actual_pair_law p{2} (pred1 r) &2).
qed.

lemma gap_signer_attempt_equiv :
  equiv [GaussianAcceptanceProduction.signer ~ SigmaJoint203Experiment.sample :
    true ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 r.
  by rewrite (gap_signer_pair_law p{2} (pred1 r) &1)
    (gr_actual_pair_law p{2} (pred1 r) &2).
qed.

(* An observational mathematical counter is added to independent calls of
   the production candidate helper. The C/Jasmin implementation is unchanged. *)
module GaussianProductionCounted = {
  proc hyperball() : int * int = {
    var r : int * bool;
    var count : int;
    count <- 1;
    r <@ GaussianAcceptanceProduction.hyperball();
    while (!r.`2) {
      count <- count+1;
      r <@ GaussianAcceptanceProduction.hyperball();
    }
    return (r.`1,count);
  }
  proc signer() : int * int = {
    var r : int * bool;
    var count : int;
    count <- 1;
    r <@ GaussianAcceptanceProduction.signer();
    while (!r.`2) {
      count <- count+1;
      r <@ GaussianAcceptanceProduction.signer();
    }
    return (r.`1,count);
  }
}.

lemma gap_hyperball_counted_equiv :
  equiv [GaussianProductionCounted.hyperball ~ GaussianCountedActual.sample :
    true ==> ={res}].
proof.
  proc; while (r{1}=r{2} /\ count{1}=count{2}).
  + call gap_hyperball_attempt_equiv; auto.
  call gap_hyperball_attempt_equiv; auto.
qed.

lemma gap_signer_counted_equiv :
  equiv [GaussianProductionCounted.signer ~ GaussianCountedActual.sample :
    true ==> ={res}].
proof.
  proc; while (r{1}=r{2} /\ count{1}=count{2}).
  + call gap_signer_attempt_equiv; auto.
  call gap_signer_attempt_equiv; auto.
qed.

lemma gap_hyperball_count_law (p : BArray26.t) (event : int -> bool) &m :
  Pr[GaussianProductionCounted.hyperball() @ &m : event res.`2] =
    mu (gae_actual_count_distribution p) event.
proof.
  rewrite -(gae_actual_count_law p event &m).
  by byequiv gap_hyperball_counted_equiv.
qed.

lemma gap_signer_count_law (p : BArray26.t) (event : int -> bool) &m :
  Pr[GaussianProductionCounted.signer() @ &m : event res.`2] =
    mu (gae_actual_count_distribution p) event.
proof.
  rewrite -(gae_actual_count_law p event &m).
  by byequiv gap_signer_counted_equiv.
qed.

lemma gap_hyperball_counted_ll : islossless GaussianProductionCounted.hyperball.
proof. by conseq gap_hyperball_counted_equiv gae_actual_counted_ll => /#. qed.

lemma gap_signer_counted_ll : islossless GaussianProductionCounted.signer.
proof. by conseq gap_signer_counted_equiv gae_actual_counted_ll => /#. qed.

(* The expectation belongs to the proved distribution of the operational
   counter, and integrability is explicit rather than implicit in E. *)
lemma gap_hyperball_count_statistics (p : BArray26.t) &m :
  (forall event, Pr[GaussianProductionCounted.hyperball() @ &m : event res.`2] =
    mu (gae_actual_count_distribution p) event) /\
  hasE (gae_actual_count_distribution p) (fun count => count%r) /\
  E (gae_actual_count_distribution p) (fun count => count%r) =
    1%r/mu (sc_actual_pair p) sc_accepted /\
  E (gae_actual_count_distribution p) (fun count => count%r)<20%r/19%r.
proof.
  split; first by move=> event; exact (gap_hyperball_count_law p event &m).
  split; first exact (gae_actual_count_hasE p).
  split; [exact (gae_actual_expected_count p) | exact (gae_actual_expected_count_bound p)].
qed.

lemma gap_signer_count_statistics (p : BArray26.t) &m :
  (forall event, Pr[GaussianProductionCounted.signer() @ &m : event res.`2] =
    mu (gae_actual_count_distribution p) event) /\
  hasE (gae_actual_count_distribution p) (fun count => count%r) /\
  E (gae_actual_count_distribution p) (fun count => count%r) =
    1%r/mu (sc_actual_pair p) sc_accepted /\
  E (gae_actual_count_distribution p) (fun count => count%r)<20%r/19%r.
proof.
  split; first by move=> event; exact (gap_signer_count_law p event &m).
  split; first exact (gae_actual_count_hasE p).
  split; [exact (gae_actual_expected_count p) | exact (gae_actual_expected_count_bound p)].
qed.
