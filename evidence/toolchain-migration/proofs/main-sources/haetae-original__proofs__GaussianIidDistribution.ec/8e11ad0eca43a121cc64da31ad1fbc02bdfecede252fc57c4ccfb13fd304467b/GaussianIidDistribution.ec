require import AllCore List Distr DList SDist StdOrder.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianIidNormalization
  GaussianIidEventLaw GaussianIidTermination GaussianIidKernel GaussianRetryCore
  GaussianRetryActual SigmaConditionalSpec Gaussian76Spec Gaussian76Identification
  GaussianBatchDistance.
import RealOrder.

(* The controller below calls the actual sign-copy, carry and finite
   Gaussian consumer. Its randomness is the explicit iid byte source. *)
lemma gii_actual_functional_law initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)] =
  Pr[GaussianIidBufferFunctional.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)].
proof. move=> hb; by byequiv gib_actual_functional. qed.

lemma gii_actual_uniform_law initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)] =
  Pr[GaussianIidBufferUniform.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)].
proof.
  move=> hb; rewrite (gii_actual_functional_law _ _ _ _ _ _ event &m hb).
  exact (gid_functional_uniform_law _ _ _ _ _ _ event &m).
qed.

lemma gii_actual_terminates initial initial_signs initial_squares n offset signoff &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : true] = 1%r.
proof.
  move=> hb.
  have he := gii_actual_functional_law initial initial_signs initial_squares
    n offset signoff (fun _ => true) &m hb.
  rewrite /= he.
  by byphoare (git_functional_total initial initial_signs initial_squares n offset signoff).
qed.

lemma gii_actual_total
    (initial : BArray32768.t) (initial_signs : BArray512.t) (initial_squares : BArray16.t)
    (n0 offset0 signoff0 : int) :
  phoare [GaussianIidBuffer.sample :
    rp=initial /\ signsp=initial_signs /\ sqsump=initial_squares /\
    n=n0 /\ sample_offset=offset0 /\ sign_offset=signoff0 /\
    gib_bounds n0 offset0 signoff0 ==> true] = 1%r.
proof.
  bypr => &m [-> [-> [-> [-> [-> [-> hb]]]]]].
  exact (gii_actual_terminates initial initial_signs initial_squares n0 offset0 signoff0 &m hb).
qed.

lemma gii_actual_lossless :
  phoare [GaussianIidBuffer.sample : gib_bounds n sample_offset sign_offset ==> true] = 1%r.
proof.
  bypr => &m hb.
  exact (gii_actual_terminates rp{m} signsp{m} sqsump{m} n{m} sample_offset{m} sign_offset{m} &m hb).
qed.

lemma gii_target_ll : is_lossless gid_target.
proof. rewrite /gid_target; apply dlist_ll; exact (gr_output_ll gik_pairs gik_acceptance_positive). qed.

lemma gii_actual_event_upper initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)] <= mu gid_target event.
proof.
  move=> hb; rewrite (gii_actual_uniform_law _ _ _ _ _ _ event &m hb).
  exact (gie_uniform_event_upper initial initial_signs initial_squares n offset signoff event &m hb).
qed.

(* Two event upper bounds become an exact distribution law only after
   independent probability-one termination has been established. *)
lemma gii_actual_joint_law initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)] = mu gid_target event.
proof.
  move=> hb.
  have hu := gii_actual_event_upper initial initial_signs initial_squares n offset signoff event &m hb.
  have hc := gii_actual_event_upper initial initial_signs initial_squares n offset signoff (predC event) &m hb.
  have hl := gii_actual_terminates initial initial_signs initial_squares n offset signoff &m hb.
  move: hc; rewrite /predC Pr [mu_not] hl mu_not gii_target_ll => hc.
  smt().
qed.

lemma gii_target_conditioned (p : BArray26.t) :
  gid_target = dlist (sc_actual_conditioned p) 256.
proof. by rewrite /gid_target (gik_pairs_law p) gr_actual_output_identity. qed.

lemma gii_target_gaussian &m :
  sdist gid_target (dlist g76_rounded 256) < 1%r/(2^31)%r.
proof.
  rewrite (gii_target_conditioned witness).
  exact (gb_batch_256_2m39 _ _ (g76_actual_conditioned_sdist witness &m)).
qed.

lemma gii_actual_gaussian_event initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  gib_bounds n offset signoff =>
  `|Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
      @ &m : event (gib_magnitudes res offset)] - mu (dlist g76_rounded 256) event|
    < 1%r/(2^31)%r.
proof.
  move=> hb; rewrite (gii_actual_joint_law _ _ _ _ _ _ event &m hb).
  exact (ler_lt_trans _ _ _ (sdist_upper_bound _ _ event) (gii_target_gaussian &m)).
qed.

lemma gii_actual_correct initial initial_signs initial_squares n offset signoff &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : true] = 1%r /\
  (forall event, Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)] = mu gid_target event) /\
  sdist gid_target (dlist g76_rounded 256) < 1%r/(2^31)%r.
proof.
  move=> hb; split; first exact (gii_actual_terminates _ _ _ _ _ _ &m hb).
  split; first by move=> event; exact (gii_actual_joint_law _ _ _ _ _ _ event &m hb).
  exact (gii_target_gaussian &m).
qed.
