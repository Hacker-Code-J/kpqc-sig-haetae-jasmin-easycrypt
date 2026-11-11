require import AllCore List Distr DList DProd DBool SDist StdOrder.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidDistribution GaussianIidNormalization.
require import GaussianUniformBytes GaussianSignBits.
require import GaussianSignIndependence GaussianSignedVector GaussianSignedTarget.
import RealOrder.

(* This projection exposes the already proved magnitude law as a program
   equivalence, so independent sign draws can be composed with it. *)
module GaussianMagnitudeObservation = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : int list = {
    var output : gib_result;
    output <@ GaussianIidBuffer.sample(rp,signsp,sqsump,n,sample_offset,sign_offset);
    return gib_magnitudes output sample_offset;
  }
}.

module GaussianMagnitudeDraw = {
  proc sample() : int list = {
    var values : int list;
    values <$ gid_target;
    return values;
  }
}.

lemma gsc_magnitude_phoare initial initial_signs initial_squares n0 offset0 signoff0
    (event : int list -> bool) :
  gib_bounds n0 offset0 signoff0 =>
  phoare [GaussianIidBuffer.sample :
    rp=initial /\ signsp=initial_signs /\ sqsump=initial_squares /\
    n=n0 /\ sample_offset=offset0 /\ sign_offset=signoff0
    ==> event (gib_magnitudes res offset0)] = (mu gid_target event).
proof.
  move=> hb; bypr => &m [-> [-> [-> [-> [-> ->]]]]].
  exact (gii_actual_joint_law _ _ _ _ _ _ event &m hb).
qed.

module GaussianIndependentSigns = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : bool list * int list = {
    var values : int list;
    var bytes : W8.t list;
    values <@ GaussianMagnitudeObservation.sample(rp,signsp,sqsump,n,sample_offset,sign_offset);
    bytes <$ gbc_bytes 32;
    return (gsb_bits bytes,values);
  }
}.

module GaussianJointBytes = {
  proc sample() : bool list * int list = {
    var values : int list;
    var bytes : W8.t list;
    var output : bool list * int list;
    values <@ GaussianMagnitudeDraw.sample();
    bytes <$ gbc_bytes 32;
    output <- (gsb_bits bytes,values);
    return output;
  }
}.

module GaussianJointDraw = {
  proc sample() : bool list * int list = {
    var output : bool list * int list;
    output <$ dlist dbool 256 `*` gid_target;
    return output;
  }
}.

lemma gsc_magnitude_law initial initial_signs initial_squares n0 offset signoff
    (event : int list -> bool) &m :
  gib_bounds n0 offset signoff =>
  Pr[GaussianMagnitudeObservation.sample(initial,initial_signs,initial_squares,n0,offset,signoff)
    @ &m : event res] = (mu gid_target event).
proof.
  move=> hb.
  byphoare (_ : rp=initial /\ signsp=initial_signs /\ sqsump=initial_squares /\
    n=n0 /\ sample_offset=offset /\ sign_offset=signoff ==> event res) => //.
  proc; call (gsc_magnitude_phoare initial initial_signs initial_squares n0 offset signoff event hb).
  skip; auto => />.
qed.

lemma gsc_magnitude_draw :
  equiv [GaussianMagnitudeObservation.sample ~ GaussianMagnitudeDraw.sample :
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 values hb.
  rewrite (gsc_magnitude_law _ _ _ _ _ _ (fun xs => xs=values) &1 hb).
  byphoare (_ : true ==> res=values) => //.
  proc; rnd; skip; auto => />.
qed.

lemma gsc_independent_bytes :
  equiv [GaussianIndependentSigns.sample ~ GaussianJointBytes.sample :
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}].
proof.
  proc; wp; rnd; call gsc_magnitude_draw; skip; auto => />.
qed.

lemma gsc_joint_bytes_draw :
  equiv [GaussianJointBytes.sample ~ GaussianJointDraw.sample : true ==> ={res}].
proof.
  proc; inline GaussianMagnitudeDraw.sample.
  rnd : *0 *0; auto => />.
  have he : dlet gid_target (fun values =>
      dmap (gbc_bytes 32) (fun bytes => (gsb_bits bytes,values))) =
      dlist dbool 256 `*` gid_target.
  + rewrite -(dmap_dprodE_swap (gbc_bytes 32) gid_target
      (fun bv : W8.t list * int list => (gsb_bits bv.`1,bv.`2))).
    by rewrite -dmap_dprodL gsb_uniform256.
  by rewrite dmap_id he.
qed.

lemma gsc_independent_joint_law initial initial_signs initial_squares n offset signoff
    (event : bool list * int list -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIndependentSigns.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event res] = mu (dlist dbool 256 `*` gid_target) event.
proof.
  move=> hb.
  have h1 : Pr[GaussianIndependentSigns.sample(initial,initial_signs,initial_squares,n,offset,signoff)
      @ &m : event res] = Pr[GaussianJointBytes.sample() @ &m : event res] by
    byequiv gsc_independent_bytes.
  have h2 : Pr[GaussianJointBytes.sample() @ &m : event res] =
      Pr[GaussianJointDraw.sample() @ &m : event res] by
    byequiv gsc_joint_bytes_draw.
  rewrite h1 h2.
  byphoare (_ : true ==> event res) => //.
  proc; rnd; skip; auto.
qed.

lemma gsc_redraw_independent (offset0 signoff0 : int) :
  equiv [GaussianIidSignRedraw.sample ~ GaussianIndependentSigns.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
    sample_offset{1}=offset0 /\ sign_offset{1}=signoff0 /\
    gib_bounds n{1} offset0 signoff0
    ==> (gsb_result_bits res{1} signoff0,gib_magnitudes res{1} offset0) = res{2}].
proof.
  proc; inline {2} GaussianMagnitudeObservation.sample.
  wp; rnd; wp; call (_ : true).
  + by sim.
  auto => />.
  move=> &2 _ _ _ hsign hcap result bytes hbytes.
  apply gsb_signs_decode32 => //.
  exact (supp_dlist_size W8.dword 32 bytes _ hbytes); trivial.
qed.

lemma gsc_redraw_joint_law initial initial_signs initial_squares n offset signoff
    (event : bool list * int list -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidSignRedraw.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gsb_result_bits res signoff,gib_magnitudes res offset)] =
    mu (dlist dbool 256 `*` gid_target) event.
proof.
  move=> hb.
  have he : Pr[GaussianIidSignRedraw.sample(initial,initial_signs,initial_squares,n,offset,signoff)
      @ &m : event (gsb_result_bits res signoff,gib_magnitudes res offset)] =
    Pr[GaussianIndependentSigns.sample(initial,initial_signs,initial_squares,n,offset,signoff)
      @ &m : event res] by byequiv (gsc_redraw_independent offset signoff).
  rewrite he; exact (gsc_independent_joint_law _ _ _ _ _ _ event &m hb).
qed.

(* Signed observations are mathematical integers, not signed64 casts. *)
op gsc_signed_result (result : gib_result) (offset signoff : int) : int list =
  gsv_apply (gsb_result_bits result signoff) (gib_magnitudes result offset).

lemma gsc_signed_size result offset signoff :
  size (gsc_signed_result result offset signoff) = 256.
proof.
  by rewrite /gsc_signed_result gsv_apply_size gsb_result_bits_size
    /gib_magnitudes size_map size_iota /=.
qed.

lemma gsc_signed_nth result offset signoff i : 0 <= i < 256 =>
  nth 0 (gsc_signed_result result offset signoff) i =
    if nth false (gsb_result_bits result signoff) i
    then -W64.to_uint (BArray32768.get64 result.`1 (offset+i))
    else W64.to_uint (BArray32768.get64 result.`1 (offset+i)).
proof.
  move=> hi.
  have hm : nth 0 (gib_magnitudes result offset) i =
      W64.to_uint (BArray32768.get64 result.`1 (offset+i)).
  + by rewrite /gib_magnitudes (nth_map 0) 1:size_iota 1:/# nth_iota 1:hi /=.
  rewrite /gsc_signed_result gsv_apply_nth.
  + by rewrite gsb_result_bits_size /gib_magnitudes size_map size_iota /=.
  + by rewrite /gib_magnitudes size_map size_iota /=.
  by rewrite /gst_apply hm.
qed.

lemma gsc_actual_joint_law initial initial_signs initial_squares n offset signoff
    (event : bool list * int list -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gsb_result_bits res signoff,gib_magnitudes res offset)] =
    mu (dlist dbool 256 `*` gid_target) event.
proof.
  move=> hb.
  have he : Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
      @ &m : event (gsb_result_bits res signoff,gib_magnitudes res offset)] =
    Pr[GaussianIidSignRedraw.sample(initial,initial_signs,initial_squares,n,offset,signoff)
      @ &m : event (gsb_result_bits res signoff,gib_magnitudes res offset)] by
    byequiv gsi_actual_redraw.
  rewrite he; exact (gsc_redraw_joint_law _ _ _ _ _ _ event &m hb).
qed.

lemma gsc_actual_signed_law initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gsc_signed_result res offset signoff)] = mu gsv_actual event.
proof.
  move=> hb; rewrite /gsc_signed_result
    (gsc_actual_joint_law _ _ _ _ _ _
      (fun bm : bool list * int list => event (gsv_apply bm.`1 bm.`2)) &m hb).
  by rewrite /gsv_actual /gsv_distribution dmapE.
qed.

lemma gsc_actual_gaussian_event initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  gib_bounds n offset signoff =>
  `|Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
      @ &m : event (gsc_signed_result res offset signoff)] - mu (dlist gst_target 256) event|
    < 1%r/(2^31)%r.
proof.
  move=> hb; rewrite (gsc_actual_signed_law _ _ _ _ _ _ event &m hb).
  exact (gsv_actual_gaussian_event event &m).
qed.

lemma gsc_actual_correct initial initial_signs initial_squares n offset signoff &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : true] = 1%r /\
  (forall event, Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gsc_signed_result res offset signoff)] = mu gsv_actual event) /\
  sdist gsv_actual (dlist gst_target 256) < 1%r/(2^31)%r.
proof.
  move=> hb; split; first exact (gii_actual_terminates _ _ _ _ _ _ &m hb).
  split; first by move=> event; exact (gsc_actual_signed_law _ _ _ _ _ _ event &m hb).
  exact (gsv_actual_gaussian &m).
qed.
