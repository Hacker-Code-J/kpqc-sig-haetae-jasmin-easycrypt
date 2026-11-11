require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HardenedHyperballTarget CheckedScaleSpec CheckedScalarCorrectness
  CheckedAcceptanceCorrectness HyperballFixedPointSpec HyperballScaleSpec
  HyperballScaleCorrectness GaussianStreamCorrectness.
import SLH64 HyperballScaleSpec HyperballScaleCorrectness GaussianStreamCorrectness.

module HCV = HardenedHyperballTarget.M.

op [opaque] hcv_fit (samples : BArray32768.t) (scale : BArray16.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    hcs_wide_magnitude (BArray32768.get64 samples i) (hb_load scale) <= 2147483647.

op [opaque] hcv_mask (samples : BArray32768.t) (scale : BArray16.t) (n : int) : W64.t =
  if hcv_fit samples scale n then W64.zero else W64.onew.

lemma hcv_fit0 samples scale : hcv_fit samples scale 0.
proof. rewrite /hcv_fit; smt(). qed.

lemma hcv_fit_step samples scale n : 0 <= n =>
  hcv_fit samples scale (n+1) =
    (hcv_fit samples scale n /\
      hcs_wide_magnitude (BArray32768.get64 samples n) (hb_load scale) <= 2147483647).
proof. rewrite /hcv_fit; smt(). qed.

lemma hcv_mask0 samples scale : hcv_mask samples scale 0 = W64.zero.
proof. by rewrite /hcv_mask hcv_fit0. qed.

lemma hcv_mask_step samples scale n : 0 <= n =>
  hcv_mask samples scale n `|` hcs_badmask (BArray32768.get64 samples n) (hb_load scale) =
    hcv_mask samples scale (n+1).
proof.
  move=> hn; rewrite /hcv_mask (hcv_fit_step samples scale n hn) /hcs_badmask.
  case (hcv_fit samples scale n);
    case (hcs_wide_magnitude (BArray32768.get64 samples n) (hb_load scale) <= 2147483647);
    by rewrite /= ?W64.orw0 ?W64.or0w ?W64.orw1 ?W64.or1w.
qed.

lemma hcv_mask_zero samples scale n :
  (hcv_mask samples scale n = W64.zero) = hcv_fit samples scale n.
proof.
  have hn : W64.onew <> W64.zero by
    rewrite W64.to_uint_eq W64.to_uint_onew W64.to_uint0.
  rewrite /hcv_mask; case (hcv_fit samples scale n); smt().
qed.

lemma hcv_mask_cases samples scale n :
  hcv_mask samples scale n = W64.zero \/ hcv_mask samples scale n = W64.onew.
proof. rewrite /hcv_mask; case (hcv_fit samples scale n); smt(). qed.

(* The same mask crosses the boundary between both output arrays. *)
lemma hcv_scale_mask_correct (samples0 : BArray32768.t) (scale0 : BArray16.t) (l t : int) :
  hoare [HCV._hb_checked_scale_samples :
    samplesp=samples0 /\ scalep=scale0 /\
    counts=W64.of_int (t*4294967296+l) /\ hb_scale_bounds l t ==>
    res.`3=hcv_mask samples0 scale0 t].
proof.
  proc.
  while (samplesp=samples0 /\ scalep=scale0 /\ total=W64.of_int t /\
    hb_scale_bounds l t /\ 0 <= W64.to_uint i <= t /\
    bad=hcv_mask samples0 scale0 (W64.to_uint i)).
  + wp; ecall (hcs_pointer_correct sample scalep sign8).
    wp; call (_ : true ==> true); first by conseq.
    auto => /> &hr hl0 hlmax hk0 hkmax ht hi0 hit hguard.
    rewrite /protect_64 /protect_ptr /hcs_scale_sample /hcs_scalar /=.
    rewrite W64.ultE W64.to_uint_small 1:/# in hguard.
    rewrite hb_scale_counter_next 1:/#.
    have hs := hcv_mask_step samples0 scale0 (W64.to_uint i{hr}) hi0.
    smt().
  wp.
  while (samplesp=samples0 /\ scalep=scale0 /\ lcount=W64.of_int l /\ total=W64.of_int t /\
    hb_scale_bounds l t /\ 0 <= W64.to_uint i <= l /\
    bad=hcv_mask samples0 scale0 (W64.to_uint i)).
  + wp; ecall (hcs_pointer_correct sample scalep sign8).
    wp; call (_ : true ==> true); first by conseq.
    auto => /> &hr hl0 hlmax hk0 hkmax ht hi0 hil hguard.
    rewrite /protect_64 /protect_ptr /hcs_scale_sample /hcs_scalar /=.
    rewrite W64.ultE W64.to_uint_small 1:/# in hguard.
    rewrite hb_scale_counter_next 1:/#.
    have hs := hcv_mask_step samples0 scale0 (W64.to_uint i{hr}) hi0.
    smt().
  auto => /> hl0 hlmax hk0 hkmax ht.
  have hd : hb_scale_bounds l t by rewrite /hb_scale_bounds; smt().
  rewrite /protect_ptr /protect_64 /W64.(`>>`) W8.of_uintK /=.
  rewrite (hb_counts_low l t hd) (hb_counts_high l t hd) hcv_mask0.
  split; first smt().
  move=> i hdone hi0 hil.
  have hi : W64.to_uint i=l by
    move: hdone; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
  rewrite hi.
  split; first smt().
  move=> i0 hdone0 hi00 hi0t.
  have hit : W64.to_uint i0=t by
    move: hdone0; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
  by rewrite hit.
qed.

lemma hcv_scale_mask_total samples scale l t :
  phoare [HCV._hb_checked_scale_samples :
    samplesp=samples /\ scalep=scale /\
    counts=W64.of_int (t*4294967296+l) /\ hb_scale_bounds l t ==>
    res.`3=hcv_mask samples scale t] = 1%r.
proof. by conseq hca_scale_samples_ll (hcv_scale_mask_correct samples scale l t). qed.

lemma hcv_scale_fit_total samples scale l t :
  phoare [HCV._hb_checked_scale_samples :
    samplesp=samples /\ scalep=scale /\
    counts=W64.of_int (t*4294967296+l) /\ hb_scale_bounds l t ==>
    (res.`3=W64.zero) = hcv_fit samples scale t /\
    (res.`3=W64.zero \/ res.`3=W64.onew)] = 1%r.
proof.
  conseq hca_scale_samples_ll (hcv_scale_mask_correct samples scale l t) => //.
  move=> &hr hpre result.
  have hz := hcv_mask_zero samples scale t.
  have hc := hcv_mask_cases samples scale t.
  smt().
qed.

lemma hcv_finish_fit samples scale n overflow compare :
  hca_finish (hcv_mask samples scale n) overflow compare = W64.one => hcv_fit samples scale n.
proof.
  rewrite /hcv_mask; case (hcv_fit samples scale n) => hf //=.
  by rewrite hca_finish_bit W64.onewE /= W64.to_uint_eq W64.to_uint0 W64.to_uint1.
qed.

lemma hcv_phase_fit_correct (samples0 : BArray32768.t) (scale0 : BArray16.t) (l t : int) :
  hoare [HCV._hb_checked_scale_and_check_values :
    samplesp=samples0 /\ scalep=scale0 /\ lcount=W64.of_int l /\ total=W64.of_int t /\
    hb_scale_bounds l t ==> res.`3=W64.one => hcv_fit samples0 scale0 t].
proof.
  proc; wp; call (_ : true ==> true); first by conseq.
  wp; ecall (hcv_scale_mask_correct samples0 scale0 l t).
  auto => />; rewrite /protect_64 /protect_ptr /W64.(`<<`) W8.of_uintK /=.
  move=> &hr hl0 hlmax hk0 hkmax ht.
  rewrite gs_pack_counts_word 1:/# /=.
  move=> result hmask result0.
  rewrite hca_final_word hmask.
  apply hcv_finish_fit.
qed.

lemma hcv_phase_fit_total samples scale l t :
  phoare [HCV._hb_checked_scale_and_check_values :
    samplesp=samples /\ scalep=scale /\ lcount=W64.of_int l /\ total=W64.of_int t /\
    hb_scale_bounds l t ==> res.`3=W64.one => hcv_fit samples scale t] = 1%r.
proof. by conseq hca_scale_and_check_ll (hcv_phase_fit_correct samples scale l t). qed.
