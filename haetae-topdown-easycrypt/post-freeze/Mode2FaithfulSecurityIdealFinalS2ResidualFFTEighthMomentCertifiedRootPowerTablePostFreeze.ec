require import AllCore IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23RootGeneratorCertificate
  KeygenM23RootTableRounding
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalClassProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.

import RField RealOrder.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalClassProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze.

(* This file reuses the proved integer certificate chain in
   KeygenM23RootTableRounding, extends its first 256 omega512 powers through
   the proved half-turn and 512-periodicity laws, and converts the scaled
   certificates into the center-radius intervals consumed by the exact P8
   bridge. It introduces no new numerical root data. *)

op scaled_rcert_interval
    (d : real) (q : KeygenM23RootTableRounding.rcert) : rinterval =
  (KeygenM23RootTableRounding.center q / d,
   KeygenM23RootTableRounding.radius q / d).

op ccert_re_interval
    (d : real) (q : KeygenM23RootTableRounding.ccert) : rinterval =
  scaled_rcert_interval d (KeygenM23RootTableRounding.real_cert q).

op ccert_im_interval
    (d : real) (q : KeygenM23RootTableRounding.ccert) : rinterval =
  scaled_rcert_interval d (KeygenM23RootTableRounding.imag_cert q).

op negate_rcert
    (q : KeygenM23RootTableRounding.rcert) :
    KeygenM23RootTableRounding.rcert =
  (- KeygenM23RootTableRounding.center q,
   KeygenM23RootTableRounding.radius q).

op negate_ccert
    (q : KeygenM23RootTableRounding.ccert) :
    KeygenM23RootTableRounding.ccert =
  (negate_rcert (KeygenM23RootTableRounding.real_cert q),
   negate_rcert (KeygenM23RootTableRounding.imag_cert q)).

lemma scaled_rcert_interval_valid d x q :
  0%r < d =>
  KeygenM23RootTableRounding.holds d x q =>
  interval_valid (scaled_rcert_interval d q).
proof.
move: q => [c r].
rewrite /scaled_rcert_interval
        /KeygenM23RootTableRounding.center
        /KeygenM23RootTableRounding.radius /=.
move=> hd hh.
have hr : 0%r <= r by
  exact (KeygenM23RootTableRounding.holds_radius_nonnegative d x c r hh).
rewrite /interval_valid /interval_radius /=.
apply divr_ge0; smt().
qed.

lemma scaled_rcert_interval_holds d x q :
  0%r < d =>
  KeygenM23RootTableRounding.holds d x q =>
  interval_holds (scaled_rcert_interval d q) x.
proof.
move: q => [c r].
rewrite /scaled_rcert_interval
        /KeygenM23RootTableRounding.center
        /KeygenM23RootTableRounding.radius /=.
move=> hd hh.
rewrite /interval_holds /interval_center /interval_radius /=.
have hd0 : d <> 0%r by smt().
have he : x - c / d = (d * x - c) / d.
+ field.
  exact hd0.
rewrite he normrM normrV.
have hdge : 0%r <= d by smt().
have hdabs : `|d| = d by rewrite ger0_norm 1:hdge.
rewrite hdabs.
apply ler_wpmul2r.
+ rewrite invr_ge0.
  exact hdge.
exact hh.
qed.

lemma cholds_to_center_radius_intervals d z q :
  0%r < d =>
  KeygenM23RootTableRounding.cholds d z q =>
  (interval_valid (ccert_re_interval d q) /\
   interval_holds (ccert_re_interval d q) (creal z)) /\
  (interval_valid (ccert_im_interval d q) /\
   interval_holds (ccert_im_interval d q) (cimag z)).
proof.
move=> hd [hre him].
split.
+ split.
  + exact (scaled_rcert_interval_valid d (creal z)
      (KeygenM23RootTableRounding.real_cert q) hd hre).
  exact (scaled_rcert_interval_holds d (creal z)
    (KeygenM23RootTableRounding.real_cert q) hd hre).
split.
+ exact (scaled_rcert_interval_valid d (cimag z)
    (KeygenM23RootTableRounding.imag_cert q) hd him).
exact (scaled_rcert_interval_holds d (cimag z)
  (KeygenM23RootTableRounding.imag_cert q) hd him).
qed.

lemma cholds_negate d z q :
  KeygenM23RootTableRounding.cholds d z q =>
  KeygenM23RootTableRounding.cholds d (cneg z) (negate_ccert q).
proof.
move: q => [[cr rr] [ci ri]].
rewrite /KeygenM23RootTableRounding.cholds
        /KeygenM23RootTableRounding.holds
        /KeygenM23RootTableRounding.real_cert
        /KeygenM23RootTableRounding.imag_cert
        /KeygenM23RootTableRounding.center
        /KeygenM23RootTableRounding.radius
        /negate_ccert /negate_rcert /=.
move=> [hre him].
rewrite creal_neg cimag_neg /=.
split.
+ have -> : d * - creal z - - cr = -(d * creal z - cr) by ring.
  rewrite normrN.
  exact hre.
have -> : d * - cimag z - - ci = -(d * cimag z - ci) by ring.
rewrite normrN.
exact him.
qed.

lemma omega512_pow512_mul q :
  cpow omega512 (512 * q) = cone.
proof.
rewrite C.exprM omega512_pow512 C.expr1z.
trivial.
qed.

lemma ideal_root_periodic512 e q :
  0 <= e =>
  0 <= q =>
  ideal_root (e + 512 * q) = ideal_root e.
proof.
move=> he hq.
rewrite /ideal_root C.exprD_nneg 1:he 1:/# omega512_pow512_mul.
exact (cmul1r (cpow omega512 e)).
qed.

lemma ideal_root_half_turn e :
  0 <= e =>
  ideal_root (e + 256) = cneg (ideal_root e).
proof.
move=> he.
rewrite /ideal_root C.exprD_nneg 1:he 1:// omega512_pow256 cmul_neg.
rewrite cmul1r.
trivial.
qed.

lemma ideal_root_mod512E e :
  0 <= e =>
  ideal_root e = ideal_root (e %% 512).
proof.
move=> he.
have hq : 0 <= e %/ 512 by rewrite divz_ge0.
have h512nz : 512 <> 0 by smt().
have hr : 0 <= e %% 512 by exact (modz_ge0 e 512 h512nz).
have heq : e = e %% 512 + 512 * (e %/ 512).
+ rewrite {1}(divz_eq e 512).
  ring.
have hp := ideal_root_periodic512 (e %% 512) (e %/ 512) hr hq.
rewrite -heq in hp.
exact hp.
qed.

lemma mod512_range e :
  (0 <= e %% 512) /\ (e %% 512 < 512).
proof.
have h512nz : 512 <> 0 by smt().
have h512pos : 0 < 512 by smt().
split.
+ exact (modz_ge0 e 512 h512nz).
exact (ltz_pmod e 512 h512pos).
qed.

op root_certificate_scale : real =
  KeygenM23RootGeneratorCertificate.certificate_scale%r.

op root_table_default_icert : KeygenM23RootTableRounding.icert =
  ((0, 0), (0, 0)).

op first_half_power_ccert (r : int) : KeygenM23RootTableRounding.ccert =
  KeygenM23RootTableRounding.ccert_of_icert
    (nth root_table_default_icert
      KeygenM23RootTableRounding.root_certificates r).

op omega512_power_ccert (r : int) : KeygenM23RootTableRounding.ccert =
  if r < 256 then first_half_power_ccert r
  else negate_ccert (first_half_power_ccert (r - 256)).

op ideal_root_power_ccert (e : int) : KeygenM23RootTableRounding.ccert =
  omega512_power_ccert (e %% 512).

op ideal_root_re_interval (e : int) : rinterval =
  ccert_re_interval root_certificate_scale (ideal_root_power_ccert e).

op ideal_root_im_interval (e : int) : rinterval =
  ccert_im_interval root_certificate_scale (ideal_root_power_ccert e).

lemma root_certificate_scale_gt0 :
  0%r < root_certificate_scale.
proof.
rewrite /root_certificate_scale
        /KeygenM23RootGeneratorCertificate.certificate_scale.
smt().
qed.

lemma first_half_power_ccert_sound r :
  0 <= r < 256 =>
  KeygenM23RootTableRounding.cholds
    root_certificate_scale (ideal_root r) (first_half_power_ccert r).
proof.
move=> hr.
rewrite /root_certificate_scale /first_half_power_ccert
        /root_table_default_icert.
exact (KeygenM23RootTableRounding.ideal_root_certificate r hr).
qed.

lemma omega512_power_ccert_sound r :
  0 <= r < 512 =>
  KeygenM23RootTableRounding.cholds
    root_certificate_scale (ideal_root r) (omega512_power_ccert r).
proof.
move=> hr.
rewrite /omega512_power_ccert.
case (r < 256) => hrhalf.
+ have hrfirst : 0 <= r < 256 by smt().
  exact (first_half_power_ccert_sound r hrfirst).
have hidx : 0 <= r - 256 < 256 by smt().
have hidx0 : 0 <= r - 256 by smt().
have hbase := first_half_power_ccert_sound (r - 256) hidx.
have hturn := ideal_root_half_turn (r - 256) hidx0.
have hleft : ideal_root r = ideal_root (r - 256 + 256).
+ congr; ring.
have hroot : ideal_root r = cneg (ideal_root (r - 256)).
+ rewrite hleft.
  exact hturn.
rewrite hroot.
exact (cholds_negate root_certificate_scale
  (ideal_root (r - 256)) (first_half_power_ccert (r - 256)) hbase).
qed.

lemma ideal_root_power_ccert_sound e :
  0 <= e =>
  KeygenM23RootTableRounding.cholds
    root_certificate_scale (ideal_root e) (ideal_root_power_ccert e).
proof.
move=> he.
have [hr0 hrlt] := mod512_range e.
have hrrange : 0 <= e %% 512 < 512 by smt().
have hcert := omega512_power_ccert_sound (e %% 512) hrrange.
have hroot := ideal_root_mod512E e he.
rewrite /ideal_root_power_ccert.
rewrite hroot.
exact hcert.
qed.

lemma ideal_root_intervals_sound e :
  0 <= e =>
  (interval_valid (ideal_root_re_interval e) /\
   interval_holds (ideal_root_re_interval e) (creal (ideal_root e))) /\
  (interval_valid (ideal_root_im_interval e) /\
   interval_holds (ideal_root_im_interval e) (cimag (ideal_root e))).
proof.
move=> he.
have hcert := ideal_root_power_ccert_sound e he.
rewrite /ideal_root_re_interval /ideal_root_im_interval.
exact (cholds_to_center_radius_intervals
  root_certificate_scale (ideal_root e) (ideal_root_power_ccert e)
  root_certificate_scale_gt0 hcert).
qed.

op odd_root_power_exponent (k j : int) : int =
  (2 * k + 1) * j.

op certified_odd_root_re_interval (k j : int) : rinterval =
  ideal_root_re_interval (odd_root_power_exponent k j).

op certified_odd_root_im_interval (k j : int) : rinterval =
  ideal_root_im_interval (odd_root_power_exponent k j).

op certified_class_re_profile8_interval
    (trace : int -> int) (k n : int) : rinterval =
  root_class_profile8_interval trace (certified_odd_root_re_interval k) n.

op certified_class_im_profile8_interval
    (trace : int -> int) (k n : int) : rinterval =
  root_class_profile8_interval trace (certified_odd_root_im_interval k) n.

lemma odd_root_power_as_ideal_root k j :
  cpow (odd_root k) j = ideal_root (odd_root_power_exponent k j).
proof.
rewrite /odd_root_power_exponent odd_rootE /ideal_root C.exprM.
trivial.
qed.

lemma certified_odd_root_power_intervals_sound k j :
  0 <= k =>
  0 <= j =>
  (interval_valid (certified_odd_root_re_interval k j) /\
   interval_holds (certified_odd_root_re_interval k j)
     (creal (cpow (odd_root k) j))) /\
  (interval_valid (certified_odd_root_im_interval k j) /\
   interval_holds (certified_odd_root_im_interval k j)
     (cimag (cpow (odd_root k) j))).
proof.
move=> hk hj.
have he : 0 <= odd_root_power_exponent k j by
  rewrite /odd_root_power_exponent; smt().
have hs := ideal_root_intervals_sound (odd_root_power_exponent k j) he.
have hroot := odd_root_power_as_ideal_root k j.
rewrite /certified_odd_root_re_interval
        /certified_odd_root_im_interval.
rewrite hroot.
exact hs.
qed.

lemma certified_odd_root_interval_certificates k n :
  0 <= k =>
  odd_root_re_interval_certificate
    (certified_odd_root_re_interval k) k n /\
  odd_root_im_interval_certificate
    (certified_odd_root_im_interval k) k n.
proof.
move=> hk.
split.
+ rewrite /odd_root_re_interval_certificate /root_interval_certificate.
  move=> j hj.
  have hj0 : 0 <= j by smt().
  have [[hrev hreh] _] :=
    certified_odd_root_power_intervals_sound k j hk hj0.
  split; first exact hrev.
  exact hreh.
rewrite /odd_root_im_interval_certificate /root_interval_certificate.
move=> j hj.
have hj0 : 0 <= j by smt().
have [_ [himv himh]] :=
  certified_odd_root_power_intervals_sound k j hk hj0.
split; first exact himv.
exact himh.
qed.

lemma ideal_final_s2_row_residual_profile8_certified_root_table_sound
    pre_bp avec row k n :
  0 <= k =>
  (interval_valid
      (certified_class_re_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) k n) /\
   interval_holds
      (certified_class_re_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) k n)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n)) /\
  (interval_valid
      (certified_class_im_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) k n) /\
   interval_holds
      (certified_class_im_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) k n)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n)).
proof.
move=> hk.
have [hre_cert him_cert] := certified_odd_root_interval_certificates k n hk.
rewrite /certified_class_re_profile8_interval
        /certified_class_im_profile8_interval.
exact (ideal_final_s2_row_residual_profile8_interval_sound
  pre_bp avec row k n
  (certified_odd_root_re_interval k)
  (certified_odd_root_im_interval k)
  hre_cert him_cert).
qed.

lemma ideal_final_s2_row_residual_profile8_certified_root_table_abs_upper
    pre_bp avec row k n :
  0 <= k =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n| <=
    interval_abs_upper
      (certified_class_re_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) k n) /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n| <=
    interval_abs_upper
      (certified_class_im_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) k n).
proof.
move=> hk.
have [hre_cert him_cert] := certified_odd_root_interval_certificates k n hk.
rewrite /certified_class_re_profile8_interval
        /certified_class_im_profile8_interval.
exact (ideal_final_s2_row_residual_profile8_interval_abs_upper
  pre_bp avec row k n
  (certified_odd_root_re_interval k)
  (certified_odd_root_im_interval k)
  hre_cert him_cert).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentCertifiedRootPowerTablePostFreeze.
