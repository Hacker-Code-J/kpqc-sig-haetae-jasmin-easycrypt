require import AllCore IntDiv List Distr DInterval.
from Jasmin require import JModel_x86.
require import BArray26 SigmaSpec SigmaRawSpec SigmaRoundingCorrectness
  SigmaNoise72Bridge CDTDistributionSpec CDTDistributionBridge.

(* The first eleven bytes hold an unsigned 83-bit CDT input.  The remaining
   fifteen bytes retain the rejection and 72-bit noise inputs unchanged. *)
op [opaque] sj_cdt83_patch (p : BArray26.t) (u : int) : BArray26.t =
  BArray26.init (fun i =>
    if 0 <= i < 8 then W64.of_int u \bits8 i
    else if 8 <= i < 11 then W64.of_int (u %/ 18446744073709551616) \bits8 (i-8)
    else BArray26.get8 p i).

lemma sj_cdt83_patch_byte p u i : 0 <= i < 26 =>
  BArray26.get8 (sj_cdt83_patch p u) i =
    if 0 <= i < 8 then W64.of_int u \bits8 i
    else if 8 <= i < 11 then W64.of_int (u %/ 18446744073709551616) \bits8 (i-8)
    else BArray26.get8 p i.
proof. by move=> hi; rewrite /sj_cdt83_patch BArray26.initiE. qed.

lemma sj_cdt83_patch_outside p u i : 11 <= i < 26 =>
  BArray26.get8 (sj_cdt83_patch p u) i = BArray26.get8 p i.
proof. move=> hi; rewrite sj_cdt83_patch_byte 1:/#; smt(). qed.

lemma sj_cdt83_assemble8 (w : W64.t) :
  (((((((zeroextu64 (w \bits8 0) `|` (zeroextu64 (w \bits8 1) `<<<` 8)) `|`
    (zeroextu64 (w \bits8 2) `<<<` 16)) `|` (zeroextu64 (w \bits8 3) `<<<` 24)) `|`
    (zeroextu64 (w \bits8 4) `<<<` 32)) `|` (zeroextu64 (w \bits8 5) `<<<` 40)) `|`
    (zeroextu64 (w \bits8 6) `<<<` 48)) `|` (zeroextu64 (w \bits8 7) `<<<` 56)) = w.
proof.
  apply W64.wordP => i hi.
  rewrite !W64.orwE !W64.shlwE !W8u8.zeroextu64_bit /=.
  smt(W8u8.bits8iE).
qed.

lemma sj_cdt83_patch_low p u :
  cdt_lo_input (sj_cdt83_patch p u) = W64.of_int u.
proof.
  rewrite /cdt_lo_input /le8_word /le6_word /le3_word /byte_word
    !sj_cdt83_patch_byte //=.
  exact (sj_cdt83_assemble8 (W64.of_int u)).
qed.

lemma sj_cdt83_patch_low_uint p u :
  W64.to_uint (cdt_lo_input (sj_cdt83_patch p u)) = u %% 18446744073709551616.
proof. by rewrite sj_cdt83_patch_low W64.of_uintK. qed.

lemma sj_cdt83_patch_high_word p u : 0 <= u < cdt83_modulus =>
  le3_word (sj_cdt83_patch p u) 8 = W64.of_int (u %/ 18446744073709551616).
proof.
  move=> hu; have hq := cdt83_split_high_range u hu.
  rewrite /le3_word /byte_word !sj_cdt83_patch_byte //= sigma_noise72_assemble3.
  apply (sigma_mask_id _ 24); first trivial.
  rewrite W64.to_uint_small 1:/#; smt().
qed.

lemma sj_cdt83_patch_high p u : 0 <= u < cdt83_modulus =>
  cdt_hi_input (sj_cdt83_patch p u) = W32.of_int (u %/ 18446744073709551616).
proof.
  move=> hu; have hq := cdt83_split_high_range u hu.
  have hm : W64.of_int (u %/ 18446744073709551616) `&` W64.of_int 524287 =
      W64.of_int (u %/ 18446744073709551616).
  + apply (sigma_mask_id _ 19); first trivial.
    rewrite W64.to_uint_small 1:/#; smt().
  rewrite /cdt_hi_input (sj_cdt83_patch_high_word p u hu) hm.
  apply W32.to_uint_eq.
  rewrite /W2u32.truncateu32 !W32.of_uintK W64.of_uintK /=.
  apply modz_dvd; trivial.
qed.

lemma sj_cdt83_patch_high_uint p u : 0 <= u < cdt83_modulus =>
  W32.to_uint (cdt_hi_input (sj_cdt83_patch p u)) = u %/ 18446744073709551616.
proof.
  move=> hu; have hq := cdt83_split_high_range u hu.
  rewrite (sj_cdt83_patch_high p u hu) W32.to_uint_small; smt().
qed.

lemma sj_cdt83_patch_count p u : 0 <= u < cdt83_modulus =>
  sr_cdt (sj_cdt83_patch p u) = cdt_rank cdt83_thresholds u.
proof.
  move=> hu; rewrite /sr_cdt sj_cdt83_patch_low (sj_cdt83_patch_high p u hu).
  have h := cdt83_split_count u hu.
  by move: h; rewrite W64.of_int_mod.
qed.

lemma sj_cdt83_patch_rejection p u :
  le6_word (sj_cdt83_patch p u) 11 = le6_word p 11.
proof. by rewrite /le6_word /le3_word /byte_word !sj_cdt83_patch_outside. qed.

lemma sj_cdt83_patch_noise_low p u :
  le6_word (sj_cdt83_patch p u) 17 = le6_word p 17.
proof. by rewrite /le6_word /le3_word /byte_word !sj_cdt83_patch_outside. qed.

lemma sj_cdt83_patch_noise_high p u :
  le3_word (sj_cdt83_patch p u) 23 = le3_word p 23.
proof. by rewrite /le3_word /byte_word !sj_cdt83_patch_outside. qed.

lemma sj_cdt83_patch_noise p u : sr_noise (sj_cdt83_patch p u) = sr_noise p.
proof. by rewrite /sr_noise sj_cdt83_patch_noise_low sj_cdt83_patch_noise_high. qed.

lemma sj_cdt83_distribution_hasE (f : int -> real) :
  hasE (cdt_distribution cdt83_modulus cdt83_thresholds) f.
proof.
  apply hasE_finite; rewrite /cdt_distribution /dmap.
  apply finite_dlet; first exact (finite_dinter 0 (cdt83_modulus-1)).
  move=> x hx; rewrite /(\o); exact (finite_dunit (cdt_rank cdt83_thresholds x)).
qed.

lemma sj_cdt83_expectation (f : int -> real) :
  E (dinter 0 (cdt83_modulus-1)) (fun u => f (cdt_rank cdt83_thresholds u)) =
  E (cdt_distribution cdt83_modulus cdt83_thresholds) f.
proof.
  have hf := sj_cdt83_distribution_hasE f.
  move: hf; rewrite /cdt_distribution => hf.
  by rewrite /cdt_distribution (exp_dmap _ _ f hf) /(\o).
qed.
