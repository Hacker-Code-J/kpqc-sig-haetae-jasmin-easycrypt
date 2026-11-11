require import AllCore IntDiv List Real RealExp Distr DList Finite StdRing StdOrder.
from Jasmin require import JModel_x86.
require import GaussianPayloadSpec GaussianPayloadEncoding GaussianTraceSpec
  GaussianAccumulatorCorrectness GaussianRetryCore HyperballGaussianBounds
  SigmaSpec SigmaCorrectness SigmaRoundingCorrectness SigmaRawSpec
  SigmaRawExponentCorrectness SigmaSquareExact SigmaRejection48Bridge
  HyperballTailSpec RawSquareMomentSpec ExpIntervalCorrectness.
import IntOrder RField RealOrder.

(* The payload contains the implemented raw square, including its final
   truncation. These equalities make no distributional assumption. *)
lemma gps_square_exact (p : BArray26.t) :
  gpd_square (gpd_pack (sigma76_spec p)) = (sr_candidate p)^2 %/ ht_q.
proof.
  have [hlo0 hlo] := sigma_le6_bound p 17.
  have [_ hhi] := sr_high_word_bounds p.
  have hs := sigma_square_word_exact (le6_word p 17)
    (le3_word p 23 `|` (W64.of_int (sr_cdt p) `<<<` 24)) hlo hhi.
  rewrite gpd_pack_square /sigma76_spec -/(sr_cdt p) /sigma_from_cdt /=
    /gauss_limb_value.
  move: hs; rewrite sr_candidate_decoding /ht_q.
  trivial.
qed.

lemma gps_square_moment (p : BArray26.t) :
  gpd_square (gpd_pack (sigma76_spec p)) = rsm_square (sr_candidate p).
proof. by rewrite gps_square_exact /rsm_square Ring.IntID.expr2. qed.

lemma gps_candidate_bounds (p : BArray26.t) :
  0 <= sr_candidate p < 167*sr_noise_modulus.
proof.
  have hn := sr_noise_bounds p; have hc := sr_cdt_bounds p.
  move: hn hc; rewrite /sr_candidate /sr_noise_modulus; smt().
qed.

lemma gps_square_bounds (p : BArray26.t) :
  0 <= gpd_square (gpd_pack (sigma76_spec p)) < 109*ht_q.
proof.
  have hz := gps_candidate_bounds p.
  have hp : sr_candidate p*sr_candidate p <=
      (167*sr_noise_modulus)*(167*sr_noise_modulus)
    by apply IntOrder.ler_pmul; smt().
  have hp0 : 0 <= sr_candidate p*sr_candidate p by apply IntOrder.mulr_ge0; smt().
  rewrite gps_square_exact Ring.IntID.expr2 /ht_q.
  apply divz_cmp; move: hp; rewrite /sr_noise_modulus /=; smt().
qed.

lemma gps_weight_plus (p : BArray26.t) :
  ht_weight_plus (gpd_pack (sigma76_spec p)) = rsm_plus (sr_candidate p).
proof.
  rewrite /ht_weight_plus /ht_raw_square gps_square_moment /rsm_plus.
  congr; ring.
qed.

lemma gps_weight_minus (p : BArray26.t) :
  ht_weight_minus (gpd_pack (sigma76_spec p)) = rsm_minus (sr_candidate p).
proof.
  rewrite /ht_weight_minus /ht_raw_square gps_square_moment /rsm_minus.
  congr; ring.
qed.

lemma gps_rejection_candidate (p : BArray26.t) u :
  sr_candidate (sigma_rejection48_patch p u) = sr_candidate p.
proof.
  by rewrite /sr_candidate /sr_noise /sr_cdt
    sigma_rejection48_patch_noise_low sigma_rejection48_patch_noise_high
    sigma_rejection48_patch_cdt_low sigma_rejection48_patch_cdt_high.
qed.

lemma gps_mismatch_square_zero (p : BArray26.t) : sr_zero_mismatch p =>
  gpd_square (gpd_pack (sigma76_spec p)) = 0.
proof.
  rewrite /sr_zero_mismatch => -[hx hy].
  have hs : 0 <= sr_noise p*sr_noise p < ht_q.
  + have hp : sr_noise p*sr_noise p <= 32768*32768 by apply IntOrder.ler_pmul; smt().
    rewrite /ht_q; smt(IntOrder.mulr_ge0).
  rewrite gps_square_exact /sr_candidate hx /=.
  by rewrite divz_small 1:/#.
qed.

lemma gps_exp_eleven_cap : RealExp.exp 11%r <= ht_cap.
proof.
  have he : RealExp.exp 11%r = RField.exp RealExp.e 11 by
    rewrite -(RealExp.rpoweE 11%r) (RealExp.rpow_int RealExp.e 11 RealExp.e_ge0).
  have hb : 0%r <= RealExp.e <= 3%r by have h := RealExp.e_boundW; smt().
  have hp := RealOrder.ler_pexp 11 RealExp.e 3%r _ hb; first trivial.
  have hthree : RField.exp 3%r 11 = 177147%r by ring.
  have hnum : RField.exp 3%r 11 <= ht_cap by rewrite hthree /ht_cap.
  rewrite he; exact (ler_trans _ _ _ hp hnum).
qed.

lemma gps_sigma_weight_plus (p : BArray26.t) :
  0%r <= ht_weight_plus (gpd_pack (sigma76_spec p)) <= ht_cap.
proof.
  have hq := gps_square_bounds p.
  have hx : ht_tplus*ht_raw_square (gpd_pack (sigma76_spec p)) <= 11%r
    by move: hq; rewrite /ht_tplus /ht_raw_square /ht_q; smt().
  have he := exp_gt0 (ht_tplus*ht_raw_square (gpd_pack (sigma76_spec p))).
  have hm : RealExp.exp (ht_tplus*ht_raw_square (gpd_pack (sigma76_spec p))) <=
      RealExp.exp 11%r by apply/exp_mono.
  rewrite /ht_weight_plus; have hc := gps_exp_eleven_cap; smt().
qed.

lemma gps_sigma_weight_minus (p : BArray26.t) :
  0%r <= ht_weight_minus (gpd_pack (sigma76_spec p)) <= 1%r.
proof.
  have hq := gps_square_bounds p.
  have hx : -ht_tminus*ht_raw_square (gpd_pack (sigma76_spec p)) <= 0%r
    by move: hq; rewrite /ht_tminus /ht_raw_square /ht_q; smt().
  have he := exp_gt0 (-ht_tminus*ht_raw_square (gpd_pack (sigma76_spec p))).
  have hm : RealExp.exp (-ht_tminus*ht_raw_square (gpd_pack (sigma76_spec p))) <=
      RealExp.exp 0%r by apply/exp_mono.
  rewrite /ht_weight_minus; move: hm; rewrite exp0; smt().
qed.

lemma gps_accepted_candidate code : code \in gpd_accepted =>
  exists p, code = gpd_pack (sigma76_spec p).
proof.
  rewrite /gpd_accepted /gr_output supp_dmap => -[outcome [ho ->]].
  move: ho; rewrite dcond_supp => -[ht ha].
  move: ht; rewrite /gpd_trial supp_dmap => -[p [hp ->]].
  exists p; by rewrite /gpd_observer /=.
qed.

lemma gps_accepted_weight_plus code : code \in gpd_accepted =>
  0%r <= ht_weight_plus code <= ht_cap.
proof. move=> hc; have [p ->] := gps_accepted_candidate code hc; exact (gps_sigma_weight_plus p). qed.

lemma gps_accepted_weight_minus code : code \in gpd_accepted =>
  0%r <= ht_weight_minus code <= 1%r.
proof. move=> hc; have [p ->] := gps_accepted_candidate code hc; exact (gps_sigma_weight_minus p). qed.

lemma gps_accepted_bounds code : code \in gpd_accepted => 0 <= code < 2^148.
proof.
  move=> hc; have hv := gpd_accepted_valid code hc.
  have hb := gpd_valid_bounds code hv.
  move: hv hb; rewrite /gpd_valid /gpd_base /hb_event_max /=; smt().
qed.

lemma gps_accepted_finite : is_finite (Distr.support gpd_accepted).
proof.
  apply/finiteP; exists (iota_ 0 (gpd_base*(hb_event_max+1))) => code hc.
  have hv := gpd_accepted_valid code hc.
  have [_ hu] := gpd_valid_bounds code hv.
  move: hv; rewrite /gpd_valid => -[hn hsq].
  rewrite mem_iota add0z; split; assumption.
qed.

lemma gps_floor_real (z : int) :
  (z*z)%r/(ht_q*ht_q)%r - 1%r/ht_q%r <= (rsm_square z)%r/ht_q%r <=
    (z*z)%r/(ht_q*ht_q)%r.
proof.
  have hd := divz_eq (z*z) ht_q.
  have hr := modz_cmp (z*z) ht_q _; first by rewrite /ht_q.
  rewrite /rsm_square /ht_q.
  move: hd hr; rewrite /ht_q; smt().
qed.

lemma gps_floor_plus (z : int) : rsm_plus z <= rsm_gaussian_plus z.
proof.
  have h := gps_floor_real z.
  rewrite /rsm_plus /rsm_gaussian_plus; apply/exp_mono.
  move: h; rewrite /ht_tplus /ht_q; smt().
qed.

lemma gps_exp_rounding :
  RealExp.exp (ht_tminus/ht_q%r) <= 1%r+1%r/(2^64)%r.
proof.
  have hd : 1%r < ht_q%r by rewrite /ht_q.
  have [_ [hl _]] := ei_exp_reciprocal_sandwich ht_q%r hd.
  have he := exp_gt0 (1%r/ht_q%r).
  have hprod : RealExp.exp (-(1%r/ht_q%r))*RealExp.exp (1%r/ht_q%r)=1%r by
    rewrite -expD addNr exp0.
  have hep : 0%r <= RealExp.exp (1%r/ht_q%r) by smt().
  have hm := RealOrder.ler_wpmul2r (RealExp.exp (1%r/ht_q%r)) hep
    (ht_q%r-1%r) (ht_q%r*RealExp.exp (-(1%r/ht_q%r))) hl.
  have heq : (ht_q%r*RealExp.exp (-(1%r/ht_q%r)))*RealExp.exp (1%r/ht_q%r) =
      ht_q%r by rewrite -mulrA hprod mulr1.
  move: hm; rewrite heq => hm.
  have hb : RealExp.exp (1%r/ht_q%r) <= 1%r+1%r/(2^64)%r by
    move: hm; rewrite /ht_q /=; smt().
  have hx : RealExp.exp (ht_tminus/ht_q%r) <= RealExp.exp (1%r/ht_q%r).
  + apply/exp_mono; rewrite /ht_tminus /ht_q; smt().
  exact (ler_trans _ _ _ hx hb).
qed.

lemma gps_floor_minus (z : int) :
  rsm_minus z <= (1%r+1%r/(2^64)%r)*rsm_gaussian_minus z.
proof.
  have h := gps_floor_real z.
  have hx : -ht_tminus*(rsm_square z)%r/ht_q%r <=
      ht_tminus/ht_q%r + (-ht_tminus*(z*z)%r/(ht_q*ht_q)%r)
    by move: h; rewrite /ht_tminus /ht_q; smt().
  have he : RealExp.exp (-ht_tminus*(rsm_square z)%r/ht_q%r) <=
      RealExp.exp (ht_tminus/ht_q%r + (-ht_tminus*(z*z)%r/(ht_q*ht_q)%r))
    by apply/exp_mono.
  rewrite expD in he.
  have hp : 0%r <= rsm_gaussian_minus z.
  + rewrite /rsm_gaussian_minus; apply/ltrW; exact (exp_gt0 _).
  have hm := RealOrder.ler_wpmul2r (rsm_gaussian_minus z) hp
    (RealExp.exp (ht_tminus/ht_q%r)) (1%r+1%r/(2^64)%r) gps_exp_rounding.
  move: hm he; rewrite /rsm_minus /rsm_gaussian_minus; smt().
qed.
