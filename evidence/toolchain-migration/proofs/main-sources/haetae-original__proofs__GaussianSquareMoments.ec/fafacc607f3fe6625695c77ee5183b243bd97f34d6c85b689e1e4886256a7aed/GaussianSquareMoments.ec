require import AllCore IntDiv Real RealExp Distr StdRing StdOrder.
from Jasmin require import JModel_x86.
require import HyperballTailSpec HyperballTailConstants RawSquareMomentSpec
  GaussianPayloadSpec GaussianPayloadMoments GaussianRawSquare GaussianLatticeMgf
  RawSquareAcceptance RawSquareIdealMoments SigmaRawSpec Gaussian76Spec
  Gaussian76Identification SigmaConditionalSpec.
import RField RealOrder.

op gsm_round_factor : real = 1%r+1%r/18446744073709551616%r.
op gsm_bplus : real = 10%r/9%r+17%r/(9*ht_q)%r.
op gsm_bminus : real = gsm_round_factor*(7%r/8%r+13%r/(8*ht_q)%r).

lemma gsm_plus_even z : rsm_gaussian_plus (-z)=rsm_gaussian_plus z.
proof.
  have h : (-z)*(-z)=z*z by ring.
  by rewrite /rsm_gaussian_plus h.
qed.

lemma gsm_minus_even z : rsm_gaussian_minus (-z)=rsm_gaussian_minus z.
proof.
  have h : (-z)*(-z)=z*z by ring.
  by rewrite /rsm_gaussian_minus h.
qed.

lemma gsm_raw_plus_cap z : 0<=z<167*sr_noise_modulus => 0%r<=rsm_plus z<=ht_cap.
proof.
  move=> hz.
  have hsq : z*z <= (167*sr_noise_modulus)*(167*sr_noise_modulus) by
    apply IntOrder.ler_pmul; smt().
  have hx : ht_tplus*(z*z)%r/(ht_q*ht_q)%r <= 11%r by
    move: hsq; rewrite /ht_tplus /ht_q /sr_noise_modulus; smt().
  have hl : 0%r<rsm_plus z by rewrite /rsm_plus; apply exp_gt0.
  have hfloor := gps_floor_plus z.
  have he : rsm_gaussian_plus z <= RealExp.exp 11%r by
    rewrite /rsm_gaussian_plus; apply exp_mono; exact hx.
  have hcap := gps_exp_eleven_cap; smt().
qed.

lemma gsm_raw_minus_cap z : 0%r<=rsm_minus z<=1%r.
proof.
  have hq : 0<=rsm_square z by rewrite /rsm_square divz_ge0 /ht_q; smt().
  have hl : 0%r<rsm_minus z by rewrite /rsm_minus; apply exp_gt0.
  have hu : rsm_minus z<=RealExp.exp 0%r.
  + rewrite /rsm_minus; apply exp_mono; move: hq; rewrite /ht_tminus /ht_q; smt().
  rewrite exp0 in hu; smt().
qed.

lemma gsm_ideal_acceptance : rsm_ideal (fun _ => 1%r)=mu sc_ideal_pair sc_accepted.
proof. by rewrite rsa_ideal_acceptance_joint g76_ideal_acceptance_kernel. qed.

lemma gsm_ratio_bound a ideal numerator B W :
  1%r/7%r<=a => `|a-ideal|<=ht_eta => 0%r<=B => 0%r<=W =>
  numerator<=ideal*B+W*ht_eta =>
  numerator/a<=B+7%r*ht_eta*(B+W).
proof.
  move=> ha he hB hW hn.
  have he0 : 0%r<=ht_eta by rewrite /ht_eta; smt().
  have hao : 0%r<a by smt().
  have he1 : ideal<=a+ht_eta by move: he; rewrite ler_norml; smt().
  have hnum : numerator<=a*B+ht_eta*(B+W) by smt().
  have hi0 : 0%r<=inv a by rewrite invr_ge0; smt().
  have hu : a*inv a=1%r by field; smt().
  have hscale := RealOrder.ler_wpmul2r (inv a) hi0 (1%r/7%r) a ha.
  have hInv : 0%r<=inv a<=7%r by smt().
  have hdiv : (a*B+ht_eta*(B+W))/a=B+ht_eta*(B+W)*inv a by field; smt().
  smt().
qed.

lemma gsm_conditioned_bound p (weight raw_weight : int -> real) B W :
  (forall candidate, weight (gpd_pack (SigmaCorrectness.sigma76_spec candidate)) =
    raw_weight (sr_candidate candidate)) =>
  0%r<=B => 0%r<=W =>
  rsm_actual p raw_weight<=rsm_ideal (fun _ => 1%r)*B+W*ht_eta =>
  E gpd_accepted weight<=B+7%r*ht_eta*(B+W).
proof.
  move=> hw hB hW hn.
  rewrite (gpm_raw_conditioned_moment p weight raw_weight hw) -(gpm_acceptance p).
  exact (gsm_ratio_bound _ _ _ B W (rsa_actual_acceptance_lower p)
    (rsa_acceptance_error p) hB hW hn).
qed.

lemma gsm_plus_numerator p :
  rsm_actual p rsm_plus<=rsm_ideal (fun _ => 1%r)*gsm_bplus+ht_cap*ht_eta.
proof.
  have hW : 0%r<=ht_cap by rewrite /ht_cap; smt().
  have ht := rsa_weighted_upper p rsm_plus ht_cap hW gsm_raw_plus_cap.
  have hc := rsi_clipped_upper rsm_plus rsm_gaussian_plus glm_plus_hasE
    gsm_plus_even _ _.
  + move=> z; rewrite /rsm_gaussian_plus; have := exp_gt0 (ht_tplus*(z*z)%r/(ht_q*ht_q)%r); smt().
  + move=> z hz; have [h0 h1] := gsm_raw_plus_cap z hz; have := gps_floor_plus z; smt().
  have hm := glm_plus_bound; have ha := ge0_mu sc_ideal_pair sc_accepted.
  rewrite gsm_ideal_acceptance /gsm_bplus; smt().
qed.

lemma gsm_minus_numerator p :
  rsm_actual p rsm_minus<=rsm_ideal (fun _ => 1%r)*gsm_bminus+ht_eta.
proof.
  have ht := rsa_weighted_upper p rsm_minus 1%r _ _.
  + trivial.
  + move=> z hz; exact (gsm_raw_minus_cap z).
  pose major := fun z => gsm_round_factor*rsm_gaussian_minus z.
  have hC : 0%r<=gsm_round_factor by rewrite /gsm_round_factor; smt().
  have hE : hasE g76_distr major.
  + rewrite /major; exact (hasEZ g76_distr rsm_gaussian_minus gsm_round_factor glm_minus_hasE).
  have heven : forall z, major (-z)=major z by move=> z; rewrite /major gsm_minus_even.
  have hpos : forall z, 0%r<=major z.
  + move=> z; have hz : 0%r<rsm_gaussian_minus z by rewrite /rsm_gaussian_minus; apply exp_gt0.
    rewrite /major; smt().
  have hc := rsi_clipped_upper rsm_minus major hE heven hpos _.
  + move=> z hz; have [h0 h1] := gsm_raw_minus_cap z; have hfloor := gps_floor_minus z.
    move: hfloor; rewrite /major /gsm_round_factor /=; smt().
  have hm := glm_minus_bound; have ha := ge0_mu sc_ideal_pair sc_accepted.
  have hmE : E g76_distr major = gsm_round_factor*E g76_distr rsm_gaussian_minus by
    rewrite /major expZ.
  have hcE := hc.
  rewrite hmE in hcE.
  rewrite gsm_ideal_acceptance /gsm_bminus; smt().
qed.

lemma gsm_plus_budget : gsm_bplus+7%r*ht_eta*(gsm_bplus+ht_cap)<=ht_mplus.
proof. rewrite /gsm_bplus /ht_eta /ht_cap /ht_mplus /ht_q /=; smt(). qed.

lemma gsm_minus_budget : gsm_bminus+7%r*ht_eta*(gsm_bminus+1%r)<=ht_mminus.
proof. rewrite /gsm_bminus /gsm_round_factor /ht_eta /ht_mminus /ht_q /=; smt(). qed.

lemma gsm_plus_bound : E gpd_accepted ht_weight_plus<=ht_mplus.
proof.
  have h := gsm_conditioned_bound (witness<:BArray26.t>) ht_weight_plus rsm_plus
    gsm_bplus ht_cap gps_weight_plus _ _ (gsm_plus_numerator witness).
  + rewrite /gsm_bplus /ht_q /=; smt().
  + rewrite /ht_cap; smt().
  have hb := gsm_plus_budget; smt().
qed.

lemma gsm_minus_bound : E gpd_accepted ht_weight_minus<=ht_mminus.
proof.
  have h := gsm_conditioned_bound (witness<:BArray26.t>) ht_weight_minus rsm_minus
    gsm_bminus 1%r gps_weight_minus _ _ (gsm_minus_numerator witness).
  + rewrite /gsm_bminus /gsm_round_factor /ht_q /=; smt().
  + trivial.
  have hb := gsm_minus_budget; smt().
qed.

lemma gsm_centered_plus_expectation : E gpd_accepted ht_centered_plus =
  RealExp.exp (-19%r/160%r)*E gpd_accepted ht_weight_plus.
proof.
  rewrite -expZ; apply eq_exp => code hc /=.
  rewrite /ht_centered_plus /ht_weight_plus -RealExp.expD; congr; rewrite /ht_tplus; field; trivial.
qed.

lemma gsm_centered_minus_expectation : E gpd_accepted ht_centered_minus =
  RealExp.exp (45%r/392%r)*E gpd_accepted ht_weight_minus.
proof.
  rewrite -expZ; apply eq_exp => code hc /=.
  rewrite /ht_centered_minus /ht_weight_minus -RealExp.expD; congr; rewrite /ht_tminus; field; trivial.
qed.

lemma gsm_centered_plus : E gpd_accepted ht_centered_plus<=ht_rplus.
proof.
  rewrite gsm_centered_plus_expectation.
  have hp := exp_gt0 (-19%r/160%r); have hm := gsm_plus_bound; have hr := ht_factor_plus; smt().
qed.

lemma gsm_centered_minus : E gpd_accepted ht_centered_minus<=ht_rminus.
proof.
  rewrite gsm_centered_minus_expectation.
  have hp := exp_gt0 (45%r/392%r); have hm := gsm_minus_bound; have hr := ht_factor_minus; smt().
qed.
