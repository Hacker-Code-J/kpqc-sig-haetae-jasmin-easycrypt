require import AllCore IntDiv List Real RealExp StdOrder StdRing.
require import ExpIntervalSpec ExpIntervalCorrectness HyperballTailCertificate
  HyperballTailCertificateChecks HyperballTailSpec HyperballIidPayloadSpec
  HyperballReferenceConstants.
import RField RealOrder.

lemma htc_ratio_le (a b c d : int) :
  0 < b => 0 < d => a*d <= c*b => a%r / b%r <= c%r / d%r.
proof.
  move=> hb hd hc.
  have hbr : 0%r < b%r by rewrite lt_fromint.
  have hdr : 0%r < d%r by rewrite lt_fromint.
  have hcr : a%r*d%r <= c%r*b%r by rewrite -!fromintM le_fromint.
  have hbq : b%r*(a%r/b%r)=a%r by field; smt().
  have hdq : d%r*(c%r/d%r)=c%r by field; smt().
  smt().
qed.

lemma htc_rational_sound D a b bound : htc_rational_ok D a b bound =>
  ei_contains D bound (a%r/b%r).
proof.
  rewrite /htc_rational_ok; move=> [hD [ha [hb [hl [hlo hhi]]]]].
  have hDr : 0%r < D%r by rewrite lt_fromint.
  have har : 0%r <= a%r by rewrite le_fromint.
  have hbr : 0%r < b%r by rewrite lt_fromint.
  have hlr : 0%r <= bound.`1%r by rewrite le_fromint.
  have hlo_r : bound.`1%r*b%r <= D%r*a%r by rewrite -!fromintM le_fromint.
  have hhi_r : D%r*a%r <= bound.`2%r*b%r by rewrite -!fromintM le_fromint.
  have hquot : b%r*(a%r/b%r)=a%r by field; smt().
  rewrite /ei_contains; smt().
qed.

(* A rational seed is justified by the analytic reciprocal sandwich. *)
lemma htc_seed_sound D a b bound : htc_seed_ok D a b bound =>
  ei_contains D bound (RealExp.exp (-(a%r/b%r))).
proof.
  rewrite /htc_seed_ok; move=> [hD [[ha hab] [hl [hlo hhi]]]].
  have hDr : 0%r < D%r by rewrite lt_fromint.
  have har : 0%r < a%r by rewrite lt_fromint.
  have habr : a%r < b%r by rewrite lt_fromint.
  have hbr : 0%r < b%r by smt().
  have hdq : a%r*(b%r/a%r)=b%r by field; smt().
  have hd : 1%r < b%r/a%r by smt().
  have he : -1%r/(b%r/a%r) = -a%r/b%r by field; smt().
  have [hx [hlower hupper]] := ei_exp_reciprocal_sandwich (b%r/a%r) hd.
  move: hx hlower hupper; rewrite he; move=> hx hlower hupper.
  have hmullo := ler_wpmul2l a%r (ltrW _ _ har) _ _ hlower.
  have hmulhi := ler_wpmul2l a%r (ltrW _ _ har) _ _ hupper.
  have hl_r : 0%r <= bound.`1%r by rewrite le_fromint.
  have hlo_r : bound.`1%r*b%r <= D%r*(b%r-a%r)
    by rewrite -fromintB -!fromintM le_fromint.
  have hhi_r : D%r*b%r <= bound.`2%r*(b%r+a%r)
    by rewrite -fromintD -!fromintM le_fromint.
  rewrite /ei_contains; smt().
qed.

lemma htc_exp_chain_sound D a b (chain : ei_interval list) :
  htc_seed_ok D a b (head witness chain) =>
  ei_square_check D chain => size chain=33 =>
  ei_contains D (last witness chain)
    (RealExp.exp (4294967296%r * (-(a%r/b%r)))).
proof.
  case: chain => [|b0 rest].
  + by rewrite /ei_square_check.
  move=> hseed hcheck hsize.
  have hfirst := htc_seed_sound D a b b0 hseed.
  have hlen : size rest=32 by move: hsize; rewrite /=; smt().
  have h := ei_square_steps_sound D rest b0 (-(a%r/b%r)) hfirst hcheck.
  by move: h; rewrite hlen ei_pow2_32 /=.
qed.

lemma htc_exp_plus_interval :
  ei_contains htc_scale htc_exp_plus_bound (RealExp.exp (-19%r/160%r)).
proof.
  have [hs [hc [hn he]]] := htc_exp_plus_checked.
  have h := htc_exp_chain_sound htc_scale 19 687194767360 htc_exp_plus_chain hs hc hn.
  have hx : 4294967296%r * (-(19%r/687194767360%r)) = -19%r/160%r by field; trivial.
  by move: h; rewrite he hx.
qed.

lemma htc_exp_minus_interval :
  ei_contains htc_scale htc_exp_minus_bound (RealExp.exp (-45%r/392%r)).
proof.
  have [hs [hc [hn he]]] := htc_exp_minus_checked.
  have h := htc_exp_chain_sound htc_scale 45 1683627180032 htc_exp_minus_chain hs hc hn.
  have hx : 4294967296%r * (-(45%r/1683627180032%r)) = -45%r/392%r by field; trivial.
  by move: h; rewrite he hx.
qed.

lemma htc_power_step_sound D base (current next : htc_power_state) (x : real) :
  ei_contains D base x =>
  ei_contains D current.`2 (x^current.`1) =>
  htc_power_step_ok D base current next =>
  0 <= next.`1 /\ ei_contains D next.`2 (x^next.`1).
proof.
  move=> hb hc; rewrite /htc_power_step_ok; move=> [hn [hnext he]].
  have hpow : x^current.`1*x^current.`1=x^(2*current.`1).
  + rewrite -exprD_nneg 1:hn 1:hn; congr; ring.
  have htwice := ei_mul_sound D current.`2 current.`2
    (x^current.`1) (x^current.`1) hc hc.
  rewrite hpow in htwice.
  case (next.`1=2*current.`1) => hcase.
  + move: he; rewrite hcase /=; move=> he.
    rewrite he; split; first smt().
    exact htwice.
  have hnxt : next.`1=2*current.`1+1 by smt().
  move: he; rewrite hcase /=; move=> he.
  have hmul := ei_mul_sound D (ei_mul D current.`2 current.`2) base
    (x^(2*current.`1)) x htwice hb.
  rewrite -exprSr 1:/# -hnxt -he in hmul.
  split; first smt().
  exact hmul.
qed.

lemma htc_power_steps_sound D base (steps : htc_power_state list) :
  forall (current : htc_power_state) (x : real), 0 <= current.`1 =>
  ei_contains D base x => ei_contains D current.`2 (x^current.`1) =>
  htc_power_steps_check D base current steps =>
  ei_contains D (last current steps).`2 (x^(last current steps).`1).
proof.
  elim: steps => [|next tail ih] current x hn hb hc hs.
  + by rewrite /=.
  have [hstep htail] : htc_power_step_ok D base current next /\
      htc_power_steps_check D base next tail by move: hs; rewrite /=.
  have [hnxt hbound] := htc_power_step_sound D base current next x hb hc hstep.
  by apply (ih next x hnxt hb hbound htail).
qed.

lemma htc_power_chain_sound D base (chain : htc_power_state list) (x : real) :
  ei_contains D base x => htc_power_check D base chain =>
  ei_contains D (last witness chain).`2 (x^(last witness chain).`1).
proof.
  move=> hb; case: chain => [|b0 rest].
  + by rewrite /htc_power_check.
  rewrite /htc_power_check; move=> [-> hc].
  have hD : 0 < D by have := ei_contains_nonnegative D base x hb; smt().
  have hzero : ei_contains D (D,D) (x^0) by rewrite expr0; exact (ei_contains_one D hD).
  apply (htc_power_steps_sound D base rest (0,(D,D)) x _ hb hzero hc); trivial.
qed.

lemma ht_factor_plus :
  RealExp.exp (-19%r/160%r) * ht_mplus <= ht_rplus.
proof.
  have hD := htc_scale_positive.
  have [_ hupper] := ei_contains_division htc_scale htc_exp_plus_bound
    (RealExp.exp (-19%r/160%r)) htc_exp_plus_interval.
  have [hu hc] := htc_factor_plus_checked.
  have hm : 0%r <= ht_mplus by rewrite /ht_mplus; smt().
  have hproduct := ler_wpmul2r ht_mplus hm _ _ hupper.
  have hr := htc_ratio_le (htc_exp_plus_bound.`2*2621449)
    (htc_scale*2359296) 3947 4000 _ _ _; first 3 smt().
  have he : (htc_exp_plus_bound.`2%r / htc_scale%r) * ht_mplus =
    (htc_exp_plus_bound.`2*2621449)%r / (htc_scale*2359296)%r.
  + rewrite /ht_mplus !fromintM; field; rewrite /htc_scale; trivial.
  move: hproduct; rewrite he /ht_rplus; smt().
qed.

lemma ht_factor_minus :
  RealExp.exp (45%r/392%r) * ht_mminus <= ht_rminus.
proof.
  have hD := htc_scale_positive.
  have [hl hc] := htc_factor_minus_checked.
  have hL : 0%r < htc_exp_minus_bound.`1%r by rewrite lt_fromint.
  have hp := exp_gt0 (45%r/392%r).
  have hlo := htc_exp_minus_interval.
  rewrite /ei_contains in hlo.
  have hscaled : htc_exp_minus_bound.`1%r <=
    htc_scale%r * RealExp.exp (-45%r/392%r) by smt().
  have hmul := ler_wpmul2r (RealExp.exp (45%r/392%r)) (ltrW _ _ hp) _ _ hscaled.
  have hexp : RealExp.exp (-45%r/392%r) * RealExp.exp (45%r/392%r)=1%r.
  + rewrite -expD; have -> : -45%r/392%r + 45%r/392%r=0%r by ring.
    exact exp0.
  have heq : htc_exp_minus_bound.`1%r *
    (htc_scale%r/htc_exp_minus_bound.`1%r)=htc_scale%r by field; smt().
  have hupper : RealExp.exp (45%r/392%r) <=
      htc_scale%r/htc_exp_minus_bound.`1%r by smt().
  have hm : 0%r <= ht_mminus by rewrite /ht_mminus; smt().
  have hproduct := ler_wpmul2r ht_mminus hm _ _ hupper.
  have hr := htc_ratio_le (htc_scale*229377)
    (htc_exp_minus_bound.`1*262144) 1963 2000 _ _ _; first 3 smt().
  have he : (htc_scale%r/htc_exp_minus_bound.`1%r) * ht_mminus =
    (htc_scale*229377)%r / (htc_exp_minus_bound.`1*262144)%r.
  + rewrite /ht_mminus !fromintM; field; smt().
  move: hproduct; rewrite he /ht_rminus; smt().
qed.

lemma htc_rplus_interval : ei_contains htc_scale htc_rplus_bound ht_rplus.
proof.
  have [h _] := htc_rational_bases_checked.
  rewrite /ht_rplus; exact (htc_rational_sound htc_scale 3947 4000 htc_rplus_bound h).
qed.

lemma htc_rminus_interval : ei_contains htc_scale htc_rminus_bound ht_rminus.
proof.
  have [_ h] := htc_rational_bases_checked.
  rewrite /ht_rminus; exact (htc_rational_sound htc_scale 1963 2000 htc_rminus_bound h).
qed.

lemma htc_power_plus_1538_interval :
  ei_contains htc_scale htc_power_plus_bound_1538 (ht_rplus^1538).
proof.
  have [hc he] := htc_power_plus_1538_checked.
  have h := htc_power_chain_sound htc_scale htc_rplus_bound
    htc_power_plus_1538 ht_rplus htc_rplus_interval hc.
  by move: h; rewrite he /=.
qed.

lemma htc_power_plus_2306_interval :
  ei_contains htc_scale htc_power_plus_bound_2306 (ht_rplus^2306).
proof.
  have [hc he] := htc_power_plus_2306_checked.
  have h := htc_power_chain_sound htc_scale htc_rplus_bound
    htc_power_plus_2306 ht_rplus htc_rplus_interval hc.
  by move: h; rewrite he /=.
qed.

lemma htc_power_plus_2818_interval :
  ei_contains htc_scale htc_power_plus_bound_2818 (ht_rplus^2818).
proof.
  have [hc he] := htc_power_plus_2818_checked.
  have h := htc_power_chain_sound htc_scale htc_rplus_bound
    htc_power_plus_2818 ht_rplus htc_rplus_interval hc.
  by move: h; rewrite he /=.
qed.

lemma htc_power_minus_1538_interval :
  ei_contains htc_scale htc_power_minus_bound_1538 (ht_rminus^1538).
proof.
  have [hc he] := htc_power_minus_1538_checked.
  have h := htc_power_chain_sound htc_scale htc_rminus_bound
    htc_power_minus_1538 ht_rminus htc_rminus_interval hc.
  by move: h; rewrite he /=.
qed.

lemma htc_power_minus_2306_interval :
  ei_contains htc_scale htc_power_minus_bound_2306 (ht_rminus^2306).
proof.
  have [hc he] := htc_power_minus_2306_checked.
  have h := htc_power_chain_sound htc_scale htc_rminus_bound
    htc_power_minus_2306 ht_rminus htc_rminus_interval hc.
  by move: h; rewrite he /=.
qed.

lemma htc_power_minus_2818_interval :
  ei_contains htc_scale htc_power_minus_bound_2818 (ht_rminus^2818).
proof.
  have [hc he] := htc_power_minus_2818_checked.
  have h := htc_power_chain_sound htc_scale htc_rminus_bound
    htc_power_minus_2818 ht_rminus htc_rminus_interval hc.
  by move: h; rewrite he /=.
qed.

lemma htc_sum_strict D boundl boundr (x y : real) denominator :
  ei_contains D boundl x => ei_contains D boundr y => 0 < denominator =>
  (boundl.`2+boundr.`2)*denominator < D =>
  x+y < 1%r/denominator%r.
proof.
  move=> hx hy hd hc.
  have hDr : 0%r < D%r by have := ei_contains_nonnegative D boundl x hx; rewrite lt_fromint; smt().
  have hdr : 0%r < denominator%r by rewrite lt_fromint.
  have hcr : (boundl.`2%r+boundr.`2%r)*denominator%r < D%r
    by rewrite -fromintD -fromintM lt_fromint.
  have he : denominator%r*(1%r/denominator%r)=1%r by field; smt().
  move: hx hy; rewrite /ei_contains; smt().
qed.

lemma ht_power_sum_1538 :
  ht_rplus^1538+ht_rminus^1538 < 1%r/536870912%r.
proof.
  apply (htc_sum_strict htc_scale htc_power_plus_bound_1538
    htc_power_minus_bound_1538 (ht_rplus^1538) (ht_rminus^1538) 536870912
    htc_power_plus_1538_interval htc_power_minus_1538_interval _
    htc_power_sum_1538_checked); trivial.
qed.

lemma ht_power_sum_2306 :
  ht_rplus^2306+ht_rminus^2306 < 1%r/17592186044416%r.
proof.
  apply (htc_sum_strict htc_scale htc_power_plus_bound_2306
    htc_power_minus_bound_2306 (ht_rplus^2306) (ht_rminus^2306) 17592186044416
    htc_power_plus_2306_interval htc_power_minus_2306_interval _
    htc_power_sum_2306_checked); trivial.
qed.

lemma ht_power_sum_2818 :
  ht_rplus^2818+ht_rminus^2818 < 1%r/18014398509481984%r.
proof.
  apply (htc_sum_strict htc_scale htc_power_plus_bound_2818
    htc_power_minus_bound_2818 (ht_rplus^2818) (ht_rminus^2818) 18014398509481984
    htc_power_plus_2818_interval htc_power_minus_2818_interval _
    htc_power_sum_2818_checked); trivial.
qed.

lemma ht_mode_power_bound mode : ht_mode mode =>
  ht_rplus^(ht_count mode)+ht_rminus^(ht_count mode) < ht_epsilon mode.
proof.
  rewrite /ht_mode /hip_mode; move=> [->|[->|->]].
  + by rewrite /ht_count /hip_total /hip_count /hip_polys /hb_ref_l /hb_ref_k
      /ht_epsilon /=; exact ht_power_sum_1538.
  + by rewrite /ht_count /hip_total /hip_count /hip_polys /hb_ref_l /hb_ref_k
      /ht_epsilon /=; exact ht_power_sum_2306.
  by rewrite /ht_count /hip_total /hip_count /hip_polys /hb_ref_l /hb_ref_k
    /ht_epsilon /=; exact ht_power_sum_2818.
qed.
