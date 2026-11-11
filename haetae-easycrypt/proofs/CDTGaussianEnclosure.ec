require import AllCore IntDiv List Real StdRing StdOrder StdBigop Distr.
require import ExpIntervalSpec GaussianIntervalBounds HalfGaussianSpec
  HalfGaussianProperties CDTGaussianCertificate CDTGaussianCertificateChecks.
import RField RealOrder HalfGaussianSpec HalfGaussianProperties.

(* The normalizer certificate sums a list prefix; the analytic statement
   sums its coordinates over an exclusive integer range. *)
lemma gi_take_sum_index ['a] (default : 'a) (xs : 'a list)
    (f : 'a -> int) (n : int) :
  0 <= n <= size xs =>
  Bigint.BIA.big predT f (take n xs) =
    Bigint.BIA.bigi predT (fun i => f (nth default xs i)) 0 n.
proof.
  move=> [hn hs]; move: hs; elim: n hn => [|n hn ih] hs.
  + by rewrite take0 Bigint.BIA.big_nil Bigint.BIA.big_geq.
  have hlt : 0 <= n < size xs by smt().
  have hp := ih _; first smt().
  by rewrite (take_nth default n xs hlt) Bigint.BIA.big_rcons
    Bigint.BIA.big_int_recr 1:hn /= hp.
qed.

(* These two assembly lemmas isolate the analytic/certificate composition
   while the final exports below discharge their interval premises. *)
lemma gi_tail_interval_from_endpoint :
  ei_contains gi_scale (nth witness gi_weight_chain 256).`1 (hg16_rho 256) =>
  ei_contains gi_scale (nth witness gi_weight_chain 256).`2 (hg16_q^513) =>
  ei_contains gi_scale (0, gi_tail_weight_upper) (hg16_tail 256).
proof.
  move=> hw hr.
  have hD : 0 < gi_scale by have := gi_positive_constants; smt().
  have ht : 0 <= gi_tail_weight_upper by have := gi_positive_constants; smt().
  have [_ [_ [hrhi [hcheck _]]]] := gi_normalizer_checked.
  have hquot := gi_geometric_tail_interval_sound gi_scale gi_tail_weight_upper
    (nth witness gi_weight_chain 256).`1 (nth witness gi_weight_chain 256).`2
    (hg16_rho 256) (hg16_q^513) hw hr hrhi ht hcheck.
  have htail0 := hg16_tail_ge0 256.
  have htailhi := hg16_tail_le 256 _; first trivial.
  rewrite /hg16_tail_bound /= in htailhi.
  have hDr : 0%r < gi_scale%r by rewrite lt_fromint.
  move: hquot; rewrite /ei_contains /= => hquot.
  rewrite /ei_contains /=; smt().
qed.

lemma gi_normalizer_join (D lo hi tail zlo zhi : int) (P T Z : real) :
  ei_contains D (lo, hi) P => ei_contains D (0, tail) T =>
  zlo = lo => zhi = hi + tail => Z = P + T =>
  ei_contains D (zlo, zhi) Z.
proof.
  move=> hp ht -> -> ->.
  rewrite /ei_contains in hp.
  rewrite /ei_contains in ht.
  rewrite /ei_contains /= fromintD.
  smt().
qed.

lemma gi_normalizer_from_weight_intervals :
  (forall i, 0 <= i < 257 =>
    ei_contains gi_scale (nth witness gi_weight_chain i).`1 (hg16_rho i) /\
    ei_contains gi_scale (nth witness gi_weight_chain i).`2 (hg16_q^(2*i+1))) =>
  ei_contains gi_scale gi_normalizer_bounds hg16_normalizer.
proof.
  move=> hweights.
  have hD : 0 < gi_scale by have := gi_positive_constants; smt().
  have hsize : size gi_weight_chain = 257 by have := gi_dimensions; smt().
  have hprefixsize : 0 <= 256 <= size gi_weight_chain by rewrite hsize.
  have hterms : forall i, 0 <= i < 256 =>
    ei_contains gi_scale (nth witness gi_weight_chain i).`1 (hg16_rho i).
  + move=> i hi.
    have hi257 : 0 <= i < 257 by smt().
    have [hw _] := hweights i hi257; exact hw.
  have hp := gi_weight_prefix_sum_interval_sound gi_scale 256 gi_weight_chain
    hg16_rho hD hprefixsize hterms.
  have hlast : 0 <= 256 < 257 by trivial.
  have [hw hr] := hweights 256 hlast.
  have ht := gi_tail_interval_from_endpoint hw hr.
  rewrite -(gi_take_sum_index witness gi_weight_chain
    (fun (s : ei_weight_state) => s.`1.`1) 256 hprefixsize)
    -(gi_take_sum_index witness gi_weight_chain
    (fun (s : ei_weight_state) => s.`1.`2) 256 hprefixsize)
    -/hg16_partial in hp.
  have [hzlo [hzhi _]] := gi_normalizer_checked.
  have hsplit := hg16_normalizer_split 256 _; first trivial.
  exact (gi_normalizer_join gi_scale _ _ gi_tail_weight_upper
    gi_normalizer_bounds.`1 gi_normalizer_bounds.`2
    (hg16_partial 256) (hg16_tail 256) hg16_normalizer hp ht hzlo hzhi hsplit).
qed.

require import ExpIntervalCorrectness.

lemma gi_q_interval :
  ei_contains gi_scale (last witness gi_squaring_chain) hg16_q.
proof.
  have hseed : ei_seed_ok gi_scale (Ring.IntID.exp 2 137)
      (head witness gi_squaring_chain).
  + rewrite ei_pow2_137 -/gi_seed_denominator; exact gi_exp_seed_checked.
  have hsize : size gi_squaring_chain = 129 by have := gi_dimensions; smt().
  have h := ei_square_q_sound gi_scale gi_squaring_chain hseed gi_exp_squarings_checked hsize.
  have he : -(1%r / 512%r) = -1%r / 512%r by ring.
  by move: h; rewrite he -/hg16_q.
qed.

lemma gi_weight_intervals i : 0 <= i < 257 =>
  ei_contains gi_scale (nth witness gi_weight_chain i).`1 (hg16_rho i) /\
  ei_contains gi_scale (nth witness gi_weight_chain i).`2 (hg16_q^(2*i+1)).
proof.
  move=> hi.
  have hsize : size gi_weight_chain = 257 by have := gi_dimensions; smt().
  have hirange : 0 <= i < size gi_weight_chain by rewrite hsize.
  have h := ei_weights_sound gi_scale (last witness gi_squaring_chain)
    gi_weight_chain hg16_q gi_q_interval gi_gaussian_weights_checked i hirange.
  by rewrite hg16_rho_power 1:/#.
qed.

lemma gi_tail_weight_interval :
  ei_contains gi_scale (0, gi_tail_weight_upper) (hg16_tail 256).
proof.
  have hindex : 0 <= 256 < 257 by trivial.
  have [hw hr] := gi_weight_intervals 256 hindex.
  exact (gi_tail_interval_from_endpoint hw hr).
qed.

lemma gi_normalizer_interval :
  ei_contains gi_scale gi_normalizer_bounds hg16_normalizer.
proof. exact (gi_normalizer_from_weight_intervals gi_weight_intervals). qed.

lemma gi_pmf_interval k : 0 <= k < 256 =>
  ei_contains gi_probability_scale (nth witness gi_pmf_bounds k)
    (mu1 hg16_distr k).
proof.
  move=> hk.
  have hk257 : 0 <= k < 257 by smt().
  have [hw _] := gi_weight_intervals k hk257.
  have hR : 0 < gi_probability_scale by have := gi_positive_constants; smt().
  have hzlo : 0 < gi_normalizer_bounds.`1 by have := gi_positive_constants; smt().
  have hchecks := gi_pmf_intervals_checked.
  rewrite List.allP in hchecks.
  have hmem : k \in iota_ 0 256 by rewrite mem_iota; smt().
  have [hp0 [hp1 [hlo hhi]]] := hchecks k hmem.
  rewrite hg16_mu1 /hg16_pmf.
  exact (gi_ratio_interval_sound gi_scale gi_probability_scale
    (nth witness gi_weight_chain k).`1 gi_normalizer_bounds (nth witness gi_pmf_bounds k)
    (hg16_rho k) hg16_normalizer hw gi_normalizer_interval hzlo hR hp0 hp1 hlo hhi).
qed.

lemma gi_tail_probability :
  mu hg16_distr (fun k => 256 <= k) <=
    gi_tail_probability_upper%r / gi_probability_scale%r.
proof.
  have hR : 0 < gi_probability_scale by have := gi_positive_constants; smt().
  have hzlo : 0 < gi_normalizer_bounds.`1 by have := gi_positive_constants; smt().
  have hpt : 0 <= gi_tail_probability_upper by have := gi_positive_constants; smt().
  have hzero : 0 <= 0 by trivial.
  have hlo : 0 * gi_normalizer_bounds.`2 <= gi_probability_scale * 0 by trivial.
  have [_ [_ [_ [_ hhi]]]] := gi_normalizer_checked.
  have [_ hbound] := gi_ratio_interval_division gi_scale gi_probability_scale
    (0, gi_tail_weight_upper) gi_normalizer_bounds (0, gi_tail_probability_upper)
    (hg16_tail 256) hg16_normalizer gi_tail_weight_interval gi_normalizer_interval
    hzlo hR hzero hpt hlo hhi.
  by rewrite hg16_tail_probability.
qed.
