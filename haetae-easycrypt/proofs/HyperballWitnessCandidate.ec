require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HyperballWitnessSpec SigmaSpec SigmaCorrectness SigmaRoundingCorrectness
  SigmaSquareExact GaussianAccumulatorCorrectness SigmaRejection48Bridge Rejection48Spec
  Rejection48Correctness SigmaExpAcceptanceCorrectness SigmaExpInputBounds
  ApproxExpSpec ApproxExpWordCorrectness ReferenceConstants CDTCorrectness CDTDistributionSpec
  CDTDistributionBridge GaussianUniformBytes GaussianRetryInputs SigmaNoise72Bridge SigmaCDT83Patch
  SigmaRawSpec SigmaRawExponentCorrectness.

op hbw_input83 mode : int =
  if mode=2 then 9667512240551696948472816
  else if mode=3 then 9671406556916854492522117
  else if mode=5 then 9596942536040522023515905 else 0.

op hbw_noise72 mode : int =
  if mode=2 then 1920552634435512831226
  else if mode=3 then 2005854724399332623078
  else if mode=5 then 2953087595120155771696 else 0.

op hbw_cdt_sample mode : int =
  if mode=2 then 57 else if mode=3 then 123 else if mode=5 then 43 else 0.

lemma hbw_candidate_encoding mode : hbw_mode mode =>
  hbw_candidate mode = gr_candidate_patch witness (hbw_input83 mode) (hbw_noise72 mode) 1.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite gbc_candidate_patch_bytes /hbw_candidate /hbw_input83 /hbw_noise72
      /gbc_encode_bytes -iotaredE /=.
qed.

lemma hbw_cdt_evaluation mode : hbw_mode mode =>
  cdt_rank cdt83_thresholds (hbw_input83 mode) = hbw_cdt_sample mode.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /cdt_rank /cdt83_thresholds /cdt83_reference_high
      /reference_cdt83_hi_words /reference_cdt83_lo_words /reference_cdt83_tail_hi
      /hbw_input83 /hbw_cdt_sample /mapi /=.
qed.

lemma hbw_input_ranges mode : hbw_mode mode =>
  0 <= hbw_input83 mode < cdt83_modulus /\
  0 <= hbw_noise72 mode < sr_noise_modulus.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_input83 /hbw_noise72 /cdt83_modulus /sr_noise_modulus.
qed.

lemma hbw_candidate_cdt mode : hbw_mode mode =>
  cdt_count (cdt_lo_input (hbw_candidate mode)) (cdt_hi_input (hbw_candidate mode)) 166 =
    hbw_cdt_sample mode.
proof.
  move=> hm; have [hu hy] := hbw_input_ranges mode hm.
  rewrite (hbw_candidate_encoding mode hm) /gr_candidate_patch
    sigma_rejection48_patch_cdt_low sigma_rejection48_patch_cdt_high
    sigma_noise72_patch_cdt_low sigma_noise72_patch_cdt_high.
  rewrite -/(sr_cdt (sj_cdt83_patch witness (hbw_input83 mode)))
    (sj_cdt83_patch_count witness (hbw_input83 mode) hu).
  exact (hbw_cdt_evaluation mode hm).
qed.

lemma hbw_candidate_noise_low mode : hbw_mode mode =>
  W64.to_uint (le6_word (hbw_candidate mode) 17) = hbw_noise72 mode %% sr_scale.
proof.
  move=> hm; by rewrite (hbw_candidate_encoding mode hm) /gr_candidate_patch
    sigma_rejection48_patch_noise_low sigma_noise72_patch_low.
qed.

lemma hbw_candidate_noise_high mode : hbw_mode mode =>
  W64.to_uint (le3_word (hbw_candidate mode) 23) = hbw_noise72 mode %/ sr_scale.
proof.
  move=> hm; have [hu hy] := hbw_input_ranges mode hm.
  by rewrite (hbw_candidate_encoding mode hm) /gr_candidate_patch
    sigma_rejection48_patch_noise_high sigma_noise72_patch_high 1:hy.
qed.

lemma hbw_candidate_rejection mode : hbw_mode mode =>
  le6_word (hbw_candidate mode) 11 = W64.one.
proof.
  move=> hm; by rewrite (hbw_candidate_encoding mode hm) /gr_candidate_patch
    sigma_rejection48_patch_decode.
qed.

lemma hbw_candidate_rounding mode : hbw_mode mode =>
  (sigma76_spec (hbw_candidate mode)).`1 = hbw_sample mode.
proof.
  move=> hm; apply W64.to_uint_eq.
  rewrite sigma76_spec_rounding /sigma76_rounding_int
    (hbw_candidate_cdt mode hm) (hbw_candidate_noise_low mode hm)
    (hbw_candidate_noise_high mode hm) /sigma_round_int /sr_scale.
  move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_noise72 /hbw_cdt_sample /hbw_sample /=.
qed.

lemma hbw_sigma_square_value (p : BArray26.t) :
  W64.to_uint (sigma76_spec p).`2 + 281474976710656 * W64.to_uint (sigma76_spec p).`3 =
    (sr_candidate p * sr_candidate p) %/ 75557863725914323419136.
proof.
  have [hlo0 hlo] := sigma_le6_bound p 17.
  have [hwindow hhi] := sr_high_word_bounds p.
  have h := sigma_square_word_exact (le6_word p 17)
    (le3_word p 23 `|` (W64.of_int (sr_cdt p) `<<<` 24)) hlo hhi.
  rewrite /= sr_candidate_decoding in h.
  by rewrite /sigma76_spec -/(sr_cdt p) /sigma_from_cdt /=.
qed.

lemma hbw_sigma_square_low (p : BArray26.t) :
  0 <= W64.to_uint (sigma76_spec p).`2 < 281474976710656.
proof.
  rewrite /sigma76_spec /sigma_from_cdt /=.
  exact (gauss_square_low_bound _ _).
qed.

lemma hbw_candidate_square_value mode : hbw_mode mode =>
  W64.to_uint (sigma76_spec (hbw_candidate mode)).`2 +
    281474976710656 * W64.to_uint (sigma76_spec (hbw_candidate mode)).`3 =
  W64.to_uint (hbw_square mode).`1 + 281474976710656 * W64.to_uint (hbw_square mode).`2.
proof.
  move=> hm; rewrite hbw_sigma_square_value /sr_candidate /sr_noise /sr_cdt
    (hbw_candidate_cdt mode hm) (hbw_candidate_noise_low mode hm)
    (hbw_candidate_noise_high mode hm) /sr_scale /sr_noise_modulus.
  move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_noise72 /hbw_cdt_sample /hbw_square /=.
qed.

lemma hbw_candidate_square mode : hbw_mode mode =>
  ((sigma76_spec (hbw_candidate mode)).`2, (sigma76_spec (hbw_candidate mode)).`3) = hbw_square mode.
proof.
  move=> hm.
  have hv := hbw_candidate_square_value mode hm.
  have hl := hbw_sigma_square_low (hbw_candidate mode).
  have hrecorded : 0 <= W64.to_uint (hbw_square mode).`1 < 281474976710656.
  + move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
      by rewrite /hbw_square /=.
  have he : W64.to_uint (sigma76_spec (hbw_candidate mode)).`2 = W64.to_uint (hbw_square mode).`1 /\
    W64.to_uint (sigma76_spec (hbw_candidate mode)).`3 = W64.to_uint (hbw_square mode).`2 by smt().
  have [h0 h1] := he.
  have e0 : (sigma76_spec (hbw_candidate mode)).`2 = (hbw_square mode).`1 by
    apply W64.to_uint_eq; exact h0.
  have e1 : (sigma76_spec (hbw_candidate mode)).`3 = (hbw_square mode).`2 by
    apply W64.to_uint_eq; exact h1.
  by rewrite e0 e1; case (hbw_square mode).
qed.

(* Each alternating coefficient pair preserves nonnegativity. The final
   positive coefficient exceeds the final negative one by seven. *)
lemma hbw_exp_integer_positive x : ae_domain x => 7 <= ae_integer x.
proof.
  move=> hx; have [hxr hx64] := ae_domain_bounds x hx.
  pose r0 := 55868746.
  pose r2 := ae_ceil (ae_ceil r0 x-743564434) x+6953427278.
  pose r4 := ae_ceil (ae_ceil r2 x-55833338892) x+390932311155.
  pose r6 := ae_ceil (ae_ceil r4 x-2345623661771) x+11728123872951.
  pose r8 := ae_ceil (ae_ceil r6 x-46912496106200) x+140737488354861.
  have h0 : 0 <= r0 by rewrite /r0.
  have h2 : 0 <= r2 by apply (ae_pair_nonnegative r0 x 743564434 6953427278 hx h0); trivial.
  have h4 : 0 <= r4 by apply (ae_pair_nonnegative r2 x 55833338892 390932311155 hx h2); trivial.
  have h6 : 0 <= r6 by apply (ae_pair_nonnegative r4 x 2345623661771 11728123872951 hx h4); trivial.
  have h8 : 0 <= r8 by apply (ae_pair_nonnegative r6 x 46912496106200 140737488354861 hx h6); trivial.
  have ht0 := ae_ceil_nonnegative r8 x h8 _; first smt().
  have ht1 := ae_ceil_lower (ae_ceil r8 x-281474976710650) x 281474976710650 hxr _ _;
    first 2 smt().
  rewrite /ae_integer /ae_integer_fold /ae_leading /ae_tail /ae_coefficients
    /reference_exp_coefficients /= -/r0 -/r2 -/r4 -/r6 -/r8.
  smt().
qed.

lemma hbw_rejection_one_accepts (p : BArray26.t) :
  le6_word p 11 = W64.one => (sigma76_spec p).`4 = W64.one.
proof.
  move=> hrej.
  have hfit := sigma_exp_threshold_fit p.
  have hp := hbw_exp_integer_positive (W64.to_uint (sigma_exp_argument p)) (ae_sigma_domain p).
  have hpositive : 0 < W64.to_uint (sigma_rejection48_threshold p).
  + by rewrite /sigma_rejection48_threshold ae_approx_exp_unsigned 1:ae_sigma_domain; smt().
  have h := rejection48_word_correct 1 (W64.to_uint (sigma_rejection48_threshold p))
    (sigma_rejection48_rounded p) _ hfit; first trivial.
  rewrite W64.to_uintK /rejection48_accept /= hpositive odd1 /b2i /= in h.
  by rewrite sigma_rejection48_spec_acceptance hrej h.
qed.

lemma hbw_candidate_spec mode : hbw_mode mode =>
  sigma76_spec (hbw_candidate mode) =
    (hbw_sample mode, (hbw_square mode).`1, (hbw_square mode).`2, W64.one).
proof.
  move=> hm.
  have hr := hbw_candidate_rounding mode hm.
  have hs := hbw_candidate_square mode hm.
  have ha := hbw_rejection_one_accepts (hbw_candidate mode) (hbw_candidate_rejection mode hm).
  smt().
qed.

lemma hbw_candidate_total mode : hbw_mode mode =>
  phoare [SamplerTarget.M.__sample_gauss_sigma76_regs : randp = hbw_candidate mode ==>
    res = (hbw_sample mode, (hbw_square mode).`1, (hbw_square mode).`2, W64.one)] = 1%r.
proof.
  move=> hm; by conseq (sigma76_regs_total_correct (hbw_candidate mode)) => />;
    rewrite (hbw_candidate_spec mode hm).
qed.

lemma hbw_candidate_jazz_total mode (r : BArray8.t) (s : BArray16.t) (a : BArray4.t) :
  hbw_mode mode =>
  phoare [SamplerTarget.M.sample_gauss_sigma76_jazz :
    rp=r /\ sqrp=s /\ acceptedp=a /\ randp=hbw_candidate mode ==>
    res = (BArray8.set64 r 0 (hbw_sample mode),
      BArray16.set64 (BArray16.set64 s 0 (hbw_square mode).`1) 1 (hbw_square mode).`2,
      BArray4.set32 a 0 W32.one)] = 1%r.
proof.
  move=> hm; conseq (sigma76_jazz_total_correct r s a (hbw_candidate mode)) => />.
  by rewrite (hbw_candidate_spec mode hm) /= /W2u32.truncateu32.
qed.
