# Verification scope and remaining obligations

This document records the scope of the function-level theorems. It distinguishes
successful loading of extracted artifacts, KAT success, component theorems, and
complete API correctness.

The [signed-output stage](docs/gaussian-signed-output.md) proves sign bits,
independence from the complete sample-array and square-word state, the signed Gaussian distribution
of actual return observations, and conditional signed32 application.
The complete non-NTT verification, including the new files, passed; exact target
counts and source hashes are recorded in [VALIDATION.md](VALIDATION.md) and the
verification manifest.

The [actual-function Hyperball counterexamples](docs/hyperball-actual-witnesses.md)
prove the results of actual finite consumption, square accumulation, Newton,
scaling, and norm calls on prescribed candidate sequences. All three modes
simultaneously yield an integer radius violation and word acceptance1; reachability
from a concrete SHAKE seed is not included.

The [Hyperball safe input domain](docs/hyperball-safe-domain.md) derives actual
numerical safety from a concrete interval for the initial sum of squares and a
canonical low limb. It does not assume sample/sign arrays or output fit.
The probability of reaching the interval and outer-retry termination are
separate obligations.

<!-- gaussian-payload:overview:start -->
The subsequent [complete accepted-payload and sum-of-squares stage](docs/gaussian-payload-and-squares.md)
jointly determines the visible vector and integer S from the same accepted history
of an iid Gaussian batch. Actual calls/offsets and initial sum of squares 0 yield
the law of the full D=1538·2306·2818 history and an exact probability formula for
the safe-interval event. Zero initialization of samples and signs is a modeling
choice in `hip_initial`; production code initializes only the sum of squares.
The full-array ghost equivalence below is internal to this iid model.
That stage did not include a numerical escape-probability bound, the ideal law
of S, concrete SHAKE, the outer Hyperball retry, or complete API correctness.
<!-- gaussian-payload:overview:end -->

<!-- hyperball-tail:overview:start -->
The [subsequent iid tail bound](docs/hyperball-iid-tail-bound.md) derives
safe-interval escape probabilities <2^-29/2^-44/2^-54 for modes 2·3·5 from
exponential moments of the actual accepted raw squares. It transfers the same
bounds to the acceptance AND excessive integer squared-norm event in a single
iid attempt composing actual Gaussian and numerical helpers. Apart from the
mode, the public endpoints below retain no premises assuming the desired
moments or tail bounds. Acceptance-conditioned probabilities, the complete outer
retry, and SHAKE are excluded; the distinction that zero-initialized sample/sign
arrays are a proof-model choice is retained from the preceding stage.
<!-- hyperball-tail:overview:end -->

## Current theorems

| Theorem file | Representative theorem | Exact scope |
| --- | --- | --- |
| [HyperballTailSpec](theories/HyperballTailSpec.ec) / [RawSquareMomentSpec](theories/RawSquareMomentSpec.ec) | `ht_raw_square`, `ht_weight_plus`, `ht_weight_minus` | Q=2^76; definitions of the implementation's floored raw square, acceptance-weighted expectation, both exponent arguments, and mode-specific numerical bounds |
| [GaussianRawSquare](proofs/GaussianRawSquare.ec) / [GaussianPayloadMoments](proofs/GaussianPayloadMoments.ec) | `gps_square_exact`, `gpm_raw_conditioned_moment` | Exact correspondence between actual payload q=floor(Z²/Q), the raw weighted acceptance probability/denominator, and the accepted-payload moment |
| [RawSquareAcceptance](proofs/RawSquareAcceptance.ec) / [RawSquareIdealMoments](proofs/RawSquareIdealMoments.ec) | `rsa_weighted_upper`, `rsi_ideal_expectation` | Connects bounded actual weighted-acceptance error to an independent Gaussian weighted sum; does not assume that the ideal infinite support is bounded by the implementation's range |
| [GaussianLatticeSum](proofs/GaussianLatticeSum.ec) / [GaussianLatticeMgf](proofs/GaussianLatticeMgf.ec) | Integer Gaussian sum/moment bounds | Convergence of the ideal lattice sum and comparison of exponential moments at rational arguments; no chi-square law for actual S is claimed |
| [GaussianSquareMoments](proofs/GaussianSquareMoments.ec) | `gsm_plus_bound`, `gsm_minus_bound`, `gsm_centered_plus`, `gsm_centered_minus` | Exponential moments of actual accepted q/Q≤10/9+2^-18 and 7/8+2^-18; centered expectations≤3947/4000 and 1963/2000 |
| [HyperballTailCertificate](theories/HyperballTailCertificate.ec) / [HyperballTailCertificateChecks](proofs/HyperballTailCertificateChecks.ec) / [HyperballTailConstants](proofs/HyperballTailConstants.ec) | `ht_factor_plus`, `ht_factor_minus`, `ht_mode_power_bound` | Integer checks of rational seeds, 32 interval squarings, and binary exponentiation, with actual exp interpretation; the sum of the two powers for each of the three modes is <epsilon |
| [IidExponentialTail](proofs/IidExponentialTail.ec) | `iet_iid_exponential_outside` | Two-sided exponential tail bounds from expectation multiplication for finite iid lists and the nonnegative Markov inequality |
| [HyperballIidAttemptSafety](proofs/HyperballIidAttemptSafety.ec) | `hia_unsafe_probability`, `hia_terminates` | Termination of one iid attempt composing the actual Gaussian batch and actual numerical tail, with unsafe joint event⊆event outside the safe input interval |
| [HyperballIidTailCorrectness](proofs/HyperballIidTailCorrectness.ec) | `ht_iid_list_tail`, `ht_iid_square_tail`, `ht_iid_unsafe_acceptance` | Probability of the full raw sum of squares leaving its interval, and of acceptance AND excessive integer norm in one attempt, <2^-29/2^-44/2^-54; the only public premise is the mode; excludes acceptance-conditioned probabilities, outer retries, and SHAKE |
| [GaussianPayloadSpec](theories/GaussianPayloadSpec.ec) / [GaussianPayloadEncoding](proofs/GaussianPayloadEncoding.ec) | `gpd_pack_magnitude`, `gpd_pack_square`, `gpd_accepted_ll`, `gpd_scan_selected` | Lossless integer encoding of actual samples and raw squares, q≤2^84−1, acceptance probability≥1/7, and conditional-distribution mass 1; required complete accepted lists and their lengths |
| [GaussianPayloadBufferSpec](theories/GaussianPayloadBufferSpec.ec) / [GaussianPayloadBufferPath](proofs/GaussianPayloadBufferPath.ec) | `gpb_actual_projection`, `gpb_history_projection`, `gpb_buffer_terminates` | Under gib_bounds, equivalence of all three return arrays between the actual iid buffer and the ghost-history model; projection of the entire history, including dummies, and termination |
| [GaussianPayloadTrace](proofs/GaussianPayloadTrace.ec) / [GaussianPayloadBufferTrace](proofs/GaussianPayloadBufferTrace.ec) | `gpt_consume`, `gpt_buffer_correct`, `gpt_buffer_total` | Connects visible values and the integer sum of raw squares from actual consumption and complete-buffer execution to the same history, under the preceding accumulation budget and total acceptances≤2818; canonical form, bounds, and termination |
| [GaussianPayloadKernel](proofs/GaussianPayloadKernel.ec) / [GaussianPayloadEventLaw](proofs/GaussianPayloadEventLaw.ec) | `gpk_refill_event`, `gpk_initial_event`, `gpe_history_law` | Exact completion distribution with known carry bytes fixed; complete accepted history=dlist gpd_accepted n for 0≤n≤512 |
| [GaussianPayloadDraw](proofs/GaussianPayloadDraw.ec) | `gpd_buffer_draw` | Equivalence between the entire-history projection of the actual buffer ghost and drawing an independent accepted-payload list; no conditions on initial arrays |
| [HyperballIidPayloadSpec](theories/HyperballIidPayloadSpec.ec) / [HyperballIidPayloadBatch](proofs/HyperballIidPayloadBatch.ec) | `hip_batch_history_law`, `hip_payload_observe_total` | Law of the complete D-element history from mode-specific requests/offsets and initial sum of squares 0; visible vector and S from that same history, and canonical form; zero initialization of samples/signs is a modeling choice |
| [HyperballIidSquareLaw](proofs/HyperballIidSquareLaw.ec) | `hips_actual_joint_law`, `hips_actual_square_law`, `hips_actual_safe_probability`, `hips_actual_terminates` | Joint visible-vector/S distribution of the explicit iid batch of actual calls, raw sum of squares including both dummies, exact safe-interval probability identity, and probability-1 termination; excludes a numerical tail bound |
| [SamplerConstants](proofs/SamplerConstants.ec) | `cdt83_hi_matches_reference`, `cdt83_lo_matches_reference`, `approx_exp_matches_reference` | Connects CDT and polynomial constants independently generated from the pinned C source to the Jasmin specification |
| [CDTCorrectness](proofs/CDTCorrectness.ec) | `sample_gauss83_jazz_total`, `sample_gauss83_max83_total` | Number of the 166 thresholds strictly below the input integer; range and output 166 at maximum input; probability-1 termination and result |
| [CDTTermination](proofs/CDTTermination.ec) | `sample_gauss83_ll` | Termination of the two actual bounded loops |
| [CDTDistribution](proofs/CDTDistribution.ec) | `cdt_distribution_mass`, `uniform_cdt_law` | Exact output probabilities for strict threshold comparison under uniform integer input: each interval's length/M; boundary +1, support, and termination |
| [CDTDistributionBridge](proofs/CDTDistributionBridge.ec) | `uniform83_jasmin_law`, `uniform83_jasmin_mass`, `uniform83_jasmin_endpoint` | Probabilistic experiment passing uniform 83-bit input to the actual Jasmin CDT; exact distribution and termination, support 0…166, Pr[166]=2^-83 |
| [HalfGaussianProperties](proofs/HalfGaussianProperties.ec) | `hg16_pmf_sum`, `hg16_distr_ll`, `hg16_normalizer_truncation256` | Implementation-independent infinite normalization, total probability 1, and tail bound for rho(k)=exp(-k²/512), k≥0 |
| [ExpIntervalCorrectness](proofs/ExpIntervalCorrectness.ec) / [CDTGaussianEnclosure](proofs/CDTGaussianEnclosure.ec) | `ei_square_q_sound`, `ei_weights_sound`, `gi_normalizer_interval`, `gi_pmf_interval` | Soundness of rational enclosures and outward-rounding certificates for the actual real exponential; numerical intervals for the infinite normalization denominator and each target probability; checked integer certificates discharge concrete numerical obligations |
| [CDTGaussianApproximation](proofs/CDTGaussianApproximation.ec) | `cdt83_half_gaussian_statistical_distance`, `uniform83_jasmin_half_gaussian_error` | Statistical distance <2^-78 between the actual Jasmin CDT's uniform 83-bit input experiment and the official nonnegative Gaussian target (σ=16); the same probability-difference bound for any output set |
| [FixedPointCorrectness](proofs/FixedPointCorrectness.ec) | `smulh48_jazz_total_correct`, `smulh48_jazz_signed_correct`, `approx_exp_jazz_reference_correct` | Ceiling result modulo 2^64 for all word inputs; signed results require explicit fit premises; C-derived degree-10 word Horner computation |
| [SigmaExpInputBounds](proofs/SigmaExpInputBounds.ec) | `sigma_exp_argument_bound`, `sigma_exp_argument_two_thirds` | Actual exponent argument uint(xi)≤183103063064576 and 3·uint(xi)≤2·2^48 for every 26-byte input; discharges subtraction, merging, and rounding-range obligations |
| [ApproxExpWordCorrectness](proofs/ApproxExpWordCorrectness.ec) | `ae_intermediate_signed64`, `ae_rounding_error3`, `ae_sigma_approx_exp_total` | Connects integer ceil-Horner to actual word execution; signed64 fit of every Horner prefix and ceiling-multiplication result, final unsigned interpretation; rounding error relative to the polynomial is 0…3/2^48 |
| [Bernstein10Correctness](proofs/Bernstein10Correctness.ec) / [ApproxExpCertificateChecks](proofs/ApproxExpCertificateChecks.ec) | `bernstein10_checked_nonnegative`, `aec_upper_0_identity` and related theorems | Basis conversion and signs of integer certificates, and six interval inequalities for the actual coefficient polynomial; checks 66 control coefficients |
| [ExponentialGridComparison](proofs/ExponentialGridComparison.ec) / [ApproxExpPolynomialBound](proofs/ApproxExpPolynomialBound.ec) | `eg_exp_grid_abs`, `approx_exp_polynomial_error` | Error≤24/2^48 between the actual coefficient polynomial and exp(-x/2^48) on the integer input grid; certificates discharge analytic recurrence conditions |
| [ApproxExpNumericalCorrectness](proofs/ApproxExpNumericalCorrectness.ec) | `approx_exp_signer_numerical_total`, `sigma76_approx_exp_numerical_total` | Absolute error≤27/2^48<2^-43 between the actual Jasmin normalized output and the real exponential, and termination; no separate range/fit premises for any sigma76 input |
| [Rejection48Correctness](proofs/Rejection48Correctness.ec) / [SigmaRejection48Bridge](proofs/SigmaRejection48Bridge.ec) | `rejection48_word_probability`, `sigma_rejection48_actual_probability` | Exact even comparison, saturation, and actual rounded-zero probability for uniform 48-bit rejection input; connected to the actual sigma procedure call |
| [SigmaExpAcceptanceCorrectness](proofs/SigmaExpAcceptanceCorrectness.ec) | `sigma_exp_acceptance_error`, `sigma_exp_acceptance_error_strict` | Difference≤α·28/2^48<2^-43 between the acceptance probability of an actual sigma call with fixed candidate bytes and α(rounded)·exp(-uint(xi)/2^48); the experiment explicitly draws uniform 48-bit rejection input |
| [SigmaSquareExact](proofs/SigmaSquareExact.ec) / [SigmaRawExponentCorrectness](proofs/SigmaRawExponentCorrectness.ec) | `sigma_square_word_exact`, `sigma_raw_exponent_exact`, `sigma_raw_exponent_error` | Integer semantics of actual square limbs and xi=floor((y(y+2^73x)+2^104)/2^105) for every 26-byte input; normalized error≤2^-49 relative to the exponent before rounding |
| [SigmaRawDensityIdentity](proofs/SigmaRawDensityIdentity.ec) | `sr_gaussian_weight_identity`, `sr_gaussian_density_ratio` | The unnormalized weight of the independent nonnegative Gaussian σ=16 multiplied by exp(-E) equals the unnormalized σ=2^76 Gaussian weight at Z=y+2^72x |
| [SigmaRawZeroCorrectness](proofs/SigmaRawZeroCorrectness.ec) / [SigmaRawNoiseSpec](theories/SigmaRawNoiseSpec.ec) | `sr_zero_tests_differ`, `sr_zero_factor_difference`, `sr_noise_mismatch_probability` | Rounded-zero and raw-zero differ exactly when x=0 and 1≤y<32768; exceptional probability under uniform 72-bit noise and maximal half-correction effect<2^-58 |
| [SigmaRawAcceptanceCorrectness](proofs/SigmaRawAcceptanceCorrectness.ec) | `sr_actual_acceptance_error`, `sr_actual_acceptance_regular` | Difference≤57/(2·2^48)+exception indicator/2 between actual acceptance probability and the raw Gaussian acceptance formula for a fixed candidate; <2^-43 outside the exception |
| [ExponentialLipschitz](proofs/ExponentialLipschitz.ec) / [FiniteExpectationError](proofs/FiniteExpectationError.ec) | `exp_neg_lipschitz`, `finite_expectation_error` | Exponential-error propagation on nonnegative reals; composes pointwise error and exceptional mass of a finite distribution into average error |
| [SigmaNoise72Bridge](proofs/SigmaNoise72Bridge.ec) / [SigmaRawAverageCorrectness](proofs/SigmaRawAverageCorrectness.ec) | `sigma_noise72_actual_probability`, `sr_average_acceptance_error_strict` | Passes fixed CDT bytes, independent uniform 72-bit noise, and 48-bit rejection input to actual sigma; difference<29/2^48<2^-43 between average raw Gaussian acceptance and actual acceptance probability |
| [SigmaRoundedOutputCorrectness](proofs/SigmaRoundedOutputCorrectness.ec) / [SigmaCDT83Patch](proofs/SigmaCDT83Patch.ec) | `sj_actual_rounding`, `sj_cdt83_patch_count`, `sj_cdt83_expectation` | Connects actual unsigned output to floor((y+2^72x+32768)/65536); CDT law and expectation transformation for actual 83-bit byte input |
| [SigmaJointAttemptBridge](proofs/SigmaJointAttemptBridge.ec) / [SigmaJoint203Bridge](proofs/SigmaJoint203Bridge.ec) | `sigma_joint_noise72_law`, `sigma_joint203_law`, `sigma_joint203_ll` | Experiments returning both the sample and acceptance bit from an actual sigma call; joint probability for every output set under independent uniform 83+72+48 bits, and single-attempt termination |
| [DistributionExpectationDistance](proofs/DistributionExpectationDistance.ec) / [SigmaJointKernelCorrectness](proofs/SigmaJointKernelCorrectness.ec) | `distribution_expectation_distance`, `sj_noise_kernel_range`, `sj_kernel_actual` | Expectation difference of [0,1] kernels over infinite support≤statistical distance; connects the independent Gaussian acceptance formula and mathematical rounding to actual arrays |
| [SigmaJointFixedCorrectness](proofs/SigmaJointFixedCorrectness.ec) | `sj_point_error`, `sj_fixed_joint_error` | Applies the output-set indicator to pointwise error first; joint acceptance-and-output probability error≤57/(2·2^48)+32767/2^73 for fixed CDT |
| [SigmaJointIdealCorrectness](proofs/SigmaJointIdealCorrectness.ec) / [SigmaJointCorrectness](proofs/SigmaJointCorrectness.ec) | `sj_ideal_joint_law`, `sj_joint_output_error`, `sj_joint_output_error_strict` | Joint acceptance-and-output probability difference<29/2^48+2^-78<30/2^48<2^-43 between the actual 203-bit experiment and an independent infinite-Gaussian-CDT experiment with unbounded integer rounding; every output set, without extra fit/accuracy premises |
| [SigmaAcceptanceLowerBound](proofs/SigmaAcceptanceLowerBound.ec) | `sc_actual_point_lower`, `sc_actual_acceptance_lower`, `sc_ideal_acceptance_lower` | Acceptance probability≥1/7 both with fixed candidates and uniform 48-bit rejection input and in the complete 203-bit attempt; ideal acceptance probability≥1/8; no additional range/positivity premises |
| [SigmaConditionalActual](proofs/SigmaConditionalActual.ec) / [SigmaConditionalIdeal](proofs/SigmaConditionalIdeal.ec) | `sc_actual_conditioned_law`, `sc_ideal_conditioned_law` | Connects event probabilities of native dcond and integer-projection distributions to joint probability÷acceptance probability of the corresponding actual/ideal procedures; retains ideal infinite support and unbounded integer outputs |
| [ConditionalRatioBound](proofs/ConditionalRatioBound.ec) | `conditional_ratio_error_lower` | Normalization error≤2δ/l from numerator/denominator errors≤δ and acceptance lower bound l>0; does not assume actual and ideal denominators are equal |
| [SigmaConditionalCorrectness](proofs/SigmaConditionalCorrectness.ec) | `sc_conditioned_distributions_correct`, `sc_conditioned_event_error`, `sc_conditioned_sdist_strict` | Conditional accepted-magnitude distributions of the actual and previous ideal experiments have mass 1; every event error and statistical distance≤16·(29/2^48+2^-78)<2^-39; numerical lower bounds discharge positivity premises |
| [Gaussian76Properties](proofs/Gaussian76Properties.ec) | `g76_rho_summable`, `g76_normalizer_ge1`, `g76_distr_mu1`, `g76_distr_ll` | Convergence and independent normalization of the infinite sum rho(k)=exp(-k²/2^153) over all integers; independent Gaussian probability masses, mass 1, and infinite support |
| [GaussianBlockReindex](proofs/GaussianBlockReindex.ec) / [Gaussian76Kernel](proofs/Gaussian76Kernel.ec) | `gb_block_sum`, `g76_full_contribution` | Quotient/remainder block-sum reindexing under absolute convergence and support conditions; Gaussian-weight cancellation for every ideal x≥0 and the exact factor 1/(N·H16) |
| [Gaussian76Folding](proofs/Gaussian76Folding.ec) / [Gaussian76Rounding](proofs/Gaussian76Rounding.ec) | `g76_accept_weight_sum`, `g76_rounded_event_law`, `g76_rounded_mass`, `g76_rounded_zero_ties` | Absolute-value weights counting zero once and positive magnitudes twice, with rounding-interval PMFs; sum of raw acceptance weights=Z/2; ±32768→1 |
| [Gaussian76Identification](proofs/Gaussian76Identification.ec) | `g76_ideal_conditioned_eq`, `g76_gaussian_mass`, `g76_actual_gaussian_correct`, `g76_actual_rounded_mass_error` | Exact equivalence between the existing ideal conditional distribution and the explicitly defined rounded absolute value of an integer Gaussian; statistical distance<2^-39 from actual accepted magnitudes, and interval-sum error for each output |
| [GaussianRetryCore](proofs/GaussianRetryCore.ec) / [GaussianRetryAttempt](proofs/GaussianRetryAttempt.ec) / [GaussianRetryActual](proofs/GaussianRetryActual.ec) | `gr_retry_total`, `gr_actual_pair_equiv`, `gr_actual_retry_law`, `gr_actual_retry_ll` | Connects actual attempt distributions for both acceptance and rejection; probability-1 termination and the exact first-accepted-value conditional distribution for repeated actual calls with independent uniform 83·72·48-bit inputs |
| [GaussianRetryTail](proofs/GaussianRetryTail.ec) / [GaussianRetryBatchTail](proofs/GaussianRetryBatchTail.ec) | `gaussian_retry_tail_bound`, `grbt_prefix_shortfall_1m7`, `grbt_all_prefix_shortfall_limit` | Probability that all t independent attempts reject≤(6/7)^t; probability of fewer than n acceptances in n·t attempts≤n·(6/7)^t; shortfall probability→0 over all finite prefix lengths |
| [GaussianRetryBatch](proofs/GaussianRetryBatch.ec) / [GaussianBatchDistance](proofs/GaussianBatchDistance.ec) / [GaussianRetryBatchCorrectness](proofs/GaussianRetryBatchCorrectness.ec) | `gra_batch_joint_law`, `gra_batch_256_gaussian`, `gra_batch_257_gaussian`, `gra_prefix256_law` | The full accepted list from repeated actual attempt calls equals an independent list from the conditional distribution; Gaussian distance<2^-31 for 256 and <257·2^-39 for 257; first-256 projection after generating the last value |
| [GaussianRetryInputs](proofs/GaussianRetryInputs.ec) / [GaussianRetryPrefixCorrectness](proofs/GaussianRetryPrefixCorrectness.ec) | `gr_candidate_stream_pairs_iid`, `gr_prefix_failure_law`, `gr_block_prefix_failure_limit` | Connects canonical 26-byte encoding of 203-bit candidates to actual word-event sequences and acceptance counts; probability of an insufficient iid prefix→0 at actual blockwise candidate counts; no uniform infinite function or SHAKE independence is assumed |
| [GaussianRetryRank](proofs/GaussianRetryRank.ec) / [GaussianRetryConsumerTotal](proofs/GaussianRetryConsumerTotal.ec) / [GaussianRetryBufferTotal](proofs/GaussianRetryBufferTotal.ec) | `grr_rank_step_bounded`, `gs_progress_consume_total` | Constructs a decreasing quantity from a finite maximum compatible block index; exact progress conditions and probability-1 termination of the actual bounded consumer |
| [GaussianRetryStreamBridge](proofs/GaussianRetryStreamBridge.ec) / [GaussianRetryStreamTermination](proofs/GaussianRetryStreamTermination.ec) | `gr_sample_gauss_N_prefix_total`, `gr_prefix_result_dummy`, `gr_prefix_result_squares` | Termination of the actual complete signing buffer and exact first 256 values, sign copy, sum of squares including the 257th dummy, and frame, under a sufficient finite prefix of the concrete SHAKE stream and the existing offset/limb premises |
| [MixedRadixUniform](proofs/MixedRadixUniform.ec) / [GaussianUnusedBits](proofs/GaussianUnusedBits.ec) / [GaussianUniformBytes](proofs/GaussianUniformBytes.ec) | `mru_join_uniform`, `gub_sigma76_spec`, `gbc_candidate_sigma_law`, `gbc_candidate_observer_law` | Canonical 203-bit projection and exact distribution of uniform 26-byte input; clearing the five unused high bits preserves all four returned words for every input |
| [GaussianBlockSampling](proofs/GaussianBlockSampling.ec) | `gbs_joint_law`, `gbs_total` | Termination and the complete independent accepted-list law for the actual probabilistic loop processing positive-sized candidate batches in order |
| [GaussianByteCarryDistribution](proofs/GaussianByteCarryDistribution.ec) / [GaussianIidKernel](proofs/GaussianIidKernel.ec) | `gbc_fixed_tail_refill`, `gik_refill_event`, `gik_initial_event` | Completion distribution with already known remaining bytes fixed; exact expectation invariants for the new 136 bytes and initial 6,664 bytes |
| [GaussianIidBufferSpec](theories/GaussianIidBufferSpec.ec) / [GaussianIidBufferPath](proofs/GaussianIidBufferPath.ec) | `gib_actual_functional` | Equivalence of the complete return tuples of the iid buffer model calling actual sign-copy, carry, and consumer functions and its list representation; no initial square-word condition beyond `gib_bounds` |
| [GaussianIidVisible](proofs/GaussianIidVisible.ec) / [GaussianIidStep](proofs/GaussianIidStep.ec) | `giv_consume_fold`, `gis_initial`, `gis_refill` | Correspondence between the physical visible prefix and the list of magnitudes accepted in order; does not read the unrecorded dummy of a request for 257 as a visible value |
| [GaussianIidInitial](proofs/GaussianIidInitial.ec) / [GaussianIidNormalization](proofs/GaussianIidNormalization.ec) | `gib_initial_law`, `gid_functional_uniform` | Exact equivalence between drawing the initial 49 blocks and drawing one uniform 6,664-byte array |
| [GaussianIidProgress](proofs/GaussianIidProgress.ec) / [GaussianIidTermination](proofs/GaussianIidTermination.ec) | `gip_refill_progress`, `git_functional_lossless` | After any fixed remaining bytes, an intact candidate in the new block guarantees progress probability≥1/7; probability-1 termination without a sufficient-prefix premise |
| [GaussianIidEventLaw](proofs/GaussianIidEventLaw.ec) / [GaussianIidDistribution](proofs/GaussianIidDistribution.ec) | `gii_actual_correct`, `gii_actual_joint_law`, `gii_actual_gaussian_event` | Under `gib_bounds`, probability-1 termination of the iid buffer model with actual calls, exact independent joint distribution of the visible 256 values for requests of 256/257, and Gaussian distance<2^-31 |
| [GaussianSignedTarget](proofs/GaussianSignedTarget.ec) | `gst_target_eq`, `gst_round_signed_ties`, `gst_target_zero_mass`, `gst_target_symmetry` | Independent signed rounding target=law obtained by applying fair signs to the rounded absolute-value distribution; preserves zero mass, ±32768→±1, and symmetry |
| [GaussianSignBits](proofs/GaussianSignBits.ec) | `gsb_uniform256`, `gsb_result_bits_nth`, `gsb_hb_sign_bit` | 32 uniform bytes→256 fair bits; connects the actual copied window's low-bit-first order to global sign index 8·signoff+i |
| [GaussianSignedVector](proofs/GaussianSignedVector.ec) | `gsv_actual_law`, `gsv_ideal_law`, `gsv_actual_gaussian` | Exact iid law of 256 signed integers combining sign and magnitude lists from an independent product distribution, and distance<2^-31 from the signed Gaussian target |
| [IndependentSignSampling](proofs/IndependentSignSampling.ec) | `IndependentSign.rectangle`, `IndependentSign.output_marginal` | Event-probability multiplication law for drawing independent signs after an arbitrary computation; no termination premise for the computation, and preservation of its output marginal requires only mass 1 of the sign distribution |
| [GaussianSignIndependence](proofs/GaussianSignIndependence.ec) | `gsi_actual_redraw`, `gsi_sign_state_independent` | Separates the sign window from the entire sample-array and square-word state in the explicit iid byte model; equivalence to redrawing fair signs while preserving that state |
| [GaussianSignedCorrectness](proofs/GaussianSignedCorrectness.ec) | `gsc_actual_joint_law`, `gsc_actual_signed_law`, `gsc_actual_gaussian_event`, `gsc_actual_correct` | Under `gib_bounds`, combines actual returned signs and visible magnitudes, with the law of 256 signed ±W64.to_uint observations and distance<2^-31 |
| [HyperballSignedScale](proofs/HyperballSignedScale.ec) | `hss_scalar_word_total`, `hss_coeff_signed_fit`, `hss_scale_samples_signed_total` | Exact word semantics of actual scalar/vector scaling signs; signed32 interpretation at coordinates with rounded magnitude≤2147483647; local→global connection requires sample_offset=8·signoff |
| [SigmaCorrectness](proofs/SigmaCorrectness.ec) | `sigma76_regs_total_correct`, `sigma76_jazz_total_correct` | For every 26-byte input, `(rounded, square_low, square_high, accepted)` matches the pure word specification, and execution terminates |
| [SigmaRoundingCorrectness](proofs/SigmaRoundingCorrectness.ec) | `sigma76_spec_rounding`, `sigma76_regs_rounding_correct`, `sigma76_jazz_rounding_correct` | Actual rounded output equals the integer rounding formula; byte assembly, shifts, and the final sum do not wrap; includes maximum CDT value 166 |
| [GaussianConsumerCorrectness](proofs/GaussianConsumerCorrectness.ec) | `sample_gauss_jazz_bounded_total`, `sample_gauss_jazz_normalized_total` | For request `n≤512` and input-byte count `b≤8192`, acceptance count `c≤n`, `26c≤b`, and preservation outside the requested output range; low sum-of-squares limb in `[0,2^48)`; finite termination |
| [GaussianTraceCorrectness](proofs/GaussianTraceCorrectness.ec) | `sample_gauss_jazz_trace_total_correct`, `sample_gauss_jazz_packed_trace_total` | The actual finite consumer's complete return tuple equals the specification fold over 26-byte candidates; stops when the request is met, including temporary writes of rejected candidates, dummy omission, and word sum of squares |
| [GaussianTraceProperties](proofs/GaussianTraceProperties.ec) | `gauss_trace_prefix_count_exact`, `gauss_trace_prefix_accepted_sequence`, `gauss_trace_prefix_full_stable` | Count and order of the first `n` candidates filtered by the acceptance bit; fold stability after the requested count is reached |
| [SigmaSquareBounds](proofs/SigmaSquareBounds.ec) | `sigma76_square_high_bound` | Actual square-high unsigned value `<2^38` for every 26-byte input; not an error theorem relative to a real square |
| [GaussianAccumulatorCorrectness](proofs/GaussianAccumulatorCorrectness.ec) | `gauss_trace_prefix_uint_sums`, `gauss_trace_result_canonical_both_exact` | Independent mod `2^64` sums of each raw limb; if both initial limbs are `<2^48` and `n≤512`, final `low + 2^48×high` equals the accepted candidates' limb sum as an integer |
| [GaussianOffsetBridge](proofs/GaussianOffsetBridge.ec) | `sample_gauss_at_trace_total_correct` | Exact tuple equivalence and termination between actual signer `__sample_gauss_at` and the input/output-window specification; `bo+b≤8192`, `oo+n≤4096`; preservation outside the requested region |
| [GaussianSequenceCorrectness](proofs/GaussianSequenceCorrectness.ec) | `sample_gauss_jazz_sequence_total`, `sample_gauss_jazz_accumulator_exact_total`, `sample_gauss_at_sequence_total` | Acceptance counts and stored acceptance order for the public finite consumer and actual signer offset consumer; exact integer sum of squares for the public consumer |
| [GaussianValueCorrectness](proofs/GaussianValueCorrectness.ec) | `sample_gauss_at_value_total` | Transfers the integer-sum theorem to the actual signer offset consumer's returned square buffer; both initial limbs `<2^48`, request `n≤512`, and valid windows |
| [GaussianStreamAccumulator](proofs/GaussianStreamAccumulator.ec) | `gauss_trace_result_stream_accumulator`, `sample_gauss_at_stream_accumulator_correct`, `gauss_stream_finite_partitions` | Preserves inter-call accumulation and overflow headroom through an integer budget based on cumulative acceptances `≤512`; does not require the high limb to be 48-bit after every call |
| [GaussianStreamSequence](proofs/GaussianStreamSequence.ec) | `gauss_stream_events_append_available`, `gauss_visible_output_concat`, `sample_gauss_at_dummy_last_total` | Splitting and joining candidate sequences from a continuous byte function; preserves acceptance order and the same dummy flag, and the actual offset consumer's dummy slot |
| [GaussianStreamBuffer](proofs/GaussianStreamBuffer.ec) | `gs_stream_advance`, `gs_refill_segment`, `gs_copy_signs_total` | Correspondence of candidate counts and remaining bytes for the initial 49 blocks and refills; connects continuous-stream buffer segments; actual 32-byte sign copy, frame, and termination |
| [GaussianStreamSpec](theories/GaussianStreamSpec.ec) | `gs_selected_complete_stable`, `gs_stream_result_unique` | The first `n` accepted results stabilize after a sufficient candidate prefix; the entire return tuple satisfying the same initial values and stream is unique |
| [GaussianStreamComposition](proofs/GaussianStreamComposition.ec) | `gs_progress_consume`, `gs_progress_consume_correct` | Connects an actual offset-consumer call to the next candidate segment of the continuous stream; preserves acceptance count, stored order, dummy handling, output frame, and the exact sum-of-squares invariant |
| [GaussianStreamCorrectness](proofs/GaussianStreamCorrectness.ec) | `sample_gauss_N_full_at_correct` | If actual `_sf_sample_gauss_N_full_at` terminates, it returns the same result as the first `n` accepted candidates in the seed/nonce word-SHAKE stream; includes all initial 49 blocks, sign copying, and repeated refills; Hoare partial correctness for `n=256/257`, valid offsets, and both initial limbs `<2^48` |
| [GaussianRefillCorrectness](proofs/GaussianRefillCorrectness.ec) | `gauss_carry_total`, `gauss_carry_squeeze_layout` | Actual carry preserves remaining bytes and terminates, accounting for the first block's sign prefix; finite buffer layout combining carry and block-serialization contracts |
| [SHAKEBlockCorrectness](proofs/SHAKEBlockCorrectness.ec) | `keccakf1600_word_total`, `squeeze256_word_total` | Correspondence to the actual signer's 24-round word permutation, 136-byte output, external-region preservation, and termination; output offset `0…8056` |
| [SHAKESeedInitCorrectness](proofs/SHAKESeedInitCorrectness.ec) | `seed_init_total`, `shake_block_stream_total` | Actual initialization equals the entire 200-byte state for a 64-byte seed, low 16 nonce bits, and domain/padding, and terminates; each squeeze matches the exact next 136 bytes of the word stream |
| [HyperballGaussianBounds](proofs/HyperballGaussianBounds.ec) | `hb_sigma76_square_high_bound`, `hb_cumulative_canonical`, `hb_sample_gauss_N_full_at_correct` | Strengthens the square-high bound to `<2^36`; accumulating at most 2,818 accepted candidates from zero preserves both initial limbs `<2^48`; connects the premises of multiple Gaussian calls |
| [HyperballFixedPointCorrectness](proofs/HyperballFixedPointCorrectness.ec) | `hb_newton_total`, `hb_half_round_integer_total`, `hb_mul_rnd13_signed_fit` | Exact word computation and termination of multiplication, conditional signs, normalization, initial estimate, and six Newton iterations; integer ceiling-halving for canonical low, and signed W32 semantics under explicit fit |
| [HyperballScaleCorrectness](proofs/HyperballScaleCorrectness.ec) / [HyperballNormCorrectness](proofs/HyperballNormCorrectness.ec) | `hb_scale_samples_total`, `hb_scale_and_check_total` | Global sample/sign indices, output partition/preservation, mod `2^64` sum of signed32 squares, unsigned acceptance decision, and termination; integer norm interpretation is a separate conditional theorem |
| [HyperballBatchCorrectness](proofs/HyperballBatchCorrectness.ec) / [HyperballHistoryCorrectness](proofs/HyperballHistoryCorrectness.ec) | `hb_batch_call_correct`, `hb_history_append`, `hb_history_finish` | The first two calls accept 257 candidates and the rest 256; exact accumulation and actual-call connection; connects previous attempts' rejection history to the first accepted result and counters |
| [HyperballByteCorrectness](proofs/HyperballByteCorrectness.ec) | `hyperball_b_raw_array_total` | Actual return array equals the first seed-SHAKE byte at the final nonce; termination |
| [HyperballCorrectness](proofs/HyperballCorrectness.ec) | `hyperball_full_correct`, `hyperball_mode2_correct`, `hyperball_mode3_correct`, `hyperball_mode5_correct` | Hoare partial correctness of the actual complete function and modes 2·3·5 against the word specification; Gaussian batches, fixed-point scaling, modular norm, retries, and final byte/counter; mode constants independently generated from C |
| [HyperballResultUniqueness](proofs/HyperballResultUniqueness.ec) / [HyperballResultProperties](proofs/HyperballResultProperties.ec) | `hb_result_unique`, `hb_result_modular_norm`, `hb_result_integer_norm` | Uniqueness of the full return value independently of unused scratch regions and block witnesses, output preservation, and modular norm; mathematical norm is connected under `<2^64` or explicit coordinate bounds |
| [HyperballSafeSpec](theories/HyperballSafeSpec.ec) / [HyperballSafeConstants](proofs/HyperballSafeConstants.ec) | `hbs_mode_certificate`, `hbs_initial_numeric_bound`, `hbs_center_good` | Q=2^76, canonical input S∈[3D/4,5D/4]·Q; certificates for mode-specific upper bounds and positive initial differences, and a nonempty interval |
| [HyperballMulBounds](proofs/HyperballMulBounds.ec) | `hmb_mul_floor_bounds`, `hmb_mul_error`, `hmb_square_floor` | Integer error and normalization of actual multiplication/squaring for operands low<2R,value≤2^88; checks masked-shift wrapping and required headroom |
| [HyperballPositiveArithmetic](proofs/HyperballPositiveArithmetic.ec) | `hpa_sub_exact`, `hpa_threehalves_exact`, `hpa_signed_mul_positive` | Exact positive difference retaining the initial subtraction's noncanonical low<2R; connects the correction term and positive path of signed multiplication |
| [HyperballNewtonBarrier](proofs/HyperballNewtonBarrier.ec) | `hnb_error_bound`, `hnb_z_bound` | Propagation of three rounding errors and an integer cubic upper bound; one-step range preservation absorbing a margin of 256 high-precision units |
| [HyperballSafeNewton](proofs/HyperballSafeNewton.ec) | `hbs_safe_newton`, `hbs_safe_newton_total` | Derives bounds on the initial state and six updates, final canonical form, and termination of the actual Newton call from hbs_good; no output-range premise |
| [HyperballSafeScale](proofs/HyperballSafeScale.ec) | `hsa_mode_scale_bound`, `hsa_rnd13_bound`, `hsa_scale_result_safe` | Reciprocal upper bound→scale≤2^85→M≤2^26 for every W64 sample; signed32 and norm safety for arbitrary signs, and the exact integer acceptance decision |
| [HyperballSafeCorrectness](proofs/HyperballSafeCorrectness.ec) | `hsc_total`, `hsc_full_magnitude`, `hsc_accepted_radius_total` | From the mode and input hbs_good alone, termination of actual numerical execution, coefficient bounds, N<2^64, exact norm word, and acceptance iff the radius condition; no sample/sign restrictions or output-fit premises |
| [HyperballWitnessSpec](theories/HyperballWitnessSpec.ec) / [HyperballWitnessArithmetic](proofs/HyperballWitnessArithmetic.ec) | `hbw_sum_exact`, `hbw_fixture_norm` | Definitions of inputs and expected observations; mode-specific integer sums, remainders, and bounds; defining expectations does not assume execution results |
| [HyperballWordEvaluation](proofs/HyperballWordEvaluation.ec) | `hwe_mul48`, `hwe_mulu`, `hwe_norm` | Integer div/mod expressions preserving input/output word wrapping; no premises requiring canonical initial low or positive high |
| [HyperballWitnessCandidate](proofs/HyperballWitnessCandidate.ec) | `hbw_candidate_spec`, `hbw_candidate_total` | Actual CDT, sample, square limbs, and acceptance1 computation on fixed 26-byte input, and termination of the actual sigma call |
| [HyperballWitnessSampling](proofs/HyperballWitnessSampling.ec) | `hbw_sampling_total`, `hbw_sampling_correct` | Actual finite-consumer calls 257/257/256…; active samples, signs0, exact raw sum of squares including both unstored dummies, and termination |
| [HyperballWitnessNewton](proofs/HyperballWitnessNewton.ec) | `hbw_newton_exact`, `hbw_scale_exact`, `hbw_magnitude_overflow` | Exact word values of initial subtraction, six updates, scale, and coefficients; negative interpretation of the computed initial high and M>2^31−1 |
| [HyperballWitnessNorm](proofs/HyperballWitnessNorm.ec) | `hbw_scale_and_check_repeated_total`, `hbw_actual_norm_total` | Exact coefficient prefix, remainder, and acceptance1 of actual scale/norm calls, and the returned array's large integer norm; numerical theorems discharge scalar premises |
| [HyperballWitnessExecution](proofs/HyperballWitnessExecution.ec) / [HyperballWitnessReplay](proofs/HyperballWitnessReplay.ec) | `hbwr_total`, `hbwr_accepted_outside_radius_total` | Termination, actual acceptance1, and radius violation for a prescribed-candidate execution taking only the mode; composes actual helpers without intermediate expected-value premises. Excludes SHAKE and the entire seeded path |
| [HyperballNormBoundary](proofs/HyperballNormBoundary.ec) | `hyperball_mode{2,3,5}_prescribed_norm_boundary` | Arithmetic theorem checking the integer sum of squares, 64-bit remainder, and bound comparison for a constructed coordinate vector; no claim of reachability from an actual SHAKE seed |
| [SigningSamplerBridge](proofs/SigningSamplerBridge.ec) | `signer_cdt83_total_correct`, `signer_smulh48_total_correct`, `signer_approx_exp_reference_total_correct`, `signer_sigma76_total_correct` | Transfers the preceding CDT, ceiling, Horner, and single-attempt results to internal functions of actual mode 2/3/5 signing extractions |
| [NTTCorrectness](proofs/NTTCorrectness.ec) | `target_poly_ntt_jazz_total`, `target_poly_invntt_jazz_total`, `target_poly_invntt_jazz_total18` | Correspondence to `NTTFullSpec.full_ntt/full_invntt` and termination under input coefficient ranges and documented arithmetic assumptions; includes the inverse transform's Montgomery factor |
| [ApiBoundaryCorrectness](proofs/ApiBoundaryCorrectness.ec) | `api_copy_addr_to_addr_backward_correct`, `api_zero_raw_len64_correct` | Original-byte copying, zero initialization, and frame under canonical/no-wrap addresses and safe alias conditions; the general `_api_prepare_pre_raw` result is limited to a source helper not currently used |
| [ProductionApiCorrectness](proofs/ProductionApiCorrectness.ec) | `production_sf_prepare_pre_raw_total_correct`, `production_sign_backward_copy_total_correct`, `production_verify_zero_total_correct` | Correctness and termination of the actually called signer-context helper, Sign backward copy, and Verify zero initialization |

For deterministic functions, theorems of the form `phoare [...] = 1` guarantee
both termination and the result under their premises. They are not interpreted
as theorems about random-input distributions or the success probability of a
complete signature operation. CDT premises in intermediate composition results
such as `sigma76_from_cdt_contract` are discharged by the actual CDT theorem
in the final `sigma76_*_correct` theorems.

## Important premises and limitations

- The CDT distribution theorem concerns the explicit uniform integer input of
  `Uniform83Jasmin.sample`. Its target is
  `exp(-k²/512)/sum_{j≥0}exp(-j²/512)`, from the definitions in official
  specification 260904 §5.1.1 and its reference [21]. The implementation table is
  not used to define the target distribution, and the floor-CDF formula in the
  C comment is not assumed. Infinite-sum normalization and numerical certificates
  are also proved. The [specification correspondence and proof boundary](docs/cdt-distribution-correspondence.md)
  record sources, hashes, and the connection.
- The statistical-distance bound for this single CDT does not automatically
  guarantee SHAKE uniformity/independence or the sigma76 rejection-sampling
  distribution. The official specification states no separate CDT error budget,
  and the Rényi bound for exponential-polynomial rejection is a different
  obligation. The standard analysis/probability foundations of `RealExp`,
  `RealSeries`, `Distr`, and `SDist` are also within the trust boundary.
- The exponential-error theorem concerns the integer grid of actual fixed-point
  input xi/2^48. It includes both the error of the actual C coefficient polynomial
  and rounding-up error during execution. The
  [mathematical bounds and connection](docs/approx-exp-mathematical-bound.md)
  record the input range, certificates, and actual procedure theorems.
  Signed64 semantics of Horner intermediate results are justified, but the
  intentional unsigned-word operations inside smulh48 are not described as
  nonwrapping.
- The acceptance-probability theorem calls the actual sigma function and varies
  only the rejection bytes uniformly. Its target retains the actual quantized
  xi and the α=1/2 correction when the actual rounded output is zero.
  Raw-exponent error and the difference in raw-zero correction are subsequently
  connected by the new theorems below. The one-sided ceiling in the C comment,
  the official Rényi error, and the complete accepted Gaussian sample
  distribution are separate obligations.
- NTT's `poly_repr_bound rp p s` means that each signed word represents a
  coefficient of `p` mod 64513 and lies in `[-2^s,2^s)`. The forward transform
  has `s=16→24`, and the inverse has `s=16/18→16`. No theorem directly feeds
  the 24-bit output range into the inverse transform's premise.
- The Gaussian consumer may write a candidate before accepting it. Preservation
  therefore applies **after the requested length `n`**, rather than after the
  returned acceptance count. The accepted-sequence theorem reads only the minimum
  of the returned acceptance count and the storable length. If
  `dont_write_last≠0`, the final dummy still contributes to the acceptance count
  and sum of squares, but its slot retains its original value.
- The sum of squares combines the initial value and **square limbs returned by
  accepted candidates**. It is not described as the sum of squared rounded
  outputs or ideal real squares. If the initial low limb is an arbitrary 64-bit
  value, lost carry during addition also prevents unconditional equivalence
  mod `2^112` for the whole sum. General theorems state headroom explicitly;
  when both initial limbs are 48-bit, concrete range theorems discharge that
  premise.
- The initial 49 blocks provide `49×136−32=6632=255×26+2` candidate-input
  bytes. Actual requests of length 256·257 require refill. The layout of the
  remaining 0…25 bytes and new 136 bytes in each refill is connected to the
  complete loop of actual `_sf_sample_gauss_N_full_at`. At return, 256 samples
  and 32 sign bytes are visible; the 257th dummy contributes to the sum of
  squares while its output slot is preserved.
- The inter-call accumulation theorem uses the total integer budget in
  `gauss_stream_acc_ok`. It does not assume the high limb remains in the 48-bit
  range at every step. This invariant is connected to repeated refills within
  one Gaussian call. For Hyperball, a stronger square-high bound and cumulative
  acceptance count `256*i + min(i,2)` establish the initial two-limb conditions
  of each polynomial call. The maximum count for mode 5 is 2,818.
- The basic Hoare theorem for complete Gaussian concerns **return values of
  terminating executions**. The subsequent `gr_sample_gauss_N_prefix_total`
  also proves termination of the actual function when the concrete seed's
  stream has a finite segment containing enough accepted candidates.
  It does not assume that all seeds satisfy this condition or that SHAKE outputs
  are independent and uniform.
- The complete Hyperball theorem likewise concerns **correspondence to a word
  specification** for terminating executions. It records every earlier rejection
  and the final acceptance in a history and connects all inputs other than
  unused scratch regions to concrete Gaussian streams. Return-value uniqueness
  does not assume nonce injectivity. The actual internal counter uses W64 addition,
  while SHAKE receives only its low 16 bits.
- Hyperball's norm acceptance condition is `N mod 2^64 <= bound`, where `N` is
  the mathematical sum of squares of the stored signed32 coefficients.
  Interpreting this as an integer radius test requires `N < 2^64`. A sufficient
  condition of coordinate magnitudes `<=2^26` and at most 2,816 coordinates is
  also proved; no premise asserts that every actual scaling output satisfies it.
  The [numerical boundary and reproduction](docs/hyperball-numerical-boundary.md)
  record identical C/Jasmin wrapping on constructed candidate sequences.
  No actual SHAKE-seed counterexample is provided.
- The Newton theorem proves exact word computation of the initial estimate and
  six updates. It does not establish convergence to the real inverse square
  root, approximation error, or absence of overflow in every intermediate
  computation. The C reference also states that the initial estimate can rarely
  be negative.
- A single SHAKE block is connected to the 24-round permutation in the
  [word specification](theories/SHAKEBlockSpec.ec). The
  [stream specification](theories/SHAKEStreamSpec.ec) includes absorption/padding
  of a 64-byte seed and the low two nonce bytes, followed by repeated squeezes.
  It does not include an arbitrary-length-input sponge or a separate equivalence
  to the FIPS 202 bit specification. Sources of reused definitions/proofs appear
  in the [SHAKE provenance inventory](manifests/shake-support-origin.tsv).
- The rounded sample has new integer-connection and no-wrap theorems. These are
  not extended into no-overflow theorems for every intermediate value in the full
  square/Horner computation or a real Gaussian computation.
- `_api_prepare_pre_raw` and actual `_sf_prepare_pre_raw` are different
  implementations. The current production-context claim relies on a theorem
  directly verifying the latter.
- Memory is the total byte map `Glob.mem`. Canonical/no-wrap and alias
  conditions do not replace actual OS allocation/access permissions or
  verification of the caller's C ABI.
- Remaining NTT arithmetic assumptions are stated in a
  [separate inventory](manifests/ntt-assumptions.md). No axioms assuming algorithmic
  correctness were added to the new sampler/API theorems.

The acceptance-formula theorem before rounding uses `Z=y+2^72x` and
`E=y(y+2^73x)/2^153` from the [separate formula record](docs/raw-gaussian-acceptance.md)
as its target. At a fixed candidate in the exceptional interval, the acceptance
probability difference can be about 1/2; a small raw-reference error is not claimed
for every fixed candidate. The average theorem concerns an actual single attempt
with explicit uniform 72-bit noise and independent uniform 48-bit rejection input,
not the accepted-sample distribution or actual SHAKE.

The [joint probability theorem for every output set](docs/joint-accepted-output.md)
also draws the CDT input uniformly. It neither truncates the ideal CDT support
at 166 nor wraps ideal outputs to 64 bits; actual outputs are read as unsigned
integers. The final comparison event is `accepted /\ S(output)`, without division
by acceptance probability. The accepted-sample conditional distribution is
therefore connected by subsequent normalization theorems. Independent-randomness
rejection repetition is addressed by the subsequent theorems below. Sign handling,
not covered at this stage, is composed separately in the sign stage below;
probabilistic properties of concrete SHAKE remain open.

The [conditional-distribution theorem](docs/conditional-accepted-output.md) divides
by the distinct acceptance probability of each experiment and excludes zero
denominators by proving actual≥1/7 and ideal≥1/8. It first bounds statistical
distance through a common non-strict bound for every event, then uses the
numerical margin to obtain <2^-39. The comparison target is the conditional
distribution of the preceding independent ideal experiment; its subsequent
identification with a separate rounded Gaussian mass formula is recorded below.

[Gaussian mass-function identification](docs/gaussian-magnitude-identification.md)
defines G's denominator as an implementation-independent sum of exponentials
over all integers and proves convergence and positivity. Since the existing
ideal conditional distribution is exactly the distribution of
floor((|G|+32768)/65536), its existing statistical-distance bound from actual
accepted magnitudes transfers without additional error. Rounded probabilities
are sums of Gaussian weights over each interval. The fact that this mathematical
G is signed is not interpreted as a proof of sign handling in the actual implementation.

[Rejection retries and accepted lists](docs/gaussian-retries-and-batches.md)
prove termination and the full joint distribution of an independent-randomness
experiment calling the actual extracted attempt each time. Acceptance
probability≥1/7 discharges the positivity premise, and repetition does not
increase the existing per-sample error. List errors use an independent-product
bound depending on the number of samples. The candidate-stream input model is
a 203-bit encoding with the five unused high bits set to zero. The convergence
of finite-prefix shortfall probability to zero is not used as proof that concrete
SHAKE generates independent uniform randomness or that every seed terminates.

The [complete iid byte-buffer theorem](docs/gaussian-iid-buffer.md) goes beyond
that retry experiment to transfer the distribution to an operational model
calling actual consumption, carry, and sign-copy functions. Each block explicitly
draws 136 independent uniform bytes; already fixed remaining bytes are not
assumed to have a fresh uniform distribution. It proves probability-1 termination
and the exact list law of the 256 stored magnitudes under the control flow
including the initial 49 blocks, partial candidates, and the dummy in a request
for 257. Initial arrays contain arbitrary word values; integer/no-wrap
interpretation of square accumulation still requires the previous limb/range
conditions. The probability law at this iid magnitude stage was restricted to
the magnitude list. Sign independence and application are separate contracts
of the following sign stage.

The state considered in the [signed-output stage](docs/gaussian-signed-output.md)
is not just the visible magnitude list, but `(entire sample array, square-word array)`.
Its independence from 256 fair sign bits is proved in the explicit iid byte model
and transferred to joint return-value events through equivalence between the
actual buffer and a sign-redrawing procedure. The final integrated gate, checking
each new source as a primary target, also passed.
A signed observation is an integer obtained by applying a sign to each
`W64.to_uint` magnitude, not `W64.to_sint`. The target `gst_target` is the
distribution of `sign(G)·floor((|G|+32768)/65536)`. Zero remains zero and the two
ties ±32768 become ±1, respectively. The independent sign-vector theorem retains
the existing 256-sample distance `<2^-31`. This does not add a Gaussian law for
the entire return tuple including square words.

The scaling connection retains exact word computation using the sign bit and
sample at the same global coordinate i. Signed32 interpretation explicitly
requires each rounded magnitude≤2147483647. Local sign bit i corresponds to
global index `8*signoff+i`, so connecting a local Gaussian sample window to the
global scaling sample window requires `sample_offset=8*signoff`. This is an
additional alignment condition not required by the distribution theorem for local
signed observations. The sign connection alone does not discharge Hyperball's
numerical conditions. The subsequent safe-input-domain stage derives fit and
norm no-overflow from hbs_good; interval-probability and distribution obligations
remain.

## Parts not yet proved

| Obligation | Current boundary and next connection |
| --- | --- |
| Gaussian distribution composition | Connected through the actual joint law of the iid sign stage and conditional signed32 application. Remaining scope includes connecting concrete SHAKE to ideal-XOF/pseudorandomness assumptions; the official Rényi bound and complete Hyperball composition are separate obligations |
| Separate Gaussian path | Correspondence and memory-contract connection between `_sample_gauss_N_full_at` taking a raw seed address and signing `_sf_sample_gauss_N_full_at`; current complete-function theorems cover only the latter |
| SHAKE sponge | Separate equivalence of the verified fixed-length seed/nonce word stream to the bit/FIPS specification, and the sponge for arbitrary-length inputs |
| Mathematical/probabilistic Hyperball semantics | Proved safe-interval escape of the iid raw sum of squares and acceptance AND excessive integer norm in one actual-call attempt with probability <2^-29/2^-44/2^-54. Remaining scope includes conditional unsafe probability given acceptance, actual-seed connection, actual inverse-square-root error, ideal S/final-output laws, outer-retry termination, and full-execution bounds; not extended to a radius guarantee for every input/seed |
| Complete KeyGen | Compose sampling, matrices, FFT guard, packing, and retries in `_keypair_full_m23/m5` with the public-key/secret-key relation |
| Complete Sign | Compose challenge, response, norm, hint, packing, and retries in `_sf_signature_core_mode{2,3,5}` with the signature specification |
| Complete Verify | Compose decode, matrix/CRT, norm, challenge, and the return decision in `_verify_full_mode{2,3,5}` with the verification specification |
| Sign→Verify | Prove that a valid KeyGen/Sign result is accepted by actual Verify for the same message/context |
| Final connection | Connect C descriptor wrappers, randomness bindings, and actual memory contracts to compiled assembly; complete implementation security |

A PASS from this project's verification gate therefore means **successful checks
of the registered component theorems**. It is not used as a status indicating
completed correctness verification of the entire HAETAE implementation.
