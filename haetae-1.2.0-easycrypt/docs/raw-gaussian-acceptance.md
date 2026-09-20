# Raw Gaussian acceptance and the actual integer computation

Let `x` be the nonnegative CDT integer, `y` the unsigned integer represented by
noise bytes 17 through 25, and `Z=y+2^72*x`. The mathematical comparison is

```
E = y*(y+2^73*x)/2^153
p_raw = (if Z=0 then 1/2 else 1) * exp(-E).
```

This is the raw-candidate acceptance rule, before sample rounding and random
signing. It follows from the Gaussian rejection ratio for `k=2^72` and
`sigma=2^76`: `(Z^2-(k*x)^2)/(2*sigma^2)`. The rule at zero concerns `Z`, not
its rounded output. It is defined independently of the fixed-point square,
quantized exponent, approximate exponential polynomial, and acceptance bits.
The source is [Rossi's thesis](https://www.di.ens.fr/~mrossi/docs/thesis.pdf),
Algorithm 12 and the subsequent ratio derivation (printed page 48), already
pinned in `manifests/specification-sources.json`. Algorithm 12 Step 4 contains
opposite reject/accept wording; the comparison follows the explicit acceptance
probability in the following derivation and the official HAETAE specification.
Step 5 tests the unrounded candidate. The exact Gaussian weight identity is
also checked in `SigmaRawDensityIdentity`, so this exponent is not assumed
correct because it resembles the executable code.

## Exact arithmetic

The implementation's two square limbs encode `floor(Z^2/2^76)`. Its actual
exponent input is `X=floor((y*(y+2^73*x)+2^104)/2^105)`. Consequently,
`|X/2^48-E| <= 2^-49`. The existing numerical evaluator error and 48-bit
acceptance quantization contribute `28/2^48`; changing the exponent adds
`1/(2*2^48)` because `exp(-t)` is 1-Lipschitz on nonnegative arguments.

## The two zero rules differ

The actual rounded sample is zero exactly when `x=0` and `0<=y<32768`.
The raw sample is zero exactly when `x=y=0`. Thus the discrepancy event is

```
x=0 and 1<=y<32768.
```

For these fixed inputs the acceptance difference can be close to one half.
A uniform tiny error bound for every fixed candidate against `p_raw` would
therefore be false. Outside this explicit event, the regular error bound is
`57/(2*2^48) < 2^-43`.

For an explicitly uniform 72-bit noise integer, with the CDT bytes held fixed,
the event probability is `32767/2^72` if `x=0` and zero otherwise. Its maximum
contribution to the averaged acceptance difference is `32767/2^73 < 2^-58`.
The target for the averaged theorem is the mean of the independently defined
raw-candidate acceptance rule over that same explicit uniform noise. The final
bound is

```
| Pr[actual attempt accepts] - E_y[p_raw] |
  <= 57/(2*2^48) + (if x=0 then 32767/2^73 else 0)
  < 29/2^48 < 2^-43.
```

At the halfway case `x=0, y=2^52`, the actual exponent is `X=1` and the ideal
exponent is `2^-49`. Thus the non-strict exponent error bound is attained;
replacing it by a strict `2^-49` bound would be false.

## Scope and verification

This stage concerns one sampling attempt. A fixed-input theorem draws only
uniform 48-bit rejection randomness; the averaged experiment additionally
replaces exactly the nine noise bytes with independent uniform 72-bit noise
and calls the actual extracted sigma routine. No concrete SHAKE uniformity is
assumed or established. The CDT bytes remain fixed, so no CDT distribution
assumption is needed for these theorems.

The acceptance-rate comparison does not yet establish the distribution of
accepted outputs. Sample rounding, random signs, rejection normalization,
repeated attempts, the official Renyi bound, concrete SHAKE, Hyperball and the
complete signature APIs remain separate obligations.

The following final contracts passed fresh EasyCrypt checking with the EOF
completion guard:

| File | Main result |
| --- | --- |
| `SigmaSquareExact` | `sigma_square_word_exact` |
| `SigmaRawExponentCorrectness` | `sigma_raw_exponent_exact`, `sigma_raw_exponent_error` |
| `SigmaRawDensityIdentity` | `sr_gaussian_weight_identity`, `sr_gaussian_density_ratio` |
| `SigmaRawZeroCorrectness` | `sr_zero_tests_differ`, `sr_zero_factor_difference` |
| `SigmaRawNoiseSpec` | `sr_noise_mismatch_probability`, `sr_noise_half_effect` |
| `ExponentialLipschitz` | `exp_neg_lipschitz` |
| `FiniteExpectationError` | `finite_expectation_error` |
| `SigmaNoise72Bridge` | `sigma_noise72_actual_probability`, `sigma_noise72_actual_ll` |
| `SigmaRawAcceptanceCorrectness` | `sr_actual_acceptance_error`, `sr_actual_acceptance_regular` |
| `SigmaRawAverageCorrectness` | `sr_average_acceptance_error_strict` |

All 90 current non-NTT files passed individually as main targets in the final
integrated run; all 18 existing gate regression tests passed. The 11 new files
include the independent `SigmaRawSpec` definitions. Existing NTT proof records
are retained with unchanged hashes. No project axioms, proof escapes, numerical
oracles, or new dependencies were introduced. Production and extracted sources
and all prior proof sources are unchanged. See `../VALIDATION.md` and the
machine-readable verification manifest for scope, commands, hashes and timing.
