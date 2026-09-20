# Official Gaussian target and the 83-bit Jasmin CDT

The target for this stage is the nonnegative discrete Gaussian with parameter
sigma=16. Its definition is independent of the implementation table:

```text
rho(k) = exp(-k*k/512)                         for k >= 0
Z      = sum_{j >= 0} rho(j)
P(k)   = rho(k)/Z                             for k >= 0; zero otherwise
```

`HalfGaussianSpec.ec` defines this infinite distribution using real arithmetic.
`HalfGaussianProperties.ec` proves convergence, `Z >= 1`, total probability one,
and the bound on the part of the sum omitted from numerical computation.

## Primary-source correspondence

| Source | Location | Requirement used here |
| --- | --- | --- |
| [HAETAE specification 260904](https://drive.google.com/file/d/1H2SFqZFG5BcWH--bJKssvXaSG0Sd3mUx/view) | Section 5.1.1, printed page 32, PDF page 33 | Base Gaussian parameter 16, 166 CDT entries, 83 input bits, and reference [21], Algorithm 12 |
| [Rossi, Extended Security of Lattice-Based Cryptography](https://www.di.ens.fr/~mrossi/docs/thesis.pdf) | Section 2.2.2, printed page 27, PDF page 39; Algorithm 12 step 1 and surrounding derivation, printed page 48, PDF page 60 | Gaussian weights `exp(-x*x/(2*sigma*sigma))`, normalization over the sampling set, and the nonnegative base distribution |

The [official release page](https://kpqc.cryptolab.co.kr/haetae) associates
specification 260904 with implementation 1.2.0. Download URLs, exact PDF hashes,
sizes and page references are pinned in
[`specification-sources.json`](../manifests/specification-sources.json).
Source-to-formula correspondence is a reviewed transcription; the proof does
not claim to verify natural-language PDF interpretation.

The nonnegative target gives zero its full weight. It is different from taking
the absolute value of a signed discrete Gaussian. The later zero rejection and
random sign in Algorithm 12 are outside this CDT theorem.

## Exact implementation distribution

Let `M=2^83`, draw `U` uniformly from `0,...,M-1`, and denote the actual 166
thresholds by `T[0],...,T[165]`. The Jasmin function counts strict inequalities
`T[i] < U`. Its output distribution `Q` therefore has masses

```text
Q(0)   = (T[0]+1)/M
Q(k)   = (T[k]-T[k-1])/M                      for 1 <= k <= 165
Q(166) = 1/M                                 because T[165]=M-2
Q(k)   = 0                                   outside 0,...,166
```

`CDTDistribution.ec` proves this inverse-CDF law for general ordered thresholds.
`CDTDistributionBridge.ec` then uses the independently generated C constants and
the existing actual-Jasmin total-correctness theorem. Its `Uniform83Jasmin.sample`
experiment draws `U`, splits the low 64 and high 19 bits, and calls the extracted
`SamplerTarget.M.sample_gauss83_jazz`. It proves the exact law, output support,
endpoint probability, and termination of this experiment.

## Mathematical approximation theorem

The composed statement in `CDTGaussianApproximation.ec` is

```text
statistical_distance(Q, P) < 32 / 2^83 = 2^-78
```

Consequently, for every set of integer outputs `E`, the probability that the
actual Jasmin experiment returns a value in `E` differs from `P(E)` by less
than `2^-78`. The public theorem has no assumed CDF accuracy, table-generation
formula, normalization value, or numerical-error premise.

The numerical certificate is checked through the following argument:

1. Bound `exp(-1/d)` between `1-1/d` and `d/(d+1)`, for `d=2^137`.
2. Square 128 times using outward-rounded integer intervals with denominator
   `2^320`, obtaining a rigorous enclosure of `q=exp(-1/512)`.
3. Enclose `q^(k*k)` and `q^(2*k+1)` for `k=0,...,256` by checked recurrences.
4. Enclose `Z` with the terms `0,...,255` and the proven tail bound
   `rho(256)/(1-q^513)`. The target remains the full infinite Gaussian.
5. Bound the differences of all point masses below 256, include the remaining
   Gaussian tail, and divide the resulting L1 bound by two.

The generator uses integer arithmetic to propose the certificate. The proof
checks each recurrence and inequality; Python output is not an analytic oracle.
The `[opaque]` attributes on large defined lists only prevent automatic
expansion in symbolic goals; the certificate and provenance checks explicitly
unfold their definitions.

## Scope and remaining obligations

- Uniform 83-bit input is explicit in the experiment. No theorem here claims
  that a fixed SHAKE seed generates uniform or independent inputs.
- The official specification does not state a separate numerical error budget
  for this CDT. The `2^-78` result is a proved approximation bound for this leaf,
  not a proof of the complete sampler's security error budget.
- Section 5.1.1's Renyi-divergence bound for exponential-polynomial rejection is
  a different claim. This theorem does not prove it or replace that metric.
- The C comment claiming exact `floor(M*CDF(k))` values is not used as a premise.
  Independent numerical checks find differences between that formula and the
  stored thresholds. The theorem bounds the actual table's distribution.
- Sigma76 rejection, repeated samples, the ideal-XOF connection, Hyperball's
  distribution and numerical interpretation, and the full signature APIs
  remain separate obligations.
- The analytic foundation includes the installed EasyCrypt `RealExp`,
  `RealSeries`, `Distr` and `SDist` theories. Their standard axioms remain in
  the trusted foundation. No project axiom asserting sampler correctness or
  certificate accuracy is introduced.

## Reproduction

```sh
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```

The gate regenerates the certificate, checks provenance and every local target
as a main theory with proof checking and the EOF guard. Regression tests also
alter a squaring interval and a compared threshold in temporary copies; both
must be rejected without changing live project files.
