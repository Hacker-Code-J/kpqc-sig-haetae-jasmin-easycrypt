# Rényi output-distribution bound for the exponential approximation

Under the independent uniform candidate-input model, compare **the distribution
of Gaussian magnitude samples using the actual exponential approximation and
machine-integer acceptance decision** with **the reference distribution accepted
using the exact exponential function**. Both distributions use the same actual
CDT, quantized exponential input, handling of 0 and output rounding.

For integer orders `2 ≤ α ≤ 1024`, verify the following upper bound.

```text
R_α(actual, exact-exp reference) ≤ 1 + 2^-68 < 1 + 2^(-451/10).
```

`451/10` expresses the specification's `45.1` as an exact rational number.
The same upper bound `1+2^-68` holds in the reverse direction. This is a proved
upper bound, not a measurement of the actual divergence.

## Distributions and numerical interpretation

| Item | Definition in this verification |
| --- | --- |
| Actual distribution P | The distribution of accepted, rounded magnitude samples after applying the machine-integer exponential approximation and 48-bit acceptance decision to the actual 83-bit CDT and 72-bit noise candidate |
| Reference distribution Q | Retain the same candidate, quantized exponent `X` and rounded magnitude `r`, but replace the acceptance probability with `(1/2 if r=0, otherwise 1) · exp(-X/2^48)` |
| Specification value | The exponential-approximation comparison bound `1+2^-45.1` in [HAETAE 260904 §5.1.1](https://drive.google.com/file/d/1H2SFqZFG5BcWH--bJKssvXaSG0Sd3mUx/view) |
| Bound in this development | At most `1+2^-68` for the above P,Q and integer orders 2–1024 |

The reference Q at this stage retains the actual finite CDT, quantization and
handling rules for 0. Comparisons that also change to an ideal Gaussian with
infinite support, an exponent before quantization, or different raw-candidate
handling of 0 require additional proofs. Existing statistical-distance results
are not relabeled as Rényi results.

Following the definition in [Rossi's dissertation §2.2.3](https://www.di.ens.fr/~mrossi/docs/thesis.pdf),
use the following quantity without taking its logarithm.

```text
R_α(P,Q) = (Σ_x P(x)^α / Q(x)^(α-1))^(1/(α-1)).
```

The actual distribution is the first argument. Finite support, total probability
mass 1, support inclusion and integrability are checked, and the likelihood-ratio
moment expression is proved equal to the power-sum expression above. This
definition does not include an extension to infinity when support inclusion
fails; the two verified distributions have the same support.

The specification uses order `α=2λ−1`. Substituting 120·180·260 from the Security
row of §4.5 Table 1 gives 239·359·519, which also fall within the verified range.
The same table lists Core-SVP estimates separately, so this substitution alone
must not be interpreted as proving λ-bit security for each mode.

## From actual code to the bound

1. The actual candidate's exponential input satisfies `0 ≤ X/2^48 ≤ 2/3`.
   Thus the exact exponential satisfies `exp(-X/2^48) ≥ 1/3`, and the reference
   acceptance probability, including handling of 0, is at least `1/6`.
2. From the existing machine-integer acceptance-probability error theorem,
   derive `|a-b| ≤ e·b`, `e=84/2^48`, for the actual and reference acceptance
   probabilities `a,b` of the same candidate.
3. First average over the 48-bit rejection randomness and incorporate it into
   these acceptance probabilities. Only the CDT and noise remain in the common
   candidate distribution. Normalizing by acceptance probability and grouping
   equal outputs gives a point-mass ratio error at most `δ=2^-39` in both directions.
4. Total probability mass 1 gives `E_Q[P/Q−1]=0`. The first-order term in the
   power expansion vanishes, yielding `E_Q[(P/Q)^α] ≤ 1+α(α−1)δ²`. Positive real
   powers and the integer-order range then give `R_α ≤ 1+2^-68`.

The comparison does not retain all 26 bytes, including the 48 rejection bits,
as the candidate and then compare the actual deterministic acceptance bit
pointwise with reference probabilistic acceptance. That would change the
observable, so the small relative-error bound above would not apply.

`GaussianRenyiActual` identifies the normalized actual kernel's output
distribution exactly with the existing `sc_actual_conditioned`.
`GaussianRenyiProduction` connects repeated calls to the two Gaussian functions
extracted from production code, and the exact-exp reference execution model,
to their respective distributions. The reference retry model is also proved
to terminate with probability 1.

## Reproduction and scope

```sh
make -C haetae-hardened prepare
python3 haetae-hardened/tests/gaussian-rate-gate.py
python3 haetae-hardened/tests/gaussian-renyi-gate.py
python3 haetae-hardened/scripts/verify.py --group gaussian-renyi
```

Set `WHY3_SERVER_SOCKET` when using an existing Why3 server. Every new theorem
and local dependency theorem is checked as a main target, together with
extraction agreement and file hashes. Per-file results are recorded in
[gaussian-renyi-results.json](gaussian-renyi-results.json). Earlier executable-code,
KAT, API and CT/SCT records are preserved by hash; the verifier and target list
modified in this stage are distinguished from their historical values.

This result concerns the specified comparison of a single Gaussian output.
A security conclusion for all signing queries additionally requires the number
and composition of Gaussian calls and a connection between the comparison and
security assumptions. Connecting concrete SHAKE to the randomness model,
termination of the outer Hyperball retry loop, and complete API correctness
are also separate tasks. The C/Jasmin executable code was not changed at this stage.
