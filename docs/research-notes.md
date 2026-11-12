# Research history and detailed results

This document preserves the detailed research descriptions from the README
before the public landing page was reorganized. References to “current,” tool
versions, and verification counts below belong to their respective research
stages. Use the [repository guide](../README.md) for public-source reproduction,
the [research map](research-map.md) for claims and theorems, and the
[validation record](../haetae-easycrypt/VALIDATION.md) to distinguish execution results.

This repository maintains the HAETAE C reference implementation and its
corresponding Jasmin implementation. Directory and document names are kept
version-independent; distribution versions and provenance are recorded in the
[working baseline](../docs/HAETAE.md).
It includes Jasmin mode 2·3·5 KATs, sampler differential tests, and C
interoperability tests. A separate EasyCrypt project verifies the new sampler's
acceptance order and sum of squares; the actual signing Gaussian function's
complete SHAKE/refill flow; the complete Hyperball flow and modes 2·3·5; NTT;
and API helpers. The basic whole-function Gaussian/Hyperball theorems concern
word return values of terminating executions. Gaussian also has a termination
theorem under a finite input-window premise containing sufficiently many
accepted candidates. Interpreting the original Hyperball norm as an integer
requires a no-overflow condition. Formal verification of the complete
KeyGen/Sign/Verify composition is not yet finished.

The separate [arithmetic hardening variant](../haetae-hardened/README.md)
preserves the original implementation and detects and rejects overflow in
coefficient conversion and sum-of-squares accumulation. It proves that **the
actual integer sum of squares of an accepted output is at most the mode
bound**, without a safe-input-interval or no-overflow premise. Termination of
the finite decision is distinguished from properties of executions in which
the complete Hyperball function returns.

The [Gaussian rejection rate and expected count](../haetae-hardened/gaussian-acceptance.md)
are also connected to the actual extracted function. Under an independent
uniform-randomness model, candidate rejection probability is **less than 5%**,
and the expected number of attempts, including the successful candidate, is
**less than 20/19**. These figures concern a single Gaussian candidate, not
Hyperball's overall retry rate.

The [Rényi bound for the exponential approximation](../haetae-hardened/gaussian-renyi.md)
compares the actual output distribution with an exact-exp reference preserving
the same candidates, quantization, 0 handling, and rounding. For integer
orders 2~1024, the non-logarithmic Rényi quantity satisfies
**`≤1+2^-68<1+2^-45.1`**. The document states the reference distribution and the
additional obligations needed to extend the result to security for complete
signature queries.

The [Rényi bound for one Hyperball attempt](../haetae-hardened/hyperball-renyi.md)
composes over all Gaussian samples of each mode while jointly retaining rounded
magnitudes, raw squares, and signs. In the explicit iid byte model, the joint
law of the hardened output candidate and acceptance bit satisfies
`R_α ≤ (1+2^-68)^D < 1+2^-56` in both directions against the exact-exp reference.
The integer orders are 2~1024, and D is 1538·2306·2818 including the two dummies.
Conditioning on acceptance and the outer retry loop remain separate.

For the 83-bit CDT, the actual Jasmin function on uniform input is also proved
to have **statistical distance <2^-78** from the official nonnegative discrete
Gaussian target (σ=16). The [mathematical specification correspondence and scope](../haetae-easycrypt/docs/cdt-distribution-correspondence.md)
record the sources, certificate, and randomness assumptions.

The actual exponential approximation also has a mathematical error theorem.
For every sigma76 input, the normalized output error of `approx_exp` is
**at most 27/2^48 and less than 2^-43**. The [scope of the numerical and acceptance-probability proofs](../haetae-easycrypt/docs/approx-exp-mathematical-bound.md)
describes the actual input interval and conditional acceptance experiment.
The relationship between the actual exponent input and the Gaussian acceptance
formula before rounding is also covered. In one attempt with explicitly uniform
72-bit noise and 48-bit rejection randomness, the average acceptance-probability
difference is **less than 29/2^48, hence less than 2^-43**. The difference between
rounded 0 and actual 0 is included through the probability of the
exceptional interval. See the [formulas and exact scope](../haetae-easycrypt/docs/raw-gaussian-acceptance.md).

In the actual experiment with uniform CDT input as well, the difference between
the probability of acceptance with output in S and the same probability in an
independent ideal experiment is **less than 29/2^48+2^-78 for every output set S**.
The ideal Gaussian's infinite tail and unbounded integer rounding are retained.
The [joint probability definition and scope](../haetae-easycrypt/docs/joint-accepted-output.md)
distinguish this result from the conditional distribution after acceptance.

The acceptance-conditioned distributions are also compared. The initial proof
establishes lower bounds **1/7·1/8** on the actual and ideal acceptance
probabilities, then normalizes by each probability to prove **statistical
distance <2^-39** between the two sample-magnitude distributions. The reference
is the conditional distribution of the preceding ideal experiment. The
[conditional distribution definition and error](../haetae-easycrypt/docs/conditional-accepted-output.md)
state the randomness model and that stage's proof scope.

The ideal conditional distribution was identified exactly as **the distribution
obtained by dividing the absolute value of an integer Gaussian G by 2^16 and
rounding**. Infinite normalization of `Pr[G=k]∝exp(-k²/2^153)` and the probability
of each rounding interval were also proved, so **statistical distance <2^-39**
holds directly between actual accepted sample magnitudes and this explicit
Gaussian target. The [Gaussian mass formula and proof](../haetae-easycrypt/docs/gaussian-magnitude-identification.md)
record 0, rounding boundaries, and that stage's proof scope.

The experiment repeatedly calling the actual Jasmin attempt with independent
uniform 83·72·48-bit inputs **terminates with probability 1**, and its first
accepted value has exactly the conditional distribution above. The joint law
of 256 accepted values has **distance <2^-31** from a list of independent
Gaussian targets; for 257 values the **distance is <257·2^-39**. Candidate byte
sequences, acceptance order, and the probability of obtaining a sufficiently
long finite prefix were also connected. The [retry and sample-list proofs](../haetae-easycrypt/docs/gaussian-retries-and-batches.md)
distinguish this explicit randomness model from properties of concrete SHAKE.

The distribution theorem was also connected to a complete buffer model supplied
with independent uniform bytes in blocks of 136. This model calls the actual
Jasmin consumer, remaining-byte copy, and sign-copy functions and **terminates
with probability 1**. For both requests 256/257, the joint law of the 256
magnitudes actually stored is exactly the independent conditional-distribution
list, retaining **statistical distance <2^-31** from the Gaussian target.
The [complete iid buffer proof and scope](../haetae-easycrypt/docs/gaussian-iid-buffer.md)
state the boundaries concerning uniform 26-byte inputs, already known remaining
bytes, dummies, and the word accumulator.

The sign stage was also proved. In the explicit iid byte model, the 256
independent fair signs are independent of the complete sample array and squared-word
state. The law of 256 integers obtained by observing actual return values as
`±W64.to_uint(word)` has **distance <2^-31** from an independent list with target
`sign(G)·floor((|G|+32768)/65536)`. Sign application after actual scaling is also
word-exact; signed32 integer interpretation retains the condition that the
rounded magnitude is ≤2147483647. 0, rounding boundaries, exact input
conditions, and global-index alignment are recorded in the
[signed-output proof](../haetae-easycrypt/docs/gaussian-signed-output.md).

The Hyperball numerical boundary was also connected to actual extracted
functions. Executions passing specified candidate sequences through the actual
finite consumer, Newton, scaling, and norm functions terminate in modes 2·3·5
and **return word acceptance value 1 even when the actual integer norm exceeds
the bound**. The results include overflow in accumulation of the two dummy
squares and in signed32 conversion. No corresponding SHAKE seed or reachability
through the complete signature API is claimed. The [actual-function counterexample proofs](../haetae-easycrypt/docs/hyperball-actual-witnesses.md)
record the exact inputs, results, and scope.

A sufficient safe interval for Hyperball's input sum of squares was also proved.
If the low limb is canonical and `3D/4 ≤ S/2^76 ≤ 5D/4`, the actual Newton and
scaling computations yield all rounded magnitudes ≤2^26, correct signed32
conversion, and no overflow in the integer norm. D is the event count including
the two dummies. Sample and sign arrays are unrestricted, and **acceptance
implies the output is within the actual radius**. The probability of reaching
this interval and the complete seeded flow remain separate obligations. The
[safe-input-interval proof](../haetae-easycrypt/docs/hyperball-safe-domain.md)
records the exact premises and actual call contracts.

<!-- gaussian-payload:overview:start -->
The subsequent [complete accepted-payload and sum-of-squares proof](../haetae-easycrypt/docs/gaussian-payload-and-squares.md)
covers the **exact joint law of the visible sample vector and integer sum of
squares S** for Gaussian batches supplied with independent uniform bytes.
The complete accepted histories for modes 2·3·5 contain D=1538·2306·2818 events,
respectively. In the same history, the two dummies are excluded only from the
visible vector and remain included in S. S sums the actual raw square limbs,
not squares of rounded samples. With initial sum of squares 0 and the actual
call order and offsets, an exact probability expression for the safe-interval
event was obtained. Initializing the sample and sign arrays to 0 is a modeling
choice; production code initializes only the sum of squares to 0. At that stage,
a numerical upper bound on interval escape and the complete seeded flow were
left as subsequent obligations.
<!-- gaussian-payload:overview:end -->

<!-- hyperball-tail:overview:start -->
The subsequent [iid sum-of-squares tail bound](../haetae-easycrypt/docs/hyperball-iid-tail-bound.md)
adds numerical upper bounds to the preceding exact law of S. Exponential moments
of actual accepted raw squares were proved, bounding the probability of leaving
the sufficient safe interval by **less than 2^-29·2^-44·2^-54**, respectively,
for modes 2·3·5. The same bounds apply to the **joint event of acceptance and the
returned coefficients' squared integer norm exceeding the mode bound** in one
iid attempt composing the actual Gaussian and numerical helpers. These are not
acceptance-conditioned probabilities or bounds for the entire outer retry loop.
The explicit uniform-byte and existing initialization models are retained;
concrete SHAKE and complete seeded execution remain separate.
<!-- hyperball-tail:overview:end -->

| Path | Purpose |
| --- | --- |
| [HAETAE/](../HAETAE/) | Unmodified reference distribution, license, and KAT |
| [haetae-jasmin/](../haetae-jasmin/) | Jasmin implementation, 8 APIs, build and validation tests |
| [haetae-easycrypt/](../haetae-easycrypt/README.md) | Component correctness theorems and verification gates for actual Jasmin extractions |
| [docs/HAETAE.md](../docs/HAETAE.md) | Distribution provenance, version differences, and restart sequence |
| [scripts/check-baseline.sh](../scripts/check-baseline.sh) | Distribution hash checks and reference KAT reproduction |
| [archive/README.md](../archive/README.md) | Earlier key documents, preservation criteria, and recovery of the full history |

## Baseline checks

On Linux, the required tools are Bash, CMake 3.18 or newer, a C11 compiler,
OpenSSL development files, `make`, `diff`, and `sha256sum`. These are already
required by the reference implementation.

```sh
bash scripts/check-baseline.sh
```

After checking the distribution SHA-256 values, this generates KATs for modes
2·3·5 and compares them byte-for-byte against all 6 stored `.req`·`.rsp` files.
Generated files are placed only in the ignored
`HAETAE/reference_implementation/build/` directory. This distribution contains
no optimized implementation, so `ref` is the verification target.

The Jasmin implementation is built with Jasmin Compiler 2026.03.0 on Linux
x86-64. The [implementation guide](../haetae-jasmin/README.md) details the API
and randomness integration; the [validation record](../docs/haetae-jasmin-validation.md)
states the checked scope.

```sh
make -C haetae-jasmin -j2 all
make -C haetae-jasmin -j2 test
```

Recheck the EasyCrypt component theorems with the following command. Consult
the [formal verification scope](../haetae-easycrypt/CLAIMS.md) for exact coverage
and premises.

```sh
make -C haetae-easycrypt verify
```

## Working practices

- `main` is the integration branch. Keep working branches short-lived and
  integrate them after verification.
- Preserve `HAETAE/` as the comparison baseline. Develop Jasmin in a separate
  directory and record verified functions together with their assumptions.
- Earlier EasyCrypt proofs are reuse candidates; their verification results
  do not automatically carry over to the current implementation.
- The first commit-message line uses `[yymmdd] <type>: <reason for change>`;
  Git-native Lore trailers such as `Tested:`, `Not-tested:`, and `Directive:`
  record verification coverage and remaining obligations.

Earlier branches and uncommitted document changes are preserved under
`archive/pre-haetae-1.2.0/*` tags. The existing Git history is retained, including
large files from earlier stages.
