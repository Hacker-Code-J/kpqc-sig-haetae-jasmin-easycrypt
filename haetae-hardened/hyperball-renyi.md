# Exponential-approximation Rényi bound for one Hyperball attempt

Under an independent uniform byte model, compare **one Hyperball attempt using
the actual integer exponential approximation** with **a reference attempt that
replaces only Gaussian acceptance probabilities with exact exp**.
The observable consists of the two output arrays and the acceptance/rejection
bit. Rejected candidates are included. The nonce, amount of randomness
consumed and final additional output `b` are not part of this observable.

For integer orders `2 ≤ α ≤ 1024`, prove the following bound in both directions.

```text
R_α(actual attempt, exact-exp reference attempt) ≤ (1 + 2^-68)^D < 1 + 2^-56.
```

| Mode | Visible coefficients | Dummies included only in the sum of squares | Total Gaussian samples D |
| --- | ---: | ---: | ---: |
| 2 | 1,536 | 2 | 1,538 |
| 3 | 2,304 | 2 | 2,306 |
| 5 | 2,816 | 2 | 2,818 |

The Rényi quantity uses the same **nonlogarithmic** definition as the
[preceding single-Gaussian proof](gaussian-renyi.md). `2^-56` is a common upper
bound on its excess over 1, not a statistical distance, measured error or
number of security bits. The mode-specific power bounds are also retained.

## What the comparison preserves and changes

The actual and reference attempts use the same finite CDT, 72-bit noise,
quantized exponent, acceptance correction for rounded 0, and output rounding.
The reference attempt replaces the actual integer exponential approximation
and 48-bit acceptance threshold with the exact acceptance probability
`exp(-X/2^48)`. The 48-bit rejection randomness is first averaged into the
acceptance kernel.

The subsequent signs, raw-square accumulation, Newton inverse square root,
fixed-point multiplication, coefficient conversion, hardened overflow checks
and acceptance decision are identical on both sides. This stage measures the
effect of that exp replacement; it does not replace all these computations
with ideal real arithmetic.

Each Gaussian sample retains both its rounded magnitude and the two limbs of
its raw square. The internal S is not the sum of squared rounded output
coefficients. The 257th accepted sample in each of the first two calls is not
stored in the array but is added to S. Both dummies are included in D for
distribution composition.

## Connection to actual execution

- `HyperballRenyiPayload`: identifies the actual accepted-payload distribution
  with the existing `gpd_accepted` and proves a single-sample Rényi bound that
  retains both the magnitude and raw square.
- `HyperballRenyiProduct`·`BatchBounds`: proves that Rényi quantities multiply
  for product distributions. Each call's independent 32-byte signs introduce
  no additional error. The exact power is retained, rather than replaced by
  `1+Dε`, to derive the common bound.
- `HyperballRenyiBuffer`·`Schedule`·`Joint`: connects the return state of the
  actual sign-copy, carry and finite consumer to the complete sample, sign and
  square arrays reconstructed from independent payload and sign blocks.
  Independence of signs and the sum of squares is not added as an assumption.
- `HyperballRenyiHardened`: proves equality of the complete return states of
  the Gaussian helpers in the new hardened extraction model and the previously
  verified buffer model.
- `HyperballRenyiArithmetic`: proves exactly which arrays and acceptance bit
  the actual hardened arithmetic helpers return. It assumes no safe interval,
  fit condition or absence of overflow.
- `HyperballRenyiMap`·`Production`: applies nonincrease of the Rényi quantity
  under the same subsequent computation and connects the actual and reference
  executions to their respective explicit distributions.

`hrf_attempt_law` and `hrf_exact_law` state the two execution distributions;
`hrf_renyi_bounds` and `hrf_common_bound` state the accumulated bounds.
A single attempt in the explicit iid model terminates with probability 1
on both sides.

This execution model uses the same sample, sign and square arrays initialized
to 0 and output scratch initialized to 0 as the existing iid proof. It calls actual
extracted helpers but supplies independent bytes instead of SHAKE. It makes
no claim about the distribution of an arbitrary complete stack, memory safety
for arbitrary pointers, or behavior for every seed.

## Reproduction and remaining scope

```sh
make -C haetae-hardened prepare
python3 haetae-hardened/tests/gaussian-rate-gate.py
python3 haetae-hardened/tests/gaussian-renyi-gate.py
python3 haetae-hardened/tests/hyperball-renyi-gate.py
python3 haetae-hardened/scripts/verify.py --group hyperball-renyi
```

Set `WHY3_SERVER_SOCKET` when using an existing Why3 server. New files and local
dependency proofs are each checked as fresh mains, with extraction agreement,
EOF completeness and source-hash checks. Per-target results are recorded in
[hyperball-renyi-results.json](hyperball-renyi-results.json).

The C/Jasmin executable code was not changed at this stage. Existing KAT, API
and CT/SCT execution records are preserved with the hashes of the unchanged
implementation and distinguished from the proof and verifier-regression checks
newly executed in this stage.

**The final distribution after retrying until Hyperball accepts** remains a
follow-up task. The distribution conditioned on acceptance, acceptance
probability and termination of the outer retry loop, a Rényi comparison with
the full ideal Gaussian, the connection between concrete SHAKE and the iid
model, complete KeyGen/Sign/Verify correctness, and security composition over
all signing queries are also outside this result.
