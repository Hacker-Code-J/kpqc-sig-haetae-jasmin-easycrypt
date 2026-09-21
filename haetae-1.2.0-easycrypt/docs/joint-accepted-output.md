# Joint accepted-output probabilities with the complete CDT law

For every set `S` of integer outputs, the comparison concerns the event

```
the attempt accepts AND its rounded magnitude belongs to S.
```

It does not divide by the probability that the attempt accepts.

## Actual and independent ideal experiments

`SigmaJoint203Experiment.sample(p)` draws independent uniform integers of
83, 72 and 48 bits. It places the CDT input in bytes 0..10, noise in bytes
17..25 and rejection input in bytes 11..16, then calls the actual extracted
`SamplerTarget.M.__sample_gauss_sigma76_regs`. The returned pair is
`(W64.to_uint rounded, accepted)`. The original template `p` is unrestricted;
no extra fit or accuracy condition is a premise of the final comparison.
The five unused high CDT bits are zero in this explicit experiment.

`SigmaJointIdeal.sample()` is independent of machine arithmetic:

1. Draw `x` from the nonnegative sigma16 Gaussian with mass proportional to
   `exp(-x*x/512)`, normalized over **all integers x>=0**.
2. Draw uniform `y` in `0..2^72-1`, and set `z=y+2^72*x`.
3. Accept with probability
   `(if z=0 then 1/2 else 1)*exp(-y*(y+2^73*x)/2^153)`.
4. Return the integer `floor((z+32768)/65536)` and the acceptance bit.

The reference rounding is unbounded integer arithmetic. It is not converted
to a 64-bit word, and the ideal Gaussian is not truncated at the largest
implementation CDT value 166. The acceptance function is extended by zero
outside the legal candidate domain, giving a bounded kernel on all integers.
The biased-bit sampler uses this exact probability: its range is proved, so
its library clamp does not change it.

The raw acceptance formula and its Gaussian weight identity are documented
in [the preceding milestone](raw-gaussian-acceptance.md). The base distribution
and its normalization are documented in [the CDT correspondence](cdt-distribution-correspondence.md).

## Every output set, not only the overall acceptance rate

Write `M=2^48` and `eta=57/(2*M)+32767/2^73`. The implementation error is first
multiplied by the indicator of `S(round(x,y))`, **before** averaging the noise.
The earlier scalar mean-acceptance bound alone would not justify this step.
The exact rounded-output theorem makes the actual and reference indicators
identical for each actual candidate. The rounded-zero discrepancy remains
explicit on `x=0, 1<=y<32768`, and its mass is included in `eta`.

For `F_S(x)=E_y[p_raw(x,y)*1_S(round(x,y))]`, the proof establishes `0<=F_S<=1`.
If `P` is the actual uniform83 CDT law and `Q` the independent infinite Gaussian
law, the two comparisons are

```
| Pr[actual accepts AND output in S] - E_P[F_S] | <= eta
| E_P[F_S] - E_Q[F_S] | <= SDist(P,Q) < 2^-78.
```

The second line uses bounded-kernel contraction with coefficient 1. It is
valid for the infinite support of Q. All implementation arithmetic bounds are
used under P; they are not applied to the infinite ideal CDT tail.

Consequently the final joint-event difference satisfies

```
| Pr[actual accepts AND output in S]
  - Pr[ideal accepts AND output in S] |
  < 29/2^48 + 2^-78 < 30/2^48 < 2^-43.
```

The event `S` is arbitrary: it may be finite or infinite, and may include
integers outside the machine output range.

## Representation boundaries

The distinction between unsigned and unbounded outputs matters:

- `round(128,0)=2^63`, so the actual returned word is read with `to_uint`.
- `round(166,2^72-1)=167*2^56 < 2^64`, including the final upward rounding.
- `round(256,0)=2^64` in the ideal tail; it must not become zero by word wrapping.

## Scope and reproduction

Both experiments have checked single-attempt losslessness. This result compares
unconditioned accepted-output masses for every S. The subsequent
[conditional-distribution proof](conditional-accepted-output.md) derives positive
acceptance bounds and compares the two native distributions after acceptance.
Identification with a separately proved closed-form rounded Gaussian law, random
signs, retry termination, the output distribution of the whole Gaussian stream,
the joint law of rejected output values, concrete SHAKE uniformity, the published
Renyi guarantee and complete APIs remain separate obligations.

The 10 new local files comprise the independent specification, exact rounding,
CDT byte patch, actual returned-pair experiments, bounded-expectation contraction,
ideal-kernel properties, fixed-CDT event bound and complete joint comparison.
At that milestone, all 100 non-NTT files passed fresh integrated checking as
independent main targets with `-no-eco`, `Proofs:check` and the EOF completion guard.
All 18 gate regression tests passed. Previous NTT records are retained with
unchanged hashes; all prior proof, implementation and extraction sources are
unchanged. See `../VALIDATION.md` and `../manifests/verification-results.json`.

The main checked interfaces are:

| File | Main result |
| --- | --- |
| `SigmaRoundedOutputCorrectness` | `sj_actual_rounding` |
| `SigmaCDT83Patch` | `sj_cdt83_patch_count`, `sj_cdt83_expectation` |
| `SigmaJointAttemptBridge` | `sigma_joint_noise72_law` |
| `SigmaJoint203Bridge` | `sigma_joint203_law`, `sigma_joint203_ll` |
| `DistributionExpectationDistance` | `distribution_expectation_distance` |
| `SigmaJointKernelCorrectness` | `sj_noise_kernel_range`, `sj_kernel_actual` |
| `SigmaJointFixedCorrectness` | `sj_point_error`, `sj_fixed_joint_error` |
| `SigmaJointIdealCorrectness` | `sj_ideal_joint_law`, `sj_ideal_joint_ll` |
| `SigmaJointCorrectness` | `sj_joint_output_error`, `sj_joint_output_error_strict` |

```
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```
