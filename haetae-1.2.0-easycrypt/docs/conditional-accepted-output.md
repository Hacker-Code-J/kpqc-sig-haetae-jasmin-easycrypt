# Conditional distributions after sampler acceptance

This stage conditions the existing actual and independent ideal experiments
on their own acceptance events. If `A` means acceptance and `R` is the rounded
unsigned magnitude, the conditional event probability is

```
Pr[R in S | A] = Pr[A and R in S] / Pr[A].
```

The denominator is different for each experiment. No equality of the two
acceptance probabilities is assumed.

## Native conditional distributions and execution connection

`SigmaConditionalSpec` defines a distribution of `(integer magnitude, boolean
acceptance)` pairs for each side. The actual pair distribution uses the exact
word observer already proved equivalent to the extracted Jasmin attempt under
independent uniform 83-bit CDT, 72-bit noise and 48-bit rejection inputs.
Its accepted-event masses are proved equal to the corresponding probabilities
of `SigmaJoint203Experiment.sample`.

The ideal pair distribution retains `SigmaJointIdeal.sample`: the full infinite
nonnegative sigma16 Gaussian input, uniform72 noise, the exact raw Gaussian
acceptance formula, and unbounded integer rounding. Its masses are also linked
to that experiment's probabilities.

The two output distributions are actual native `Distr` objects:

```
sc_actual_conditioned(p) = dmap(dcond(sc_actual_pair(p), sc_accepted), sc_output)
sc_ideal_conditioned     = dmap(dcond(sc_ideal_pair,     sc_accepted), sc_output).
```

`sc_output` projects the integer component. Neither the ideal Gaussian input
nor its rounded output is truncated or converted to a machine word.

## Acceptance cannot have zero mass

The quantitative lower bounds are

```
Pr[actual attempt accepts] >= 1/7
Pr[ideal attempt accepts]  >= 1/8.
```

The actual bound holds first with the CDT and noise candidate bytes fixed,
while the 48 rejection bits are resampled uniformly. It is a probability over
those rejection bits, not over a completely fixed deterministic call. The
subsequent 72/83-bit averaging randomizes the noise and CDT inputs as well.
The checked machine exponent lies in `[0,2/3]` after scaling by `2^48`, so the
linear exponential bound gives `exp(-xi/2^48)>=1/3`. The actual zero factor is
at least `1/2`, and the existing exponential/rejection error is at most
`alpha*28/2^48`. These inequalities imply a probability greater than `1/7`;
the public theorem retains the non-strict bound. Uniform noise and CDT averaging
preserve it.

The ideal lower bound follows by transferring the actual bound through the
previous joint probability error. The implementation's bounded exponent domain
is not applied to the infinite ideal CDT tail.

Both conditioned distributions are proved lossless (total mass one). Native
`dcondE` has a ratio convention even at zero mass; the proved positive lower
bounds ensure the final results do not rely on that convention. No positivity
or input-fit premise remains in the final distribution contracts.

## Normalization error and statistical distance

Let `delta=29/2^48+2^-78`. For a fixed output set S, let `a,b` be the two joint
accepted-event masses, and `P,Q` their respective acceptance probabilities.
The earlier theorem bounds both `|a-b|` and `|P-Q|` by delta. Together with
`0<=a<=P`, `0<=b<=Q`, and positive denominators, real arithmetic proves

```
|a/P-b/Q| <= 2*delta/P.
```

Using the common lower bound `1/8` yields the uniform bound

```
|mu(sc_actual_conditioned(p),S)-mu(sc_ideal_conditioned,S)|
  <= 16*(29/2^48+2^-78) < 2^-39.

SDist(sc_actual_conditioned(p),sc_ideal_conditioned)
  <= 16*(29/2^48+2^-78) < 2^-39.
```

The non-strict common bound is established before taking the supremum over
all output events; its strictly smaller numerical margin then proves the
strict statistical-distance statement. There is no additional factor two
when taking this supremum. S is any set of integer magnitudes.

## Scope and reproduction

The reference in this milestone is the **previous independent ideal experiment
conditioned on acceptance**. The subsequent
[Gaussian identification](gaussian-magnitude-identification.md) proves that it
is exactly the rounded absolute value of the independent integer Gaussian
with weights exp(-k²/2^153), preserving the existing actual error bound.
Random signs, repeated rejection, the distribution of the whole Gaussian
stream, concrete SHAKE randomness, the published Renyi guarantee, Hyperball
mathematics and complete APIs remain separate obligations.

Six new specification/proof files provide native conditionals, actual and
ideal execution links, acceptance lower bounds, a generic ratio estimate,
and the final event/SDist composition. At that milestone, all 106 non-NTT files passed
fresh integrated checks as separate main targets using `-no-eco`, `Proofs:check`
and the EOF completion guard. All 18 gate regression tests passed. The 12 NTT
records are retained with unchanged hashes; all prior proof, production and
extraction sources are unchanged. See `../VALIDATION.md` and the verification
manifest for exact source hashes, commands and timing.

| File | Main checked result |
| --- | --- |
| `SigmaConditionalSpec` | Native actual/ideal pair and conditional distributions |
| `SigmaAcceptanceLowerBound` | `sc_actual_point_lower`, `sc_actual_acceptance_lower`, `sc_ideal_acceptance_lower` |
| `ConditionalRatioBound` | `conditional_ratio_error_lower` |
| `SigmaConditionalActual` | `sc_actual_conditioned_law`, `sc_actual_conditioned_ll` |
| `SigmaConditionalIdeal` | `sc_ideal_conditioned_law`, `sc_ideal_conditioned_ll` |
| `SigmaConditionalCorrectness` | `sc_conditioned_event_error`, `sc_conditioned_sdist_strict`, `sc_conditioned_distributions_correct` |

The helper conditional-losslessness lemmas state a positivity premise; the
final `SigmaConditionalCorrectness` contracts discharge it with the proved
numerical lower bounds. No project axiom or numerical oracle is added.

```
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```
