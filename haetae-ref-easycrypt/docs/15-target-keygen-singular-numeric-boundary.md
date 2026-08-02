# Target mode-2 singular numerical boundary

## Scope

The existing refinement proves exact `W32`/`W64` behavior and totality for the
actual fixed `(3, 2, 5, 58, 24)` `_singular_full` call.  This milestone starts
the separate numerical interpretation layer.  It does not identify the word
evaluator with the paper's complex spectral quantity.

The paper defines the mode-2 rejection quantity from the five largest values
of

```text
1 + sum over the five stored secret polynomials of |p(omega)|^2
```

at primitive 512th roots.  Four selected values have weight 58 and the fifth
has weight 24, for total weight `4 * 58 + 24 = 256`.  The reference
implementation is intended to realize the odd-root evaluations with a twisted
256-point Q16 FFT:

- `haetae-ref/src/fft.c:5-11` describes the rounded Q16 root table;
- `haetae-ref/src/fft.c:142-157` defines rounded scalar and complex products;
- `haetae-ref/src/fft.c:185-197` twists and bit-reverses the input;
- `haetae-ref/src/fft.c:213-234` implements the eight radix-2 stages; and
- `haetae-ref/src/polyvec.c:515-568` accumulates five squared magnitudes,
  selects five entries, adds the implicit leading polynomial, and applies the
  `(58, 24)` finish calculation.

## Checked fixed-point facts

`easycrypt/spec/KeygenM23FixedPointSemantics.ec` defines the integer Q16
decoder

```text
mulrnd16_int(x, y) = floor((x * y + 32768) / 65536)
```

and proves:

- `q16_round_error`: the scaled integer rounding error lies in
  `(-32768, 32768]`; and
- `mulrnd16_word_to_sint`: whenever the rounded result fits signed 32-bit
  range, the exact word operation decodes to `mulrnd16_int`.

The theory contains no authored axiom declarations. It derives a signed
shift-by-16 result from the already checked shift-by-32 word theorem and
proves all required range facts. This is an integer fixed-point theorem, not
yet a theorem about real or complex multiplication.

`easycrypt/spec/KeygenM23SingularBoundary.ec` names the remaining local safety
obligations:

- initialization products must fit signed 32-bit words;
- each rounded complex product and butterfly output must fit signed 32-bit
  words;
- both squared-magnitude terms and their sum must be nonnegative signed
  32-bit values;
- every pointwise running accumulator must remain below `2^31`; and
- selection, finish terms, and finish accumulation must remain in their
  signed ranges.

These predicates are intentionally explicit.  Exact word totality does not
imply that signed fixed-point decoding is valid.

`easycrypt/spec/KeygenM23SingularIntegerSemantics.ec` discharges the local
word-to-integer step once those premises are supplied.  Its compiled lemmas
decode:

- a rounded Q16 multiplication and an initialization product;
- both rounded complex-product terms and all four scalar butterfly outputs;
- one squared-magnitude expression;
- one pointwise accumulator update; and
- the frame of every other accumulator entry.

`KeygenM23SingularFFTButterflyBridge` now lifts the butterfly portion through
exactly one valid, distinct-index array update: all four stored words and both
decoded destinations are identified, every other complex cell is framed, and
the local decoded arithmetic is within `1/65536` of the exact decoded-root
complex butterfly. This result remains conditional on
`fft_butterfly_safe_at`. `KeygenM23SingularFFTKPrefixBridge` now composes its
exact rounded destination and frame semantics through an arbitrary valid inner
prefix with safety evaluated on every evolving pre-step state.
`KeygenM23SingularFFTBlockPrefixBridge` composes complete inner loops through
an arbitrary valid block prefix with safety evaluated on every exact pre-block
state. `KeygenM23SingularFFTStageBridge` closes the exact owner-block endpoint
for each reachable complete stage. `KeygenM23SingularFFTScheduleBridge`
composes all eight rounds under explicit per-stage safety, but does not prove
that the safety premise holds on an actual trace.

## Checked tie discrepancy

The implementation does not assign weight 24 to exactly one fifth-ranked
entry.  Its factor is 24 for every selected value equal to the retained
minimum and 58 only for a strictly larger value:

- `haetae-ref/src/polyvec.c:548-565`;
- `haetae-ref-jasmin/jasmin/singular_values.jinc:50-77`; and
- `easycrypt/spec/KeygenM23SingularSpec.ec:105-113`.

`zero_tie_finish_discrepancy` proves the exact finish-stage calculation for
five already-selected zero entries:

```text
implementation: 5 * 24 = 120
paper weights:   4 * 58 + 24 = 256
```

`easycrypt/spec/KeygenM23SingularZeroFinish.ec` strengthens the implementation
side without adding an FFT assumption. `finish_mode2_zero_sum` carries the
zero invariant through initialization, all 251 remaining selector insertions,
minimum selection, and finish accumulation to prove an implementation score
of `120` for any zero 256-word accumulator. `finish_mode2_clear_sum` proves
the same result after the evaluator's actual clear operation. These theorems
still make no claim that the five FFT accumulation passes leave the array
zero.

`easycrypt/spec/KeygenM23SingularTieRegression.ec` gives a separate
finish-stage guard regression.  For five already-selected equal values it
proves:

```text
implementation score = 375000
paper fixed-weight score = 800000
375000 <= 611098 < 800000
```

This demonstrates that the two policies can disagree on the mode-2 guard.
The theorem deliberately does not assert that its selected entries are
reachable from the preceding FFT and selector.

The C reference, Jasmin source, and extracted evaluator all implement the same
multiplicity-sensitive rule.  An unretained, one-off diagnostic over the
retained 100-case KAT corpora observed no retained-minimum tie in modes 2, 3,
or 5.  In the same diagnostic, a disposable mode-2 reference variant that
assigned the remainder exactly once left all 100 response cases
byte-identical; the response-file SHA-256 remained
`8414c29dc5d24b548b748dfc4208796619877a7e2e7605da978a8875fa36951b`.
Only the retained case counts and current response-file hash are reproducible
from this workspace; the diagnostic itself is coverage evidence, not a proof
that ties are unreachable.  Because a reachable guard-changing tie could alter
the retry counter and therefore the generated key pair, the verified
implementation behavior is retained here.  Changing it requires a coordinated
algorithm/specification decision and refreshed compatibility vectors.

The finish logic therefore prevents an unconditional correspondence theorem
between `mode2_singular_word` and the paper statistic.  A future
correspondence theorem must:

1. preserve the current rule and expose its multiplicity-dependent tie
   deficit, or assume a unique selected minimum; or
2. follow a deliberately versioned implementation change that applies the
   remainder adjustment exactly once.

## Range boundary

The verified coefficient facts give stored `s1` coefficients in `[-1, 1]` and
adjusted `s2` coefficients in `[-2, 2]`.  A conservative magnitude calculation
indicates that initialization and the eight butterfly stages can stay in
signed range, but no compiled global range theorem is claimed here. The same
coefficient bounds cannot establish safe squared-magnitude accumulation.

At the first odd root, an all-one degree-255 polynomial has ideal squared
magnitude

```text
1 / sin(pi / 512)^2, approximately 26561.
```

Three such `s1` polynomials alone have ideal energy around `79683`, exceeding
the nonnegative signed-Q16 capacity below `32768`.  Therefore pointwise
coefficient bounds cannot discharge the accumulator contract.  A later
theorem needs one of:

- a proved spectral safe-trace condition;
- a quantified bad-event probability for unsafe traces; or
- widened implementation arithmetic.

Machine acceptance cannot be used retrospectively to prove that earlier
wrapped arithmetic was safe.

## Analytic scaffold

`easycrypt/spec/KeygenM23ComplexReal.ec` now supplies transparent real-pair
complex arithmetic, conjugation, squared-norm, scaling, and coordinatewise
error propagation. `easycrypt/spec/KeygenM23IdealRootDFT.ec` constructively
selects the lower-half-plane 512th root, checks its dyadic primitivity
criterion, defines the abstract odd-root DFT, and proves its coefficient-twist
identity. `easycrypt/spec/KeygenM23IdealFFTSchedule.ec` proves that the pure
exact-complex bit-reversed eight-stage schedule computes `dft256`, and that
the same schedule on the twisted input computes `odd_dft256`.
`easycrypt/spec/KeygenM23FFTTableCertificate.ec` proves
that the extracted 256-entry permutation table is exactly `bsrev 8` and that
all 512 extracted signed root coordinates lie in `[-65536,65536]`.
`KeygenM23RootGeneratorCertificate`, `KeygenM23RootTableRounding`, and
`KeygenM23RootTableTargetBridge` further prove that each of those extracted
coordinates is the unique nearest Q16 encoding of the corresponding exact
`ideal_root j` coordinate, with strict error below `1/131072`.
`KeygenM23SingularFFTInitBridge` lifts these facts through the complete
initialization fold: under coefficient magnitude at most two, all raw products
fit signed `W32`, every destination and frame is exact, and the initialized
vector is within `1/65536` coordinatewise of the exact bit-reversed twisted
input. `KeygenM23SingularFFTButterflyBridge` then supplies the exact
array-level one-butterfly update and local `1/65536` rounding endpoint under
its explicit signed-safety premise. `KeygenM23SingularFFTKPrefixBridge` composes
that exact rounded meaning through every valid inner prefix under explicit
evolving-state safety. `KeygenM23SingularFFTBlockPrefixBridge` further composes
complete inner loops through every valid block prefix on exact evolving
pre-block states.

Those facts remove the exact-root, ideal-schedule, root-table-rounding, and
initialization and single-kernel preliminaries. No theorem yet identifies the
rounded butterfly stage folds with the proved exact-complex schedule.

## Sound next theorem

With the current implementation, the strongest honest bridge has the shape

```text
root-table certificate
and FFT/butterfly safe trace
and squared-magnitude/accumulator safe trace
and finish safe trace
imply
absolute(machine score - tie-sensitive decoded-table score) <= error bound.
```

Relating that decoded-table score to the ideal quantity now requires
discharging the composed schedule's safe decoded trace and proving its global
error against the exact-complex schedule, plus an explicit
multiplicity-sensitive finish statement or versioned policy change.
Acceptance can then be related only outside the proved numerical error band.
The completed table certificate is detailed in
[`19-target-keygen-root-table-rounding.md`](19-target-keygen-root-table-rounding.md).
The initialization endpoint is detailed in
[`20-target-keygen-fft-initialization-bridge.md`](20-target-keygen-fft-initialization-bridge.md).
The one-butterfly endpoint is detailed in
[`21-target-keygen-fft-butterfly-bridge.md`](21-target-keygen-fft-butterfly-bridge.md).
The exact evolving-state inner-prefix endpoint is detailed in
[`22-target-keygen-fft-k-prefix-bridge.md`](22-target-keygen-fft-k-prefix-bridge.md).
The exact evolving-state block-prefix endpoint is detailed in
[`23-target-keygen-fft-block-prefix-bridge.md`](23-target-keygen-fft-block-prefix-bridge.md).

Outer key-generation termination is a later probabilistic theorem.  The
paper's reported `0.1` acceptance rate is empirical and is not a proof of
losslessness for the deterministic counter-indexed SHAKE loop.
