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

The finish logic therefore prevents an unconditional correspondence theorem
between `mode2_singular_word` and the paper statistic without an explicit tie
premise or resolution. A correspondence theorem must either:

1. assume a unique selected minimum;
2. expose a multiplicity-dependent tie deficit; or
3. follow a corrected implementation that applies the remainder adjustment
   exactly once.

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

Relating that decoded-table score to the paper quantity additionally requires
an axiom-free complex/odd-root DFT development, a certificate for every
rounded root-table coordinate, and an explicit resolution of the tie defect.
Acceptance can then be related only outside the proved numerical error band.

Outer key-generation termination is a later probabilistic theorem.  The
paper's reported `0.1` acceptance rate is empirical and is not a proof of
losslessness for the deterministic counter-indexed SHAKE loop.
