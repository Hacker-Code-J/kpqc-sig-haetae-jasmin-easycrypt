# Target mode-2 FFT safe bounds

## Scope

This milestone discharges the signed-arithmetic safety premises of the rounded
eight-stage FFT under the explicit input contract
`fft_coefficient_bound xp 2`. It proves safety for the actual extracted root
table and every reachable schedule prefix from round zero through round eight.

The proof is split across five checked theories:

- `KeygenM23SingularFFTBounds` defines the raw signed-Q16 word invariant and
  proves initializer, root-table, butterfly, and inner-prefix bounds;
- `KeygenM23SingularFFTStageBounds` lifts the invariant through all disjoint
  blocks of one reachable stage;
- `KeygenM23SingularFFTScheduleBounds` composes the eight stages and
  specializes the result to the actual root and bit-reversal tables;
- `KeygenM23SingularFFTGlobalTrace` removes the former safety premise from the
  full decoded endpoint whenever the coefficient bound holds; and
- `KeygenM23SingularFFTErrorTrace` records the explicit endpoint budget and
  the round-0/final wrappers that any future rounded-machine-to-ideal proof
  must discharge.

## Raw signed-Q16 invariant

`fft_word_bound data B` bounds the signed real and imaginary words of every
complex cell by `B`. The extracted root table satisfies
`fft_root_word_bound`, namely a coordinate bound of `65536`.

The initialized and bit-reversed actual array has bound `131072` when every
input coefficient lies in `[-2, 2]`. A safe butterfly maps two operands with
bound `B` to outputs with bound `3 * B`: each rounded root product remains
within `B`, each complex product coordinate is within `2 * B`, and the final
addition or subtraction is within `3 * B`.

The stage proof does not multiply this bound once per butterfly. Butterfly
destinations are disjoint within a stage. It proves that the current pair is
still equal to the stage input, while already processed pairs satisfy the
stage output bound. Consequently each complete stage applies exactly one
factor of three.

The resulting schedule bounds are:

| Prefix round | Raw coordinate bound |
| --- | ---: |
| 0 | 131072 |
| 1 | 393216 |
| 2 | 1179648 |
| 3 | 3538944 |
| 4 | 10616832 |
| 5 | 31850496 |
| 6 | 95551488 |
| 7 | 286654464 |
| 8 | 859963392 |

Every executing round therefore starts at or below `286654464`, which is
sufficient for all four rounded products and all signed additions and
subtractions. The final bound `859963392` is strictly below `2^31`.

`actual_fft_schedule_safe_bound2` discharges the complete
`fft_schedule_safe` predicate. `actual_fft_full_word_bound2` records the final
raw bound. `actual_fft_full_decode_bound2` then exposes the exact decoded
eight-round machine observer without retaining a separate safety premise.

## Global-error target

The remaining error proof is organized around the explicit budget sequence
with base `1/65536` and endpoint `44833/65536`.

`KeygenM23SingularFFTErrorTrace` fixes that endpoint budget, reuses the
already-proved round-0 initializer fact, and compiles the final reduction from
any future `actual_fft_schedule_trace ... fft_trace_eps` theorem to the target
`odd_dft256` endpoint.

What is still missing is the owner-stage rounded-machine-to-ideal lift that
realizes the intermediate recurrence against `ideal_stage`. Accordingly,
`44833/65536` is a recorded target budget and compiled endpoint wrapper, not
yet a theorem about the complete machine output.

## Deliberate boundary

The input coefficient predicate is a theorem premise; its connection to every
actual key-generation slice is still required before this result can be used
unconditionally in the parent procedure.

The final FFT word bound proves signed storage and butterfly nonoverflow only.
It is intentionally not used to claim `fft_sqabs_safe` or
`fft_accumulate_safe`: squaring the coarse coordinate bound is far too large
for the nonnegative signed-32 accumulator contract. Closing the score path
requires a sharper pointwise spectral-energy bound across the three `s1` and
two adjusted-`s2` slices, a quantified unsafe-trace event, or a wider
implementation arithmetic design.

The remaining work is therefore:

1. prove the stage-local owner/index alignment and multiplication-perturbation
   theorem that realizes the recorded global error recurrence;
2. thread the coefficient predicate from the actual sampler/finalizer state;
3. establish squared-magnitude and five-pass accumulator safety; and
4. connect the resulting score to acceptance and retry semantics.

## Verification

The reproducible gate is:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The retained gate compiles every manifest entry with `-no-eco` and then runs
the proof-hole, authored-axiom, and debug-command scans.
