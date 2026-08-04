# Target mode-2 FFT safe bounds

## Scope

This milestone discharges the signed-arithmetic safety premises of the rounded
eight-stage FFT under the explicit input contract
`fft_coefficient_bound xp 2`. It proves safety for the actual extracted root
table and every reachable schedule prefix from round zero through round eight.

The proof and error lift are split across six checked theories:

- `KeygenM23SingularFFTBounds` defines the raw signed-Q16 word invariant and
  proves initializer, root-table, butterfly, and inner-prefix bounds;
- `KeygenM23SingularFFTStageBounds` lifts the invariant through all disjoint
  blocks of one reachable stage;
- `KeygenM23SingularFFTScheduleBounds` composes the eight stages and
  specializes the result to the actual root and bit-reversal tables;
- `KeygenM23SingularFFTGlobalTrace` removes the former safety premise from the
  full decoded endpoint whenever the coefficient bound holds; and
- `KeygenM23SingularFFTStageErrorBridge` proves the root/input perturbation
  bound for either owner lane and normalizes every coordinate to its unique
  butterfly owner; and
- `KeygenM23SingularFFTErrorTrace` composes that stage theorem through all
  eight prefixes and exposes the explicit odd-DFT endpoint.

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

## Actual first-attempt reachability

`TargetKeygenM23SingularFFTInputBounds` connects the generic coefficient
premise to the sampler/finalizer state exposed by the peeled first attempt of
the actual mode-2 parent. Slots zero through two read the three sampled `s1`
polynomials, whose coefficients lie in `[-1,1]`. Slots three and four read the
two finalized `s2` polynomials. Each finalized coefficient is a sampled
`[-1,1]` value minus a verified low decomposition term in `[-1,1]`, so it lies
in `[-2,2]`.

`mode2_fft_inputs_bound2_of_mode2_sampler_finalize` proves the combined
five-slice predicate. `TargetKeygenM23FullFirstAttempt` threads it into the
immutable snapshot and exports schedule-safety and final-word-bound
corollaries for every valid slot and arbitrary scratch input. The arbitrary
scratch quantification matches `_singular_full`'s threaded workspace; the FFT
initializer overwrites the active cells before each schedule.

## Checked global-error lift

The checked error proof uses an explicit budget sequence with base `1/65536`
and endpoint `44833/65536`.

For round `r`, the stage recurrence is

```text
eps(r + 1) = 3 * eps(r) + (2 * 3^r + 1) / 65536.
```

`KeygenM23SingularFFTStageErrorBridge` accounts separately for local product
rounding, the certified root-table error, and perturbation of the odd input.
It proves both butterfly lanes, reduces an arbitrary output coordinate to its
unique block and lane, and obtains the recurrence above without introducing a
spurious product of the root and input errors.

`actual_fft_schedule_explicit_trace_bound2` then proves the complete prefix
trace by induction. `actual_fft_full_odd_dft256_close_bound2` specializes the
round-eight result to `odd_dft256`, with coordinatewise error at most
`44833/65536` for every coefficient-bounded input. The target bridge exports
the same theorem for every valid first-attempt slice. See
[`28-target-keygen-fft-error-trace.md`](28-target-keygen-fft-error-trace.md).

`KeygenM23SingularFFTAccumulatorBridge` uses this endpoint to bound decoded
squared magnitude and every prefix of the five-pass ideal-energy sum. Its
first-attempt wrapper discharges the coefficient premise but retains the
evolving `fft_accumulate_safe` trace. See
[`29-target-keygen-fft-accumulator-trace.md`](29-target-keygen-fft-accumulator-trace.md).

## Deliberate boundary

The input coefficient predicate remains a premise of the reusable generic FFT
theories. Its connection to all five slices is now discharged for the exposed
actual first attempt, but no theorem in this milestone records equivalent
sampler/finalizer facts for each later residual-loop attempt.

The final FFT word bound proves signed storage and butterfly nonoverflow only.
It is intentionally not used to claim `fft_sqabs_safe` or
`fft_accumulate_safe`: squaring the coarse coordinate bound is far too large
for the nonnegative signed-32 accumulator contract. The new conditional error
bridge therefore keeps the exact evolving safety trace visible. The subsequent
headroom theory proves that a conservative ideal-energy trace and decoded
coordinate cap imply that machine trace. Closing the unconditional score path
still requires a probability bound for headroom failure or a wider
implementation arithmetic design.

The remaining work is therefore:

1. quantify failure of the conservative five-pass accumulator headroom event;
2. lift the input and error facts to later retry attempts; and
3. connect the resulting score to acceptance and retry semantics.

## Verification

The reproducible gate is:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The retained gate compiles all 51 manifest entries with `-no-eco`, including
the stage-error, accumulator, and first-attempt input bridges, and then runs
the proof-hole, authored-axiom, and debug-command scans. The target-level
details are in
[`27-target-keygen-fft-input-reachability.md`](27-target-keygen-fft-input-reachability.md),
[`28-target-keygen-fft-error-trace.md`](28-target-keygen-fft-error-trace.md),
[`29-target-keygen-fft-accumulator-trace.md`](29-target-keygen-fft-accumulator-trace.md),
and
[`30-target-keygen-fft-accumulator-headroom.md`](30-target-keygen-fft-accumulator-headroom.md).
