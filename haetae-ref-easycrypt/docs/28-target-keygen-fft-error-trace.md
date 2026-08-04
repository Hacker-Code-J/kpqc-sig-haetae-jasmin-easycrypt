# Target mode-2 FFT machine-to-ideal error trace

## Scope

This milestone proves a coordinatewise numerical-error bound from the rounded
Q16 FFT used by the fixed mode-2 singular evaluator to the exact complex
`odd_dft256` specification. The reusable theorem assumes coefficient magnitude
at most two. The target refinement discharges that premise for all five slices
in the immutable first-attempt trace.

The separate accumulator bridge now carries this endpoint through decoded
squared magnitudes and the five-pass running sum under an explicit evolving
signed-safety premise. Neither theorem covers later retry attempts, the final
score correspondence, or acceptance.

## Stage perturbation

`KeygenM23SingularFFTStageErrorBridge` combines three checked facts at each
butterfly owner:

- the decoded table root is within `1/131072` per coordinate of the exact
  `ideal_twiddle`;
- the current odd operand has raw coordinate bound `2 * 3^round`; and
- the rounded complex product contributes `1/65536` local coordinate error.

The multiplication comparison is deliberately split as

```text
decoded_root * machine_odd
  -> ideal_root * machine_odd
  -> ideal_root * ideal_odd
```

so the proof uses the machine word bound for the root perturbation and the
unit coordinate bound for the exact root when propagating input error. This
avoids an unnecessary product of the root and input errors.

The resulting recurrence is

```text
eps(round + 1)
  = 3 * eps(round) + (2 * 3^round + 1) / 65536.
```

`actual_fft_stage_low_close` and `actual_fft_stage_high_close` prove the two
butterfly lanes. `actual_fft_stage_close_at` then uses the reachable schedule
parameters and the unique owner block to normalize every coordinate in
`0..255` to one of those lanes.

## Eight-round trace and endpoint

`KeygenM23SingularFFTErrorTrace` starts from the proved initializer budget
`eps(0) = 1/65536` and checks the explicit numerators

```text
1, 6, 25, 94, 337, 1174, 4009, 13486, 44833.
```

`actual_fft_schedule_explicit_trace_bound2` inducts over all prefixes from
zero through eight. At each step it obtains the exact reachable schedule
parameters, current word bound, and current stage-safety fact from the existing
schedule bridges, applies `actual_fft_stage_close_at` at every coordinate, and
rewrites the exact ideal schedule successor.

The unconditional reusable endpoint is
`actual_fft_full_odd_dft256_close_bound2`: for every valid coordinate and every
input satisfying `fft_coefficient_bound xp 2`, the decoded complete machine FFT
is within `44833/65536` per real and imaginary coordinate of
`odd_dft256 (fft_coefficient_vector xp)`.

## First-attempt reachability

`TargetKeygenM23SingularFFTInputBounds` exports
`mode2_fft_slot_full_odd_dft256_close_bound2` for every one of the three sampled
`s1` and two finalized-`s2` slots. The sampler/finalizer bridge supplies the
coefficient bound, and the theorem remains parameterized by the threaded FFT
scratch array because the initializer overwrites the active region.

`TargetKeygenM23FullFirstAttempt` exposes the corresponding immutable-snapshot
wrapper `first_attempt_snapshot_fft_slot_full_odd_dft256_close_bound2`.

`TargetKeygenM23FirstAttemptAccumulator` then exports
`first_attempt_snapshot_accumulator_error`. The snapshot discharges all five
coefficient bounds; the theorem retains `first_attempt_trace_accumulator_safe`
for the actual evolving `W32` updates. The subsequent accumulator-safety
theory proves that a conservative ideal headroom trace implies this machine
trace, and the wrapper exports the error bound outside the corresponding
headroom failure event.

## Deliberate boundary

The FFT endpoint is coordinatewise. It must not be converted into an
accumulator safety claim by squaring the coarse raw word bound. The checked
headroom theorem instead uses a `127` decoded-coordinate cap plus ideal prefix
energy margins. Remaining work includes:

1. a probability bound for the conservative headroom failure event;
2. a score-level comparison with the intended singular statistic;
3. propagation of the input and error facts to later retry attempts; and
4. acceptance and outer-loop termination.

## Verification

Run:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles all 51 authored manifest entries with `-no-eco`, including
the stage-error bridge, global error trace, conditional accumulator bridge,
accumulator-headroom safety theorem, target slice endpoint, and first-attempt
wrappers, before running the
proof-hole, authored-axiom, and debug scans.
