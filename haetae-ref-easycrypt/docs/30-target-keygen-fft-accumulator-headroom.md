# Target mode-2 FFT accumulator headroom

## Scope

This milestone replaces the bare first-attempt machine-safe-trace premise with
a conservative condition stated over the ideal odd-root FFT outputs and the
already-proved numerical error budgets. It covers all five accumulator passes
of the exposed first attempt. It does not assign a probability to headroom
failure, cover later retry attempts, identify the final score with the paper's
singular statistic, or prove acceptance or termination.

The checked theory is
`easycrypt/spec/KeygenM23SingularFFTAccumulatorSafety.ec`. The target wrapper
is extended in
`easycrypt/refinement/TargetKeygenM23FirstAttemptAccumulator.ec`.

## Headroom condition

For every accumulator coordinate and processed prefix,
`mode2_accumulator_prefix_headroom` requires both

- the folded error budget to be no larger than the folded ideal energy; and
- ideal energy plus that error budget to be strictly below the decoded signed
  Q16 ceiling `2^31 / 2^16 = 32768`.

The first inequality gives the lower margin needed to prove that the actual
decoded accumulator prefix is nonnegative. The second gives the upper margin
needed to prove that it remains a nonnegative signed 32-bit word.

For the current FFT output,
`mode2_accumulator_coordinate_headroom` requires the absolute value of each
ideal real and imaginary coordinate plus the checked endpoint error
`44833/65536` to be at most `127`. This implies a raw signed-coordinate bound
of `127 * 65536 = 8323072`. Each rounded self-square is then at most
`1057030144`, so their sum is at most `2114060288 < 2^31` and
`fft_sqabs_safe` follows.

`mode2_accumulator_headroom_step` combines the current prefix margin, current
coordinate margin, and next-prefix margin. The trace quantifies that condition
over every executed slice and all 256 accumulator coordinates.

## Machine-safety theorem

`mode2_actual_accumulate_step_safe_from_headroom` proves one exact
`fft_accumulate_safe` obligation on the actual evolving machine state. It uses
the existing coefficient-bound-two FFT endpoint, the local squared-magnitude
rounding theorem, and the accumulator-prefix error theorem. In particular,
the proof checks the signed integer sum used by the target update; it does not
replace the machine predicate with a decoded-real approximation.

`mode2_actual_accumulate_safe_from_headroom` inducts over the slice prefix.
At each step, safety of the preceding exact machine trace makes the prefix
error theorem available, and the current ideal headroom step proves the next
machine update safe. Thus ideal headroom for the full five-slice trace implies
the exact evolving signed-`W32` safety trace required by the accumulator error
bridge.

## Conservative bad event

`mode2_accumulator_headroom_bad_event` is the existence of an executed
slice/coordinate at which the sufficient headroom step fails.
`mode2_accumulator_headroom_trace_iff_no_bad_event` proves that its absence is
equivalent to the headroom trace. The event is intentionally conservative:
headroom failure is not claimed to be equivalent to an actual overflow.

The first-attempt wrapper exposes
`first_attempt_trace_accumulator_headroom_bad` and proves:

- `first_attempt_snapshot_accumulator_safe_outside_headroom_bad`; and
- `first_attempt_snapshot_accumulator_error_outside_headroom_bad`.

Consequently, outside this ideal-side failure event, the existing decoded
five-slice energy-error theorem no longer needs a separately supplied machine
safe-trace premise.

## Remaining probability boundary

The current target sampler proofs provide exact finite-stream, range, frame,
and progress-certificate results. They do not provide a distribution or tail
bound for the odd-root DFT energies used in the headroom condition. Therefore
this milestone proves no probability bound for
`mode2_accumulator_headroom_bad_event`.

Closing that boundary requires a sampler-distribution theorem strong enough
to bound the ideal spectral prefix energies and coordinate maxima, followed by
lifting the same facts to every retry attempt. The tie-sensitive finish rule,
score correspondence, acceptance, retry termination, and packing remain
separate obligations.

## Verification

Both proof files are entries in
`manifests/keygen-m23-matrix-proof-files.txt` and are checked by:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate performs fresh `-no-eco` compilation and the existing proof-hole,
authored-axiom, and debug-command scans. No axiom or final assumption is added;
the missing headroom-event probability remains recorded under
`OBL-FFT-SAFE-TRACE`.
