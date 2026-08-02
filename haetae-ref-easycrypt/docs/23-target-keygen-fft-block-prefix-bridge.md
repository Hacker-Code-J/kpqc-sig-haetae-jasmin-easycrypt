# Target mode-2 FFT block-prefix bridge

## Scope

This milestone lifts the exact decoded inner-prefix result through an arbitrary
prefix of `KeygenM23SingularFFTSpec.fft_blocks_prefix`. For every complex-cell
index in `0..255`, the final machine array decodes to a folded observer whose
current block is evaluated from the exact rounded machine state produced by all
earlier blocks.

The result remains conditional on signed safety for every executed butterfly.
It is an exact rounded-machine block-prefix theorem. It is not the stage
bridge and does not approximate the ideal FFT schedule.

## Executed-index schedule repair

`KeygenM23SingularFFTKPrefixBridge.fft_k_schedule_wf` now bounds exactly the
twiddle indices that execute:

```text
forall k, 0 <= k < processed => k * to_uint(stride) < 256.
```

The former endpoint condition bounded `processed * stride`, which is the first
unexecuted twiddle. It made the reachable first stage vacuous: with `m = 2`,
`md2 = 1`, `stride = 256`, and one executed inner iteration, the only accessed
twiddle is index `0`, but the old condition incorrectly required `256 < 256`.

The block theory carries the same executed-index formulation and includes
`fft_blocks_schedule_wf_stage0`, a checked certificate for all 128 blocks of
that first-stage schedule. The certificate establishes schedule
non-vacuity only; it does not establish signed arithmetic safety.

## Block schedule and evolving safety

`easycrypt/spec/KeygenM23SingularFFTBlockPrefixBridge.ec` defines integer block
starts and ends together with their `W64` representation. Its schedule contract
requires:

- a nonnegative block-prefix length;
- positive `m` with `m = 2 * md2`;
- every complete processed block to fit in the 256 complex cells; and
- every executed inner-loop twiddle index to fit in the 256-entry root table.

`fft_blocks_prefix_safe` quantifies the existing `fft_k_prefix_safe` contract
over every processed block. For block `b`, safety is evaluated on
`fft_blocks_prefix ... b`, the exact machine state immediately before that
block executes. One-block decoding additionally states `0 <= b` explicitly;
the outer induction supplies that premise from its prefix index.

No theorem in this milestone proves that initialized reachable states satisfy
the safety contract.

## Folded decoded observer

`fft_blocks_prefix_decode_at` is a scalar `foldl` over the processed block
indices. At a cell inside the current block, its step selects the already
proved rounded `fft_k_prefix_decode_at` observer on that block's exact
pre-state. Outside the block, it retains the previously folded value.

This form avoids division or an owner-block calculation while preserving the
machine's Q16 rounding. Replacing it with exact complex multiplication would
erase the local rounding already exposed by the butterfly bridge and would be
false.

The proof supplies:

- exact integer/`W64` block-start correspondence and bounds;
- a local K-prefix schedule for every processed block;
- exact one-block decoded semantics and an outside-block frame;
- zero, successor, current-block, and framed observer equations; and
- the main induction theorem `fft_blocks_prefix_decode`.

The main theorem proves pointwise equality between the decoded final
`fft_blocks_prefix` array and the folded observer for every valid complex-cell
index under the schedule and evolving-safety contracts.

## Deliberate boundary

This milestone closes only arbitrary complete block prefixes. It does not:

1. discharge `fft_blocks_prefix_safe` on the reachable machine trace;
2. identify a complete `fft_stage` with `ideal_stage`;
3. prove a global FFT error bound;
4. prove squared-magnitude or accumulator safety and nonoverflow; or
5. establish score, acceptance, retry, packing, or modes 3/5 semantics.

The [stage bridge](24-target-keygen-fft-stage-bridge.md) now specializes the
block-prefix theorem to each reachable stage schedule. The
[schedule bridge](25-target-keygen-fft-schedule-bridge.md) composes all eight
stages while keeping the signed-safety premise explicit. The remaining FFT
work must discharge that premise and prove the numerical-error recurrence.

## Verification

Run the complete authored gate:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles this theory from source with `-no-eco` and includes it in the
proof-hole, project-authored-axiom, and debug-command scans.
