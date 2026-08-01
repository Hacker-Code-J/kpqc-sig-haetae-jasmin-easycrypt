# Target mode-2 FFT stage bridge

## Scope

This milestone lifts the exact decoded block-prefix result to each reachable
outer FFT stage. It covers the eight executing triples:

| r | m | md2 | stride |
| --- | --- | --- | --- |
| 1 | 2 | 1 | 256 |
| 2 | 4 | 2 | 128 |
| 3 | 8 | 4 | 64 |
| 4 | 16 | 8 | 32 |
| 5 | 32 | 16 | 16 |
| 6 | 64 | 32 | 8 |
| 7 | 128 | 64 | 4 |
| 8 | 256 | 128 | 2 |

For every reachable triple and every complex-cell index in `0..255`, the
final machine array decodes to an owner-block observer that:

- picks the unique block containing that cell by integer division;
- evaluates the rounded block-prefix observer on the exact pre-block machine
  state for that owner block;
- uses the block frame lemmas to show every later non-owner block leaves that
  cell unchanged; and
- keeps the exact pre-block safety premise explicit.

The terminal `(512, 256, 1)` round is excluded. `fft_stage_reachable_params`
names only the eight executing schedules, and the actual schedule prefix stops
after stage 8.

## Exact stage surface

`easycrypt/spec/KeygenM23SingularFFTStageBridge.ec` defines the stage
reachability predicate, the stage schedule contract, the owner-block
calculation, the stage safety predicate, and the owner-block decoded observer.

The main theorem is `fft_stage_decode_reachable`. It proves that:

- reachable parameters imply `fft_stage_schedule`;
- every `j` in `0..255` has a unique owner block with the expected block-range
  bounds; and
- under `fft_stage_safe`, the decoded `fft_stage` equals the owner-block
  observer at `j`.

Supporting lemmas `fft_stage_schedule_r1` through `fft_stage_schedule_r8`,
`fft_stage_owner_block_range`, `fft_stage_owner_block_here`,
`fft_stage_owner_block_unique`, `fft_stage_owner_block_outside`,
`fft_stage_decode_at_owner`, `fft_stage_decode_at_suffix`, and
`fft_blocks_prefix_decode_at_stage` organize the proof.

## Deliberate boundary

This milestone does not:

1. discharge `fft_stage_safe` on reachable traces;
2. compose the eight stages into the full `fft_full` trace;
3. prove global FFT error or accumulator nonoverflow; or
4. establish equality with the ideal exact-complex schedule.

The remaining FFT bridge should compose the eight stage proofs and then carry
the error and safety obligations through the accumulator and finish logic.

## Verification

Run the complete authored gate:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles this theory from source with `-no-eco` and rejects proof
holes, project-authored axiom declarations, and leftover debug commands.
