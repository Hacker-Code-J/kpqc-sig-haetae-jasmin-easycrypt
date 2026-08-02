# Target mode-2 FFT schedule bridge

## Scope

This milestone composes the exact per-stage FFT bridge through the full
eight-round machine fold. It covers the schedule prefix states `0..8`, where
`round = p` names the machine state immediately before stage `p + 1`:

| round | m | md2 | stride |
| --- | --- | --- | --- |
| 0 | 2 | 1 | 256 |
| 1 | 4 | 2 | 128 |
| 2 | 8 | 4 | 64 |
| 3 | 16 | 8 | 32 |
| 4 | 32 | 16 | 16 |
| 5 | 64 | 32 | 8 |
| 6 | 128 | 64 | 4 |
| 7 | 256 | 128 | 2 |
| 8 | 512 | 256 | 1 |

The first eight rows are the executing rounds. The terminal `(512, 256, 1)`
state is tracked as the `processed = 8` endpoint, but it is not an executing
round.

`easycrypt/spec/KeygenM23SingularFFTScheduleBridge.ec` adds a full-state-plus-
scalar observer to the existing exact stage bridge. Its folded state carries:

- the exact machine schedule state `(data, m, md2, stride)`; and
- the decoded scalar observer for the current cell.

`fft_schedule_decode_step` threads the machine state through
`fft_round_step` and replaces the scalar observer with the owner-block
decoded value for the current round. `fft_schedule_decode_prefix` folds that
step across `iota_ 0 processed`. `fft_schedule_prefix_decode_at` names the
scalar projection. `fft_schedule_safe` asks for stage safety on every already
completed round. `fft_full_decode_at` specializes the observer to
`fft_stages_i = 8`.

The main theorem, `fft_schedule_decode_prefix`, proves that for every
`processed` in `0..8` and every `j` in `0..255`, the decoded machine state of
`fft_schedule_prefix data roots processed` agrees with the folded observer
under `fft_schedule_prefix_safe data roots processed`. The endpoint theorem
`fft_full_decode` specializes this to the full eight-round fold.

## Exact schedule surface

The proof surface consists of:

- `fft_schedule_params_at`, the exact prefix-state predicate for `0..8`;
- `fft_schedule_params_step`, which advances the schedule by one round;
- `fft_schedule_params_reachable`, which maps prefix states `0..7` to the
  reachable outer schedules proved by the stage bridge;
- `fft_schedule_prefix_params`, which tracks the exact prefix-state evolution
  through `fft_schedule_prefix`;
- `fft_schedule_prefix_safe`, which records explicit stage safety for each
  completed round;
- `fft_schedule_prefix_safe_prev` and `fft_schedule_prefix_safe_here`, which
  expose the inductive safety obligations used in the fold;
- `fft_schedule_decode_prefix0`, `fft_schedule_decode_prefixS`, and
  `fft_schedule_decode_prefix_machine`, which establish the folded observer
  shape;
- `fft_schedule_decode_prefix`, which composes the eight executing stages
  under explicit safety; and
- `fft_full_decode`, which specializes the proof to the full `fft_full`
  evaluator.

## Deliberate boundary

This milestone does not discharge `fft_schedule_prefix_safe` on reachable
traces. It does not prove equality with the ideal exact-complex schedule. It
also does not establish global numerical FFT error or accumulator
nonoverflow, finish semantics, packing semantics, or any outer retry or
acceptance result.

## Verification

The reproducible gate for this milestone family is:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The retained `2026-08-02T01:20:20Z` run passed all 41 authored manifest
entries with `-no-eco`, followed by clean proof-hole, authored-axiom, and
debug-command scans.
