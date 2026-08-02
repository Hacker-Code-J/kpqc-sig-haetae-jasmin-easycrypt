# Target mode-2 FFT k-prefix bridge

## Scope

This milestone lifts the exact decoded one-butterfly result through an arbitrary
prefix of `KeygenM23SingularFFTSpec.fft_k_prefix`. For every complex-cell index
in `0..255`, the final machine array decodes to an explicit observer that
records the rounded butterfly result at processed destinations and the original
decoded value everywhere else.

The result remains conditional on signed safety at every executed butterfly.
It is an exact machine-prefix theorem, not yet a numerical approximation theorem
against the ideal FFT schedule.

## Schedule and safety contracts

`easycrypt/spec/KeygenM23SingularFFTKPrefixBridge.ec` defines the integer
schedule projections

- `fft_k_even_index n k = to_uint(n) + k`;
- `fft_k_odd_index n md2 k = to_uint(n) + k + to_uint(md2)`; and
- `fft_k_twid_index stride k = k * to_uint(stride)`.

`fft_k_schedule_wf` requires a nonnegative prefix no longer than `md2`, keeps
both destination ranges within the 256 complex cells, and bounds every executed
`k * stride` twiddle within the 256-entry root table. The quantified
executed-index condition deliberately excludes the first unexecuted twiddle.
This matters at the reachable first stage: `md2 = 1` and `stride = 256`, so the
only executed root index is `0`, while the old prefix-end condition incorrectly
required `256 < 256`. The accompanying lemmas prove the three index bounds,
destination distinctness, and the exact correspondence between the extracted
`W64` schedule arithmetic and these integer indices.

`fft_k_prefix_safe` quantifies `fft_butterfly_safe_at` over every `k` before the
prefix endpoint. Crucially, each premise is evaluated on
`fft_k_prefix ... k`, the exact evolving machine state immediately before that
butterfly executes. The theorem does not assume safety only on the initial
array and does not claim that the actual eight-stage execution establishes this
predicate.

## Exact decoded prefix

`fft_k_prefix_decode_at` is deliberately defined on the rounded machine
surface:

- a processed even destination is the rounded even result computed from its
  exact pre-step prefix state;
- a processed odd destination is the corresponding rounded odd result from the
  same pre-step state; and
- every other cell is the original decoded input.

This observer preserves the Q16 multiplication rounding exposed by
`fft_butterfly_even_decode_at` and `fft_butterfly_odd_decode_at`. Replacing it
with exact complex multiplication would be false because one scalar rounded
product may differ from the exact product by half an ulp.

The proof first transports the one-butterfly destination and frame theorems to
`fft_k_step`. Successor lemmas then identify the two newly processed observer
cells and show that every other observer cell is unchanged. The main theorem

```text
fft_k_prefix_decode
```

uses induction on the processed count to prove pointwise equality between the
decoded final `fft_k_prefix` array and `fft_k_prefix_decode_at` for every valid
complex-cell index.

## Deliberate boundary

This milestone closes only the inner `k`-prefix composition step. It does not:

1. discharge `fft_k_prefix_safe` for reachable initialized states;
2. turn the rounded prefix observer into a global error bound against the exact
   complex schedule;
3. establish squared-magnitude, accumulator, score, acceptance, or packing
   semantics.

The arbitrary block-prefix composition is now closed by
[`23-target-keygen-fft-block-prefix-bridge.md`](23-target-keygen-fft-block-prefix-bridge.md).
The stage bridge now specializes it to each reachable outer stage schedule;
see [`24-target-keygen-fft-stage-bridge.md`](24-target-keygen-fft-stage-bridge.md).
The schedule bridge now composes all eight stages under explicit safety; see
[`25-target-keygen-fft-schedule-bridge.md`](25-target-keygen-fft-schedule-bridge.md).
The later [safe-bounds milestone](26-target-keygen-fft-safe-bounds.md)
discharges that safety contract under coefficient bound two.
The later [error-trace milestone](28-target-keygen-fft-error-trace.md)
identifies the composed rounded recurrence with `ideal_stage` and carries the
root-table, incoming-state, and per-butterfly rounding errors through all eight
rounds. Squared-magnitude and accumulator safety remain open.

## Verification

Run the complete authored gate:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles this theory from source with `-no-eco` and includes it in the
proof-hole, project-authored-axiom, and debug-command scans.
