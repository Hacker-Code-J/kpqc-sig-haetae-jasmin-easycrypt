# Target mode-2 FFT initialization bridge

## Scope

This milestone gives the exact word-array FFT initializer a decoded complex
meaning. It covers all 256 complex-cell updates (512 word stores) performed by
`fft_init_and_bitrev`, proves their signed-product safety for coefficient
magnitude at most two, and relates the initialized target array to the
bit-reversed ideal twisted input.

This initialization milestone does not cover the rounded butterfly or any of
the eight FFT stages, squared-magnitude accumulation, selection, finish, or
rejection. The follow-on one-butterfly result is documented in
[`21-target-keygen-fft-butterfly-bridge.md`](21-target-keygen-fft-butterfly-bridge.md).
Its exact evolving-state inner-prefix composition is documented in
[`22-target-keygen-fft-k-prefix-bridge.md`](22-target-keygen-fft-k-prefix-bridge.md).

## Decoded surface

`easycrypt/spec/KeygenM23SingularFFTInitBridge.ec` defines:

- `q16_decode_word`, the signed `W32.to_sint / 65536` interpretation;
- `fft_decode_at`, which decodes adjacent array words as one complex value;
- `fft_coefficient_vector`, which embeds the signed coefficient words into
  the transparent real-pair complex theory;
- `fft_table_twist`, which scales a decoded target root by one coefficient;
- `fft_init_cell_safe` and `fft_init_prefix_safe`, the exact signed-fit
  obligations consumed by initialization; and
- `fft_vector_close`, the pointwise 256-cell coordinate-error relation used by
  the next stage proof.

These operations do not reinterpret wrapped arithmetic as integer arithmetic.
Every direct `W32` multiplication is decoded only through
`fft_init_product_to_sint` and an explicit `fft_init_product_safe` fact.

## Complete prefix invariant

The proof first establishes two one-step facts:

- `fft_init_step_decode_written` decodes the newly written bit-reversed cell
  as `fft_table_twist xp roots i`; and
- `fft_init_step_decode_frame` proves that every other bit-reversed cell is
  unchanged.

The frame proof uses the checked `jfft_brv8_exact` table theorem and
involutivity of `bsrev 8`, so distinct source indices cannot alias a
destination cell.

`fft_init_prefix_decode` then inducts over the actual `foldl` prefix. For
`0 <= processed <= 256`, it proves

```text
decode(prefix processed, bsrev8(i)) =
  if i < processed
  then coefficient(i) * decoded_root(i)
  else decode(initial_data, bsrev8(i)).
```

At `processed = 256`, every logical cell has been overwritten. Consequently
`fft_init_and_bitrev_decode` and
`actual_fft_init_and_bitrev_table_bitrev_bound2` identify the whole initialized
array, pointwise on `0..255`, with the exact bit reversal of the decoded-table
twisted coefficient vector. The theorem is independent of the incoming
scratch-array contents.

## Initialization safety

`actual_fft_init_cell_safe_bound2` combines:

- `fft_coefficient_bound xp 2`; and
- the checked target-root coordinate range `[-65536, 65536]`.

Each raw initialization product therefore lies in `[-131072, 131072]`, well
inside signed 32-bit range. `actual_fft_init_prefix_safe_bound2` lifts that
fact to all 256 cells. This closes initialization nonoverflow under the
explicit coefficient predicate; it does not yet connect that predicate to
all five reachable mode-2 slice arrays.

## Ideal-root error endpoint

`actual_root_decode_close` converts the strict target certificate into

```text
cclose (1 / 131072) decoded_target_root(i) ideal_root(i).
```

Scaling by a coefficient gives `actual_table_twist_close_bounded`. Under
coefficient magnitude at most two, the final theorem
`actual_fft_init_and_bitrev_vector_close_bound2` proves

```text
fft_vector_close (1 / 65536)
  (fft_init_and_bitrev data xp jfft_roots jfft_brv8)
  (ideal_bitrev8 (twist256 (fft_coefficient_vector xp))).
```

This is an error relation, not an equality with the exact root: the extracted
table is rounded.

## Deliberate boundary

The exact inner `k`-prefix composition is now closed by
[`22-target-keygen-fft-k-prefix-bridge.md`](22-target-keygen-fft-k-prefix-bridge.md).
The complete block-prefix composition is now closed by
[`23-target-keygen-fft-block-prefix-bridge.md`](23-target-keygen-fft-block-prefix-bridge.md).
The remaining FFT bridge must:

1. lift the now-proved decoded and framed block-prefix theorem through the
   stage and eight-round folds while proving
   the carried `(m, md2, stride)` parameters match `ideal_stage`;
2. discharge the eight-stage signed-fit predicates for coefficient magnitude
   at most two and propagate a global coordinate-error bound to
   `ideal_fft256`; and
3. separately address squared-magnitude and five-pass accumulator safety.

The third item cannot be derived from coefficient bounds alone: the
high-energy example documented in
[`15-target-keygen-singular-numeric-boundary.md`](15-target-keygen-singular-numeric-boundary.md)
already exceeds the nonnegative signed-Q16 accumulator capacity. Any later
score or rejection theorem therefore needs a spectral safe-trace condition,
a quantified unsafe event, or widened arithmetic. Acceptance cannot justify
earlier wrapped arithmetic retroactively.

## Verification

Run the complete authored gate:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles this theory from source with `-no-eco` and includes it in
the proof-hole, project-authored-axiom, and debug-command scans.
