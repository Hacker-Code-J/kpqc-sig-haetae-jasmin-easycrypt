# Target mode-2 FFT butterfly bridge

## Scope

This milestone gives one invocation of the extracted rounded FFT butterfly an
exact array-level and decoded complex meaning. It covers all four destination
word stores, both destination complex cells, and every unchanged cell. It also
proves the local Q16 rounding error against complex multiplication of the
decoded root and odd operands.

The signed decoding theorem is conditional on the existing
`fft_butterfly_safe` predicate. This milestone does not claim that every
scheduled butterfly satisfies that predicate.

## Exact word and frame surface

`easycrypt/spec/KeygenM23SingularFFTButterflyBridge.ec` defines the six source
word projections, the array-indexed safety predicate, the rounded product, and
the corresponding exact decoded butterfly.

For valid `even`, `odd`, and `twid` cells with `even <> odd`:

- `fft_butterfly_words_written` identifies all four stored `W32` values;
- `fft_butterfly_decode_written` identifies both destination complex cells
  under `fft_butterfly_safe_at`; and
- `fft_butterfly_decode_frame` proves every other complex cell unchanged.

The distinctness premise is essential because the implementation writes the
even cell before the odd cell. Without it, the final odd stores can overwrite
the earlier even stores. The `0..255` index premises are also essential
because the target shifts the three `W64` indices before accessing the
512-word arrays.

The existing target refinement
`TargetKeygenM23SingularFFT.fft_butterfly_correct` connects the extracted
`_fft_butterfly` procedure to the pure word operation used by these theorems.

## Signed decoding boundary

`fft_butterfly_safe_at` instantiates the established
`KeygenM23SingularBoundary.fft_butterfly_safe` contract with the six words read
from the two data cells and one root cell. The contract contains:

- four safe rounded multiplications;
- signed-fit checks for the real and imaginary product combinations; and
- signed-fit checks for all four output additions or subtractions.

Only under this contract may the proof use
`fft_butterfly_outputs_to_sint` to interpret the target words as the intended
signed integers. Exact word totality alone would not exclude `W32` wrap.

## Local rounding endpoint

`q16_mulrnd16_decode_error` proves the generic scalar half-ulp bound

```text
|decode(round16(x * y)) - decode(x) * decode(y)| <= 1 / 131072.
```

The real and imaginary complex products each combine two such terms.
`fft_butterfly_term_rounding_close` therefore proves coordinatewise error at
most `1/65536` between the rounded decoded product and exact multiplication of
the decoded root and odd input.

Finally, `fft_butterfly_decode_close` transports that bound through the even
addition and odd subtraction:

```text
cclose (1 / 65536) decoded_even_output
  (decoded_even_input + decoded_root * decoded_odd_input)

cclose (1 / 65536) decoded_odd_output
  (decoded_even_input - decoded_root * decoded_odd_input).
```

This endpoint measures local arithmetic rounding only. Root-table
approximation and incoming-vector error are deliberately not folded into the
same theorem.

## Deliberate boundary

The `k`-prefix composition step is now closed by
[`22-target-keygen-fft-k-prefix-bridge.md`](22-target-keygen-fft-k-prefix-bridge.md),
using these two destination theorems and the 254-cell frame. The complete
block-prefix composition is now closed by
[`23-target-keygen-fft-block-prefix-bridge.md`](23-target-keygen-fft-block-prefix-bridge.md).
The complete reachable-stage endpoint is now closed by
[`24-target-keygen-fft-stage-bridge.md`](24-target-keygen-fft-stage-bridge.md).
The next FFT bridge must:

1. compose that stage endpoint through all eight rounds while identifying
   `(m, md2, stride)` with `ideal_stage`;
2. discharge `fft_butterfly_safe_at` for every reachable scheduled call and
   propagate root-table, incoming-vector, and local rounding errors to a global
   bound against `ideal_fft256`; and
3. separately address squared-magnitude and five-pass accumulator safety.

The third item cannot follow from coefficient bounds alone. The high-energy
example in
[`15-target-keygen-singular-numeric-boundary.md`](15-target-keygen-singular-numeric-boundary.md)
already exceeds the nonnegative signed-Q16 accumulator capacity.

## Verification

Run the complete authored gate:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles this theory from source with `-no-eco` and includes it in
the proof-hole, project-authored-axiom, and debug-command scans.
