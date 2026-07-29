# Target mode-2 root-table rounding

## Scope

This milestone identifies every signed coordinate in the extracted
`jfft_roots` table with the unique nearest Q16 encoding of the corresponding
exact `ideal_root j` coordinate, for `0 <= j < 256`.

The endpoint is about the pinned extracted constant itself. It does not decode
the complete fixed-point FFT trace or prove stage safety, nonoverflow, a global
FFT error bound, score correspondence, or rejection equivalence.

## Checked certificate chain

`easycrypt/spec/KeygenM23RootGeneratorCertificate.ec` encloses the
lower-half-plane generator `omega512` with rational intervals at scale
`10^18`. The intervals are derived through the same proved nested-square-root
construction used by `KeygenM23IdealRootDFT`; they are lemmas, not decimal
axioms.

`easycrypt/spec/KeygenM23RootTableRounding.ec` supplies a generic soundness
layer for center-radius certificates over real and complex multiplication.
Its concrete data then checks:

- 256 complex interval certificates;
- the base certificate for `ideal_root 0`;
- all 255 successive multiplications by `omega512`;
- 256 Q16 integer pairs; and
- both strict half-cell inequalities for every pair, for 512 coordinate checks
  in total.

Induction over the checked transitions proves that certificate `j` encloses
`ideal_root j`. Combining that enclosure with its strict Q16 cell proves, for
both coordinates,

```text
abs(ideal_coordinate - q / 65536) < 1 / 131072.
```

The strict inequality excludes a half-way tie. The generic rounding and
uniqueness lemmas consequently prove

```text
floor(65536 * ideal_coordinate + 1/2) = q
```

and prove that any other integer satisfying the same strict error bound equals
`q`.

## Extracted-target endpoint

`easycrypt/spec/KeygenM23RootTableTargetBridge.ec` connects the certified pairs
to the actual `W32.to_sint` values read from
`KeygenMode2ParentTarget.jfft_roots`. The bridge uses 256 named concrete pair
lemmas, sixteen bounded dispatch lemmas, and one universal lookup theorem.
These theorem boundaries keep concrete-table normalization within the
verifier's memory envelope while preserving a fully checked proof.

The exported target theorems are:

- `jfft_roots_q16_coordinate_error`;
- `jfft_roots_q16_rounds`; and
- `jfft_roots_q16_unique`.

Together they establish the strict coordinate error, the exact Q16 rounding
equations, and uniqueness for all 256 extracted root pairs. No project-authored
axiom or proof-hole command is used.

## Deliberate boundary

The target table is now related to the exact root schedule. The follow-on
`KeygenM23SingularFFTInitBridge` consumes that result and closes the complete
decoded initialization permutation, signed raw-product safety under
coefficient magnitude at most two, and a whole-vector `1/65536` error bound
against the exact bit-reversed twisted input.

The rounded butterfly stages are not yet related to `ideal_fft256`. The next
sound bridge must:

1. prove a decoded and framed butterfly theorem and lift it through all eight
   FFT stages;
2. prove the signed-fit and nonoverflow premises for those stages and the five
   squared-magnitude passes;
3. propagate the certified root and local multiplication errors to a global
   bound against `ideal_fft256`; and
4. carry that bound through accumulation, selection, and the retained
   multiplicity-sensitive finish rule before relating rejection decisions.

The completed initialization endpoint is detailed in
[`20-target-keygen-fft-initialization-bridge.md`](20-target-keygen-fft-initialization-bridge.md).

## Verification

Run the complete authored gate:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles all three certificate theories from source with `-no-eco`
and rejects proof holes, project-authored axiom declarations, and leftover
debug commands.
