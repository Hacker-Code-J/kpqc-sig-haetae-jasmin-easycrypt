# Target Jasmin NTT Extraction

## Scope

This extraction is generated from the actual target source:

```text
haetae-ref-jasmin/jasmin/hpoly.jazz
```

It intentionally selects only these public functions and their dependencies:

- `poly_ntt_jazz`
- `poly_invntt_jazz`

Limiting the extraction keeps the first refinement boundary reviewable while
still including the target's direct-loop `_poly_ntt`, `_poly_invntt`,
Montgomery multiplication, constants, and array representations.

## Regeneration

From the project directory:

```sh
./scripts/regenerate-ntt-extract.sh
```

The effective extraction command is:

```sh
jasmin2ec --array-model=barray \
  --output-array=<temporary-directory> \
  -o <temporary-directory>/HpolyTarget.ec \
  -f poly_ntt_jazz \
  -f poly_invntt_jazz \
  ../haetae-ref-jasmin/jasmin/hpoly.jazz
```

Generation occurs in a temporary directory. The script requires the generated
file set to match `manifests/ntt-extract-files.txt` before copying results into
`easycrypt/extract/ntt/`. This prevents an extraction-tool change from silently
adding or removing theories.

## Drift and compilation checks

```sh
./scripts/check-ntt-extract-drift.sh
./scripts/verify-ntt-extract.sh
```

The drift check regenerates from the pinned target source and compares every
generated file byte-for-byte. The verifier then compiles all generated theories
with `easycrypt compile -no-eco` and records a summary under
`logs/ntt-extract-summary.txt`.

## Mathematical refinement

The target procedures are now connected to the checked algebraic NTT:

```sh
./scripts/verify-ntt-proof.sh
```

`easycrypt/refinement/TargetNTTRefinement.ec` proves pRHL equivalences from the
current target's scalar Montgomery multiplication and direct-loop forward and
inverse procedures to `Hpoly_loop.M`. That loop module is the checked adapter
used by the existing NTT proof. The bridge does not assume source identity:
both sides are explicit EasyCrypt procedures, and their calls and loop states
are synchronized by compiled equivalence proofs.

The final Hoare theorems are:

- `target_poly_ntt_correct` and `target_poly_ntt_jazz_correct`: an input
  represented with signed bound 16 is returned as
  `NTTFullSpec.full_ntt p` with bound 24;
- `target_poly_invntt_correct` and `target_poly_invntt_jazz_correct`: an input
  represented with signed bound 16 is returned as the Montgomery
  representation of `NTTFullSpec.full_invntt p`, again with bound 16;
- `target_poly_invntt_correct18` and
  `target_poly_invntt_jazz_correct18`: the same inverse postcondition from the
  conservative signed input bound 18 needed after a three-term mode-2
  pointwise accumulation; and
- `target_fqmul_correct`: the current target multiplication computes the
  checked signed Montgomery reduction.

The proof gate regenerates the current target extraction, pins all 18 imported
proof-support theories by hash, checks the three shared generated
representation theories byte-for-byte, compiles the authored refinement with
`-no-eco`, and rejects proof holes and authored axioms. The imported NTT bundle
retains its declared foundational axiom boundary in `GFq.ec` and
`Montgomery.ec`.

The retained `2026-07-23T20:40:27Z` gate passed the source-hash check, zero
target-extraction drift, all 18 imported-support hashes, three byte-identical
generated representations, fresh `-no-eco` compilation, and the proof-hole
and authored-axiom scans.

## Mode-2 wide-array composition

The standalone theorems still describe one `BArray1024` polynomial. The
fixed-mode key-generation proof now lifts them through the actual
`BArray8192` parent procedures:

- `TargetKeygenM23WideSupport.wide_slice_poly_repr_bound` relates each
  256-word wide-array slice to the single-polynomial representation;
- `TargetKeygenM23WideNTT.parent_polyvec_ntt_mode2_correct` proves the actual
  three-polynomial forward loop from bound 16 to bound 24;
- `TargetKeygenM23Pointwise.polymat_pointwise_mode2_repr_bound18_frame`
  proves the exact two-row, three-column Montgomery sum at bound 18; and
- `TargetKeygenM23WideInvNTT.polyvec_invntt_mode2_pointwise_correct18`
  proves the actual two-polynomial inverse loop from that bound 18 input to
  bound 16.

`TargetKeygenM23Arithmetic.kp_m23_matrix_mode2_arithmetic_correct` composes
those results through the actual extracted `_kp_m23_matrix` helper at
`(rows, cols) = (2, 3)`. The separate
`TargetKeygenM23Matrix.kp_m23_matrix_mode2_ll` theorem proves fixed-mode
probability-one termination.

The same downstream gate now also checks the actual mode-2
`_keypair_finalize_m23` at count 512. `KeygenM23FinalizeSpec` records its exact
word-level freeze, frozen-sum, and EGen low/high operations, while
`TargetKeygenM23Finalize.keypair_finalize_m23_mode2_correct` proves both
first-512-word results and both tail frames. For signed-18-bit scalar inputs,
`KeygenM23FinalizeSemantics` also proves that the target freeze is canonical
reduction modulo `q = 64513`. The proof-only
`CheckedMode2ParentM23Finalize` observer composes the checked sampler, actual
M23 helper, and actual finalizer. Its semantic theorem derives the signed-18-bit
premise for all 512 active words from the bound-16 M23 output, centered `s2`,
and canonical uniform-vector bounds. It returns the high coefficients and
exact adjusted `s2` pointwise according to `HAETAE_Algebra` coefficient
decomposition and preserves both tail frames. The gate compiles the current
authored manifest with `-no-eco` after checking source/support hashes and
parent, sampler-caller, and target-NTT extraction drift.

## Remaining boundary

The wide-array composition is mode-2-specific and reaches exact word-level and
pointwise coefficient-decomposition finalization only in a proof-only
sampler-plus-M23-plus-finalizer observer. It is not a theorem about
`_keypair_full_m23` or the public key-generation API. In particular, it does
not identify the target NTT/matrix representation with the security model's
list-polynomial multiplication or equate the complete observer with the
security model's key-generation procedure. FFT/singularity rejection, retry
control and termination, packing, pointer aliasing/separation safety, universal
sampler-progress certificates, distributions, modes 3 and 5, and security
composition remain open.
