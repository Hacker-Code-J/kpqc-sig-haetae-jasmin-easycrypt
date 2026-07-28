# Actual Mode-2 Parent-Module Sampler-Prefix Refinement

> **Claim boundary:** this proof binds the established seed-expansion and
> sampler contracts to procedures in the actual generated
> `KeygenMode2ParentTarget.M` module, then composes those procedures in an
> authored proof-only sampler prefix. It does not prove
> `_keypair_full_m23`, `crypto_sign_keypair_internal_mode2_jazz`, or a complete
> key-generation refinement. A later, separate M23 gate relates the actual
> fixed-parameter `_keypair_full_m23` to a result-carrying first-attempt mirror
> and gives its fixed singular/FFT call exact machine-word semantics and
> totality; it does not retroactively enlarge this sampler-prefix gate.

## Verified proof surface

The proof has three layers:

1. seven pRHL equivalences connect corresponding generated procedures in
   `KeygenSamplerCallersTarget.M` and `KeygenMode2ParentTarget.M`;
2. parent-qualified Hoare and pHoare theorems transport the established seed,
   caller, and leaf contracts to `KeygenMode2ParentTarget.M`; and
3. `CheckedMode2ParentSamplerPrefix.run` composes actual parent-module calls
   with the mode-2 dimensions, seed flow, first eta-attempt schedule, and
   five-slot counter advance.

The third layer is an authored observer. It deliberately stops before
`_kp_m23_matrix`, `_keypair_finalize_m23`, `_singular_full`, the retry guard,
and key packing. It is not an extracted parent procedure.

A separate proof surface now targets the actual extracted `_kp_m23_matrix`
helper itself. It establishes the fixed-mode copy footprint, active-prefix
scratch independence, algebraic matrix-product postcondition, and helper
totality, then composes those results with the sampler and finalizer in
separate observers. None of those results belongs to this sampler-prefix
gate. See
[`14-target-keygen-m23-matrix.md`](14-target-keygen-m23-matrix.md).

That later M23 proof surface also composes the checked sampler, matrix, and
finalizer facts into an immutable trace of the first parent attempt. Its
relational theorem preserves the actual residual retry loop and both packing
calls while comparing the returned packed arrays. These are separate theorems
over a peeled mirror, not results of the parent-prefix manifest documented
here.

## Cross-target bridge

The generated sampler-caller extraction and actual-parent extraction contain
the same sampler code in different top-level EasyCrypt modules. The following
equivalences bind the two module-qualified copies:

| Parent-module procedure | Bridge theorem |
| --- | --- |
| `_kp_expand_seedbuf` | `kp_expand_seedbuf_cross_equiv` |
| `_kp_poly_uniform_at_seedbuf_8192` | `uniform8192_leaf_cross_equiv` |
| `_kp_poly_uniform_at_seedbuf_2048` | `uniform2048_leaf_cross_equiv` |
| `_kp_poly_uniform_eta_at_seedbuf_2048` | `eta2048_leaf_cross_equiv` |
| `_kp_polymatkm_expand_matA` | `expand_matA_cross_equiv` |
| `_kp_polyveck_expand_vecA` | `expand_vecA_cross_equiv` |
| `_kp_polyvec_expand_eta` | `expand_eta_cross_equiv` |

Each theorem equates all procedure inputs and results. The dedicated
verification gate also checks the exact inventory and byte identity of the 24
generated support theories shared by the two extraction closures. These facts
justify theorem transport; they do not make either top-level generated target
an authored specification.

## Parent-qualified contracts

`TargetKeygenMode2Parent.ec` transports the following contracts to procedures
under `KeygenMode2ParentTarget.M`:

| Contract | Parent-qualified theorem |
| --- | --- |
| Exact 128-byte SHAKE256 seed expansion | `kp_expand_seedbuf_correct` |
| Uniform seed slice `[0, 32)` | `kp_expand_seedbuf_uniform_slice_correct` |
| Eta seed slice `[32, 96)` | `kp_expand_seedbuf_eta_slice_correct` |
| Key slice `[96, 128)` | `kp_expand_seedbuf_key_slice_correct` |
| Uniform matrix finite-stream, range, and frame result | `expand_matA_stream_correct` |
| Uniform vector finite-stream, range, and frame result | `expand_vecA_stream_correct` |
| Eta vector finite-stream, centered-range, and frame result | `expand_eta_stream_correct` |
| 2048-word uniform-leaf probability-one termination under a certificate | `uniform2048_leaf_progress_ll` |
| 8192-word uniform-leaf probability-one termination under a certificate | `uniform8192_leaf_progress_ll` |
| 2048-word eta-leaf probability-one termination under a certificate | `eta2048_leaf_progress_ll` |

The Hoare theorems are partial-correctness results: their postconditions hold
when a call returns. The three pHoare theorems establish probability-one
termination only under their exact destination, seed-slice, and explicit
deterministic finite-progress premises.

## Exact mode-2 certificate bundle

`KeygenMode2ParentSpec.ec` groups the finite progress obligations for the
sampler prefix:

| Bundle predicate | Covered calls |
| --- | --- |
| `mode2_matrix_uniform_progress` | Six matrix cells, with rows `0..1`, columns `0..2`, seed offset 0, and nonce word `256 * row + col` |
| `mode2_vector_uniform_progress` | Two `agen` slots, seed offset 0, and nonce words 515 and 516 |
| `mode2_first_attempt_eta_progress` | Five first-attempt eta slots, seed offset 32, and nonce words `0..4` |

Each predicate accepts an explicit endpoint map, so each of the 13 sampler
invocations has its own finite progress witness.
`mode2_sampler_prefix_progress` ties all three bundles to the exact
SHAKE256-expanded seed by quantifying over every `BArray128` satisfying
`KeygenSeedXofSpec.output_matches` for the supplied raw `BArray32` seed.

The bundle is a deterministic sufficient condition. The proof does not show
that these endpoints exist for every seed and does not infer a rejection
probability or output distribution from them.

## Certificate-conditioned caller and prefix totality

`TargetKeygenMode2ParentComposition.ec` lifts the endpoint maps through the
actual parent-module callers:

| Scope | pHoare theorem |
| --- | --- |
| Exact expanded-seed result | `parent_kp_expand_seedbuf_output_matches_pr` |
| Six-cell mode-2 matrix caller | `mode2_matrix_uniform_progress_ll` |
| Two-slot mode-2 vector caller | `mode2_expand_vecA_progress_ll` |
| Count-three eta caller at nonce zero | `mode2_eta_nonce0_count3_progress_ll` |
| Count-two eta caller at nonce three | `mode2_eta_nonce3_count2_progress_ll` |
| Complete proof-only sampler prefix | `checked_mode2_parent_sampler_prefix_progress_ll` |

The proof stack also exposes the tailored leaf helpers
`mode2_matrix_uniform_leaf_ll`, `mode2_vector_uniform_leaf_ll`, and
`mode2_eta_first_attempt_leaf_ll`, plus the generic first-attempt eta segment
theorem `mode2_eta_segment_progress_ll`.

`checked_mode2_parent_sampler_prefix_progress_ll` requires equality with the
supplied initial seed buffer and raw seed plus
`mode2_sampler_prefix_progress raw_seed mat_limit vec_limit eta_limit`. Under
that precondition it proves probability-one termination of the authored prefix.
It does not make termination unconditional: the certificate bundle remains an
explicit premise and no theorem establishes it for every raw seed.

## Proof-only composed prefix

`CheckedMode2ParentSamplerPrefix.run` calls only procedures from
`KeygenMode2ParentTarget.M`, in this order:

1. `_kp_expand_seedbuf`;
2. `_kp_polymatkm_expand_matA` with `(rows, cols) = (2, 3)`;
3. `_kp_polyveck_expand_vecA` with `(k, m) = (2, 3)`;
4. `_kp_polyvec_expand_eta` for three `s1` polynomials at nonce zero;
5. `_kp_polyvec_expand_eta` for two `s2` polynomials at nonce three; and
6. a returned retry counter advanced to five.

`checked_mode2_parent_sampler_prefix_correct` proves, on return:

- exact SHAKE256 identity for the expanded seed and all three named slices;
- exact finite-stream, range, and aggregate frame contracts for the six-cell
  uniform matrix and two-slot uniform vector;
- exact finite-stream, centered-range, and frame contracts for the three-slot
  and two-slot eta vectors; and
- the exact first-attempt counter value `5`.

This closes the previous raw-array gap inside this proof-only prefix: the
uniform and eta caller postconditions refer to the same array returned by the
actual parent module's `_kp_expand_seedbuf`. It does not establish that the
extracted `_keypair_full_m23` is equivalent to this sampler-prefix observer.
The later `mode2_full_first_attempt_equiv` theorem instead uses a distinct
result-carrying mirror that retains all remaining parent control flow.

The separate pHoare theorem
`checked_mode2_parent_sampler_prefix_progress_ll` proves probability-one
termination of this same observer under the exact deterministic bundle above.
The Hoare and pHoare results are intentionally separate: semantic
postconditions hold on return, while totality requires the finite progress
certificates.

## Checked artifacts

| Role | Artifact |
| --- | --- |
| Actual generated parent target | `easycrypt/extract/keygen-mode2-parent/KeygenMode2ParentTarget.ec` |
| Generated bridge target | `easycrypt/extract/keygen-sampler-callers/KeygenSamplerCallersTarget.ec` |
| Mode-2 certificate specification | `easycrypt/spec/KeygenMode2ParentSpec.ec` |
| Cross-target and transported contracts | `easycrypt/refinement/TargetKeygenMode2Parent.ec` |
| Proof-only prefix composition | `easycrypt/refinement/TargetKeygenMode2ParentComposition.ec` |
| Proof compilation order | `manifests/keygen-mode2-parent-proof-files.txt` |
| Shared-theory identity inventory | `manifests/keygen-mode2-parent-shared-theories.txt` |
| Reproduction command | `scripts/verify-keygen-mode2-parent-proof.sh` |

The generated target remains governed by the extraction and drift boundary in
[`12-target-keygen-mode2-parent-extraction.md`](12-target-keygen-mode2-parent-extraction.md).

## Reproduction

Run from the `haetae-ref-easycrypt` project directory:

```sh
./scripts/verify-keygen-mode2-parent-proof.sh
```

The gate checks pinned source hashes, regenerates and compares both extraction
surfaces, verifies the exact 24-file shared-theory inventory byte-for-byte,
compiles the 17-entry parent proof manifest with `easycrypt compile -no-eco`,
and rejects `admit`/`abort` proof commands and axiom declarations.

The retained 2026-07-23 run passes all of those checks and ends with:

```text
RESULT: PASS compiled=17 total=17 mode=-no-eco
```

## Explicit exclusions

These are boundaries of this sampler-prefix milestone. The separate
first-attempt result in
[`14-target-keygen-m23-matrix.md`](14-target-keygen-m23-matrix.md) closes the
specifically documented fixed-parameter equivalence, trace, and exact
singular-machine-evaluator facts; it does not turn the exclusions below into a
complete key-generation theorem.
This milestone does not establish:

- a semantic, relational, Hoare, or losslessness theorem for
  `_keypair_full_m23` or `crypto_sign_keypair_internal_mode2_jazz`;
- composition of the separate structural `_kp_m23_matrix` result into the
  actual `_keypair_full_m23`, or arithmetic correctness for the helper's NTT
  operations and pointwise matrix sum;
- correctness of `_keypair_finalize_m23`, the `egen - b0` adjustment,
  `_singular_full`, its acceptance decision, or public/secret-key packing;
- termination of the outer eta/singular-value retry loop or an acceptance
  certificate for any attempt;
- universal existence of the uniform or eta progress certificates,
  unconditional whole-caller or prefix totality, or any sampler distribution;
- source-pointer safety, aliasing, or a correspondence between source memory
  and the extracted value-array model; or
- correspondence with the paper/security model, public-API refinement, or
  composition with the HAETAE security theorem.
