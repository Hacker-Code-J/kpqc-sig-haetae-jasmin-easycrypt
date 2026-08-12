# Week 16 MINCORE KeyGen first-task report

## Decision

**Superseded continuation decision: STOP-KG-NTT.**

The actual `_kp_m23_matrix` and `_keypair_finalize_m23` procedures are now
composed in one transparent, two-call Hoare harness.  The returned matrix
snapshot is carried through exact finalization, scalar HAETAE low/high
semantics, the KG-2-like decomposition, the adjusted `s2` component of KG-4,
and a coefficientwise snapshot congruence modulo `2q`.

This is not `GO-KG`: faithful KG-1, KG-3, the complete KG-4 vector, and the
paper equation `A s = q j (mod 2q)` are not proved.  The KG-NTT-MUL
continuation confirmed that the checked tree lacks the odd-root
orthogonality/full-NTT convolution theorem needed to identify
`KeygenM23ArithmeticSpec.output_row` with `Agen * sgen`, and also lacks the
`Rq.poly`-to-security-list multiplication adapter.  The exact continuation
audit is in `WEEK16_KG_NTT_MUL_REPORT.md`; KeyGen is frozen here and the active
lane moves to Sign.

## Fresh baseline

Before the Week 16 proof files were added, the exact repository verifier
passed with:

```text
RESULT PASS authored-targets=74 cache=-no-eco
```

The preserved log is `logs/verify-all-before-week16.log`, SHA-256
`da7a7516166d54e93665d36e9a81348050ac6a83786111eb83ac6901743d6056`.

## Actual procedure surface

`Mode2KeygenCoreEquation.ActualM23MatrixFinalizeSnapshot.run` is transparent:

1. it calls `KeygenMode2ParentTarget.M._kp_m23_matrix` with the literal mode-2
   dimensions `(rows, cols) = (2, 3)`;
2. it records the actual returned `bp` array as `pre_bp`;
3. it calls `KeygenMode2ParentTarget.M._keypair_finalize_m23` with
   `count = 512`; and
4. it returns `(pre_bp, s1hatp, final_bp, adjusted_s2)`.

The harness contains no sampler, retry loop, acceptance guard, packer, or
public API.  It does not replace either actual procedure by an abstract
implementation.

## Fresh-compiled theorem surface

| File | Theorem or predicate | Exact role |
| --- | --- | --- |
| `easycrypt/refinement/keygen/Mode2KeygenSnapshotAlgebra.ec` | `snapshot_residue_exact_low_high` | proves `r = 2*high(r)+low(r)`, `low(r) in [-1,1]`, and the high range for `0 <= r < q` |
| same | `raw_sum_raw_residue_congruent_mod_2q` | lifts reduction modulo `q` to the doubled congruence modulo `2q` |
| same | `snapshot_expression_from_product_congruent_mod_2q` | proves the pure snapshot expression congruence without an opaque certificate |
| `easycrypt/refinement/keygen/Mode2KeygenCoreEquation.ec` | `actual_m23_matrix_finalize_snapshot` | directly composes the two actual procedures and exports matrix/NTT representations, exact finalization, and frames |
| same | `finalize_semantic_output_low_high_decomposition` | derives the KG-2-like scalar split and adjusted-`s2` equation from finalizer semantics |
| same | `finalize_semantic_output_snapshot_mod2q_zero` | derives `actual_snapshot_mod2q_zero` from the same actual finalizer result |
| same | `actual_m23_matrix_finalize_semantic_snapshot` | exports the exact, semantic, HAETAE, low/high, snapshot-mod-`2q`, and frame results through the transparent harness |

No new axiom, admit, abort, sorry, proof hole, success premise, or opaque
procedure was introduced.

## Exact Hoare contract

Both harness theorems require only:

- exact bindings for `bp`, `s1hatp`, `mat`, `s1`, `s2`, and `avec`;
- `matrix_active_bound16 mat0`;
- `mode2_input_repr_bound16 s10 p0 p1 p2`;
- the active `s2` words in `[-1,1]`; and
- the active `avec` words canonical below `q`.

They do not assume finalizer output, semantic output, any KG predicate, the
snapshot congruence, acceptance, success, or the desired paper equation.

The strongest postcondition contains:

- `mode2_output_repr_bound16` for the actual pre-finalization `bp` snapshot;
- `mode2_ntt_repr_bound24` for the returned `s1hatp`;
- exact `finalize_output` and its scalar/HAETAE semantic lifts;
- for every active coefficient, with
  `r = (pre_bp + s2 + avec) mod q` and `b0 = low(r)`,
  `r = 2*b1 + b0`, `-1 <= b0 <= 1`, and
  `adjusted_s2 = s2 - b0`;
- the honest snapshot-only congruence
  `2*(avec - 2*b1) + 2*pre_bp + 2*adjusted_s2 = 0 (mod 2q)`; and
- the initial-to-snapshot, initial-to-final, NTT scratch, and `s2` tail frames.

The congruence calls `pre_bp` exactly what it is: the actual matrix helper's
returned snapshot.  It does not rename that array to `Agen*sgen`.

## KG accounting

| Obligation | Status after this task | Reason |
| --- | --- | --- |
| KG-1 | **BLOCKED** | actual output is represented as `output_row`; no compiled bridge identifies it with `Agen*sgen` in the paper ring |
| KG-2 | **PROVED at the actual snapshot/finalizer coefficient boundary** | the canonical residue is exactly `b0 + 2*b1`, with `b0 in {-1,0,1}` |
| KG-3 | **BLOCKED** | the augmented paper matrix containing `2*Agen` is not constructed without the multiplication/representation bridge |
| KG-4 | **PARTIAL** | `adjusted_s2 = egen-b0` is proved pointwise; the full vector `(1 | sgen | egen-b0)` is not constructed |
| `A s = q j (mod 2q)` | **BLOCKED** | the snapshot zero congruence cannot be promoted to the paper matrix-vector equation without KG-1/KG-3 |

The blocker is independently visible in the reused upstream boundary:
`output_row` is defined as `array256_mont(full_invntt(pointwise_row_ntt ...))`,
while the existing matrix theorem exports only that representation.  The
upstream proof-status document also records the NTT/matrix-to-list
security-model multiplication bridge as open.  Substituting the legacy
`Rq.ntt` is invalid: `NTTFullSpec.rq_ntt_is_not_full_ntt_on_one` proves the two
transforms differ.

## Verification and scope

Both new targets compile individually with `easycrypt compile -script
-no-eco`.  The aggregate gate manifests 76 authored targets and checks the
direct-call surface, non-circular precondition, proof integrity, extraction
and table drift, selected upstream baselines, read-only roots, and LaTeX.  The
final aggregate result is recorded in `logs/verify-all-summary.txt`.

No claim is made about sampler distributions, retry termination, packing,
public APIs, KeyGen termination, pointer safety, Sign/Verify correctness, or
implementation security.

## Historical next target and stop result

The requested continuation attempted the full-NTT convolution/representation
edge and stopped at the absent spectral-action theorem
`mont(full_invntt(ahat * full_ntt(p) * inv R)) = full_invntt(ahat) &* p`.
No desired product was added as a premise.  The new single target is the
actual accepted Sign-core composition named in the continuation report.
