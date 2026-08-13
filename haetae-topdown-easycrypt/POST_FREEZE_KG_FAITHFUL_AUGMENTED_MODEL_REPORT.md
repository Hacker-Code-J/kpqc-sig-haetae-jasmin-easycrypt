# Post-freeze faithful augmented KeyGen model report

## Verdict

`GO-KG-FAITHFUL-AUGMENTED`

The separate post-freeze model proves that the actual checked Mode-2 KeyGen
core path satisfies the paper augmented key equation coefficientwise modulo
`2q`.  This is a statement about the actual sampler, generated matrix product,
and finalizer snapshot.  It is not a correspondence theorem for the existing
synthetic security model.

## Frozen boundary

- Work branch: `post-freeze-kg-rq-haetae-bridge`.
- Frozen `main`/paper sources, PDF, the 82-target manifest, reference
  extraction, NTT sources, and existing security sources were not changed.
- The new proof is isolated in
  `post-freeze/KgFaithfulAugmentedModel.ec`; it is compiled separately from the
  frozen authored-target manifest.
- The existing `KgActualAvecQjBlocker.ec` mismatch remains intact.  No equality
  with `haetae_mode23_qj_vector` is used or required.

## Faithful 2 by 6 model

The new carrier defines the paper blocks over integer coefficients interpreted
modulo `2q`:

```text
A = (2(a - 2b1) + qj | 2Agen | 2I2)
s = (1 | sgen | egen - b0).
```

The six columns are represented explicitly by
`faithful_augmented_matrix_coeff` and
`faithful_augmented_secret_coeff`.  The actual instance is given by
`actual_faithful_augmented_matrix` and
`actual_faithful_augmented_secret`; its matrix-vector coefficient semantics is
`faithful_augmented_matrix_vector_product_coeff`.

That product operator receives only the explicit matrix and secret carriers.
It reads the head and identity columns directly, reconstructs the three
generated polynomials from columns 1--3, and evaluates that middle block with
the existing HAETAE `poly_dot`.  There is no separately supplied generated
matrix or secret argument that could drift away from the displayed `A` and
`s`.

`faithful_j_coeff row coeff` is one exactly when `row = 0` and `coeff = 0`,
and zero otherwise.  Thus the first entry of `j=(1,0)^T` is the ring identity
polynomial, not a polynomial whose every coefficient is one.

`actual_faithful_augmented_productE` expands the actual width-6 product to

```text
2(a - 2b1) + qj + 2*HAETAE.poly_dot(Agen,sgen) + 2(egen-b0)
```

at every active row and coefficient.  The separate
`faithful_generated_row_product_haetae_dot` representation theorem identifies
that middle dot with the native NTT/Rq row product; the final statement uses
the resulting coefficient congruence modulo `2q`, not an unproved equality of
integer representatives.

## Connection to the actual KeyGen spine

The proof connects each previously checked layer without changing it:

- actual `avec`: `mode2_sampler_facts_actual_paper_a` identifies the actual
  stored two-row sampler output with the paper `a` coefficients;
- NTT row product: `actual_generated_row_product` reuses
  `Mode2KeygenNttMulBridge.mode2_row_product`, and
  `mode2_m23_facts_generated_row_product` connects it to the actual `pre_bp`
  row snapshots;
- Rq to HAETAE: `faithful_generated_row_product_haetae_dot` applies the
  existing `mode2_row_product_haetae_dot` theorem and
  `RqHAETAEBridge.rq_poly_repr` to the actual three-column generated block;
- finalizer snapshot: the checked finalizer semantics yields the existing
  coefficientwise snapshot congruence and the adjusted error
  `egen-b0`.

The terminal Hoare theorem is
`checked_mode2_parent_m23_finalize_faithful_augmented_paper_as_qj`.  For every
active `row < 2` and `coeff < 256`, it concludes

```text
faithful_augmented_matrix_vector_product_coeff A s row coeff
  == faithful_qj_coeff row coeff  (mod 2q).
```

It also retains the actual-`avec`/paper-`a` result in the same postcondition,
so the matrix head and the sampler correspondence cannot drift apart.

## Deliberate non-claims

This result does not claim a security-theorem refinement, distribution or
uniformity, sampler termination or losslessness, packing correctness, or a
public-API theorem.  Nor is the mixed modulo-`2q` block evaluator the existing
modulo-`q`, width-four security `matrix_vec_mul`; that operation would erase
the `qj` lift.  The result is partial correctness for the checked actual
KeyGen core path.  The synthetic security model's object mismatch remains a
separate formal-model correspondence defect.

## Verification

- `post-freeze/KgFaithfulAugmentedModel.ec` passes a fresh `easycrypt compile
  -script -no-eco` with Z3 and the repository KeyGen/NTT/Rq/HAETAE include
  surface.
- `scripts/check-proof-holes.sh`, plus explicit scans of the post-freeze target,
  find no proof holes, authored axioms, or debug declarations.  The target also
  contains no `haetae_mode23_qj_vector` reference.
- `algebraist-guide/build.sh` rebuilds the guide and checks unresolved
  references/citations.  The generated evidence is
  `algebraist-guide/main.pdf`.
- A single full `scripts/verify-all.sh` run regenerated
  `logs/verify-all-summary.txt` with 82 `PASS fresh compile` rows, baseline and
  research-notes checks, the final paper-freeze evidence audit, and terminal
  `RESULT PASS authored-targets=82 cache=-no-eco`.  Its SHA-256 is
  `08ef9639dc73d56dba42d02999d07897d29bc8e60aa100a648e9437fd64387ad`.
- `manifests/proof-targets.txt` remains byte-for-byte unchanged from `e87bcc3`,
  and neither the frozen paper sources nor the existing security model are in
  this change set.
