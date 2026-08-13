# Post-freeze KG Rq/HAETAE bridge report

## Verdict

`STOP-KG-RQ-HAETAE`

The requested Rq-to-HAETAE coefficient bridge and the Mode-2 native row-product
KG-1 bridge are proved.  The full KG-3/KG-4 and
`As = qj (mod 2q)` composition is not claimed.

## Frozen boundary

- Frozen commit: `4bde1207e2a290952d491d5b41c4bd773081e3c4`
- Post-freeze branch: `post-freeze-kg-rq-haetae-bridge`
- Frozen PDF SHA-256:
  `be935948028829556951863b44ceb2e6c5b2037820991b3a43a4b461b036e53d`
- Frozen 82-target summary SHA-256 before this work:
  `08ef9639dc73d56dba42d02999d07897d29bc8e60aa100a648e9437fd64387ad`

## Newly closed leaves

`haetae-ntt-verify/easycrypt/RqHAETAEBridge.ec` defines the representation
predicate `rq_poly_repr`.  Its premises contain only polynomial well-formedness
and coefficientwise equality; they contain neither a desired convolution result
nor an `As = qj` equation.

- `rq_poly_add_repr`: preservation of `Rq.(&+)` by
  `HAETAE_Algebra.poly_add`.
- `rq_poly_mul_repr`: preservation of the checked negacyclic `Rq.(&*)` by
  `HAETAE_Algebra.poly_mul`.  It uses the already-proved
  `rq_mul_coeff_foldr_to_bigi` leaf and does not use the incomplete legacy
  `Rq.ntt` operator.
- `rq_poly_dot3_repr`: independent three-term row-product lift to
  `HAETAE_Algebra.poly_dot`.
- `Mode2KeygenNttMulBridge.mode2_row_product_haetae_dot`: connects the
  completed native Mode-2 `Rq` row product to the corresponding HAETAE
  three-polynomial dot product under six coefficientwise representation
  hypotheses.

The existing KG-2 snapshot facts, including
`actual_snapshot_low_high_decomposition` and `actual_snapshot_mod2q_zero`, are
reused unchanged.

## Minimum blocking leaf

The first missing faithful composition leaf is
`OBL-KG-ACTUAL-AVEC-QJ-SEMANTICS`:

> From the checked first-attempt seed/XOF and uniform-vector sampler facts,
> relate the active runtime `avec` words (the `avec0` parameter of the snapshot
> theorem) to the coefficients of
> `HAETAE_Algebra.haetae_mode23_qj_vector Mode2 rho`, where `rho` is the
> list-level public seed represented by the actual seed bytes.

Coefficientwise, the required conclusion has the following shape for
`0 <= row < 2` and `0 <= i < 256`:

```text
W32.to_uint (BArray8192.get32 avec (row * 256 + i))
=
HAETAE_Algebra.poly_coeff
  (nth HAETAE_Algebra.poly_zero
    (HAETAE_Algebra.haetae_mode23_qj_vector Mode2 rho) row) i
```

No current theorem supplies this relation.  The extracted path characterizes
`avec` through `uniform_vector_stream8192` and decoded SHAKE/XOF samples, while
the current security-side `public_rounding_vector_seed` is defined through the
synthetic `public_key_seed_polyveck`/`public_key_seed_poly` construction.  A
seed-byte/list bridge alone therefore does not establish the equality; the two
sampler semantics must first be related or the security-side specification must
be refined.

Without this leaf, substituting the seed-derived `qj` into the already-proved
snapshot congruence would assume the desired semantic identification.  Thus
KG-3, whole-vector KG-4, and the paper-level `As = qj (mod 2q)` result remain
blocked.  Matrix/secret and adjusted-error list packaging are downstream
transport obligations and were not promoted to claims in this run.

## Verification

The standalone bridge passes fresh compilation with the following command:

```sh
easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
  -I haetae-ntt-verify/easycrypt \
  -I haetae-ntt-verify/easycrypt-ct \
  -I haetae-security/provable-security/easycrypt \
  haetae-ntt-verify/easycrypt/RqHAETAEBridge.ec
```

The aggregate run was executed from the repository root with:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

It freshly compiled all 82 authored targets, including
`Mode2KeygenNttMulBridge.ec`, and terminated with:

```text
PASS baseline verification
PASS LaTeX research notes build
PASS read-only roots unchanged after verification
PASS paper-freeze scope and 82-target evidence audit
RESULT PASS authored-targets=82 cache=-no-eco
```

The regenerated aggregate summary has SHA-256
`08ef9639dc73d56dba42d02999d07897d29bc8e60aa100a648e9437fd64387ad`,
identical to the frozen pre-work summary.  The PDF remains unchanged at
SHA-256 `be935948028829556951863b44ceb2e6c5b2037820991b3a43a4b461b036e53d`.
Both local `main` and `origin/main` remain at frozen commit
`4bde1207e2a290952d491d5b41c4bd773081e3c4`.
