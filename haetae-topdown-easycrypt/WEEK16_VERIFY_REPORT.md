# CONTINUE-VERIFY-MATRIX-CRT final report

## Decision

**STOP-VERIFY-MATRIX-CRT.**

The requested theorem

```text
verify_matrix_crt_mode2_fromcrt_freeze_exact
```

did not close in this continuation. The checked tree lacks the exact NTT/CRT
leaves recorded below; treating the desired row-product/output equality as a
premise would only hide that gap, so no such premise was added. The previously
compiled V-1, V-2, V-5, V-6, W64 norm, tail-trace, and mismatch-word theorems
remain unchanged, and the authored-target baseline remains 82.

## Preserved 82/82 baseline

Before this continuation, the completed aggregate summary was copied
byte-for-byte to `logs/verify-all-before-verify-matrix-crt.log`. It has exactly
82 `PASS fresh compile` lines, exactly one terminal result, and ends with

```text
RESULT PASS authored-targets=82 cache=-no-eco
```

Its SHA-256 is
`46e7dac8e442c820f746139a164c8bc00d6af17b7ad25cbd5d195507fddae03c`.
The final continuation aggregate again fresh-compiles the same 82 targets; no
new EasyCrypt target or manifest entry is used to manufacture the stop result.
It is preserved as `logs/verify-all-week16-verify-matrix-crt.log` with SHA-256
`4cd64e5a656be82710bca1410c4d19403a3c661d6b91b0319a0ea8f7c91646da`.

## Actual procedure boundary

Fresh focused extraction confirms that actual `_verify_matrix_crt` executes
these helpers in order:

1. `_polyvec_ntt(z1p, cols)`
2. `_polymat_pointwise_acc(highp, a1p, z1p, rows, cols)`
3. `_polyvec_invntt(highp, rows)`
4. `_polyveck_poly_fromcrt(z1p, highp, wprimep, rows)`
5. `_polyvec_freeze2q(z1p, rows * 256)`

For mode 2, `rows = 2` and `cols = 4`. The extracted from-CRT body has the
following exact word behavior before freezing:

- indices `0..255` use
  `high + ((0 - ((high xor wprime) & 1)) & 64513)`;
- indices `256..511` use
  `high + ((0 - (high & 1)) & 64513)`.

The final helper applies extracted `__freeze2q` pointwise to those 512 words.
These observations come from opened generated procedure bodies; they are not
treated as semantic theorems.

## Closure attempts

Three independent proof attempts were made and discarded when they did not
fresh-compile or did not cover the actual four-column semantics.

- A direct from-CRT/freeze proof defined the two parity cases, the exact
  `__freeze2q` word function, prefix predicates, and frame predicates. Its
  fresh compile stopped in the first `_polyveck_poly_fromcrt` loop with
  `nothing to introduce`. The non-compiling block was removed.
- Reusing the checked KeyGen NTT and pointwise theorems can fresh-compile only
  a three-slice statement. Those theorems fix `cols = 3` and witnesses
  `p0,p1,p2`; they say nothing about Verify's fourth column. No such partial
  reuse was retained as if it proved the 2-by-4 row product.
- A direct spectral-action prototype reached the coefficient comparison for
  `Rq.&*` but could not normalize its `foldr (iota_ 0 256)` definition to the
  finite-sum form needed by the full-NTT double-sum argument. The prototype
  was removed after fresh compilation failed.

Consequently there is no new theorem hidden behind an unmanifested or
non-compiling file.

## Exact missing leaves

The stopped headline needs two Verify-side procedural leaves.

### NTT/row-product leaf

```text
verify_matrix_ntt_acc_mode2_cols4_correct
```

This leaf must open or refine the actual `_polyvec_ntt`,
`_polymat_pointwise_acc`, and `_polyvec_invntt` calls with `rows = 2` and
`cols = 4`, then prove that each returned `highp` row represents

```text
sum (c = 0..3) (matrix_poly a1p row c Rq.&* input_poly c).
```

The existing checked arithmetic interface is KeyGen-specific and fixes
`rows = 2`, `cols = 3`; it cannot instantiate this leaf.

Under this procedural leaf, the first concrete pure-algebra normalization
leaf absent from the checked NTT tree is:

```text
rq_mul_coeff_foldr_to_bigi
```

For `0 <= i < 256`, it must turn the implementation-facing definition

```text
foldr
  (fun k ci =>
     if 0 <= i-k then ci + a.[k] * b.[i-k]
     else ci - a.[k] * b.[256+i-k])
  0 (iota_ 0 256)
```

into the corresponding `Rq.BigDom.BAdd.bigi` negacyclic coefficient sum. That
normalization is required before proving the still-absent spectral-action leaf

```text
full_ntt_montgomery_spectral_action
```

with mathematical content

```text
array256_mont
  (full_invntt
    (Array256.init (fun j =>
       ahat.[j] * (full_ntt p).[j] * inv R)))
= (full_invntt ahat) Rq.&* p.
```

The subsequent finite-sum proof also needs the absent 256-term odd-root
orthogonality identity. The checked NTT artifact proves the imperative
forward/inverse transforms equal `full_ntt`/`full_invntt`; it does not prove
this convolution theorem.

### CRT/freeze leaf

```text
verify_crt_freeze_mode2_word_exact
```

This leaf must prove the two extracted parity cases above for
`_polyveck_poly_fromcrt`, prove the pointwise 512-word semantics of
`_polyvec_freeze2q`, preserve the inactive tail, and compose both actual
helpers. The attempted loop invariant did not compile, so this result is not
claimed from source inspection alone.

Only after both procedural leaves exist can
`verify_matrix_crt_mode2_fromcrt_freeze_exact` connect actual output to the
mathematical 2-by-4 polynomial row product and then be composed into the
existing Verify control theorem.

## Non-circularity and scope audit

No theorem precondition assumes any of the following:

- V-3 or V-4;
- the requested row-product or final output equality;
- `reject = 0`, a norm pass, or challenge equality;
- sampler distribution or termination.

This continuation did not modify or re-prove V-1, V-2, V-5, V-6, norm, or
tail results. It did not expand into KeyGen NTT, Sign challenge semantics,
codec, parser, public API, distribution, termination, or security.
The independently absent challenge leaf remains
`verify_tail_m23_highbits_lsb_sampleinball_correct`; it was not reopened in
this matrix/CRT continuation.

## Verification evidence

The focused `VerifyCoreTarget.ec` was regenerated and fresh-compiled. All four
existing Verify targets were individually fresh-compiled with `-no-eco`.
The final single-writer aggregate fresh-compiled all 82 targets and passed
proof-hole, authored-axiom, debug/temporary, manifest, extraction/hash,
actual-call-order, forbidden-premise, stopped-theorem, scope, selected
baseline, LaTeX, and before/after source-drift checks. It contains exactly 82
fresh-compile lines and exactly one terminal result line.

This evidence preserves the previous 82/82 result; it does not turn either
missing leaf into an assumption. The frozen verdict is therefore
**STOP-VERIFY-MATRIX-CRT**, not `GO-VERIFY`.
