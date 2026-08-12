# Week 16 KG-NTT-MUL continuation report

## Decision

**STOP-KG-NTT.**

The actual `_kp_m23_matrix` loop chain already has checked forward-NTT,
three-column pointwise-accumulation, and inverse-NTT procedure theorems.  The
continuation fresh-compiles the last representation rewrite from that chain,
but the repository has no checked full-NTT convolution theorem.  Consequently
the actual `output_row` value still cannot be identified with the paper or
security-model product `Agen*sgen` without adding the desired result as a
premise.

The KeyGen lane is therefore frozen at the already-compiled KG-2/finalization
boundary.  KG-1, KG-3, the complete KG-4 vector, and
`A s = q j (mod 2q)` are not claimed.  The active MINCORE lane moves to Sign;
sampler distributions, KeyGen retry termination, packers, and public APIs stay
out of scope.

## Fresh continuation baseline

The immediately preceding complete `verify-all.sh` run fresh-compiled the
existing 76 authored targets with `-no-eco`.  Before modifying the proof
manifest, that completed log was preserved byte-for-byte as
`logs/verify-all-before-kg-ntt-mul.log`, SHA-256
`c556834b6e881930c8357ed136c5eb138a1a63bfdb977f194a63edae3298f348`.

## Existing actual procedure chain

No actual loop was copied or rewritten.  The reused chain is:

1. `TargetKeygenM23WideNTT.parent_polyvec_ntt_mode2_correct` proves that the
   actual parent `_polyvec_ntt` transforms the three secret polynomials to
   `full_ntt p0`, `full_ntt p1`, and `full_ntt p2`;
2. `TargetKeygenM23Pointwise.polymat_pointwise_mode2_repr_bound18_frame`
   proves the actual `_polymat_pointwise_acc` field products and row sums;
3. `TargetKeygenM23WideInvNTT.polyvec_invntt_mode2_pointwise_correct18`
   proves that the actual `_polyvec_invntt` returns the Montgomery
   representation of `full_invntt` for both rows; and
4. `TargetKeygenM23Arithmetic.kp_m23_matrix_mode2_arithmetic_correct`
   composes those leaves inside the actual `_kp_m23_matrix` and exports
   `mode2_output_repr_bound16 ... output_row`.

The new authored theory `Mode2KeygenNttMulBridge` proves the last sound
rewrite:

```text
output_row m p0 p1 p2 row
  = array256_mont
      (full_invntt (pointwise_row_words m transformed row))
```

under the actual transformed-secret representation.  Its
`actual_m23_matrix_snapshot_rows_explicit` corollary then applies that rewrite
to both active rows of the transparent harness which directly calls
`_kp_m23_matrix` and `_keypair_finalize_m23`.  Its precondition is exactly the
six initial-array bindings, the actual matrix/input representation bounds,
centered active `s2`, and canonical active `a`; its postcondition is the two
row slices represented by the corresponding actual returned transformed-secret
array's `full_invntt(pointwise_row_words ...)`.  It reuses
`actual_m23_matrix_finalize_semantic_snapshot` by consequence rather than
copying either actual loop proof.

None of these three theorems mentions or assumes `Rq.&*`,
`HAETAE_Algebra.poly_mul`, `Agen*sgen`, or a key equation.

## Exact missing NTT leaf

Let `ahat` be one stored matrix polynomial in NTT/Montgomery form and `p` one
coefficient-domain secret polynomial.  The first missing checked theorem is
the following spectral-action identity, including the actual Montgomery
factors:

```text
array256_mont
  (full_invntt
    (Array256.init (fun j =>
       ahat.[j] * (full_ntt p).[j] * inv NTT_Fq.R)))
= (full_invntt ahat) Rq.&* p
```

Linearity would then give, for each `row` in `[0,2)`,

```text
output_row m p0 p1 p2 row
= (full_invntt (matrix_poly m row 0) Rq.&* p0) Rq.&+
  ((full_invntt (matrix_poly m row 1) Rq.&* p1) Rq.&+
   (full_invntt (matrix_poly m row 2) Rq.&* p2)).
```

The first absent sublemma needed by a direct expansion proof is the
**odd-root orthogonality** formula

```text
sum_(j=0)^255 zroot ^ ((2 * br j + 1) * (k - i))
= if k = i then incoeff 256 else Zq.zero
```

for `0 <= i,k < 256`.  The checked NTT files prove the actual forward loop is
`full_ntt` and the actual inverse loop is `full_invntt`, but they do not prove
this orthogonality formula, `full_invntt(full_ntt p)=p`, or the pointwise-
product/negacyclic-convolution identity.  The NTT artifact itself labels the
inverse identity as pen-and-paper only and records base multiplication as not
fully functionally verified.

The legacy `Rq.ntt` cannot fill the gap:
`NTTFullSpec.rq_ntt_is_not_full_ntt_on_one` proves it differs from the actual
full transform.

## Second representation leaf after convolution

Even after the native `Rq` convolution theorem, a separate non-circular
adapter is required from `Rq.poly = Zq.coeff Array256.t` to the security
model's integer-list polynomials.  It must prove coefficientwise that

```text
rq_to_haetae (x Rq.&* y)
= HAETAE_Algebra.poly_mul (rq_to_haetae x) (rq_to_haetae y)
```

with canonical `Zq.asint` representatives, and lift the three-term row sum to
`HAETAE_Algebra.poly_dot` / `matrix_vec_mul`.  No such adapter theorem exists
in the checked refinement tree.

## KG scope after the stop decision

| Obligation | Final status | Compiled boundary |
| --- | --- | --- |
| KG-1 | **STOPPED / not proved** | both actual rows reach explicit `full_invntt(pointwise_row_words ...)`, not `Agen*sgen` |
| KG-2 | **PROVED** | actual finalizer canonical residue satisfies `b = b0 + 2*b1`, `b0 in {-1,0,1}` |
| KG-3 | **STOPPED / not proved** | no formal augmented matrix using the actual `Agen` product |
| KG-4 | **PARTIAL only** | actual adjusted words satisfy `e' = e-b0`; the full `(1 | sgen | e-b0)` object is not built |
| `A s = q j (mod 2q)` | **STOPPED / not proved** | only the snapshot equation over actual `pre_bp` is compiled |

No desired multiplication result, KG predicate, success fact, or final
equation was added to an operational theorem precondition.

## Fresh verification result

The final authored manifest contains 77 targets.  Both
`Mode2KeygenCoreEquation.ec` and `Mode2KeygenNttMulBridge.ec` were first
compiled individually with `easycrypt compile -script -no-eco -timeout 5`
and the same include surface used by the aggregate verifier; both exited 0.
The new declarations are:

- `output_row_from_mode2_ntt_words` at line 16;
- `output_row_repr_from_mode2_ntt_words` at line 33; and
- `actual_m23_matrix_snapshot_rows_explicit` at line 49.

A final single-instance run of `scripts/verify-all.sh` contains exactly 77
`PASS fresh compile` lines and exactly one terminal result:

```text
RESULT PASS authored-targets=77 cache=-no-eco
```

The preserved final log is `logs/verify-all-week16-kg-ntt-mul.log`, SHA-256
`8480d2e2f2ddda421c3d244ab5ec0a50196cadd7a8e1a29e996fd307aec7db57`.
It records successful proof-hole, authored-axiom, debug/temporary, manifest,
focused-extraction regeneration, generated table certificate, procedure
identity, selected upstream baseline, LaTeX, and post-verification read-only
root checks.

An independent read-only verifier audited the actual-call surface, theorem
pre/postconditions, absence of circular product premises, exact missing
leaves, claim boundaries, clean log counts/hash, and document consistency. Its
verdict was **PASS**, with no material residual risk beyond the two explicitly
stopped algebraic leaves.

## Sign transition

The next single MINCORE target is
`Mode2SignAcceptedCore.actual_sign_accepted_core_equations_mode2`: directly
compose the actual `_sf_round_challenge_mode2`, `_sf_z_check`, and
`_sf_hint_mode2` accepted-core helpers and derive the response, exact norm
predicates, and hint equation for terminating accepted executions.  This
transition does not reopen general KeyGen NTT algebra and does not include
sampler distributions, retry termination, packing, or a public API theorem.
