# NTT proof scope and assumptions

`proofs/NTTCorrectness.ec` proves mathematical correctness of the fresh
`generated/ntt/HpolyTarget.ec` extraction. Its top-level theory is
`NTTCorrectness`. The historical arithmetic and loop proofs are local source
files in `theories/ntt`; no archive tree or historical `.eco` file is required
to replay them.

## Statements proved

For each coefficient, `poly_repr_bound rp p s` means that the signed 32-bit
word in `rp` represents the corresponding coefficient of `p` modulo 64513,
and lies in `[-2^s, 2^s)`. These are coefficient bounds, not a claim about
how many bits the input buffer occupies.

| Current target procedure | Mathematical result | Input bound | Output bound | Total-correctness theorem |
| --- | --- | --- | --- | --- |
| `_poly_ntt` | `NTTFullSpec.full_ntt p` | `s = 16` | `s = 24` | `target_poly_ntt_total` |
| `poly_ntt_jazz` | `NTTFullSpec.full_ntt p` | `s = 16` | `s = 24` | `target_poly_ntt_jazz_total` |
| `_poly_invntt` | `array256_mont (full_invntt p)` | `s = 16` | `s = 16` | `target_poly_invntt_total` |
| `_poly_invntt` | `array256_mont (full_invntt p)` | `s = 18` | `s = 16` | `target_poly_invntt_total18` |
| `poly_invntt_jazz` | `array256_mont (full_invntt p)` | `s = 16` | `s = 16` | `target_poly_invntt_jazz_total` |
| `poly_invntt_jazz` | `array256_mont (full_invntt p)` | `s = 18` | `s = 16` | `target_poly_invntt_jazz_total18` |

Each total theorem is a `phoare [...] = 1%r` statement: under its input
condition, execution terminates and satisfies the stated result with
probability 1. The original corresponding `*_correct` Hoare statements
remain available. `target_fqmul_correct` identifies the exact signed
Montgomery reduction result, and `target_fqmul_ll` proves its losslessness.

Here `br` reverses 8 index bits, `z = 426` in the field modulo 64513, and
the sum indices range from 0 through 255:

```text
full_ntt(p)[i]    = sum_j p[j] * z^((2 * br(i) + 1) * j)
full_invntt(p)[i] = 256^-1 * sum_j p[j] * z^(-(2 * br(j) + 1) * i)
array256_mont(p)  = coefficientwise multiplication by 2^32 mod 64513
```

The inverse result includes the Montgomery factor used by the implementation.
The multiplication path applies a Montgomery product between the forward
and inverse transforms. Its output bound supplies the inverse transform's
input condition; the forward output bound alone does not supply it.

## Multiplication and vector composition

`theories/NTTProductExpansion.ec` expands `Rq.(&*)` into its signed cyclic
convolution sum. `theories/NTTTransformAlgebra.ec` proves, for all two
polynomials `p` and `q`,

```text
full_invntt(full_ntt(p)) = p
full_ntt(p &* q) = pointwise(full_ntt(p), full_ntt(q))
R * full_invntt(R^-1 * pointwise(full_ntt(p), full_ntt(q))) = p &* q
```

Here `p &* q` is multiplication modulo `X^256 + 1`, `pointwise` is ordinary
coefficientwise field multiplication, and `R = 2^32 mod 64513`. The scalar
factors in the last equality act on every coefficient. These statements use
the full 256-point transform, not the legacy even/odd transform `Rq.ntt`.
Root order, character orthogonality, the inverse identity, and the product
identity are proved from the existing field representation.

`proofs/NTTMontgomeryBounds.ec` proves that the signed result of the actual
`__fqmul` represents `a*b*R^-1` modulo 64513. For two signed inputs in
`[-2^24,2^24)`, the result lies in `[-2^17,2^17)`. If the first input is
canonical in `[0,64513)` and the other has exponent bound 24, the result
lies in `[-2^15,2^15)`. All these values are stored in 32-bit words.

`proofs/NTTPointwiseCorrectness.ec` proves total correctness of the actual
API `_polyvec_poly_pointwise` for at most eight polynomials: the returned
vector represents the coefficientwise Montgomery product, has exponent
bound 17, and preserves output bytes beyond the active polynomials.
`proofs/NTTVectorCorrectness.ec` proves exact byte-result equivalence of the
actual vector transform loops and repeated calls to the verified scalar
transform. It accounts for the actual 64-bit counters and block offsets.

`proofs/NTTVectorTotal.ec` transfers the scalar total-correctness results
through those equivalences. The actual API vector NTT has exponent bounds
16 to 24; the vector inverse has bounds 18 to 16 and returns
`array256_mont(full_invntt p)` in each active block. Both results preserve
the inactive bytes and cover every vector length from zero through eight.

`proofs/NTTProductCorrectness.ec:sign_compute_cs2_total` proves total
correctness of `NTTProductTarget.M.sign_compute_cs2_jazz`, freshly extracted
from `signing_challenge_product.jazz`. Its input vector represents
`map full_ntt ps` and its other input represents `full_ntt c`, both with
exponent bound 24. The output represents `map (fun p => p &* c) ps` with
bound 16 and preserves inactive output bytes. The intermediate bound 17
implies the inverse routine's required bound 18. This entry receives
transformed inputs; its theorem does not insert a forward transform that
the source entry does not execute.

`proofs/NTTMatrixCorrectness.ec` proves total correctness of the actual API
`_polymat_pointwise_acc`. The matrix coefficients must be canonical in
`[0,64513)` and the vector coefficients must have exponent bound 24. There
are at most eight rows and eight columns, with at most 32 matrix blocks.
For every active output coefficient, the signed integer result is the sum
of the corresponding signed Montgomery products and lies in
`[-2^18,2^18)`. Its field interpretation is the matrix dot product times
`R^-1`; the proof also preserves every inactive output byte. The canonical
matrix condition supplies the stronger exponent-15 bound on each product,
which bounds accumulation over at most eight columns.

`proofs/NTTMatrixProductCorrectness.ec` then verifies the fresh
`NTTMatrixTarget` extraction of `keypair_matrix.jazz`. Starting with a
vector of exponent bound 16, `copy_ntt_export_total` proves the actual
copy-and-transform entry returns `map full_ntt ps` with bound 24.
`matrix_m5_export_total` proves that the mode-5 entry returns the matrix
image in the NTT domain with bound 18. `matrix_m23_export_total` proves
that the mode-2/3 entry instead applies the Montgomery-scaled inverse
transform to that image and returns bound 16. Both entries also return
the transformed input vector with bound 24 and preserve the inactive
bytes of both output arrays. The matrix image is defined coefficientwise
as the field dot product times `R^-1`. Matrix generation from a seed and
the remaining key-generation calculations are outside these entry theorems.

These component results do not assert correctness of the whole signature
algorithm or its unforgeability.

## Shared composition theorem

`theories/NTTComposition.ec` is the same shared source as the NTRU+768
`ntt_common/NTTComposition.ec`. It states a total-correctness rule for two
forward calls, a multiplication call, and an inverse call. The transformed
representation, the multiplication-result representation, and their bounds
are separate parameters. Each instance proves all three procedure premises;
the shared theory adds no algorithm-correctness axiom or ring assumption.

`proofs/NTTCompositionInstance.ec:haetae_ntt_product_total` applies that rule
to adapters that call the actual extracted scalar NTT, actual vector
pointwise multiplication with one active polynomial, and actual scalar
inverse NTT. The input arrays represent polynomials `p` and `q` with exponent
bound 16. The result represents `p &* q`, has exponent bound 16, and is
returned with probability 1. The intermediate bounds are 24 and 17. The
product representation explicitly includes `R^-1 * full_ntt(p &* q)`;
its bound 17 implies the inverse routine's required bound 18.

The verified four-call program is an EasyCrypt composition of the extracted
kernels. No new native entry point is asserted. This shared theorem reuses
program composition; transform-specific algebra and range proofs remain
in the two concrete instances. The shared-source digest is checked by the
normal project provenance gate.

## Retained arithmetic assumptions

This extension leaves the existing support sources unchanged. They contain the following
assumptions, so this suite must not be described as axiom-free.

- `GFq.prime_q` assumes `prime 64513`. `GFq.ec` does not prove primality.
  Its clone of `ZModField` discharges `prime_p` by this assumption; consequently
  all field-based NTT statements retain this arithmetic trust assumption.
- `Montgomery.SignedReductions` is a parameterized reduction theory with
  axioms `q_bnd`, `q_odd1`, `q_odd2`, `qqinv`, `qinv_bnd`, `Rinv_gt0`, and
  `RRinv`, and the constrained parameter `2 < k` named `gt2_k`.
  The concrete `Fq.SignedReductions` clone sets `k = 32`, `q = 64513`,
  `qinv = 940508161`, and `Rinv = 50386`. Its seven explicit `proof` clauses
  discharge the seven numeric axioms for these constants. The unchanged
  clone does not discharge `gt2_k`: EasyCrypt reports
  `Fq.SignedReductions.gt2_k` as the residual axiom `2 < 32`. This trivially
  true numeric proposition is nevertheless retained as an axiom and is
  included in this inventory. The seven discharged conditions print as
  lemmas; their original generic axioms also remain in the imported file.
- The same unchanged `Montgomery.ec` also contains generic theories
  `Montgomery'`, `Montgomery`, and `MontgomeryLimbs`. These declare or clone
  `k_pos`, `N_bnd`, `NN'`, and `RRinv`; `MontgomeryLimbs` further declares
  `r_ge0`, `w_ge0`, `REDCk0`, and `REDCkS`. They remain in the imported
  environment. The HAETAE reduction is instantiated from `SignedReductions`,
  not those generic unsigned or multi-limb algorithms. This is a source-level
  dependency classification, not an exported minimal-axiom certificate.
- `axiomatized by` declarations `GFq.qE`, `SignedReductions.smodE`,
  `Rq.nttE`, and `Rq.invnttE` name equations for explicitly supplied
  definitions. They are distinct from an unproved assertion that a Jasmin
  routine implements an algorithm. The final NTT specification uses
  `NTTFullSpec.full_ntt` and `full_invntt`.
- The `Fastexp` and `BigComRing` algebraic clones are instantiated with
  field operations, and their algebraic obligations are realized locally
  using the imported field laws. They inherit the `prime_q` assumption.

No new algorithm-correctness axiom or admitted proof was added by this port.
EasyCrypt's logic, installed standard and Jasmin libraries, SMT provers, and
the Jasmin extraction/compiler semantics remain part of the trusted tooling.
The verified boundary is the extracted Jasmin program, not a separate proof
of the emitted assembly or of equivalence with every C reference procedure.

## Replay and provenance

`ntt-support-origin.tsv` lists the 11 support sources in dependency order,
followed by `proofs/NTTCorrectness.ec`. It records historical snapshot paths
and SHA-256 digests for review; those paths are provenance data only.
The gate accepts the historical bytes or the specifically reviewed 2026.09
ports recorded in `scripts/verify.py`; four NTT support files have such port
entries. This extension changes neither those sources nor their allowed
digests. The root proof has a distinct theory name and version header, and
adds total correctness by combining the existing
`NTT_Fq.ntt_spec_ll` / `invntt_spec_ll` results with checked refinements.

Run the project verification gate to check every local support source and the
root proof. The NTT group also checks every new composition theory listed in
`ntt-composition-targets.txt`; its entries must exactly match the discovered
top-level NTT theories and proofs. `bash scripts/verify-one.sh proofs/NTTCorrectness.ec` checks the
root proof alone; EasyCrypt does not check imported proof scripts by default.
`-no-eco` disables cached-result output but does not change that import policy.
