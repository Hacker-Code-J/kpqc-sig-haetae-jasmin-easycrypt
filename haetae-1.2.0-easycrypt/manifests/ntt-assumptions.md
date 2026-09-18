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
This suite does not prove that a forward transform with arbitrary 24-bit
output can immediately satisfy the inverse transform's 18-bit precondition.
It also does not establish whole-signature correctness or a separate
polynomial-multiplication theorem.

## Retained arithmetic assumptions

The support sources are preserved byte-for-byte. They contain the following
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
All 11 support sources are byte-exact copies. The root proof has a new theory
name and version header, and adds total correctness by combining the existing
`NTT_Fq.ntt_spec_ll` / `invntt_spec_ll` results with checked refinements.

Run the project verification gate to check every local support source and the
root proof. `bash scripts/verify-one.sh proofs/NTTCorrectness.ec` checks the
root proof alone; EasyCrypt does not check imported proof scripts by default.
`-no-eco` disables cached-result output but does not change that import policy.
