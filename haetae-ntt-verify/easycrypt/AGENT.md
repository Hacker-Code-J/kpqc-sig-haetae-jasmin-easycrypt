# Processing Task: End-to-End HAETAE NTT Correctness

## Current Goal

Build a checked end-to-end proof for the HAETAE Jasmin NTT implementation against
the full abstract polynomial NTT specification.

The already checked implementation refinement layer is:

```easycrypt
equiv RefJasminNTT.poly_ntt_core_ref :
  Hpoly_extract.M._poly_ntt ~ NTT_Fq.NTT.ntt :
  NTT_Fq.poly_repr_bound rp{1} r{2} 16 /\
  zetas{2} = NTT_Fq.zetas
  ==> NTT_Fq.poly_repr_bound res{1} res{2} 24.

equiv RefJasminNTT.poly_invntt_core_ref :
  Hpoly_extract.M._poly_invntt ~ NTT_Fq.NTT.invntt :
  NTT_Fq.poly_repr_bound rp{1} r{2} 16 /\
  zetas_inv{2} = NTT_Fq.zetas_inv
  ==> NTT_Fq.poly_repr_bound res{1} (NTT_Fq.array256_mont res{2}) 16.
```

The inverse postcondition is intentionally Montgomery-scaled; do not weaken or
erase that factor.

## Correct Abstract Target

Do not use `Rq.ntt` / `Rq.invntt` as the final full HAETAE NTT specification.
`NTTFullSpec.ec` proves that the existing `Rq.ntt` is an incomplete even/odd
128-point transform, not the full 256-point negacyclic transform computed by the
Jasmin core.

Use the full forward specification:

```easycrypt
op NTTFullSpec.full_ntt (p : poly) : poly =
  Array256.init (fun i =>
    Rq.BigDom.BAdd.bigi predT
      (fun j => p.[j] * ZqRing.exp zroot ((2 * br i + 1) * j))
      0 256).
```

and the analogous inverse operator in `NTTFullSpec.ec`.

## Checked Facts Available

- `RefJasminNTT.ec` compiles and proves the loop-level pRHL refinements from
  extracted Jasmin cores to `NTT_Fq.NTT.ntt` and `NTT_Fq.NTT.invntt`.
- `NTTAlgebra.ec` compiles and proves only inlining/equivalence to the local
  optimized imperative model. It does not prove algebraic NTT correctness.
- `NTTFullSpec.ec` compiles and proves:
  - `full_ntt_spec_imp`, converting the bit-reversed partial-sum spec into the
    closed-form full NTT;
  - `full_invntt_spec_imp`, converting the bit-reversed inverse closed-form
    spec into `full_invntt`;
  - `rq_ntt_is_not_full_ntt_on_one`, a concrete counterexample showing that
    `Rq.ntt` is not the full HAETAE NTT.

## Remaining Proof Obligation

The missing machine-checked bridge is:

```easycrypt
hoare NTT_Fq.NTT.ntt :
  arg = (p, NTT_Fq.zetas)
  ==> res = NTTFullSpec.full_ntt p
```

and the corresponding inverse theorem, with the final Montgomery representation
fact needed to compose with `poly_invntt_core_ref`.

The MLKEM algebra proof cannot be copied mechanically. Its partial-transform
exponent contains the incomplete-transform factor

```easycrypt
bsrev 8 ((s %% len) * 2)
```

whereas the full HAETAE transform needs

```easycrypt
bsrev 8 (s %% len)
```

with eight layers ending at length `256`.

## Verification

Before claiming any end-to-end theorem, run:

```sh
easycrypt compile NTTFullSpec.ec -I .
easycrypt compile NTTAlgebra.ec -I .
easycrypt compile RefJasminNTT.ec -I .
rg -n "\b(admit|abort|axiom)\b" RefJasminNTT.ec NTTFullSpec.ec NTTAlgebra.ec
```

Do not claim that complete HAETAE Jasmin NTT correctness has been
machine-checked until the imperative-to-`NTTFullSpec.full_ntt` bridge and its
inverse counterpart are present and compile without `admit`, `abort`, or new
axioms.
