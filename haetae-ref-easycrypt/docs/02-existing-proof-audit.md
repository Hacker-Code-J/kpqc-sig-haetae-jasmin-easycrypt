# Existing Proof Audit

This audit records what the repository's existing proof artifacts establish
before new `haetae-ref-easycrypt` extraction or refinement work begins.

## Managed security proof surface

The managed surface in `../../haetae-security/provable-security/proof-files.txt`
contains 16 EasyCrypt targets. On 2026-07-13:

- the repository verifier passed 16/16 targets on its first attempt;
- `../scripts/verify-security-fresh.sh` independently passed 16/16 targets with
  `easycrypt compile -no-eco`;
- a proof-command scan found no `admit` or `abort` commands; and
- an axiom-declaration scan found no EasyCrypt `axiom` declarations.

The word `abort` does occur as an ordinary bound variable in rejection-sampling
proofs. It is not an EasyCrypt proof-hole command, so the automated scan is
anchored to command position rather than matching every occurrence of the
word.

### Abstract foundations and theorem premises

The absence of `axiom` declarations does not make the security theorem
assumption-free. In particular:

- `HAETAE_Assumptions.ec:15-19` declares abstract lossless distributions for
  MLWE, Module-SIS, and bimodal self-target Module-SIS instances.
- `HAETAE_Security.ec:136-149` proves the displayed bound only after receiving
  the EUF-CMA-to-NMA hop, NMA-to-MLWE/bimodal hop, bimodal-to-Module-SIS hop,
  and the MLWE/Module-SIS hardness bounds as premises.
- `PAPER_CORRESPONDENCE_GAPS.md:7-16` identifies the structural portions that
  still prevent a paper-faithful implementation-security claim.

These boundaries are classified in `../manifests/assumptions.md`. Structural
correspondence premises are `TO_PROVE`; MLWE, Module-SIS, and ROM assumptions
may remain only when stated precisely in the final theorem.

## Existing NTT proof bundle

The full-safe constant-time NTT proof command completed in 8 minutes 56 seconds:

```sh
cd haetae-ntt-verify/easycrypt-ct
./scripts/check-full-functional-correctness.sh
```

Evidence from the fresh run:

- 17/17 EasyCrypt targets compiled with `-no-eco`;
- all 19/19 steps passed, including proof-hole and axiom-boundary scans;
- no `admit`/`abort` markers were found in checked targets; and
- axioms were confined to the declared foundational files `GFq.ec` and
  `Montgomery.ec`.

### Source-correspondence resolution and remaining limitation

The stored NTT extraction alone is not evidence about the exact target source:

- the stored extraction is associated with
  `../../haetae-ntt-verify/jasmin/hpoly.jazz`;
- the target is `../../haetae-ref-jasmin/jasmin/hpoly.jazz`;
- the target's `poly.jinc` uses materially different direct-loop code, while
  the NTT proof source is stage-specialized; and
- the full functional-correctness checker compiles the stored extraction but
  does not regenerate it during that command.

That missing single-polynomial connection is now checked separately.
`easycrypt/extract/ntt/HpolyTarget.ec` is regenerated from the exact target,
and `TargetNTTRefinement` proves its scalar, forward-loop, inverse-loop, and
wrapper equivalences to the checked direct-loop adapter before transporting
the algebraic postconditions. `./scripts/verify-ntt-proof.sh` pins the imported
proof sources and compiles that bridge.

The result still does not cover the `BArray8192` vector loops or pointwise
matrix accumulator used by `_kp_m23_matrix`; those are distinct extracted
procedures with additional representation and bound obligations.

## Jasmin behavioral baseline

A forced `make -B test` rebuilt the target Jasmin sources and passed smoke tests
and KAT comparisons for modes 2, 3, and 5. Each mode completed 100 positive
sign/verify iterations, and every generated KAT request/response matched its
tracked baseline.

The harness currently leaves extended negative tests disabled and can return
zero after printing an `Invalid on ...` message. The project wrapper therefore
scans output for that marker and requires three completion markers in addition
to the build/KAT exit status.

This is behavioral regression evidence only; it does not prove memory safety,
constant-time behavior, functional correctness, compiler correctness, or
cryptographic security.
