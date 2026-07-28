# Mathematical guide to the HAETAE EasyCrypt refinement layer

This folder gives mathematician-oriented notes for the six original
specification/refinement pairs and the mode-2-parent specification with its
two refinements. The notes state the exact machine-checked results, explain
their invariants as ordinary mathematics, and separate them from the
probabilistic and compositional lemmas still needed for an
implementation-level HAETAE security theorem.

Start with `HAETAERefinementMap.pdf`. It explains how the caller, uniform, eta,
Keccak, SHAKE-stream, and seed-expansion pairs fit together and how they relate
to the separate provable-security development.

| Mathematical note | EasyCrypt source pair | Main checked result |
| --- | --- | --- |
| `HAETAERefinementMap.pdf` | All fifteen authored files | Proof-stack and security-boundary overview |
| `TargetKeygenMode2Parent.pdf` | `KeygenMode2ParentSpec.ec` + `TargetKeygenMode2Parent.ec` + `TargetKeygenMode2ParentComposition.ec` | Actual-parent procedure bridges, mode-2 certificate bundles, and proof-only first-attempt sampler-prefix composition |
| `TargetKeygenSamplerCallers.pdf` | `KeygenSamplerCallersSpec.ec` + `TargetKeygenSamplerCallers.ec` | Matrix/vector/eta caller schedules agree with transparent recurrences |
| `TargetKeygenUniformXofLeaf.pdf` | `KeygenUniformXofLeafSpec.ec` + `TargetKeygenUniformXofLeaf.ec` | Exact finite SHAKE128 decoding, range/frame, and certificate-conditioned totality through both uniform leaves |
| `TargetKeygenEtaSampler.pdf` | `KeygenEtaSamplerSpec.ec` + `TargetKeygenEtaSampler.ec` | Exact finite SHAKE256 eta decoding, centered range/frame, and certificate-conditioned eta-leaf totality |
| `TargetKeygenShakeStream.pdf` | `KeygenKeccak1600Spec.ec` + `TargetKeygenKeccak1600.ec` + `KeygenShakeStreamSpec.ec` + `TargetKeygenShakeStream.ec` + `KeygenSeedXofSpec.ec` + `TargetKeygenSeedXof.ec` | Exact Keccak-f transition, bounded SHAKE blocks, and on-return seed expansion with named slices |

The recommended mathematical reading order is caller schedules, uniform
leaves, eta sampler, Keccak/SHAKE framing and seed expansion, the mode-2
parent prefix, and then the overview again.

## Build the collection

Use the locally available `pdflatex` toolchain:

```sh
cd haetae-ref-easycrypt/latex
make
```

The six PDFs are written to `build/`. Build one note with, for example:

```sh
make build/TargetKeygenEtaSampler.pdf
```

Run `make clean` to remove generated LaTeX files. The older first version of
the caller note is retained under `backup/` for comparison.

## Replay the EasyCrypt evidence

From the project root, run:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-sampler-callers-proof.sh
```

The gate checks pinned source hashes, rejects extraction drift across the
25-file/31-procedure unified target, compiles the generated target plus all six
specifications and all six refinements with `-no-eco`, and scans the authored
files for proof holes and axiom declarations.

Replay the actual-parent bridge and sampler-prefix evidence separately:

```sh
./scripts/verify-keygen-mode2-parent-proof.sh
```

This second gate checks both extraction closures, verifies that their 24
shared generated theories are byte-identical, and compiles its 17-entry
manifest with `-no-eco`. The retained 2026-07-23 run reports 17/17 compiled
with source, drift, shared-file identity, proof-hole, and axiom checks passing.

## Scope boundary

These notes document deterministic refinement and safety results, including an
exact Keccak-f transition, bounded SHAKE blocks, and on-return equality of
`_kp_expand_seedbuf` with the first 128 SHAKE256 bytes plus named slices. They
also document unconditional termination of the bounded uniform/eta consumers
and probability-one termination of both actual uniform leaves and the actual
eta leaf under their explicit deterministic `uniform_progress_prefix` or
`eta_progress_prefix` certificates and exact memory/slice bounds. They also
document parent-qualified versions of the seed, caller, and leaf theorems,
plus the proof-only mode-2 sampler prefix through its first five eta nonces.
They do not claim universal certificate existence, semantics or termination
of `_keypair_full_m23`, rejection-loop acceptance, sampler distributions,
source-pointer safety, side-channel security, or an implementation-level
EUF-CMA theorem. The overview lists the missing bridges explicitly.
