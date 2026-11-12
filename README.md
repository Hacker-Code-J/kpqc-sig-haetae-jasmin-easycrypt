# HAETAE — Jasmin / EasyCrypt

Thesis research artifacts for a Jasmin implementation of HAETAE and its
machine-checked analysis in EasyCrypt. The repository contains a reference-aligned
implementation, component specifications and proofs, a Hyperball variant with
additional arithmetic checks, reproduction tests and verification evidence.

Start with the [research-to-artifact map](docs/research-map.md). The
[claim boundaries](haetae-easycrypt/CLAIMS.md) state each result's assumptions and
scope; the [validation record](haetae-easycrypt/VALIDATION.md) identifies executions.

## Research scope

- **Component correctness:** connect extracted Jasmin Gaussian arithmetic and
  buffers, Hyperball, SHAKE, NTT multiplication and API memory helpers to their
  specifications.
- **Distributions and retry costs:** study Gaussian output distributions,
  rejection rates, expected attempt counts and one-attempt Hyperball probability
  bounds under explicitly independent uniform randomness models.
- **Arithmetic hardening:** check coefficient conversion and squared-norm
  overflow, proving that the true integer squared norm of a returned vector
  accepted by the hardened variant is at most the mode's bound.

These results do not establish correctness of the complete KeyGen/Sign/Verify
composition, a security argument replacing concrete SHAKE with iid randomness,
termination of the outer Hyperball retry loop, or complete signature
unforgeability. The hardened variant additionally rejects some inputs and is
not claimed equivalent to the original implementation on every input. KAT
success and machine-checked proof scope are reported separately.

## Getting started

The supported platform is Linux x86-64. Use Jasmin 2026.09.0, EasyCrypt r2026.09,
and the matching Why3/provers. Follow the [environment guide](env/README.md)
for installation, tool checks and resources. Tool versions are independent of
implementation directory names.

```sh
git clone https://github.com/Hacker-Code-J/kpqc-sig-haetae-jasmin-easycrypt.git
cd kpqc-sig-haetae-jasmin-easycrypt
bash env/bootstrap.sh
source env/activate.sh
bash scripts/reproduce.sh quick
bash scripts/reproduce.sh full
```

`quick` performs bounded execution, integrity and regression checks; `full`
runs the complete reproduction procedure selected for this artifact. The
[runner](scripts/reproduce.sh) and environment guide define the actual stages
and output locations. A successful quick check is not a complete proof replay.
Individual tasks can also be run as follows:

```sh
make -C haetae-jasmin -j2 test
make -C haetae-easycrypt verify
python3 haetae-hardened/scripts/materialize.py
python3 haetae-hardened/scripts/verify.py --group all
```

## Repository layout

| Path | Purpose |
| --- | --- |
| [HAETAE/](HAETAE/) | Original reference distribution, license and official KATs |
| [haetae-jasmin/](haetae-jasmin/) | Reference-aligned Jasmin implementation and tests |
| [haetae-easycrypt/](haetae-easycrypt/) | Extracted models, specifications and proofs for the original Jasmin implementation |
| [haetae-hardened/](haetae-hardened/) | Hyperball hardening code with separate extractions, proofs and tests |
| [docs/research-map.md](docs/research-map.md) | Research claims, implementations, proofs and reproduction commands |
| [docs/HAETAE.md](docs/HAETAE.md) | Reference-distribution provenance and identity |
| [archive/](archive/) | Earlier research records, preserved separately from current results |

Both `haetae-easycrypt` and `haetae-hardened` use EasyCrypt. The former is the
verification workspace for the original implementation; the latter contains a
behavior-changing implementation and its proofs. Historical verification records
remain evidence of their original source/tool states and are not automatically
promoted to PASS for current sources. See the [research history](docs/research-notes.md)
for the detailed development record.

Maintained reader documentation is in English. Frozen evidence, archived source
snapshots and historical path literals retain their original bytes and language.

## Citation and publication

[CITATION.cff](CITATION.cff) provides citation metadata. Cite the exact commit or
fixed artifact release used in the paper. The [release guide](docs/release.md)
describes how to freeze public sources and bind them to verification results.

Project-owned material uses [MIT](LICENSE). Existing notices for the reference
implementation and included external code are retained; the
[third-party guide](docs/THIRD-PARTY.md) identifies their respective provenance.
