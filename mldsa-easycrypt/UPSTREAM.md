# Upstream provenance

## Primary artifact

- Repository: <https://github.com/formosa-crypto/formosa-mldsa-correctness>
- Default branch: `main`
- Commit: `2dc59703c38bb29bb3f6e3a765f0a9934e143263`
- Commit date: 2026-06-18
- Imported: 2026-08-05
- Releases/tags at import: none

The upstream repository had no README and no license file at the imported
revision. This directory adds `README.md`, `UPSTREAM.md`, and
`LICENSE-STATUS.md` as local documentation.

## Pinned dependencies

The primary artifact records these Git submodule revisions:

- EasyCrypt: `cd6faa0ef208935347915e16bb29e9edb1e64ac1`
- formosa-mldsa: `91f9c5ffd2d2a98ec0c7bf4e5d70a36ebdd3acc1`
- Jasmin compiler: `fe014bf18283a064c2796e54442d6ef9801c8c71`

The formosa-mldsa dependency in turn pins:

- formosa-keccak: `2db21a051a0caa750d52ab9552a5825c015cfc3d`
- crypto-specs: `fb050598ed356c5c6604d92a1e198b2dd4543777`

Only the dependency paths referenced by `Makefile` and `easycrypt.project`
are materialized here. Full EasyCrypt and Jasmin compiler source trees,
benchmarks, unrelated architecture sources, Git histories, and nested `.git`
metadata are intentionally omitted.

The retained upstream `.gitmodules` file is provenance metadata only. Since
this directory is vendored inside another repository, its entries are not
live submodules.

## Proof scope at this revision

The artifact supplies a high-level ML-DSA specification and implementation
equivalence developments for:

- x86-64;
- AVX2;
- ML-DSA-65; and
- deterministic key generation plus hedged signing and verification.

Named top-level implementation lemmas include:

- `ml_dsa_65_keygen_correct`;
- `ml_dsa_65_sign_correct`; and
- `ml_dsa_65_verify_correct`.

These lemmas depend transitively on admitted obligations. A textual audit of
the imported tree found 67 `admit`/`admitted` occurrences across 17 EasyCrypt
files; one occurrence is in explanatory text, while the remainder include
open proof obligations. This snapshot must therefore be treated as work in
progress.

## Relationship to `mldsa-jasmin`

`../mldsa-jasmin/` records upstream commit
`9f658bd495867d24224742a3935a02a4896cac92`. This proof artifact instead pins
`91f9c5ffd2d2a98ec0c7bf4e5d70a36ebdd3acc1`. The implementation changed
substantially between those commits, so the proofs must not be attributed to
the newer snapshot without a new extraction and proof-maintenance pass.

## Import verification

- The primary source files were copied from the exact commit above.
- Required public submodules were resolved at their recorded commits.
- No nested `.git` directories or build caches were imported.
- `make extract` succeeded with Jasmin Compiler 2026.03.0 and regenerated the
  tracked `ml_dsa_65_avx2.ec` model without changing the upstream tree.
- A full `make check` with the locally installed EasyCrypt failed before
  checking files because that build rejects the required
  `+Circuit:timing` pragma.
- `easycrypt compile -no-eco proofs/specs/Parameters.ec` succeeded locally.
- Direct compilation of `proofs/specs/MLDSA.ec` with the local toolchain
  stopped at the missing `ZModPCentered` theory, another pinned-toolchain
  compatibility requirement.
- Building the pinned EasyCrypt revision locally was not completed because
  its additional OCaml dependencies (`lwt.unix`, `bitwuzla-cxx`, and
  `ppx_deriving_yojson`) are not installed in the current switch.
- The upstream GitHub Actions run for this exact `main` commit also concluded
  with failure in its `Check proofs` step.
