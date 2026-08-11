# ML-DSA EasyCrypt specifications and proofs

This directory vendors the research artifact from
[`formosa-crypto/formosa-mldsa-correctness`](https://github.com/formosa-crypto/formosa-mldsa-correctness)
at commit `2dc59703c38bb29bb3f6e3a765f0a9934e143263`.

It contains:

- the EasyCrypt ML-DSA specification under `proofs/specs/`;
- correctness developments for the x86-64 AVX2 ML-DSA-65 Jasmin
  implementation under `proofs/x86-64/avx2/ml_dsa_65/`;
- the NTT development and generated array support used by those proofs; and
- the minimal, commit-pinned Jasmin, Keccak, and crypto-spec dependencies
  needed by the checked files.

See `UPSTREAM.md` for exact revisions and import details.

## Status

This is an incomplete research artifact, not a completed verification of all
ML-DSA implementations in this repository.

- The implementation-level development currently targets only ML-DSA-65 AVX2.
- The parameter theory currently admits ML-DSA-65 and ML-DSA-87; the
  ML-DSA-44 tuple is commented out because one stated bound does not discharge.
- `admit`/`admitted` placeholders remain in the specification and correctness
  files, including sampling, polynomial arithmetic, NTT bridges, and rounding.
- The upstream `main` CI run for the imported commit is failing.
- The proof artifact pins `formosa-mldsa` commit `91f9c5f...`; it therefore
  does **not** prove the newer code vendored in `../mldsa-jasmin/` at
  `9f658bd...`.

Do not describe this snapshot as a complete functional-correctness,
constant-time, memory-safety, or production-readiness proof.

## Layout

- `proofs/specs/`: ML-DSA algorithms, serialization, sampling, algebra, and
  parameter definitions.
- `proofs/x86-64/avx2/common/`: NTT specifications and proofs.
- `proofs/x86-64/avx2/ml_dsa_65/`: extracted Jasmin model and
  key-generation, signing, and verification equivalence developments.
- `proofs/eclib/`, `proofs/arrays/`, `proofs/xarrays/`, `proofs/xwords/`:
  supporting EasyCrypt libraries and generated array theories.
- `submodules/`: only the dependency subsets used by this proof tree,
  materialized at the upstream-pinned revisions. These are ordinary vendored
  files, not live Git submodules.

## Reproduction

The upstream workflow pins:

- OCaml `5.3.0`;
- EasyCrypt commit `cd6faa0ef208935347915e16bb29e9edb1e64ac1`;
- Jasmin compiler commit `fe014bf18283a064c2796e54442d6ef9801c8c71`;
- CVC5 `1.3.3`; and
- Z3 `4.15.8`.

With that toolchain installed, the upstream entry point is:

```sh
env TERM=xterm-256color make check
```

`make check` first re-extracts `ml_dsa_65_avx2.ec` from the pinned Jasmin
source and then runs the EasyCrypt suite configured by
`config/tests.config`.

The locally installed EasyCrypt build does not recognize the required
`+Circuit:timing` pragma, so a successful local full proof check was not
claimed during import. The Jasmin-to-EasyCrypt extraction step did succeed.

The separate [`formosa-crypto/dilithium`](https://github.com/formosa-crypto/dilithium)
repository was not copied here. It develops an algorithm-level ROM security
proof for pre-standard Dilithium and is not a correctness proof of the pinned
Jasmin implementation.

## Licensing

The top-level correctness repository has no `LICENSE` or `COPYING` file.
Public availability does not itself grant redistribution rights. Read
`LICENSE-STATUS.md` before redistributing or publishing this snapshot.
