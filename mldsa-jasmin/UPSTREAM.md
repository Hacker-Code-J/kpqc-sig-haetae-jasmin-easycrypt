# Upstream provenance

- Upstream repository: <https://github.com/formosa-crypto/formosa-mldsa>
- Project page: <https://formosa-crypto.org/projects/formosamldsa>
- Default branch: `main`
- Default-branch commit recorded for this vendor drop: `9f658bd495867d24224742a3935a02a4896cac92`
- Imported: 2026-08-04
- Visible tags at the time of import: `ml-dsa-65-ref-before-sct`, `ml-dsa-65-ref-after-sct`
- License: Apache-2.0

## What is vendored here

This directory mirrors the tracked source files from `formosa-crypto/formosa-mldsa` at the commit above.

The upstream repository describes itself as Jasmin implementations of the pure, hedged version of ML-DSA for:

- `x86-64/ref`
- `x86-64/avx2`
- `arm-m4/ref`
- `arm-m4/lowram`

It covers all ML-DSA parameter sets:

- ML-DSA-44
- ML-DSA-65
- ML-DSA-87

## Status caveat

Upstream marks this repository as experimental and explicitly says it is lightly tested only and not formally verified or proven for memory safety, constant-time behavior, speculative constant-time behavior, or functional correctness.

## Jasmin toolchain

Upstream README says to use the Jasmin compiler from the latest commit on the `main` branch and to ensure `jasminc` is in `PATH`.

The GitHub workflows build Jasmin with:

- `git clone --branch main --depth 1 https://gitlab.com/jasmin-lang/jasmin-compiler.git`
- `cd jasmin-compiler/compiler`
- `nix-shell --run 'make'`

## Build and test entry points

From the repository root:

- Generate assembly:
  - `env ARCHITECTURE=x86-64 PARAMETER_SET=65 IMPLEMENTATION_TYPE=avx2 make`
  - `env ARCHITECTURE=arm-m4 PARAMETER_SET=44 IMPLEMENTATION_TYPE=lowram make`
- Known-answer tests:
  - `make JASMINC='jasmin-compiler/compiler/jasminc' ARCHITECTURE='x86-64' PARAMETER_SET=65 IMPLEMENTATION_TYPE=ref test`
  - `env QEMU_LD_PREFIX=/usr/arm-linux-gnueabihf make JASMINC='jasmin-compiler/compiler/jasminc' CROSS_COMPILER='arm-linux-gnueabihf-gcc' ARCHITECTURE='arm-m4' PARAMETER_SET=44 IMPLEMENTATION_TYPE=ref test`
- Safety and CT checks:
  - `make JASMINC='jasmin-compiler/compiler/jasminc' ARCHITECTURE=x86-64 PARAMETER_SET=65 IMPLEMENTATION_TYPE=ref run-interpreter`
  - `make JASMINC='jasmin-compiler/compiler/jasminc' ARCHITECTURE=x86-64 PARAMETER_SET=65 IMPLEMENTATION_TYPE=ref check-ct`
  - `make JASMINC='jasmin-compiler/compiler/jasminc' ARCHITECTURE=x86-64 PARAMETER_SET=65 IMPLEMENTATION_TYPE=ref check-sct`

## Generated files

No git submodules are declared in upstream.

The vendored tree contains only tracked source and test assets from upstream; no build outputs were copied.

## Local import verification

The snapshot was checked with `Jasmin Compiler 2026.03.0`:

- All six x86-64 combinations (`ref` and `avx2` for ML-DSA-44/65/87)
  compiled and passed the six upstream pytest checks, for 36 passing checks in
  total.
- All six ARMv7M combinations (`ref` and `lowram` for ML-DSA-44/65/87)
  generated assembly successfully. Jasmin reports that ARMv7 support is
  experimental.
- The upstream `check-ct` target exited successfully for all twelve
  architecture/implementation/parameter-set combinations. The x86-64 `ref`
  checks emitted warnings that some `#declassify` annotations were ignored
  because only local variables are supported.
- The upstream `check-sct` target exited successfully for the three x86-64
  `ref` parameter sets.
- The ARMv7M known-answer tests were not run because the required
  `arm-linux-gnueabihf-gcc` and `qemu-arm` tools are not installed locally.

These test results do not supersede the upstream security and correctness
notice. Treat this snapshot as research code and do not use it in production.
