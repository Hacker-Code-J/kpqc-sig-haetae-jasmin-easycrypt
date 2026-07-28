# Scope, Claims, and Trust Boundaries

## Verification target

The target is the Jasmin source under `../../haetae-ref-jasmin/jasmin/`, with
public behavior exposed through key generation, detached signing, and detached
verification for modes 2, 3, and 5. The initial specification artifact is
`../../haetae-security/HAETAE_v260204.pdf`, SHA-256
`80d28b3af9af2a27dba0eb4746f9b5755e05cb9a86bb6596f45fda06c605f3f6`.

This artifact selection is pinned but provisional: final publication must
confirm that it is the intended authoritative revision and record differences
from the TCHES 2024 artifact.

## Allowed claim ladder

### 1. Behavioral testing

`make test` demonstrates that smoke tests run and deterministic outputs match
the tracked KAT files. It can detect regressions but does not quantify all
inputs and is not a functional-correctness or security proof.

### 2. Jasmin-to-EasyCrypt extraction

A reproducible `jasmin2ec` result demonstrates that an EasyCrypt procedure
model was generated from a pinned Jasmin source. Extraction alone proves
neither that the procedure implements HAETAE nor that it is secure.

### 3. Functional correctness

Functional-correctness theorems must relate the extracted Jasmin procedures to
paper-faithful operations using explicit representation, memory, range,
aliasing, failure-path, and randomness conditions. Primitive theorems such as
NTT correctness do not imply end-to-end keygen/sign/verify correctness.

### 4. Provable security

The security theorem must define the exact HAETAE games and reductions and
retain only documented hardness and ROM assumptions. A structurally simplified
scheme that compiles in EasyCrypt is not automatically the scheme specified in
the paper or implemented in Jasmin.

### 5. Composed implementation security

An implementation-security statement requires both public-API functional
correctness and the paper-faithful security theorem. The composition must carry
all probability loss terms, memory/randomness preconditions, and trusted-tool
assumptions into its final statement.

## Source-level and assembly-level boundaries

The primary target is source-level Jasmin semantics as represented by
`jasmin2ec`. Lifting this result to generated assembly depends on the Jasmin
compiler's semantic-preservation guarantee and the pinned compiler. It does not
cover arbitrary downstream compiler/linker transformations.

## Separate non-functional claims

Memory safety, constant-time behavior, speculative constant-time behavior,
fault resistance, and physical leakage resistance are not consequences of
functional correctness or EUF-CMA security. They require separate tools,
models, and evidence. Until such checks are integrated and reported, they are
explicitly excluded by `../manifests/assumptions.md`.

## Status language

- `PINNED`: the exact artifact is fingerprinted, without a correctness claim.
- `PASS`: a command completed successfully for its stated scope.
- `PARTIAL`: checked evidence exists but cannot support the final claim.
- `BLOCKED`: a required prerequisite is missing or false.
- `VERIFIED`: the named theorem compiles against pinned sources and all
  retained assumptions are classified.

Only `VERIFIED` may be used for completed proof claims.
