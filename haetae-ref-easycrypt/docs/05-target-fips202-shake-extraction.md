# Target Jasmin FIPS202/SHAKE Extraction

## Scope

This extraction is generated from the target source and its direct dependency:

```text
haetae-ref-jasmin/jasmin/fips202.jazz
haetae-ref-jasmin/jasmin/keccak.jinc
```

Both files are pinned by `manifests/sources.sha256`. The extraction selects the
smallest coherent public one-shot SHAKE boundary:

- `fips202_shake128_jazz`
- `fips202_shake256_jazz`

The generated module also contains their reachable Keccak-f[1600], absorb,
padding, and squeeze dependencies. The public SHA3-256 and SHA3-512 wrappers
are deliberately excluded because they are not needed for this SHAKE
milestone.

## Regeneration

From the project directory:

```sh
./scripts/regenerate-fips202-shake-extract.sh
```

The effective extraction command is:

```sh
jasmin2ec --array-model=barray \
  --output-array=<temporary-directory> \
  -o <temporary-directory>/Fips202ShakeTarget.ec \
  -f fips202_shake128_jazz \
  -f fips202_shake256_jazz \
  ../haetae-ref-jasmin/jasmin/fips202.jazz
```

Generation occurs in a temporary directory. The script requires the generated
file set to match `manifests/fips202-shake-extract-files.txt` before copying
results into `easycrypt/extract/fips202/`. Generated EasyCrypt files must not
be edited manually.

## Drift and compilation checks

```sh
./scripts/check-fips202-shake-extract-drift.sh
./scripts/verify-fips202-shake-extract.sh
```

The drift check regenerates from the pinned sources and compares all eight
generated files byte-for-byte. The verifier compiles each generated theory
with `easycrypt compile -no-eco`, rejects proof-hole or axiom declarations,
and records source hashes and results in
`logs/fips202-shake-extract-summary.txt`.

## Claim boundary

Successful extraction and compilation establish that:

1. `Fips202ShakeTarget.M.fips202_shake128_jazz` and
   `Fips202ShakeTarget.M.fips202_shake256_jazz` are reproducibly generated from
   the pinned target Jasmin source; and
2. their generated procedures and array theories are accepted by EasyCrypt
   without cache reuse.

They do **not** establish FIPS202 functional correctness, Keccak permutation
correctness, memory safety, or equivalence to the security proof's random
oracle. Those require refinement lemmas for padding, domain separation,
little-endian lane encoding, absorb order, output length, and framed memory
effects.

The target `keypair.jazz`, `sign.jazz`, and `verify.jazz` paths also use
specialized low-level Keccak/SHAKE routines rather than calling these one-shot
public wrappers. Consequently, this extraction is a reusable primitive
foothold; it is not yet evidence that the mode-2 public API call paths refine
the extracted wrapper procedures.

## Relationship to the mode-2 call paths

A repository-wide call search finds no call from `keypair.jazz`, `sign.jazz`,
or `verify.jazz` to either extracted wrapper. Transitive `jasmin2ec` selection
of each mode-2 internal entry point instead exposes source-local hashing
boundaries over the same `keccak.jinc` implementation:

| Mode-2 path | Internal entry point | Extracted boundary | Pending focused boundaries |
| --- | --- | --- | --- |
| Key generation | `crypto_sign_keypair_internal_mode2_jazz` (`keypair.jazz:1305`) | `_kp_expand_seedbuf` (`:974`); all three sampler leaves; `_kp_polymatkm_expand_matA` (`:841`), `_kp_polyveck_expand_vecA` (`:894`), and `_kp_polyvec_expand_eta` (`:937`); separate extraction of the actual `_keypair_full_m23` parent and deterministic mode-2 entry | The proof-only parent-module prefix now composes exact seed expansion with the matrix, vector, and first-attempt eta calls; `_keypair_full_m23` retry/downstream semantics, singular rejection, and end-to-end refinement remain open |
| Signing | `crypto_sign_signature_internal_mode2_jazz` (`sign.jazz:2725`) and `crypto_sign_signature_mode2_jazz` (`:2806`) | None | `_sf_mu_rawpre` (`:255`), `_sf_mu_preptr` (`:300`), `_sf_sign_expand_seedbuf` (`:344`), `_sf_shake128_init_seed32` (`:450`), `_sf_shake256_init_seed64` (`:834`), `_sf_hyperball_b_raw` (`:1060`), `_sf_challenge_mode2` (`:1813`) |
| Verification | `sign_verify_internal_mode2_jazz` (`verify.jazz:484`) | None | `__poly_sample_shake128_init` (`polynomial_sampler.jinc:79`), `__verify_hash_mu` (`verification_transcript.jinc:216`), `__verify_challenge_m23` (`verification_transcript.jinc:305`) |

Focused key-generation, signing, and verification modules keep their descriptor
and memory preconditions reviewable. The deterministic mode-2 key-generation
parent is now reproducibly extracted as a separate 32-file, 56-procedure
closure; see
[`12-target-keygen-mode2-parent-extraction.md`](12-target-keygen-mode2-parent-extraction.md).
That result is extraction-and-compilation evidence only. A separate checked
proof-only prefix connects the exact seed-expansion result to the actual parent
module's matrix, vector, and first-attempt eta sampler calls; see
[`13-target-keygen-mode2-parent-refinement.md`](13-target-keygen-mode2-parent-refinement.md).
It does not prove `_keypair_full_m23`, its retry/downstream control, packing,
source-pointer safety, distributions, or the remaining FIPS202/security
composition needed to close `GAP-PK-FIPS202` or a ROM transcript obligation.

The later signing/verification bridge must prove two encoding facts rather
than assume the two paths hash the same bytes:

1. signing absorbs the first `vkbytes` bytes of the secret-key buffer, while
   verification absorbs the explicit public key, so the packed secret-key
   prefix must be proved equal to that public key; and
2. signing computes a 64-byte `mu` but the challenge absorbs its first 32
   bytes, while verification directly computes a 32-byte `mu`, so the proof
   must establish `verify_mu = take 32 sign_mu`.

The first follow-up leaf, `_kp_expand_seedbuf` (`keypair.jazz:974-1021`), is now
reproducibly extracted. It is reached from the mode-2 key-generation entry
through `_keypair_full_m23` and expands a 32-byte seed into a 128-byte buffer
using the target's SHAKE256 loop. `kp_expand_seedbuf_correct` proves that the
unified generated procedure returns exactly `SHAKE256(seed, 128)`, and named
Hoare corollaries expose bytes 0 through 31, 32 through 95, and 96 through 127.
The extraction/refinement split and remaining actual-parent composition
obligations are documented in
[`06-target-keygen-seed-xof-extraction.md`](06-target-keygen-seed-xof-extraction.md).

The next completed extraction contains the two SHAKE128/rejection-sampling
leaves used for the matrix `Agen`/`A0` and vector `agen`/`a`. Their caller
loops are documented reachability evidence, not part of the generated module.
See
[`07-target-keygen-uniform-xof-extraction.md`](07-target-keygen-uniform-xof-extraction.md).

The SHAKE256 eta-sampler leaf and parameterized eta vector caller are also
reproducibly extracted. Exact deterministic leaf and vector-caller finite-stream
refinement is now checked, and an authored proof-only wrapper composes two
actual caller invocations with the mode-2 counts and nonce split.
Distributional properties and semantic composition of the seed-XOF result and
sampler calls through the actual `_keypair_full_m23` remain proof obligations.
See
[`08-target-keygen-eta-xof-extraction.md`](08-target-keygen-eta-xof-extraction.md).

The three parameterized sampler callers and `_kp_expand_seedbuf` are now
extracted together with all three sampler-leaf closures. Their exact loop
formulas and the seed-expansion body are present, while mode-2 instantiation and
cross-caller composition remain outside that generated module. See
[`09-target-keygen-sampler-callers-extraction.md`](09-target-keygen-sampler-callers-extraction.md).
