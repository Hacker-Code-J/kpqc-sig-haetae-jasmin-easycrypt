# HAETAE Jasmin

An x86-64 Jasmin implementation corresponding to the HAETAE reference
implementation. It includes KeyGen, signing and verification for modes 2, 3 and 5.
The algorithm implementation is in `jasmin/`; production libraries are built
entirely from Jasmin-generated assembly.

## Baseline sources and changes

- Comparison baseline: the [official distribution](../HAETAE/reference_implementation/),
  pinned by [per-file SHA-256 hashes](../docs/UPSTREAM-SHA256SUMS).
- Starting point: `haetae-ref-jasmin/` at preserved commit
  `6177f8db0a2887314dbff213e5ca04234eece58e`. No previous build artifacts or KAT
  vectors were imported.
- Sampler: updated to an 83-bit, 166-entry CDT, upward-rounded `smulh48`,
  degree-10 `approx_exp`, 26-byte random inputs, and separate rounding that
  avoids shift overflow for large samples.
- Gaussian stream: both the common function and the signing-internal path use
  49 SHAKE blocks (6664 bytes) with the 26-byte consumption and carry rules.
- API: detached signatures are distinguished from signatures combined with
  messages; combined signing with the same buffer copies the message backwards.

The MIT license is in [LICENSE](LICENSE). NIST notices in the KAT drivers are
retained in their respective files.

## Build and tests

Requires Linux x86-64, GNU Make, a C11 compiler and Jasmin Compiler **2026.09.0**.
KATs require OpenSSL development files and `libcrypto`, as in the reference
implementation. `JASMINC`, `CC`, `CFLAGS` and other settings may be supplied
as Make variables.

```sh
make -C haetae-jasmin -j2 all
make -C haetae-jasmin -j2 test
```

| Target | Checks |
| --- | --- |
| `all` | Builds shared libraries and basic execution tests for all three modes |
| `sign-test` | 100 randomized signing/verification runs per mode; exits abnormally on failure |
| `api-test` | 8 APIs, context length, input tampering, buffer overlap and failure outputs |
| `sampler-test` | Differential comparisons against the actual C sampler for CDT boundaries, upward rounding, rare tails and refills |
| `interop-test` | C/Jasmin key and signature byte comparisons and signing/verification/open in both directions |
| `kat` | Byte equality of `.req` and `.rsp` files for 100 official KATs per mode |
| `check-reference` | Checks the pinned distribution and KAT hashes |

Libraries are generated at
`build/mode{2,3,5}/lib/libhaetae-mode{2,3,5}-jazz.so`.
Test programs are placed in `build/bin/` and generated KATs in `build/kat/`.
All generated artifacts are under `build/` and excluded from Git.

## API and randomness integration

Include [include/api.h](include/api.h) and set `HAETAE_CONFIG_MODE` to one of
`HAETAE_MODE2`, `HAETAE_MODE3` or `HAETAE_MODE5`.

| API | Meaning |
| --- | --- |
| `crypto_sign_keypair` | Key generation using randomness |
| `crypto_sign_keypair_internal` | Key generation using an input seed |
| `crypto_sign_signature` | Detached signing |
| `crypto_sign_signature_internal` | Detached signing using a raw prefix and input randomness |
| `crypto_sign` | Output combining the signature and message |
| `crypto_sign_verify` | Detached-signature verification including a context |
| `crypto_sign_verify_internal` | Verification using a raw prefix |
| `crypto_sign_open` | Verifies a combined signature and recovers the message |

The call interface is compatible with the reference C API. Because Jasmin
limits the number of x86-64 arguments, thin C inline functions in the header
pass long argument lists through descriptors. Descriptor symbols exported by
the shared library are distinct from the C reference library's binary ABI.
Message processing, signing and verification execute in Jasmin.

Randomized APIs use the following application-provided Jasmin randomness function.

```c
uint8_t *__jasmin_syscall_randombytes__(uint8_t *out, uint64_t outlen);
```

For tests, [test/randombytes.c](test/randombytes.c) connects to operating-system
randomness. For KATs, [kat/jasmin_randombytes.c](kat/jasmin_randombytes.c) connects
to the reference driver's deterministic DRBG. The reference C algorithm is linked
only into differential and interoperability test executables.

## Compiler-check scope

If `jasmin-ct` is installed, run CT/SCT checks on the modified sampler with:

```sh
make -C haetae-jasmin sampler-ct
```

Targets are the CDT, upward-rounded multiplication, exponential approximation,
single Gaussian attempt, fixed-buffer consumption and Gaussian stream modules.
These checks assume the explicit declassification contracts in the source.
KATs, differential tests and these limited compiler checks do not replace a
security proof of the complete algorithm or an EasyCrypt proof of HAETAE.

A separate [EasyCrypt verification project](../haetae-easycrypt/README.md)
contains extractions from the current sources. It distinguishes proofs for
samplers, NTT and API helpers from outstanding obligations for the complete API.
