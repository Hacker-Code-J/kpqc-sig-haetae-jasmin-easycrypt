# Toolchain and Baseline Reproduction

## Pinned inputs

From the project directory, verify the specification, target Jasmin files, and
KAT baselines:

```sh
./scripts/check-sources.sh
```

This executes `sha256sum -c manifests/sources.sha256`. A mismatch means the
existing proof status does not apply to the current file and must stop the
verification pipeline.

The repository base commit and tool binaries are recorded in
`../manifests/toolchain.md`.

## Existing baseline commands

Run all three existing baselines sequentially:

```sh
./scripts/verify-baselines.sh
```

The wrapper also recompiles every managed security-proof target with
`easycrypt compile -no-eco`; this closes the cache-freshness gap in the
repository's existing security gate.

Equivalent individual commands from the repository root are:

```sh
make -C haetae-ref-jasmin test

cd haetae-security
sh provable-security/verify-provable-security.sh

cd ../haetae-ref-easycrypt
./scripts/verify-security-fresh.sh

cd ../haetae-ntt-verify/easycrypt-ct
./scripts/check-full-functional-correctness.sh
```

The project wrapper uses `make -B` for the Jasmin baseline and additionally
rejects any `Invalid on ...` message. This output scan is necessary because the
current smoke harness can return zero after printing a validation failure.

The security and NTT scripts maintain their own summaries and per-target logs
under their existing workspaces. The current results are transcribed, with
scope caveats, into `proof-status.md`.

## Freshness policy

- EasyCrypt project proofs must be compiled with `-no-eco`.
- Generated extraction must eventually be regenerated into a temporary
  directory and compared byte-for-byte with tracked `easycrypt/extract/` files.
- A verification report must include tool versions or binary hashes, source
  hashes, exit status, checked target count, proof-hole scan, and axiom boundary.
- Changing a pinned input invalidates downstream status until affected checks
  and proofs are rerun.

## Current limitation

These baseline commands establish the state of existing artifacts only. The
security proof currently has documented paper-correspondence gaps, and the NTT
proof targets a different Jasmin source. Neither result is yet an end-to-end
proof for `haetae-ref-jasmin`.
