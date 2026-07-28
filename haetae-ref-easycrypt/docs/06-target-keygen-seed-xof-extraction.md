# Target Mode-2 Key-Generation Seed-XOF Extraction

## Scope and reachability

This extraction selects one exact target procedure:

```text
haetae-ref-jasmin/jasmin/keypair.jazz:974-1021
_kp_expand_seedbuf
```

The procedure is statically reachable from
`crypto_sign_keypair_internal_mode2_jazz` through `_keypair_full_m23`. The
source loop absorbs 32 seed bytes, finalizes with rate 136 and domain `0x1f`,
applies Keccak-f[1600], and writes the first 128 output bytes. The dedicated
extraction records that implementation boundary; the authored refinement
described below proves its exact byte meaning in the unified target.

## Regeneration

From the project directory:

```sh
./scripts/regenerate-keygen-seed-xof-extract.sh
```

The effective extraction command is:

```sh
jasmin2ec --array-model=barray \
  --output-array=<temporary-directory> \
  -o <temporary-directory>/KeygenSeedXofTarget.ec \
  -f _kp_expand_seedbuf \
  ../haetae-ref-jasmin/jasmin/keypair.jazz
```

The generated file set must exactly match
`manifests/keygen-seed-xof-extract-files.txt`. The procedure closure must
exactly match `manifests/keygen-seed-xof-procedures.txt`: the selected
procedure, `_keccak_init_state`, `_keccak_finalize`, `_keccakf1600`, and eleven
Keccak round helpers. Broad includes in `keypair.jazz` cause additional array
theories to be emitted, but do not add procedures to this closure.

Generated files under `easycrypt/extract/keygen-seed-xof/` must not be edited
manually.

## Drift and compilation checks

```sh
./scripts/check-keygen-seed-xof-extract-drift.sh
./scripts/verify-keygen-seed-xof-extract.sh
```

The drift checker regenerates from the pinned source and compares all 20 files
byte-for-byte while also checking the 15-procedure closure. The verifier
compiles all 20 theories using `easycrypt compile -no-eco` and rejects
`admit`, `abort`, or axiom declarations. Its summary is written to
`logs/keygen-seed-xof-extract-summary.txt`.

## Exact authored refinement

The reusable proof is attached to the copy of `_kp_expand_seedbuf` in the
unified sampler-caller target:

```text
easycrypt/spec/KeygenSeedXofSpec.ec
easycrypt/refinement/TargetKeygenSeedXof.ec
KeygenSamplerCallersTarget.M._kp_expand_seedbuf
```

`KeygenSeedXofSpec.output_matches` compares all 128 returned bytes with the
pinned `HAETAE_FIPS202.shake256` model applied to exactly the 32 input bytes.
The model and bridge lemmas identify the target state as the one-block
SHAKE256 padding state: the domain byte `0x1f` is at byte 32 and the final rate
bit `0x80` is at byte 135. The proof then uses the checked 24-round
Keccak-f[1600] bridge and identifies the target's 128-byte output loop with the
first 128 bytes of the 136-byte SHAKE256 rate block.

The main theorem is:

```text
kp_expand_seedbuf_correct
```

It is a Hoare theorem about the actual unified generated procedure, with
precondition `outp = out0 /\ seedp = seed0` and postcondition
`KeygenSeedXofSpec.output_matches res seed0`. Three named Hoare corollaries
expose the slices consumed later in key generation:

| Corollary | Output interval | Predicate |
| --- | --- | --- |
| `kp_expand_seedbuf_uniform_slice_correct` | `[0, 32)` (bytes 0 through 31) | `uniform_seed_slice_matches` |
| `kp_expand_seedbuf_eta_slice_correct` | `[32, 96)` (bytes 32 through 95) | `eta_seed_slice_matches` |
| `kp_expand_seedbuf_key_slice_correct` | `[96, 128)` (bytes 96 through 127) | `key_seed_slice_matches` |

Run the unified authored proof gate with:

```sh
./scripts/verify-keygen-sampler-callers-proof.sh
```

The dedicated 20-file, 15-procedure extraction remains the narrow provenance
gate for `KeygenSeedXofTarget.M._kp_expand_seedbuf`; the authored Hoare theorems
use the unified generated module so that the seed proof and sampler proofs
share one procedure namespace. A separate 25-file, 31-procedure extraction
gate checks that unified module; see
[`09-target-keygen-sampler-callers-extraction.md`](09-target-keygen-sampler-callers-extraction.md).

## Remaining boundary

The exact standalone seed-XOF theorem does not by itself prove source-pointer
safety, identify the three byte slices with paper/security-model names, or
show that the actual parent passes this returned array to every sampler and
packer. The actual deterministic mode-2 parent is now reproducibly extracted
as a separate 32-file, 56-procedure closure; see
[`12-target-keygen-mode2-parent-extraction.md`](12-target-keygen-mode2-parent-extraction.md).
The separate proof-only parent-module prefix now connects the exact expanded
array and named slices to the matrix, vector, and first-attempt eta sampler
calls, with probability-one termination under its explicit deterministic
certificate bundle; see
[`13-target-keygen-mode2-parent-refinement.md`](13-target-keygen-mode2-parent-refinement.md).
It is not `_keypair_full_m23` and proves neither packing nor the outer retry and
downstream dataflow. Those full-parent, memory-relation, distributional, and
end-to-end composition obligations remain before this leaf can close
`GAP-PK-FIPS202` or a random-oracle transcript claim.
