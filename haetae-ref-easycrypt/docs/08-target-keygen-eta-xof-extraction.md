# Target Mode-2 Key-Generation Eta-XOF Leaf Extraction

## Scope

This extraction selects the concrete SHAKE256 eta-sampler leaf reached by
mode-2 key generation:

```text
haetae-ref-jasmin/jasmin/keypair.jazz:781-839
_kp_poly_uniform_eta_at_seedbuf_2048
```

It appears as
`KeygenEtaXofTarget.M._kp_poly_uniform_eta_at_seedbuf_2048` at generated lines
871-929. The selection brings in the reachable Keccak-f[1600], SHAKE256
squeeze, centered-mod-3, seed initialization, and rejection-consumer
procedures.

This is deliberately a leaf-only extraction. `jasmin2ec` follows callees, not
callers, so `_kp_polyvec_expand_eta`, its mode-2 layout, and the key-generation
retry loop are not inside the generated module. The generic eta leaf and
consumer are also absent because this path reaches only the 2048-word variant.

## Mode-2 reachability and seed slice

The internal and randomized mode-2 entries call
`_keypair_full_m23(k = 2, m = 3)` at `keypair.jazz:1317` and `:1376`. The
shared body is defined at `keypair.jazz:1123-1215`. On each key-generation
attempt it calls `_kp_polyvec_expand_eta` (`:937-972`) twice, at lines 1168 and
1171, and that caller reaches the selected leaf.

The caller fixes `seedoff = 32`, while `__kp_shake256_init_seedbuf` reads 64
bytes. The concrete slice is therefore `seedbuf[32:96]`. The reference C
implementation calls this slice `sigma`; Figure 8 of the specification calls
the corresponding input to `expandS` `seedsk`. It is not the rho-prime slice.
Connecting these names and the upstream `_kp_expand_seedbuf` output is a later
composition theorem, not an extraction result.

## Mode-2 retry and nonce schedule

For retry index `j`, starting from `j = 0`, the source-level schedule is:

| Output before later key-generation adjustments | Buffer bases | Nonces |
| --- | --- | --- |
| `s1` / `sgen`, three polynomials | 0, 256, 512 | `5j`, `5j + 1`, `5j + 2` |
| raw `s2` / `egen`, two polynomials | 0, 256 | `5j + 3`, `5j + 4` |

The shared body starts `counter = 0` and advances it by `m + k = 5` after
each pair of caller invocations. Only the low 16 bits of each nonce are
absorbed, so the transcript schedule is modulo `2^16`. The reference C counter
is a `uint16_t`; the Jasmin counter is a `u64` whose upper bits do not affect
this leaf. `expand_eta_stream` now accounts for the generated caller's word
nonce and the leaf's low-16-bit absorption for every slot. The authored
proof-only `CheckedMode2EtaPair.expand` wrapper checks two calls with nonce
slots `start` through `start + 4` and returns the next nonce word `start + 5`.
It does not establish that the actual `_keypair_full_m23` executes this wrapper
or its retry loop. The sampled raw `s2` is later adjusted to `egen - b0`, which
is also outside this proof.

## Stream and centered-trit behavior visible in the source

For each invocation, the source constructs the stream corresponding to:

```text
SHAKE256(seedsk[64 bytes] || little_endian_16(nonce))
```

`__kp_shake256_init_seedbuf` (`keypair.jazz:127-179`) absorbs the 64-byte seed
slice and the low two nonce bytes. It places SHAKE domain byte `0x1f` at byte
66 and the final padding bit at byte 135. `_keccak_finalize` is therefore not
in the reachable closure. `__poly_sample_squeeze256`
(`polynomial_sampler.jinc:40-77`) emits one 136-byte block initially and more
136-byte blocks until 256 coefficients have been written.

The local consumer (`keypair.jazz:376-471`) accepts a byte only when it is
below `243 = 3^5`. Each accepted byte yields up to five centered base-3 digits
through the helpers at `polynomial_sampler.jinc:187-266`. The word values are
`0`, `1`, and `0xffffffff`, with the last representing signed `-1`; bytes
243-255 are rejected completely. The final accepted byte may contribute fewer
than five coefficients when the output counter reaches 256.

These are inspected source facts. The extraction does not prove the base-3
identities, signed representation, uniform distribution, independence, or
almost-sure termination.

## Regeneration and exact inventories

From the project directory:

```sh
./scripts/regenerate-keygen-eta-xof-extract.sh
```

The effective extraction command is:

```sh
jasmin2ec --array-model=barray \
  --output-array=<temporary-directory> \
  -o <temporary-directory>/KeygenEtaXofTarget.ec \
  -f _kp_poly_uniform_eta_at_seedbuf_2048 \
  ../haetae-ref-jasmin/jasmin/keypair.jazz
```

Generation must produce exactly the 21 theories listed in
`manifests/keygen-eta-xof-extract-files.txt` and the 20 procedures listed in
`manifests/keygen-eta-xof-procedures.txt`. Only after both inventories match
are files copied into `easycrypt/extract/keygen-eta-xof/`. Generated files must
not be edited manually.

## Drift and compilation checks

```sh
./scripts/check-keygen-eta-xof-extract-drift.sh
./scripts/verify-keygen-eta-xof-extract.sh
```

The drift checker regenerates in a temporary directory, checks both exact
inventories, and compares all 21 theories byte-for-byte. The verifier compiles
the manifest in order with `easycrypt compile -no-eco`, prevents EasyCrypt
from consuming the manifest loop's standard input, rejects `admit`/`abort`
proof commands and axiom declarations, and records results in
`logs/keygen-eta-xof-extract-summary.txt`.

## Claim boundary and next step

A passing gate proves that the named EasyCrypt procedure and its 19-procedure
callee closure are reproducibly generated from the pinned target source and
accepted by EasyCrypt without cache reuse. It does not prove:

- Keccak-f or SHAKE256 byte-level correctness;
- the centered base-3 identities or signed-word representation;
- uniformity, independence, rejection termination, or losslessness;
- coefficient or memory bounds;
- caller-level seed slicing, dimensions, buffer bases, retry behavior, nonce
  scheduling, or composition with `_kp_expand_seedbuf`;
- correspondence to `expandS` or the random-oracle interface in the security
  proof.

The parameterized sampler caller layer and `_kp_expand_seedbuf` are now
reproducibly extracted in one 25-file, 31-procedure module; see
[`09-target-keygen-sampler-callers-extraction.md`](09-target-keygen-sampler-callers-extraction.md).
Follow-on refinement proves exact padding, consecutive SHAKE256 blocks, the
capped centered-trit decoder through the actual eta leaf, and per-slot exact
finite-stream semantics through the actual generated eta vector caller. An
authored proof-only wrapper additionally checks the mode-2 count-three/count-two
pair and five-slot nonce split; see
[`11-target-keygen-sampler-consumers.md`](11-target-keygen-sampler-consumers.md).
`eta_consume2048_ll` proves unconditional termination of the finite generated
consumer. Under the exact seed/base/capacity/slice preconditions and an explicit
`eta_progress_prefix seed seedoff nonce limit` certificate,
`eta2048_leaf_progress_ll` proves probability-one termination of the actual
generated eta leaf. The certificate states a finite endpoint with 256 decoded
values and strict progress at every still-incomplete block prefix before that
endpoint; the development does not prove a certificate for every input.
The actual deterministic mode-2 parent is also available as a separate
32-file, 56-procedure extraction; see
[`12-target-keygen-mode2-parent-extraction.md`](12-target-keygen-mode2-parent-extraction.md).
The separate proof-only parent-module prefix now connects the exact
`seedbuf[32:96]` identity to the three-slot and two-slot first-attempt eta
calls. Their caller-level and whole-prefix probability-one results require the
five explicit endpoint certificates; see
[`13-target-keygen-mode2-parent-refinement.md`](13-target-keygen-mode2-parent-refinement.md).
Universal certificate existence, distributions, source-pointer safety, later
retry attempts, and semantic composition through the actual
`_keypair_full_m23` retry/downstream control remain open.
