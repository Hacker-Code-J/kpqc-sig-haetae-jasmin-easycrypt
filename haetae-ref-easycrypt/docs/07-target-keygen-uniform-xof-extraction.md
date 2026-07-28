# Target Mode-2 Key-Generation Uniform-XOF Leaf Extraction

## Scope

This extraction selects the two concrete SHAKE128 rejection-sampler leaves
reached by mode-2 key generation:

```text
haetae-ref-jasmin/jasmin/keypair.jazz:554-638
_kp_poly_uniform_at_seedbuf_8192

haetae-ref-jasmin/jasmin/keypair.jazz:640-724
_kp_poly_uniform_at_seedbuf_2048
```

They appear in the generated module as
`KeygenUniformXofTarget.M._kp_poly_uniform_at_seedbuf_8192` at lines 813-893
and `KeygenUniformXofTarget.M._kp_poly_uniform_at_seedbuf_2048` at lines
894-976. The selection also brings in the reachable Keccak-f[1600],
SHAKE128-squeeze, seed initialization, and rejection-consumer procedures.

This is deliberately a two-leaf extraction. `jasmin2ec` follows callees, not
callers, so the matrix/vector expansion loops and their mode-2 layout are not
inside the generated module.

## Mode-2 reachability and inputs

The internal and randomized mode-2 entries call
`_keypair_full_m23(k = 2, m = 3)` at `keypair.jazz:1317` and `:1376`,
respectively. The shared body is defined at `keypair.jazz:1123-1215` and
reaches the selected leaves through:

```text
_kp_polymatkm_expand_matA (keypair.jazz:841-892)
  -> _kp_poly_uniform_at_seedbuf_8192

_kp_polyveck_expand_vecA (keypair.jazz:894-935)
  -> _kp_poly_uniform_at_seedbuf_2048
```

The two caller loops set `seedoff = 0`, so the leaves read `seedbuf[0:32]`.
The source names that slice `rhop` at `keypair.jazz:1209`; it is the expanded
rho-prime value, not the original external key-generation seed.

For mode 2, the source-level caller schedule is:

| Role | Buffer bases | Nonces | Appended little-endian bytes |
| --- | --- | --- | --- |
| Matrix `Agen`/`A0`, 2 by 3 | 0, 256, 512, 768, 1024, 1280 | 0, 1, 2, 256, 257, 258 | `00 00`, `01 00`, `02 00`, `00 01`, `01 01`, `02 01` |
| Vector `agen`/`a`, length 2 | 0, 256 | 515, 516 | `03 02`, `04 02` |

These dimensions, bases, and nonces are caller reachability facts. They are
not behaviors proved by this leaf-only generated module.

## Stream and rejection behavior visible in the source

For each leaf invocation, the source constructs the stream corresponding to:

```text
SHAKE128(rho' || little_endian_16(nonce))
```

`__kp_shake128_init_seedbuf` (`keypair.jazz:73-125`) absorbs 32 seed bytes and
the low two nonce bytes. It writes SHAKE domain byte `0x1f` at byte 34 and the
final padding bit at byte 167, so `_keccak_finalize` is not in the reachable
closure. Four initial 168-byte squeezes produce 672 bytes; further 168-byte
blocks are squeezed when rejection requires them.

Both consumers parse little-endian 16-bit candidates, accept a candidate only
when it is below `HAETAE_Q = 64513`, and continue until 256 coefficients have
been written. The 8192-memory leaf calls `__poly_uniform_consume` from
`polynomial_sampler.jinc:268-329`; the 2048-memory leaf calls the parallel
local `__kp_poly_uniform_consume_2048` at `keypair.jazz:320-374`. Their memory
types and instrumentation differ, so each needs an explicit refinement result.

These are inspected source facts. Reproducible extraction alone does not turn
them into a functional-correctness or distribution theorem.

## Regeneration and exact inventories

From the project directory:

```sh
./scripts/regenerate-keygen-uniform-xof-extract.sh
```

The effective extraction command is:

```sh
jasmin2ec --array-model=barray \
  --output-array=<temporary-directory> \
  -o <temporary-directory>/KeygenUniformXofTarget.ec \
  -f _kp_poly_uniform_at_seedbuf_8192 \
  -f _kp_poly_uniform_at_seedbuf_2048 \
  ../haetae-ref-jasmin/jasmin/keypair.jazz
```

Generation must produce exactly the 23 theories listed in
`manifests/keygen-uniform-xof-extract-files.txt` and the 19 procedures listed
in `manifests/keygen-uniform-xof-procedures.txt`. Only after both inventories
match are files copied into `easycrypt/extract/keygen-uniform-xof/`. Generated
files must not be edited manually.

## Drift and compilation checks

```sh
./scripts/check-keygen-uniform-xof-extract-drift.sh
./scripts/verify-keygen-uniform-xof-extract.sh
```

The drift checker regenerates in a temporary directory, checks both exact
inventories, and compares all 23 theories byte-for-byte. The verifier compiles
the manifest in order with `easycrypt compile -no-eco`, prevents EasyCrypt
from consuming the manifest loop's standard input, rejects `admit`/`abort`
proof commands and axiom declarations, and records results in
`logs/keygen-uniform-xof-extract-summary.txt`.

## Claim boundary and next step

A passing gate proves that the two named EasyCrypt procedures and their
17-procedure dependency closure are reproducibly generated from the pinned
target source and accepted by EasyCrypt without cache reuse. It does not prove:

- Keccak-f or SHAKE128 byte-level correctness;
- uniformity, independence, rejection termination, or losslessness;
- coefficient or memory bounds;
- caller-loop dimensions, nonce scheduling, buffer layout, or composition with
  `_kp_expand_seedbuf`;
- correspondence to the random-oracle interface in the security proof.

The SHAKE256 eta-sampler leaf is now reproducibly extracted separately; see
[`08-target-keygen-eta-xof-extraction.md`](08-target-keygen-eta-xof-extraction.md).
The shared parameterized caller layer and `_kp_expand_seedbuf` are now
reproducibly extracted in one 25-file, 31-procedure module; see
[`09-target-keygen-sampler-callers-extraction.md`](09-target-keygen-sampler-callers-extraction.md).
Follow-on refinement gives the finite rejection consumers accepted-prefix and
destination-frame contracts and connects both enclosing leaves to exact
consecutive SHAKE128 blocks. The terminating-leaf Hoare theorems expose the
final 256 accepted values, their strict `< 64513` bound, and the destination
frame; `uniform_consume2048_ll` and `uniform_consume8192_ll` separately prove
unconditional termination of the two bounded generated consumers. The
separate `uniform2048_leaf_progress_ll` and
`uniform8192_leaf_progress_ll` pHoare theorems prove probability-one
termination of the two actual leaves under exact seed/base/capacity/slice
preconditions plus an explicit deterministic
`uniform_progress_prefix seed seedoff nonce limit` certificate. Its endpoint
contains at least 256 accepted candidates, and every still-incomplete full
block prefix from block four to that endpoint must make strict progress. The
generated matrix and vector callers retain per-cell finite-stream witnesses.
See
[`11-target-keygen-sampler-consumers.md`](11-target-keygen-sampler-consumers.md).

The actual deterministic mode-2 parent is also available as a separate
32-file, 56-procedure extraction; see
[`12-target-keygen-mode2-parent-extraction.md`](12-target-keygen-mode2-parent-extraction.md).
That gate does not itself semantically compose the leaf results. The separate
proof-only parent-module prefix connects the exact expanded seed to all six
matrix and two vector calls and lifts their explicit endpoint maps through both
callers; see
[`13-target-keygen-mode2-parent-refinement.md`](13-target-keygen-mode2-parent-refinement.md).
Its probability-one result remains certificate-conditioned. Universal
progress-certificate existence, distributions, source-pointer safety, and
composition through the actual `_keypair_full_m23` retry/downstream control
remain open. Bounded-consumer losslessness alone still does not imply that an
enclosing rejection loop collects 256 accepted candidates.
