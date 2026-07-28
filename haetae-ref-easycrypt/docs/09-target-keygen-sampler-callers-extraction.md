# Target Key-Generation Sampler-Caller Extraction

## Scope

This extraction selects the seed expansion and the three parameterized callers
that assemble the sampler leaves:

| Procedure | Target source | Generated range |
| --- | --- | --- |
| `_kp_polymatkm_expand_matA` | `keypair.jazz:841-892` | `KeygenSamplerCallersTarget.ec:1302-1348` |
| `_kp_polyveck_expand_vecA` | `keypair.jazz:894-935` | `KeygenSamplerCallersTarget.ec:1349-1387` |
| `_kp_polyvec_expand_eta` | `keypair.jazz:937-972` | `KeygenSamplerCallersTarget.ec:1388-1420` |
| `_kp_expand_seedbuf` | `keypair.jazz:974-1021` | `KeygenSamplerCallersTarget.ec:1421-1469` |

The generated module also contains the two uniform leaves, the eta leaf, and
the shared SHAKE128, SHAKE256, rejection, centered-trit, finalization, and
Keccak-f dependencies. It deliberately excludes `_keypair_full_m23`, generic
sampler siblings, and standalone FIPS202 wrappers.

## Parameterized behavior inside the extraction

The three caller formulas are visible in the generated procedures. The table
uses their natural-number form; later refinement must supply the stated
no-wrap preconditions for the underlying `W64` arithmetic.

| Caller | Loop | Seed offset | Output base | Leaf nonce |
| --- | --- | --- | --- | --- |
| Matrix `Agen`/`A0` | `i < rows`, `j < cols` | 0 | `(i * cols + j) * 256` | `(i << 8) + j` |
| Vector `agen`/`a` | `i < k` | 0 | `i * 256` | `(k << 8) + m + i` |
| Eta vector | `i < count` | 32 | `i * 256` | `nonce0 + i` |

Thus the matrix and `agen` callers pass `seedbuf[0:32]` to their SHAKE128
leaves, while the eta caller passes `seedbuf[32:96]` to its SHAKE256 leaf. The
offsets and formulas are now part of the extraction. Although
`_kp_expand_seedbuf` is in the same generated module, extraction alone does not
prove that the actual parent passes its result to these callers or identify the
slices as paper `seedA`/rho-prime and `seedsk`/sigma. The separate proof-only
parent-module prefix now closes the first of those cuts for the actual
module-qualified seed expansion, uniform callers, and first eta attempt; see
[`13-target-keygen-mode2-parent-refinement.md`](13-target-keygen-mode2-parent-refinement.md).
It does not establish the paper-name identification or full-parent control.

When `i, j < 256`, including every mode-2 invocation, the matrix numeric nonce
`(i << 8) + j` is absorbed little-endian by its leaf as bytes `j, i`, matching
the reference `SHAKE128(rho || j || i)` ordering.

## Mode-2 instantiation outside the extraction

The internal and randomized mode-2 entries instantiate
`_keypair_full_m23(k = 2, m = 3)` at `keypair.jazz:1317` and `:1376`. The
shared body is defined at `keypair.jazz:1123-1215` and calls the selected
procedures at lines 1161, 1162, 1168, and 1171. Because that body is not
selected, the following remain source reachability facts rather than generated
composite behavior:

| Role | Mode-2 bases | Mode-2 nonces |
| --- | --- | --- |
| Matrix `Agen`/`A0`, 2 by 3 | 0, 256, 512, 768, 1024, 1280 | 0, 1, 2, 256, 257, 258 |
| Vector `agen`/`a`, length 2 | 0, 256 | 515, 516 |
| Retry `j` raw `s1`/`sgen`, length 3 | 0, 256, 512 | `5j`, `5j + 1`, `5j + 2` |
| Retry `j` raw `s2`/`egen`, length 2 | 0, 256 | `5j + 3`, `5j + 4` |

The full body also supplies one expanded seed buffer to all callers, pairs the
two eta invocations, advances the retry counter by five, applies the singular
value rejection, and later changes raw `egen` to `egen - b0`. Those operations
are not represented by this generated module. A separate extraction now
contains the actual deterministic mode-2 parent and this control flow; see
[`12-target-keygen-mode2-parent-extraction.md`](12-target-keygen-mode2-parent-extraction.md).
That gate is extraction-and-compilation evidence only. A separate semantic
theorem covers an authored proof-only prefix that calls procedures from the
actual parent module with these dimensions and first-attempt nonces. It stops
before `_kp_m23_matrix` and is not a theorem about `_keypair_full_m23`.

Two authored proof-only wrappers exercise actual procedures from this
extraction. `CheckedMode2UniformPair.expand` calls the matrix and vector uniform
callers with dimensions `(2, 3)` and one shared raw `BArray128` seed array.
`CheckedMode2EtaPair.expand` mirrors the two eta invocations by calling the
actual extracted `_kp_polyvec_expand_eta` twice. Neither wrapper turns
`_keypair_full_m23` into generated composite behavior; that source procedure
remains absent from this extraction. The later
`CheckedMode2ParentSamplerPrefix.run` observer additionally composes exact
parent-module seed expansion with both uniform callers and the first eta pair,
but remains proof-only and leaves retry/downstream behavior open.

## Memory and arithmetic proof obligations

The extracted value-array procedures type-check. The authored functional-array
proof supplies capacity preconditions and aggregate frames, while source-level
refinement still needs pointer and aliasing obligations:

- matrix arithmetic must not wrap and must satisfy `rows * cols <= 32`, which
  keeps every `base + 255` below the 8192-word output capacity;
- `agen` requires `k <= 8`, and eta expansion requires `count <= 8`, keeping
  every write below the 2048-word output capacity;
- nonce shifts and additions must obey their intended natural-number formulas,
  and the leafs' low-16-bit absorption must be related to reference `uint16_t`
  semantics;
- each 256-word output region must be disjoint and all unused regions must be
  preserved in the generated value-array model; and
- the source output buffers, seed buffer, and leaf scratch storage must be
  separated when relating pointer memory to EasyCrypt value arrays.

Mode 2 satisfies the numeric capacity bounds with a 2-by-3 matrix, `agen`
length 2, `sgen` length 3, and raw `egen` length 2. The pure schedule theory
proves the integer capacity and disjointness facts, relevant `W64` encodings,
and mode-2 base/nonce schedules. Separate Hoare theorems now give both generated
uniform callers exact per-cell finite SHAKE128 streams, strict coefficient
ranges, and aggregate byte frames, and give the eta caller exact finite-stream,
centered-range, and functional-array frame contracts. Source-pointer
separation and source memory safety remain open.

## Regeneration and exact inventories

From the project directory:

```sh
./scripts/regenerate-keygen-sampler-callers-extract.sh
```

The effective extraction command is:

```sh
jasmin2ec --array-model=barray \
  --output-array=<temporary-directory> \
  -o <temporary-directory>/KeygenSamplerCallersTarget.ec \
  -f _kp_expand_seedbuf \
  -f _kp_polymatkm_expand_matA \
  -f _kp_polyveck_expand_vecA \
  -f _kp_polyvec_expand_eta \
  ../haetae-ref-jasmin/jasmin/keypair.jazz
```

Generation must produce exactly the 25 theories listed in
`manifests/keygen-sampler-callers-extract-files.txt` and the 31 procedures in
`manifests/keygen-sampler-callers-procedures.txt`. Only after both inventories
match are files copied into `easycrypt/extract/keygen-sampler-callers/`.
Generated files must not be edited manually.

## Drift and compilation checks

```sh
./scripts/check-keygen-sampler-callers-extract-drift.sh
./scripts/verify-keygen-sampler-callers-extract.sh
```

The drift checker regenerates in a temporary directory, checks both exact
inventories, and compares all 25 theories byte-for-byte. The verifier compiles
the manifest in order with `easycrypt compile -no-eco`, isolates EasyCrypt
from the manifest loop's standard input, rejects `admit`/`abort` proof commands
and axiom declarations, and records results in
`logs/keygen-sampler-callers-extract-summary.txt`.

## Claim boundary and follow-on proof

A passing gate proves that the four selected procedures and their
27-procedure callee closure are reproducibly generated from the pinned target
source and accepted by EasyCrypt without cache reuse. It does not prove:

- the functional correctness or distribution of any sampler leaf;
- caller loop invariants, termination, arithmetic bounds, or memory frames;
- composition of `_kp_expand_seedbuf` with the sampler callers or paper seed
  names;
- mode-2 parameter instantiation, paired eta calls, retry-counter behavior,
  singular-value rejection, or the later `egen - b0` adjustment;
- correspondence to paper `expandA`, `expandS`, or the security model.

The first authored follow-on proof is now available:

```sh
./scripts/verify-keygen-sampler-callers-proof.sh
```

Its proof manifest has 13 entries: the unified generated target, six authored
specifications, and six authored refinements. The gate compiles each entry with
`-no-eco` and scans the authored files for proof holes and axiom declarations.

It proves that the three generated callers are relationally equivalent to
authored integer-counter schedule programs while both sides call the same
extracted leaves. `kp_expand_seedbuf_correct` separately proves that the fourth
selected procedure returns exactly `SHAKE256(seed, 128)`; its named corollaries
identify byte intervals `[0, 32)`, `[32, 96)`, and `[96, 128)` with the
corresponding SHAKE256 output slices. Separate pure lemmas prove the `W64`
schedule encodings,
generic capacity and region-disjointness arithmetic, and mode-2 bases, nonces,
and conditional low-16-bit facts. The same gate proves exact uniform and eta
leaf streams; exact per-cell finite SHAKE128, range, and aggregate byte-frame
contracts through both actual uniform callers; and the actual eta vector
caller's per-slot finite SHAKE256 decoder contract, centered range, and
outside-vector frame. It also proves unconditional losslessness of the bounded
uniform/eta consumers and probability-one termination of both actual uniform
leaves and the actual eta leaf under their explicit deterministic
`uniform_progress_prefix` or `eta_progress_prefix` certificates and exact
seed/base/capacity/slice bounds. No universal certificate, caller totality, or
distribution follows from that sampler proof gate alone. The separate
parent-module prefix proof establishes totality only for the exact mode-2
matrix, vector, first-attempt eta segments, and composed observer under their
bundled endpoint maps. `caller_uniform_seed_input_prefix` proves that the
uniform SHAKE128 input prefix is the same raw seed array's bytes `0..31`, while
the two mode-2 nonce-tail lemmas prove matrix tails `[col, row]` and vector tails
`[3 + slot, 2]`. The authored proof-only uniform wrapper calls the actual matrix
and vector procedures with dimensions `(2, 3)` over that same raw array. The
eta wrapper checks counts three and two, five consecutive nonce slots, and a
nonce-word advance of five. See
[`10-target-keygen-sampler-callers-refinement.md`](10-target-keygen-sampler-callers-refinement.md)
for the schedule theorem map and
[`11-target-keygen-sampler-consumers.md`](11-target-keygen-sampler-consumers.md)
for the consumer theorem map.

The standalone seed theorem does not by itself establish that either raw caller
input equals the returned array from `_kp_expand_seedbuf`. The separate
proof-only parent-module prefix closes that cut for its first-attempt calls,
but does not identify paper rho/`seedA` or sigma/`seedsk` and does not prove
that `_keypair_full_m23` follows the observer. Source-pointer memory safety,
unconditional whole-leaf/caller losslessness, universal progress certificates
and distributions, actual retry control, singular-value rejection, and the
later `egen - b0` adjustment remain outside the proof.
