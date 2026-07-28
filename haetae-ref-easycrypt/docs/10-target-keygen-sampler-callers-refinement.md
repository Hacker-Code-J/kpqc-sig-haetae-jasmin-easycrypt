# Target Key-Generation Sampler-Caller Refinement

## Verified claim

This proof has two distinct layers. Three pRHL equivalences relate the generated
caller loops to authored integer schedule programs while both sides invoke the
same extracted leaves. Separate Hoare theorems lift exact finite SHAKE decoder
semantics, coefficient ranges, and aggregate functional-array frames through
both actual uniform callers and the actual eta vector caller.

The schedule equivalences alone do not assign SHAKE or distribution semantics
to a leaf. The Hoare theorems provide deterministic finite-stream partial
correctness, not termination, independence, or a probabilistic distribution.

Separate Hoare theorems give the actual generated eta vector caller
centered-range, outside-vector frame, and exact per-slot finite SHAKE256 decoder
contracts. These semantic theorems are distinct from the narrower three pRHL
schedule equivalences.

The shared sampler-consumer gate also gives both actual uniform leaves exact
deterministic SHAKE128-to-decoder continuity through their complete rejection
loops. Conditional on an in-bounds 32-byte seed slice, exported Hoare theorems
relate a terminating leaf's 256 stored coefficients to an accepted prefix of a
finite exact SHAKE128 byte sequence. This is separate from the caller-schedule
pRHL claim and remains a partial-correctness result.

The separate pHoare theorems `uniform2048_leaf_progress_ll` and
`uniform8192_leaf_progress_ll` prove probability-one termination of those two
actual generated leaves under exact seed identity, seed-offset, nonce,
destination-base, destination-capacity, and 32-byte seed-slice premises plus
`uniform_progress_prefix seed seedoff nonce limit`. This deterministic
certificate supplies an endpoint with at least 256 accepted candidates and
requires strict accepted-count progress at every still-incomplete full-block
prefix from block four to that endpoint. The proofs do not construct a
certificate for every input or lift leaf totality through either caller.

`expand_vecA_stream_correct` and `expand_matA_stream_correct` now lift those
leaf results through the actual generated uniform vector and matrix callers.
Every selected slot or cell has its own `blocks >= 4` and `pairs` witnesses
for exactly 256 accepted values, all below 64513. The combined postconditions
also preserve every byte outside the complete selected output prefix. The
vector theorem requires `k <= 8`; the matrix theorem requires
`rows * cols <= 32`.

The same gate now gives the generated eta leaf exact deterministic
SHAKE256-to-decoder continuity. Under an in-bounds 64-byte seed slice and the
theorem's destination-capacity bound,
`eta2048_leaf_stream` relates a terminating leaf to successive 136-byte
offset-zero overwrite blocks from the exact padded seed/nonce state. The
consumer rejects bytes at least 243, expands each accepted byte into five
centered trits, and caps the stored prefix at 256 even when the cap falls in the
middle of those five trits. This is also a separate finite Hoare
partial-correctness theorem, not a caller-schedule or termination result.

Eta termination is handled by a distinct pHoare theorem.
`eta2048_leaf_progress_ll` proves probability-one termination of the actual
generated eta leaf under the exact seed, seed-offset, nonce, destination-base,
destination-capacity, and 64-byte seed-slice bounds plus
`eta_progress_prefix seed seedoff nonce limit`. That predicate is an explicit
deterministic certificate: its finite endpoint decodes 256 values, and every
still-incomplete block prefix from block one to that endpoint makes strict
progress. The proof does not construct such a certificate for every input and
does not imply a centered-trit distribution.

`expand_eta_stream` similarly lifts the eta leaf result through the actual generated
`_kp_polyvec_expand_eta`. For every selected slot, `eta_vector_stream8192`
provides a per-slot finite SHAKE256 prefix witness at seed offset 32 and
nonce `start + slot`, with exactly 256 decoded values equal to that slot's
stored signed prefix. `expand_eta_stream_correct` combines the stream theorem
with the existing centered-range and outside-vector frame result.

The authored proof-only `CheckedMode2UniformPair.expand` wrapper invokes the
actual matrix and vector uniform callers with dimensions `(2, 3)` over one raw
`BArray128` seed array. `checked_mode2_uniform_pair_correct` composes their
exact stream, range, and aggregate byte-frame contracts. Named input lemmas
prove that both callers use raw seed bytes `0..31` at offset zero and the exact
mode-2 little-endian nonce tails `[col, row]` and `[3 + slot, 2]`.

The authored proof-only `CheckedMode2EtaPair.expand` wrapper invokes the actual
generated eta caller twice with counts three and two over one input seed array.
`checked_mode2_eta_pair_correct` composes both exact vector contracts and the
five-step nonce-word advance. The wrapper is not `_keypair_full_m23` and does
not prove its surrounding retry control.

The same proof gate now checks the extracted `_kp_expand_seedbuf` directly.
The Hoare theorem `kp_expand_seedbuf_correct` proves that, on return, all 128
output bytes equal the first 128 SHAKE256 bytes of the 32-byte input seed.
`kp_expand_seedbuf_uniform_slice_correct`,
`kp_expand_seedbuf_eta_slice_correct`, and
`kp_expand_seedbuf_key_slice_correct` specialize that result to output ranges
`0..31`, `32..95`, and `96..127`. These remain standalone results in this
proof surface. The separate proof-only parent-module prefix now connects the
actual module-qualified seed-expansion result to the raw arrays used by both
uniform callers and the first eta pair; it does not prove
`_keypair_full_m23`.

## Checked artifacts

| Role | Artifact |
| --- | --- |
| Generated target | `easycrypt/extract/keygen-sampler-callers/KeygenSamplerCallersTarget.ec` |
| Authored schedule, arithmetic, uniform-caller, and eta-vector stream theory | `easycrypt/spec/KeygenSamplerCallersSpec.ec` |
| Authored relational, caller Hoare, and proof-only paired-call proof | `easycrypt/refinement/TargetKeygenSamplerCallers.ec` |
| Seed-expansion FIPS202 specification | `easycrypt/spec/KeygenSeedXofSpec.ec` |
| Extracted seed-expansion Hoare refinement | `easycrypt/refinement/TargetKeygenSeedXof.ec` |
| Consumer, leaf, caller, paired-attempt, and SHAKE initializer contracts sharing this gate | [`11-target-keygen-sampler-consumers.md`](11-target-keygen-sampler-consumers.md) |
| Separate actual mode-2 parent extraction boundary | [`12-target-keygen-mode2-parent-extraction.md`](12-target-keygen-mode2-parent-extraction.md) |
| Separate proof-only actual-parent-module sampler prefix | [`13-target-keygen-mode2-parent-refinement.md`](13-target-keygen-mode2-parent-refinement.md) |
| Compilation order | `manifests/keygen-sampler-callers-proof-files.txt` |
| Verification command | `scripts/verify-keygen-sampler-callers-proof.sh` |
| Retained summary | `logs/keygen-sampler-callers-proof-summary.txt` |

The unified generated target selects four roots: the three sampler callers and
`_kp_expand_seedbuf`. Its exact closure contains 25 generated files and 31
procedures. The authored files are a separate proof layer, not extraction
surfaces. The source ranges and inventory are documented in
[`09-target-keygen-sampler-callers-extraction.md`](09-target-keygen-sampler-callers-extraction.md).
The actual mode-2 parent is extracted separately as a 32-file, 56-procedure
closure; that gate establishes extraction and compilation only, not a semantic
parent theorem.

## Authored schedule model

`KeygenSamplerCallersSpec.CallerSpec` defines three procedures with integer
loop counters:

| Authored procedure | Schedule |
| --- | --- |
| `expand_matA` | rows by columns, base `(i * cols + j) * 256`, nonce `256 * i + j`, seed offset 0 |
| `expand_vecA` | `k` entries, base `i * 256`, nonce `256 * k + m + i`, seed offset 0 |
| `expand_eta` | `count` entries, base `i * 256`, nonce `start + i`, seed offset 32 |

The procedures convert these integer schedules to `W64` arguments and call the
same 8192-word uniform, 2048-word uniform, or 2048-word eta leaf used by the
generated caller.

## Relational theorems

The refinement file proves the following pRHL equivalences:

| Generated procedure | Authored procedure | Theorem |
| --- | --- | --- |
| `_kp_polymatkm_expand_matA` | `CallerSpec.expand_matA` | `expand_matA_relative_orchestration_equiv` |
| `_kp_polyveck_expand_vecA` | `CallerSpec.expand_vecA` | `expand_vecA_relative_orchestration_equiv` |
| `_kp_polyvec_expand_eta` | `CallerSpec.expand_eta` | `expand_eta_relative_orchestration_equiv` |

The loop invariants relate each generated `W64` counter, base, and nonce to
the corresponding authored integer expression. The leaf calls are discharged
with self-equivalence lemmas because both programs deliberately invoke the
same extracted leaf. Consequently, the result proves call order and argument
scheduling; it does not establish a separate leaf postcondition.

## Uniform matrix and vector exact partial correctness

`caller_uniform_values seed nonce blocks pairs` applies the exact strict
`< 64513` decoder to the first `pairs` little-endian candidates from `blocks`
SHAKE128 rate blocks. It fixes the caller seed offset to zero. The caller-level
stream predicates retain separate witnesses for each destination polynomial:

- `uniform_vector_stream8192` uses base `slot * 256` and nonce
  `256 * k + m + slot`; and
- `uniform_matrix_stream32768` uses base
  `(row * cols + col) * 256` and nonce `256 * row + col`.

`expand_vecA_stream_correct` proves the vector stream predicate directly for
the actual generated `_kp_polyveck_expand_vecA` under `0 <= k <= 8`. Its joint
postcondition also gives `uniform_vector_range8192`, which bounds all selected
coefficients, and `uniform_vector_frame8192`, which preserves every byte outside
the first `k * 256` words.

`expand_matA_stream_correct` proves the corresponding matrix predicates for the
actual generated `_kp_polymatkm_expand_matA` under nonnegative dimensions and
`rows * cols <= 32`. Its nested invariant records lexicographically visited
cells, preserving earlier exact prefixes through each later leaf's byte frame.
The final `uniform_matrix_range32768` and `uniform_matrix_frame32768`
postconditions cover all selected cells and preserve every byte outside the
first `rows * cols * 256` words.

`caller_uniform_seed_input_prefix` identifies positions `0..31` of each
specialized SHAKE128 input with bytes from the same raw `BArray128` at offset
zero. `mode2_matrix_uniform_nonce_input_tail` identifies positions 32 and 33 as
`[col, row]`; `mode2_vector_uniform_nonce_input_tail` identifies them as
`[3 + slot, 2]`. These are exact raw-input identities. They do not identify the
array with rho/`seedA` or with the output of `_kp_expand_seedbuf`.

## Proof-only mode-2 uniform pair

`CheckedMode2UniformPair.expand` is authored proof code. It calls the actual
generated matrix caller and vector caller with dimensions `(2, 3)`, passing the
same raw `BArray128` to both. `checked_mode2_uniform_pair_correct` composes both
exact stream, coefficient-range, and aggregate byte-frame contracts.

The wrapper is not `_keypair_full_m23`. Its theorem does not prove that the raw
array came from `_kp_expand_seedbuf`, that the actual parent supplies the same
array and dimensions, or that either rejection sampler terminates. The separate
`CheckedMode2ParentSamplerPrefix.run` observer closes those seed/dimension cuts
inside its proof-only first-attempt scope and proves probability-one
termination under explicit per-call endpoint certificates. It is still not
the actual parent.

## Eta vector exact partial correctness

`expand_eta_correct` proves a centered-range and word-frame contract directly
for the actual generated `_kp_polyvec_expand_eta`. `expand_eta_stream`
additionally proves `eta_vector_stream8192`: for every selected slot there
exists a `blocks >= 1` witness whose `caller_eta_values` list has
size 256 and equals the returned signed prefix at base `slot * 256`.
`caller_eta_values` fixes seed offset 32 and nonce `start + slot`.

`expand_eta_stream_correct` combines the exact stream, centered-range, and
outside-vector frame postconditions. The extension proof uses each new leaf's
`poly_frame8192` result to preserve all earlier exact polynomial prefixes. The
precondition requires a nonnegative integer `count` and enough `BArray8192`
capacity for `count * 256` words, restricting the caller to `0..8` polynomials.
These are ordinary Hoare partial-correctness theorems and do not prove that a
leaf or caller terminates.

## Proof-only mode-2 eta pair

`CheckedMode2EtaPair.expand` is authored proof code. It calls the actual
generated eta vector caller first with count three and then with count two over
the same input seed array, shifting the second start by three and the returned
nonce word by five. `checked_mode2_eta_pair_correct` composes both exact
vector-stream, centered-range, and outside-vector frame contracts.

Neither the wrapper nor its theorem is `_keypair_full_m23`. They do not
establish the upstream `_kp_expand_seedbuf` identity, actual retry-loop control,
singular-value rejection, or the later `egen - b0` adjustment.

## Pure arithmetic results

The authored schedule theory proves four groups of facts:

- `matrix_nonce_wordE`, `matrix_base_wordE`, `vector_nonce_wordE`, and the
  counter/base/nonce step lemmas connect the integer expressions to the exact
  `W64` operations used by the generated loops.
- `matrix_capacity`, `linear_capacity`, and `stride_regions_disjoint` prove
  generic integer bounds for `rows * cols <= 32` and `count <= 8`, plus
  disjoint 256-word linear regions. These are arithmetic facts, not array-frame
  theorems.
- The mode-2 address and region lemmas cover the 2-by-3 matrix and the linear
  vector layouts; the concrete schedule lemmas give matrix bases
  `0, 256, 512, 768, 1024, 1280`, matrix nonces
  `0, 1, 2, 256, 257, 258`, and vector bases `0, 256` with nonces `515, 516`.
- `mode2_eta_retry_schedule` gives slots `5 * retry` through
  `5 * retry + 4`. Matrix and vector low-16-bit lemmas give the exact bounded
  nonce values. `mode2_eta_nonce_low16` gives the eta nonce modulo 65536 under
  its explicit nonnegative-index and `< W64.modulus` preconditions. The
  proof-only paired wrapper agrees with this split for one modeled attempt;
  these facts still do not prove the complete `_keypair_full_m23` retry control
  flow.

## Reproduction

From `haetae-ref-easycrypt/`, run:

```sh
./scripts/verify-keygen-sampler-callers-proof.sh
```

The script first checks all pinned source hashes and regenerates the unified
four-root extraction to reject drift. It then compiles the generated target,
six authored specifications, and six authored refinements in manifest
order with `easycrypt compile -no-eco`. Finally, it rejects `admit`/`abort`
proof commands and axiom declarations in the authored files. This shared gate
now covers the caller schedule results documented here and the consumer,
whole-leaf, exact uniform-caller and eta-vector, proof-only paired-attempt,
SHAKE128/SHAKE256 initializer, and single-call squeeze serialization/frame
contracts plus the exact one-call 24-round lane-level Keccak-f transition,
byte/lane bridge, exact short-message padding states, and capacity-bounded
consecutive-block compositions documented in the
[sampler-consumer proof milestone](11-target-keygen-sampler-consumers.md).
It also covers the on-return equality of `_kp_expand_seedbuf` with the first
128 SHAKE256 bytes and the three named output-slice corollaries.
The generated finite uniform/eta consumers and all fixed-bound Keccak,
initializer, and squeeze procedures also have separate unconditional
losslessness lemmas; those do not by themselves prove whole-leaf termination.
For the whole leaves, the separate `uniform2048_leaf_progress_ll`,
`uniform8192_leaf_progress_ll`, and `eta2048_leaf_progress_ll` theorems supply
probability-one termination only when their respective explicit finite
progress certificates and exact memory/slice preconditions hold.

The authored uniform proofs additionally follow the actual four-call SHAKE128
prelude, the first consumer, and every later squeeze/consumer iteration. Under
an in-bounds 32-byte seed slice, the initial cuts record the four-step state,
four retained blocks, flat 672-byte prefix, outside-region frame, and exact
first-consumer decoding of up to 336 little-endian candidates. The
`consume2048_block168` and `consume8192_block168` theorems extend an existing
exact decoded prefix with the accepted values from an exact 168-byte block,
processing `0..84` pairs and stopping full or exhausted.

At the real loop boundary, the checked invariant has `buflen = 672` initially
and `buflen = 168` thereafter. Both values are even, so the generated
`off = buflen & 1` is zero, its carry-copy loop is empty, and every actual
squeeze writes exactly the next abstract SHAKE128 block at offset zero. The
exported `uniform2048_leaf_stream` and `uniform8192_leaf_stream` postconditions
then witness `blocks >= 4` and `0 <= pairs <= 84 * blocks`; the accepted values
among those first `pairs` candidates have size 256 and equal the stored decoded
prefix. These are finite Hoare partial-correctness facts, not by themselves
termination, losslessness, distribution, or arbitrary infinite-stream results.
The separate uniform pHoare theorems add only the explicit
`uniform_progress_prefix`-conditioned probability-one result. The caller
refinement additionally carries per-slot and per-cell finite witnesses through
both actual uniform callers and composes the mode-2 matrix/vector pair over one
raw input array.

The eta proof follows its different real control flow. Every squeeze writes the
next exact 136-byte SHAKE256 block at offset zero, replacing the previous buffer
contents while advancing the abstract state. `eta_consume2048_block136` proves
that one such block extends the incoming exact decoded prefix with five
low-to-high centered base-three digits for every byte below 243, contributes
nothing for a rejected byte, and applies the 256-value cap exactly, including
mid-byte truncation. `eta2048_leaf_stream` composes those blocks and consumers
through the generated 2048-word leaf and exports its finite 256-value decoded
prefix on termination under the theorem's seed-slice and
destination-capacity bounds. `expand_eta_stream` carries per-slot finite
block witnesses through the actual generated vector caller and uses each leaf
frame to preserve earlier slots. `checked_mode2_uniform_pair_correct` composes
the actual uniform matrix and vector calls with dimensions `(2, 3)`, exact seed
offset zero, and the named mode-2 nonce-input tails.
`checked_mode2_eta_pair_correct` then composes
count-three and count-two actual caller invocations inside its authored
proof-only wrapper.

The losslessness boundary is exact: all bounded uniform/eta consumers are
unconditional. The two actual uniform leaves are probability one only under a
concrete `uniform_progress_prefix` certificate, and the actual eta leaf is
probability one only under `eta_progress_prefix`. None of these theorems
establishes certificate existence for every seed/nonce, termination of a
caller or paired wrapper, or a probability distribution.

The retained 2026-07-22 full proof gate establishes the following inventory:

- 64 pinned inputs checked;
- zero drift across 25 generated theories and the exact 31-procedure
  inventory;
- 13 manifest entries (one generated target, six specifications, and six
  refinements);
- no proof holes and no axiom declarations; and
- terminal line `RESULT: PASS compiled=13 total=13 mode=-no-eco`.

## Explicit exclusions

This refinement does not prove:

- SHAKE128, SHAKE256, rejection-consumer, or sampler semantics from the
  caller-schedule equivalences themselves; the finite deterministic leaf and
  caller contracts are separate Hoare theorems;
- unconditional whole-leaf/caller termination, universal progress-certificate
  existence, uniformity, centered-trit distribution, independence, or other
  distributional properties; the bounded consumers are unconditionally
  lossless and all three actual leaf variants are certificate-conditionally
  probability one;
- source pointer separation or pointer memory safety; the uniform aggregate
  byte frames and eta vector word frame are proved only in the generated
  functional-array model;
- identification of the expanded slices with the paper's seed names. The
  proof-only parent-module prefix does connect exact `_kp_expand_seedbuf`
  output to the matrix, vector, and first-attempt eta calls, but only inside
  that observer;
- that the actual `_keypair_full_m23` shares the intended expanded seed,
  invokes those calls, or advances its retry counter. The older paired
  wrappers and the newer parent-module prefix verify authored observers, not
  the generated full parent;
- singular-value rejection or the later `egen - b0` adjustment; or
- correspondence to paper `expandA`, `expandS`, a public key-generation API,
  or a security-game distribution.

The separately checked deterministic layer proves uniform-consumer and
whole-uniform-leaf range/frame partial correctness, both exact uniform caller
contracts and their proof-only mode-2 pair, eta helper/consumer contracts, eta
whole-leaf centered-range/frame partial correctness, the exact eta vector
caller contracts and proof-only paired attempt above, certificate-conditioned
probability-one termination of all three actual leaf variants, and the exact
target-functional framing performed by the specialized SHAKE128 and SHAKE256
initializers. The squeeze
theorems prove the exact 24-round lane-level Keccak-f transition, rate-block
serialization, and output-buffer frame. `CheckedShakeBlocks` composes one
actual initializer with a capacity-bounded number of retained consecutive
blocks, while `shake128_seedbuf_four_blocks` specializes that proof-only
wrapper to the uniform prelude.

The leaf-specific proofs go further along the real sampler control flow. Exact
initial cuts and `consume*_first672` connect the first four blocks to the first
accepted prefix. The `consume*_block168` theorems, the reachable
`buflen in {672, 168}` invariant, and the resulting zero carry offset connect
each later actual squeeze and consumer to the next exact abstract block. The
conditional `uniform*_leaf_stream` postconditions export the final finite
256-value decoded prefix, although procedure-local state snapshots remain
internal. `expand_vecA_stream_correct` and `expand_matA_stream_correct` preserve
those per-polynomial results through the two generated caller loops. The eta
counterparts use `eta_consume2048_block136` and the
offset-zero overwrite invariant to export the corresponding capped finite
SHAKE256 decoded prefix from `eta2048_leaf_stream`; `expand_eta_stream` lifts it
through the actual eta vector caller, and `checked_mode2_eta_pair_correct`
composes two such calls in an authored proof-only wrapper. The standalone
seed-XOF theorem additionally identifies the extracted expansion output and
its three slices on return, while the separate 32-file/56-procedure parent gate
only extracts the actual mode-2 control flow. The separate proof-only
parent-module prefix now closes the first-attempt seed/slice-to-caller cut and
has probability-one termination under exact endpoint maps. The broad claim
that mode-2 sampler caller composition is functionally correct remains
`PARTIAL`: universal progress certificates, distributions, source-pointer
safety, actual `_keypair_full_m23` retry/downstream dataflow, and a semantic
theorem for that full parent remain open.
